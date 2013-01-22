// Copyright © Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)

#light

namespace Microsoft.SolverFoundation.FSharpDSL

module Compiler = 
    
    open System
    open System.Collections.Generic
    open Microsoft.SolverFoundation.Common
    open Microsoft.SolverFoundation.Solvers
    open Microsoft.FSharp.Quotations
    open Microsoft.SolverFoundation.FSharpDSL.Language
    
    type internal Variablebounds =
        | Lower of float
        | Upper of float
        | Equal of float
        | Box of (float * float)
    /// Represents an MSF linear programming solver, compiled from an F# expression
    type Solver(expr:Expr<bool>) = 
        /// Parsed F# expression
        let prog = expr |> Parse

        let (update, getGoal, getVariableValue, solver, allVariables) = 
            /// Compile the generated object expression to a Simplex Solver program
            match prog with
            | LinearProgram (vars, externalRefs, (goal, LinearFunction (goalCoeffVars), goalRef), constraints) -> 
                /// Allocate a new Simplex solver
                let solver = new SimplexSolver ()
                /// A function to convert a number into a rational number
                let rational x = Rational.op_Implicit (x:float)

                // Split off the integrality constraints
                let integralityConstraints, linearConstraints =
                    constraints
                    |> List.partition (function IntegralityConstraint _ -> true | _ -> false)
                    
                // Split the linear constraints into those comprised of one variable and those with more variables
                let singleVariableConstraints, otherConstraints = 
                    linearConstraints 
                    |> List.partition (fun constr ->
                        match constr with
                        | LowerBound (LinearFunction (coeffVars), _) ->
                            coeffVars.Length = 1 && (fst coeffVars.[0] = 1.0)
                        | UpperBound (LinearFunction (coeffVars), _) -> 
                            coeffVars.Length = 1 && (fst coeffVars.[0] = 1.0)
                        | EqualityConstraint (LinearFunction (coeffVars), _) -> 
                            coeffVars.Length = 1 && (fst coeffVars.[0] = 1.0)
                        | _ -> failwith "unreachable code path"
                    )
                /// Maps the single variable constraints into a dictionary for quick lookup
                let variableBounds = 
                    singleVariableConstraints
                    |> List.choose (function
                        | LowerBound (LinearFunction ([| (coeff, Some var) |]), b) ->
                            (var, Lower b) |> Some
                        | UpperBound (LinearFunction ([| (coeff, Some var) |]), b) -> 
                            (var, Upper b) |> Some
                        | EqualityConstraint (LinearFunction ([| (coeff, Some var) |]), b) -> 
                            (var, Equal b) |> Some
                        | _ -> None
                    )
                    |> Seq.groupBy fst
                    |> Seq.map (fun (var, boundsSeq) -> 
                        let upper = ref None
                        let lower = ref None
                        let equality = ref None
                        boundsSeq
                        |> Seq.iter (function
                            | _, Lower b -> lower := b |> Some
                            | _, Upper b -> upper := b |> Some
                            | _, Equal b -> equality := b |> Some
                            | _ -> ()
                        )
                        match !lower, !upper, !equality with
                        | None,     None,   Some e  -> var, Equal e
                        | Some l,   Some u, None    -> var, Box (l, u)
                        | Some l,   None,   None    -> var, Lower l
                        | None,     Some u, None    -> var, Upper u
                        | _ -> failwith "Can't have bounds and equality constraints on the same variable"
                    )
                    |> Map.ofSeq
                
                /// Stores a mapping of variables to Solver Foundation internal variable indices        
                let variableToIdx = new Dictionary<_,_> ()
                /// Stores a mapping of Solver Foundation internal variable indices to external references,
                /// one entry per scalar variable
                let externalRefToIdx = new ResizeArray<_> ()
                /// Stores a mapping of Solver Foundation internal variable indices to external references,
                /// one entry per array1D variable
                let externalRefToIdx1 = new ResizeArray<_> ()
                /// Stores a mapping of Solver Foundation internal variable indices to external references,
                /// one entry per array2D variable
                let externalRefToIdx2 = new ResizeArray<_> ()
                /// All MSF variables, with arrays unrolled
                let allVars = new ResizeArray<_>()
                
                // Add all variables to the solver (arrays and scalars)
                vars |> Set.iter (fun var ->
                    /// Adds a variable to the linear solver and to allVars,
                    /// and sets upper and lower bounds
                    let AddVariable (var) = 
                        let varIdx = ref 0
                        if solver.AddVariable (var.ToString(), varIdx) then
                            match variableBounds.TryFind(var) with
                            | Some (Upper u) ->
                                solver.SetBounds (!varIdx, Rational.NegativeInfinity, u |> rational)
                            | Some (Lower l) ->
                                solver.SetBounds (!varIdx, l |> rational, Rational.PositiveInfinity)
                            | Some (Box (l, u)) ->
                                solver.SetBounds (!varIdx, l |> rational, u |> rational)
                            | Some (Equal (e)) ->
                                solver.SetBounds (!varIdx, e |> rational, e |> rational)
                            | _ -> ()
                            variableToIdx.Add(var, !varIdx)
                        else
                            failwith (sprintf "Unable to add variable %s" (var.ToString()))
                        allVars.Add var
                        !varIdx
                    match var with
                    | MsfScalar s -> 
                        let idx = AddVariable (var)
                        match externalRefs.Scalar.TryFind s with
                        | None      -> ()
                        | Some r    -> externalRefToIdx.Add (idx, r)
                    | MsfArray1 (s, length) ->
                        let idx = Array.init length (fun i -> AddVariable (MsfArray1(s, i)))
                        match externalRefs.Array1.TryFind s with
                        | None      -> ()
                        | Some r    -> externalRefToIdx1.Add (idx, r)
                    | MsfArray2 (s, length1, length2) ->
                        let idx = Array2D.init length1 length2 (fun i j -> AddVariable (MsfArray2(s, i, j)))
                        match externalRefs.Array2.TryFind s with
                        | None      -> ()
                        | Some r    -> externalRefToIdx2.Add (idx, r)
                                                        
                )
                
                // Sets the integrality constraints
                integralityConstraints
                |> List.iter (function
                    | IntegralityConstraint varName ->
                        let mutable idx = 0
                        let found = variableToIdx.TryGetValue (varName, &idx)
                        if not found then
                            failwith (sprintf "Variable %s is undeclared" (varName.ToString()))
                        solver.SetIntegrality(idx, true)
                    | _ -> ()
                )

                // Adds the linear constraints to the solver
                otherConstraints
                |> Seq.iteri (fun i c ->
                    let lower, upper, linFunc = 
                        match c with
                        | UpperBound(LinearFunction lf, b)          -> Rational.NegativeInfinity,   b |> rational,              lf
                        | LowerBound(LinearFunction lf, b)          -> b |> rational,               Rational.PositiveInfinity,  lf
                        | EqualityConstraint(LinearFunction lf, b)  -> b |> rational,               b |> rational,              lf
                        | _ -> failwith "unreachable code path"
                    let rowIdx = ref 0
                    let varIdx = ref 0
                    let biasTerm = ref Rational.Zero
                    if solver.AddRow ((sprintf "constraint%d" i), rowIdx) then 
                        linFunc
                        |> Array.iter (function
                            | coeff, None       -> 
                                biasTerm := coeff |> rational
                            | coeff, Some var   -> 
                                if variableToIdx.TryGetValue(var, varIdx) then
                                    solver.SetCoefficient (!rowIdx, !varIdx, rational coeff)
                                else
                                    failwith (sprintf "Variable %s is undeclared" (var.ToString()))
                        )
                        solver.SetBounds (!rowIdx, lower - !biasTerm, upper - !biasTerm) 
                    else
                        failwith "Cannot add constraint" 
                )

                // Adds the goal to the solver
                let goalIdx = ref 0
                if solver.AddRow ("goal", goalIdx) then 
                    goalCoeffVars 
                    |> Array.iter (function
                        | coeff, None       ->
                            failwith "Bias terms are not allowed in the objective (goal) function"
                        | coeff, Some var   ->
                            solver.SetCoefficient (!goalIdx, variableToIdx.[var], rational coeff)
                    )
                    solver.AddGoal (!goalIdx, 1, (goal = Minimise)) |> ignore
                else
                    failwith "Cannot add goal" 
                
                /// Read out the objective function (goal) of the solver    
                let getGoal = fun () -> solver.GetValue (!goalIdx)
                /// Read the value of an MSF variable
                let getVariableValue = 
                    fun var -> 
                        let idx = ref 0
                        if variableToIdx.TryGetValue(var, idx) then
                            solver.GetValue(!idx)
                        else
                            failwith (sprintf "Invalid variable %s (variable name invalid or index out of bounds)" (var.ToString()))

                /// Computes the update function for all externally referenced variables
                let update = fun () -> 
                    externalRefToIdx
                    |> Seq.iter (fun (idx,vRef) -> 
                        vRef := solver.GetValue (idx) |> Rational.op_Explicit
                    )
                    externalRefToIdx1
                    |> Seq.iter (fun (idx,vRef) -> 
                        vRef := 
                            idx
                            |> Array.map (fun i -> (solver.GetValue(i) |> Rational.op_Explicit) : float)
                    )
                    externalRefToIdx2
                    |> Seq.iter (fun (idx,vRef) -> 
                        vRef :=
                            idx
                            |> Array2D.map (fun i -> (solver.GetValue(i) |> Rational.op_Explicit) : float)
                    )
                    match goalRef with
                    | None      -> ()
                    | Some r    -> r := (getGoal() |> Rational.op_Explicit)
                    
                (update, getGoal, getVariableValue, solver, allVars)
            //| _ -> failwith "This function can only compile linear programs"            
                
        let vars = match prog with LinearProgram (vars, _, _, _) -> vars
        
        /// Solves the simplex, by calling Microsoft Solver Foundation
        member this.Solve () = 
            solver.Solve ([| SimplexSolverParams () |]) |> ignore
            update ()
        /// Returns the solution quality of the simplex/MIP solver
        member this.SolutionQuality = solver.SolutionQuality
        /// Returns the report from the simplex/MIP solver
        member this.GetReport reportType = solver.GetReport reportType
        /// Returns the actual solver object that has been comppiled from the expression
        member this.Solver = solver
        /// Gets the value of the objective function 
        member this.ObjectiveFunction with get () = getGoal ()
        /// Gets the value of a variable
        member this.Item with get name = getVariableValue name
        /// Returns a sequence of all variables (decisions) of the linear program
        /// Note that array variables will be unrolled, and a variable per array element
        /// will be returned
        member this.Variables = 
            allVariables
            |> Seq.readonly
