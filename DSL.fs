// Copyright © Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)

#light

namespace Microsoft.SolverFoundation.FSharpDSL

module Language =
    
    open System
    open System.Collections.Generic
    open Microsoft.FSharp.Quotations
    open Microsoft.FSharp.Quotations.Patterns
    open Microsoft.FSharp.Quotations.DerivedPatterns
    open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions

    /// A type for Solver Foundation variables, declared in the quotation
    type MsfVariable = 
        /// Scalar variable, identified by its name
        | MsfScalar of string
        /// 1D array of variables, represented by name and index
        | MsfArray1 of string * int
        /// 2D array of variables, represented by name and indexes
        | MsfArray2 of string * int * int
        override this.ToString() = 
            match this with
            | MsfScalar s               -> s
            | MsfArray1 (s, idx)        -> sprintf "%s.[%i]" s idx
            | MsfArray2 (s, idx1, idx2) -> sprintf "%s.[%i,%i]" s idx1 idx2
        member this.Name = 
            match this with
            | MsfScalar s           -> s
            | MsfArray1 (s, _)      -> s
            | MsfArray2 (s, _, _)   -> s

    /// Stores mappings from scalar, 1D and 2D array variables to external references
    type internal ExternalVariableMap =
        { 
            Scalar  : Map<string,float ref>
            Array1  : Map<string,float [] ref>
            Array2  : Map<string,float [,] ref>
        }
        
    /// The internal language that represents valid optimisation problems
    type internal OptimisationProblem = 
        /// A linear program is an optimisation problem with linear objective function and linear constraints
        | LinearProgram of (Set<MsfVariable> * ExternalVariableMap * (Goal * LinearFunction * float ref option) * LinearConstraint list)
    and internal 
        /// Bounds on variables
        Bounds = Bounds of (float * float) 
    and internal 
        /// A lower-bound constraint
        LinearConstraint = 
        | LowerBound of LinearFunction * float
        /// An upper-bound constraint
        | UpperBound of LinearFunction * float
        /// An equality constraint
        | EqualityConstraint of LinearFunction * float
        /// An integrality constraint (real-valued variable that takes on only integral values)
        | IntegralityConstraint of MsfVariable
    and internal 
        /// A linear function is an array of weighting coefficients and variables
        /// Bias term is represented by a (bias, None) pair
        LinearFunction = LinearFunction of (float * MsfVariable option) array
    /// The goal of the optimisation
    and internal Goal = 
        /// Minimise the objective function
        | Minimise
        /// Maximise the objective function
        | Maximise

    /// General error message when the expression to be quoted are used directly
    let private fail () = failwith "Not useable directly."
    
    /// Defines a optimization variable, possibly with units-of-measure
    let var<[<Measure>] 'u> () : float<'u> = fail ()
    /// Defines an external variable, possibly with units-of-measure
    let varinto<[<Measure>] 'u> (xr:float<'u> ref) : float<'u> = fail ()
    /// Defines a minimisation problem 
    let minimise<[<Measure>] 'u> (z : float<'u>) : unit = fail ()
    /// Defines a minimisation problem, with result written into an external reference
    let minimiseinto<[<Measure>] 'u> (gr: float<'u> ref) (z : float<'u>) : unit = fail ()
    /// Defines a maximisation problem 
    let maximise<[<Measure>] 'u> (z : float<'u>) : unit = fail ()
    /// Defines a maximisation problem, with result written into an external reference
    let maximiseinto<[<Measure>] 'u> (gr: float<'u> ref) (z : float<'u>) : unit = fail ()
    /// Defines a constraint set
    let where (constr : bool list) : bool = fail ()
    /// Defines a 1-dimensional array of variables.
    /// This allocates 1 variable per sequence element (Seq.length elements in total).
    /// You need to ensure that the sequence is a valid sequence for indexing arrays, 
    /// that is, it needs to go from 0 .. Seq.length - 1 to make sense!
    let vararray1<[<Measure>] 'u> (i1:seq<int>) : float<'u> [] = fail () 
    /// Defines a 1-dimensional array of variables, bound to an external reference.
    /// This allocates 1 variable per sequence element (Seq.length elements in total).
    /// You need to ensure that the sequence is a valid sequence for indexing arrays, 
    /// that is, it needs to go from 0 .. Seq.length - 1 to make sense!
    let vararray1into<[<Measure>] 'u> (xr:float<'u>[] ref) (i1:seq<int>) : float<'u> [] = fail () 
    /// Defines a 2-dimensional array of variables
    /// This allocates 1 variable per sequence element along each dimension 
    /// (Seq.length i1 * Seq.length i2 elements in total). You need to ensure that the sequences
    /// are valid sequence for indexing arrays, that is, they needs to go from 
    /// 0 .. Seq.length - 1 to make sense!
    let vararray2<[<Measure>] 'u> (i1:seq<int>,i2:seq<int>) : float<'u> [,] = fail()
    /// Defines a 2-dimensional array of variables, bound to an external reference
    /// This allocates 1 variable per sequence element along each dimension 
    /// (Seq.length i1 * Seq.length i2 elements in total). You need to ensure that the sequences
    /// are valid sequence for indexing arrays, that is, they needs to go from 
    /// 0 .. Seq.length - 1 to make sense!
    let vararray2into<[<Measure>] 'u> (xr:float<'u>[,] ref) (i1:seq<int>) (i2:seq<int>) : float<'u> [,] = fail () 
    /// Returns true if the function returns true when evaluated on all elements of the sequence
    /// (equivalent to Seq.forall pred range)
    let foreach (range:seq<int>) (pred: int -> bool) : bool = fail ()
    /// Sums over a sequence (equivalent to Seq.sumBy pred range)
    let sum<[<Measure>] 'u>  (range: seq<int>) (f:int -> float<'u>) : float<'u> = fail()
    /// Integrality constraint
    let integral<[<Measure>] 'u> (v: float<'u>) : bool = fail()

    /// This function takes an F# expression and computes the underlying optimisation expression
    let internal Parse (expr:Expr<bool>) = 
        /// Gets the values of a sequence expression
        let rec GetRange (expr : Expr) =
            let error() = failwith "Unable to extract sequence value from range expression"
            match expr with
            | PropertyGet (_, v, _) ->
                // we get the method of the enumeration...
                let get = v.GetGetMethod()
                // and invoke it...
                let obj = get.Invoke (null, [| |]) 
                // and cast the result (an object)
                match obj with 
                | :? seq<int> as res -> res
                | _ -> error()
            | Value (s, ty) ->
                match s with 
                | :? seq<int> as x ->  x
                | _ -> error()
            | Coerce (sub, ty) -> 
                GetRange sub
            | _ ->  error()
        /// Maps from the name of a scalar variable to its associated reference
        let extScalars = new Dictionary<_,_>()
        /// Maps from the name of a 1D array variable to its associated reference
        let extArray1 = new Dictionary<_,_>()
        /// Maps from the name of a 2D array variable to its associated reference
        let extArray2 = new Dictionary<_,_>()
        /// Parses a block of variable definitions
        let rec ParseVariableDeclarations = function
            | Let (v,value,qCont) ->
                let newVar = 
                    match value with 
                    | SpecificCall <@ var @> (obj,_,[])              -> 
                        MsfScalar v.Name
                    | SpecificCall <@ varinto @> (obj,_,[Value (x,ty)]) when ty = typeof<float ref>  -> 
                        extScalars.Add(v.Name, (x :?> float ref))
                        MsfScalar v.Name
                    | SpecificCall <@ vararray1 @> (obj,_,[range]) -> 
                        let rangeSeq = GetRange range
                        MsfArray1 (v.Name, Seq.length rangeSeq)
                    | SpecificCall <@ vararray1into @> (obj,_,[Value (x,ty); range]) when ty = typeof<float[] ref> -> 
                        extArray1.Add(v.Name, (x :?> float[] ref))
                        let rangeSeq = GetRange range
                        MsfArray1 (v.Name, Seq.length rangeSeq)
                    | SpecificCall <@ vararray2 @> (obj,_,[range1; range2]) -> 
                        let range1Seq = GetRange range1
                        let range2Seq = GetRange range2
                        MsfArray2 (v.Name, Seq.length range1Seq, Seq.length range2Seq)
                    | SpecificCall <@ vararray2into @> (obj,_,[Value (x,ty); range1; range2]) when ty = typeof<float[,] ref> -> 
                        extArray2.Add(v.Name, (x :?> float[,] ref))
                        let range1Seq = GetRange range1
                        let range2Seq = GetRange range2
                        MsfArray2 (v.Name, Seq.length range1Seq, Seq.length range2Seq)
                    | _ -> failwith "Unrecognized form of variable declaration."
                let (sub: Set<MsfVariable>, goalExpr, whereExpr) = ParseVariableDeclarations qCont
                if sub.Contains(newVar) then
                    failwith "Duplicate variable definition"
                (sub.Add newVar, goalExpr, whereExpr)
            | Sequential (goalExpr,whereExpr) -> (Set.empty, goalExpr, whereExpr)
            | _ -> failwith "The expression should be of the form 'let x = var (\"x\") ... in minimise (3.0 * x ...); where [x > 0.0; x < 1.0; ...]'"

        /// Parses the objective function and constraints, based on information about the 
        /// Solver Foundation variables that had been declared in the ODSL
        let ParseObjectiveFunctionAndConstraints (declaredNames: Set<string>) objExpr whereExpr =
            /// Matches a double constant
            let (|DoubleConst|_|) expr = 
                match expr with 
                | Double (d)    
                    -> Some d 
                | Value (x,ty) when ty = typeof<double> 
                    -> Some (x :?> double)
                | _ -> None
            /// Matches a one-dimensional array of constants
            let (|CstArrayGet1|_|) expr =
                match expr with
                | SpecificCall <@ GetArray @> (_,_, [Value (obj,ty) ; idx]) when ty = typeof<float[]> ->
                    Some ((obj :?> float[]), idx)
                | _ -> None
            /// Matches a 2-dimensional array of constants
            let (|CstArrayGet2|_|) expr =
                match expr with
                | SpecificCall <@ GetArray2D @> (_,_, [Value (obj,ty) ; idx1; idx2]) when ty = typeof<float[,]>  ->
                       Some ((obj :?> float[,]), idx1, idx2)
                | _ -> None
            /// Matches an integer constant
            let (|IntConst|_|) expr = 
                match expr with 
                | Int32 (d)    
                    -> Some d 
                | Value (x,ty) when ty = typeof<int> 
                    -> Some (x :?> int)
                | _ -> None

            /// Parses a linear function expression 
            let rec ParseLinearFunction (rangeBindings:Map<_,_>) expr = 
                /// Matches an integer index, relative to the current bindings
                let (|IntegerIndex|_|) expr =
                    match expr with
                    | IntConst(idx) -> 
                        Some idx
                    | Var(v) -> 
                        match rangeBindings.TryFind(v.Name) with
                        | Some value    -> Some value
                        | None          -> failwith (sprintf "Array index %s must be declared locally in a foreach or sum operation" v.Name)
                    | _ -> None
                /// Matches a variable expression (scalar, array 1D or array 2D Msf variables)
                let (|MsfVariable|_|) expr = 
                    match expr with 
                    // A single variable
                    | Var (v) when declaredNames.Contains(v.Name) -> 
                        MsfScalar v.Name |> Some
                    // A  1D array variable, indexed by a constant or locally bound variable
                    | SpecificCall <@ GetArray @> (_,_, [Var(v) ; IntegerIndex(idx)]) when declaredNames.Contains(v.Name) ->
                        MsfArray1 (v.Name, idx) |> Some
                    // A  2D array variable, indexed by a constant or locally bound variable
                    | SpecificCall <@ GetArray2D @> (_,_, [Var(v) ; IntegerIndex(idx1); IntegerIndex(idx2)]) when declaredNames.Contains(v.Name) ->
                        MsfArray2 (v.Name, idx1, idx2) |> Some
                    | _ -> None
                /// Matches a constant expression, either explicitly written down or by accessing an array
                let (|ScalarOrArrayConstant|_|) expr = 
                    match expr with 
                    | DoubleConst d -> 
                        Some d
                    | CstArrayGet1 (cst, IntegerIndex(idx)) -> 
                        Some cst.[idx]
                    | CstArrayGet2 (cst, IntegerIndex(idx1), IntegerIndex(idx2)) ->
                        Some cst.[idx1, idx2]
                    | _ -> None
                    
                match expr with
                | SpecificCall <@ (*) @> (_,_,[ScalarOrArrayConstant c; MsfVariable v]) -> 
                    [ (c, Some v) ]
                | SpecificCall <@ (*) @> (_,_,[MsfVariable v; ScalarOrArrayConstant c]) -> 
                    [ (c, Some v) ]
                | SpecificCall <@ (+) @> (_,_, [l;r])     -> 
                    ParseLinearFunction rangeBindings l
                    |> List.append (ParseLinearFunction rangeBindings r)
                | SpecificCall <@ (-) @> (_,_, [l;r])     ->
                    ParseLinearFunction rangeBindings r
                    |> List.map (fun (weight, var) -> (-weight, var))
                    |> List.append (ParseLinearFunction rangeBindings l)
                | SpecificCall <@ sum @> (_,_, [range ; Lambda(arg, body)])  -> 
                    let rangeValues = GetRange range
                    [
                        for i in rangeValues do
                            if rangeBindings.ContainsKey arg.Name then
                                failwith "Arguments of lambda expressions in nested sum/foreach expressions must have distinct names"
                            let updatedBindings = rangeBindings.Add(arg.Name, i)
                            yield! (ParseLinearFunction updatedBindings body)
                    ]
                | MsfVariable(v) -> [ (1.0, Some v) ]
                | DoubleConst d -> [ (d, None) ]
                | _ -> failwith (sprintf "Invalid operator in a linear function expression: %A" expr)

            /// Collect all the weights for all unique variables
            let CompressLinearFunction lf =
                let vars = new Dictionary<_,_> ()
                let weight = ref 0.0
                lf
                |> List.iter (fun (curWeight,var) -> 
                    if vars.TryGetValue (var, weight) then
                        vars.[var] <- !weight + curWeight
                    else
                        vars.Add (var, curWeight)
                )
                // Return an array of variable * coeff pairs
                vars 
                |> Seq.map (fun kvp -> (kvp.Value,kvp.Key))
                |> Seq.toArray
                |> LinearFunction
                    
            let ParseAndCompressLinearFunction rangeBindings =
                ParseLinearFunction rangeBindings 
                >> CompressLinearFunction
            
            /// Parses the objective function definition 
            let ParseObjectiveFunction goalExpr = 
                match goalExpr with 
                | SpecificCall <@ minimise @> (_,_,[obj])   -> 
                    (Minimise, ParseAndCompressLinearFunction Map.empty obj, None)
                | SpecificCall <@ maximise @> (_,_,[obj])   -> 
                    (Maximise, ParseAndCompressLinearFunction Map.empty obj, None)
                | SpecificCall <@ minimiseinto @> (_,_,[Value (x,ty); obj]) when ty = typeof<float ref> -> 
                    (Minimise, ParseAndCompressLinearFunction Map.empty obj, Some(x :?> float ref))
                | SpecificCall <@ maximiseinto @> (_,_,[Value (x,ty); obj]) when ty = typeof<float ref> -> 
                    (Maximise, ParseAndCompressLinearFunction Map.empty obj, Some(x :?> float ref))
                | _ -> failwith "Goals must be of the form 'minimise (3.0 * x + ...)' or 'maximise (3.0 * x + ...)'."
                
            /// Parses the WHERE clause
            let ParseConstraints whereExpr = 
                /// Error text that gets thrown in case a variable definition cannot be parsed
                let error () = failwith "Constraint must be of the form 'where [x > 0.0; x < 1.0; ...]'."
                
                /// Gets a list of Boolean expressions
                let rec GetBoolExprList expr = 
                    match expr with
                    | NewUnionCase (ty, (hd::tl)) ->
                        if ty.DeclaringType = typeof<bool list> && ty.Name = "Cons" then
                            hd :: (tl |> List.map GetBoolExprList |> List.concat)
                        else
                            failwith "List of constraints must only contain boolean expressions"
                    | _ -> [] 
            
                /// Parses a constraint, with resolving bindings to identifiers declared locally in foreach or sum expressions
                let rec ConvertConstraint (rangeBindings: Map<_,_>) expr = 
                    /// Matches an integer index, relative to the current bindings
                    let (|IntegerIndex|_|) expr =
                        match expr with
                        | IntConst(idx) -> 
                            Some idx
                        | Var(v) -> 
                            match rangeBindings.TryFind(v.Name) with
                            | Some value    -> Some value
                            | None          -> failwith (sprintf "Array index %s must be declared locally in a foreach or sum operation" v.Name)
                        | _ -> None
                    /// Matches a variable expression (scalar, array 1D or array 2D Msf variables)
                    let (|MsfVariable|_|) expr = 
                        match expr with 
                        // A single variable
                        | Var (v) when declaredNames.Contains(v.Name) -> 
                            MsfScalar v.Name |> Some
                        // A  1D array variable, indexed by a constant or locally bound variable
                        | SpecificCall <@ GetArray @> (_,_, [Var(v) ; IntegerIndex(idx)]) when declaredNames.Contains(v.Name) ->
                            MsfArray1 (v.Name, idx) |> Some
                        // A  2D array variable, indexed by a constant or locally bound variable
                        | SpecificCall <@ GetArray2D @> (_,_, [Var(v) ; IntegerIndex(idx1); IntegerIndex(idx2)]) when declaredNames.Contains(v.Name) ->
                            MsfArray2 (v.Name, idx1, idx2) |> Some
                        | _ -> None
                    /// Recognizes if the left or right-hand side evaluates to a constant
                    let rec (|ConstantSide|_|) expr = 
                        match expr with
                        | DoubleConst d -> 
                            Some d
                        | CstArrayGet1 (tab, IntegerIndex(idx)) -> 
                            Some (tab.[idx])
                        | CstArrayGet2 (tab, IntegerIndex idx1, IntegerIndex idx2) -> 
                            Some (tab.[idx1, idx2])
                        | _ -> None
                    match expr with
                    | SpecificCall <@ (>=) @> (_,_,[l; ConstantSide lowerBound]) ->
                        [ LowerBound (ParseAndCompressLinearFunction rangeBindings l, lowerBound) ]
                    | SpecificCall <@ (>=) @> (_,_,[ConstantSide upperBound; r]) ->
                        [ UpperBound (ParseAndCompressLinearFunction rangeBindings r, upperBound) ]
                    | SpecificCall <@ (<=) @> (_,_,[l; ConstantSide upperBound]) ->
                        [ UpperBound (ParseAndCompressLinearFunction rangeBindings l, upperBound) ]
                    | SpecificCall <@ (<=) @> (_,_,[ConstantSide lowerBound; r]) ->
                        [ LowerBound (ParseAndCompressLinearFunction rangeBindings r, lowerBound) ]
                    | SpecificCall <@ (=) @> (_,_,[l; ConstantSide equ]) ->
                        [ EqualityConstraint (ParseAndCompressLinearFunction rangeBindings l, equ) ]
                    | SpecificCall <@ (=) @> (_,_,[ConstantSide equ; r]) ->
                        [ EqualityConstraint (ParseAndCompressLinearFunction rangeBindings r, equ) ]
                    | SpecificCall <@ foreach @>  (_,_,[range; Lambda(arg, body)]) ->
                        let rangeValues = GetRange range
                        [
                            for i in rangeValues do
                                if rangeBindings.ContainsKey arg.Name then
                                    failwith "Arguments of lambda expressions in nested sum/foreach expressions must have distinct names"
                                let updatedBindings = rangeBindings.Add(arg.Name, i)
                                yield! (ConvertConstraint updatedBindings body)
                        ]
                    | SpecificCall <@ integral @> (_,_, [MsfVariable(v)]) -> 
                        [ IntegralityConstraint(v) ]
                    | _ -> error()

                match whereExpr with
                | SpecificCall <@ where @> (_,_,[expr])   ->
                    GetBoolExprList expr 
                    |> List.map (ConvertConstraint Map.empty)
                    |> List.concat
                | _ -> error ()
                
            (ParseObjectiveFunction objExpr, ParseConstraints whereExpr)

        // First get all the variable defintions
        let (declaredVariables, goalExpr,whereExpr) = ParseVariableDeclarations expr.Raw
        let declaredNames = 
            declaredVariables
            |> Set.map (fun v -> v.Name)
        // Now get the minimise function and the constraints
        // Need to know the names of the declared variables here, to be able to distinguish between
        // locally declared MSF variables and those that refer to, for example, constants declared outside the DSL
        let (goalParts, linearConstraints) = 
            ParseObjectiveFunctionAndConstraints declaredNames goalExpr whereExpr
        let Dict2Map (d: Dictionary<_,_>) =
            d.Keys
            |> Seq.map (fun i -> (i, d.[i]))
            |> Map.ofSeq
        // The mapping from internal to external variables
        let externalVars = 
            { 
                Scalar = extScalars |> Dict2Map
                Array1 = extArray1 |> Dict2Map
                Array2 = extArray2 |> Dict2Map
            }
        LinearProgram (declaredVariables, externalVars, goalParts, linearConstraints)
        