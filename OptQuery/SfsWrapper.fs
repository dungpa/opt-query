// Copyright © Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)

#light

namespace Microsoft.SolverFoundation

module SfsWrapper =

    open Microsoft.FSharp
    open Microsoft.SolverFoundation.Services
    open Microsoft.SolverFoundation.Common
    open System.Collections.Generic
    open System
    
    /// Distinguishes between the major SFS solvers
    type SolverDirectives = 
        | ConstraintProgramming
        | Simplex
        | InteriorPointMethod
        
    
    /// Describes an SFS constraint
    type SfsConstraint (c: Constraint) =
        /// The wrapped SFS constraint
        member this.Constraint with get () = c
        /// The name of the constraint
        member this.Name with get () = c.Name
        /// Outputs the constraint
        override this.ToString() = 
            c.ToString()
        
    /// Describes an SFS objective function (goal)
    type SfsGoal (g: Goal) = 
        /// The wrapped SFS goal
        member this.Goal with get () = g
        /// The name of the goal
        member this.Name with get () = g.Name
            
        /// Outputs the goal
        override this.ToString() = 
            g.ToString()

    /// Describes an SFS objective function (goal) that takes on integer values
    /// and has a unit-of-measure
    type SfsIntGoal<[<Measure>] 'u> (g: Goal) = 
        inherit SfsGoal(g)

        /// Returns the integer value assigned to the goal in the current solution
        member this.Value = 
            g.ToInt32() 
            |> unbox<int<'u>>

            
    /// Describes an SFS objective function (goal) that takes on real values
    /// and has a unit-of-measure
    type SfsRealGoal<[<Measure>] 'u> (g: Goal) =
        inherit SfsGoal(g)
    
        /// Returns the float value assigned to the goal in the current solution
        member this.Value =  
            g.ToDouble() 
            |> unbox<float<'u>>

        
    /// Describes a Solver Foundation Services term that can represent
    /// variables, constants, or more complex real/integer/Boolean expressions
    type SfsTerm (m : SfsModel, d : Term) =

        /// The actual SFS term
        member this.Term with get() = d
        
        /// The model in which the term was created
        member this.Model with get() = m
        
        /// Outputs the actual SFS term
        override this.ToString() = this.Term.ToString()

        /// Checks whether the two terms were created in the same model.
        /// Throws a FailureException if that is not the case
        static member CheckModels (l: #SfsTerm, r: #SfsTerm) =
            // this is a temporary solution - 
            // strings should be resourced / localized
            if not (System.Object.ReferenceEquals(l.Model, r.Model)) then
                failwith "Terms do not belong to the same model"    

            
    /// Describes a Solver Foundation Services symbolic variable that is linked to 
    /// an F# discriminated union type.
    /// The discriminated union type must only have argumentless constructors
    /// for this to work. If not, an exception is thrown at runtime
    and SfsSymbolicVariable<'a>  (m : SfsModel, d : Decision) =
        inherit SfsTerm(m, d)
        
        /// Internal cache for the SFS domain for the given F# type
        [<DefaultValue>]
        static val mutable private CachedDomain : Domain
        /// Internal cache for the constructors for the given F# type, indexed by their name
        [<DefaultValue>]
        static val mutable private CachedValues : Map<string,'a>

        /// The name of the variable
        member this.Name with get () = d.Name
        
        /// Returns the SFS domain representation for the given F# type
        // Static members don't work here for some reason - each call to Domain then
        // creates a new Domain object, thus solved with a static mutable
        static member Domain =
            let ty = typeof<'a>
            if not (Reflection.FSharpType.IsUnion ty) then
                failwith "Symbolic variables can only be created from F# discriminated union types"
            let unionCases = ty |> Reflection.FSharpType.GetUnionCases
            let hasArgumentlessConstructors =
                unionCases
                |> Array.forall (fun case -> case.GetFields().Length = 0)
            if not hasArgumentlessConstructors then
                failwith "Symbolic variables can only be created from discriminated union types with argumentless constructors"
            if SfsSymbolicVariable<'a>.CachedDomain = null then
                /// The names of the constructors
                let names = unionCases |> Array.map (fun case -> case.Name)
                // The SFS domain is just the set of constructor names, passed as integers
                SfsSymbolicVariable<'a>.CachedDomain <- Domain.Enum(names)
                /// Pre-generate a value for each case of the union type, index it by the constructor name
                let namedValues = 
                    unionCases
                    |> Array.map (fun case -> 
                        let value = Reflection.FSharpValue.PreComputeUnionConstructor case [| |]
                        (case.Name, unbox<'a> value)
                    )
                    |> Map.ofArray
                SfsSymbolicVariable<'a>.CachedValues <- namedValues
            SfsSymbolicVariable<'a>.CachedDomain
                
        /// Returns the value of the symbolic variable
        member this.Value = 
            SfsSymbolicVariable<'a>.CachedValues.Item(d.GetString())
        /// Returns the value of the symbolic variable, or None if it has not been assigned yet
        member this.TryGetValue () =        
            try 
                this.Value |> Some
            with
            | :? KeyNotFoundException -> None
                        
        /// Infix equality
        static member ( ==== ) (l: SfsSymbolicVariable<'a>, r: SfsSymbolicVariable<'a>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Equal [| l; r |]

        /// Infix inequality
        static member ( <<>> ) (l: SfsSymbolicVariable<'b>, r: SfsSymbolicVariable<'b>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.AllDifferent [| l; r |]

            
    /// Describes a Solver Foundation Services term that takes on Boolean values
    and SfsBooleanTerm (m : SfsModel, d : Term) =
        inherit SfsTerm(m, d)

        /// Logical and
        static member ( &&&& ) (l: SfsBooleanTerm, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.And [| l ; (r :> SfsBooleanTerm) |]

        /// Logical or
        static member ( |||| ) (l: SfsBooleanTerm, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Or [| l ; (r :> SfsBooleanTerm) |]

        /// Logical implication 
        static member ( ==>> ) (l: #SfsBooleanTerm, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Or [| m.Not l ; r |]
        
        
    /// Describes a Solver Foundation Services variable that the solvers can set
    and SfsBooleanVariable (m : SfsModel, d : Decision) =
        inherit SfsBooleanTerm(m, d)
        /// The name of the variable
        member this.Name with get () = d.Name
        /// Returns the value of the boolean variable
        member this.Value = (d.GetDouble() >= 0.5)
        /// Returns the value of the boolean variable, or None if it has not been assigned yet
        member this.TryGetValue () =        
            try 
                this.Value |> Some
            with
            | :? KeyNotFoundException -> None

        /// Logical and
        static member ( &&&& )(l: SfsBooleanVariable, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.And [| l ; (r :> SfsBooleanTerm) |]
        /// Logical and
        static member ( &&&& )(l: #SfsBooleanTerm, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.And [| l ; (r :> SfsBooleanTerm) |]


        /// Logical or
        static member ( |||| ) (l: SfsBooleanVariable, r: #SfsBooleanTerm) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Or [| l ; (r :> SfsBooleanTerm) |] 


    /// Describes a Solver Foundation Services term that takes on integer values
    and SfsIntTerm<[<Measure>] 'u> (m : SfsModel, d : Term) =
         
        inherit SfsTerm(m, d) 
        
        /// Infix addition for integer terms
        static member ( + ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            l.Model.Sum [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix addition for integer terms
        static member ( + )(ll: int<'u>, r: #SfsIntTerm<'u>) =
            let l = r.Model.CreateIntConstant ll
            r.Model.Sum [| l; (r :> SfsIntTerm<'u>) |]
        /// Infix addition for integer terms
        static member ( + ) (l: #SfsIntTerm<'u>, rr: int<'u>) =
            let r = l.Model.CreateIntConstant rr
            l.Model.Sum [| (l :> SfsIntTerm<'u>) ; r |]

        /// Infix subtraction for integer terms
        static member ( - ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            l.Model.Difference ((l :> SfsIntTerm<'u>) , (r :> SfsIntTerm<'u>))
        /// Infix subtraction for integer terms
        static member ( - ) (ll: int<'u>, r: #SfsIntTerm<'u>) =
            let l = r.Model.CreateIntConstant ll
            r.Model.Difference (l, (r :> SfsIntTerm<'u>))
        /// Infix subtraction for integer terms
        static member ( - ) (l: #SfsIntTerm<'u>, rr: int<'u>) =
            let r = l.Model.CreateIntConstant rr
            l.Model.Difference ((l :> SfsIntTerm<'u>), r)

        /// Infix product for integer terms
        static member ( * ) (l: SfsIntTerm<'v>, r: #SfsIntTerm<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsIntTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntVariable<'v>, r: SfsIntTerm<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsIntTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntVariable<'v>, r: SfsIntVariable<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsIntTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (ll: int<'v>, r: SfsIntTerm<'w>)  =
            let l = r.Model.CreateIntConstant ll
            new SfsIntTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (ll: int<'v>, r: SfsIntVariable<'w>)  =
            let l = r.Model.CreateIntConstant ll
            new SfsIntTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntTerm<'v>, rr : int<'w>) =
            let r = l.Model.CreateIntConstant rr
            new SfsIntTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntVariable<'v>, rr : int<'w>) =
            let r = l.Model.CreateIntConstant rr
            new SfsIntTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (ll: float<'v>, r: SfsIntTerm<'w>)  =
            let l = r.Model.CreateRealConstant ll
            new SfsRealTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (ll: float<'v>, r: SfsIntVariable<'w>)  =
            let l = r.Model.CreateRealConstant ll
            new SfsRealTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntTerm<'v>, rr : float<'w>) =
            let r = l.Model.CreateRealConstant rr
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for integer terms
        static member ( * ) (l: SfsIntVariable<'v>, rr : float<'w>) =
            let r = l.Model.CreateRealConstant rr
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
            
        /// Infix strictly less than for integer terms
        static member ( <<<< ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Less [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix strictly less than for integer terms
        static member ( <<<< ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.Less  [| (m.CreateIntConstant l) ;  (r :> SfsIntTerm<'u>) |]
        /// Infix strictly less than for integer terms
        static member ( <<<< ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.Less  [| (l :> SfsIntTerm<'u>) ; (m.CreateIntConstant r) |]
            
        /// Infix "less or equal" for integer terms
        static member ( <<== ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.LessEqual [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix "less or equal" for integer terms
        static member ( <<== ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.LessEqual  [| (m.CreateIntConstant l) ;  (r :> SfsIntTerm<'u>) |]
        /// Infix "less or equal" for integer terms
        static member ( <<== ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.LessEqual  [| (l :> SfsIntTerm<'u> ); (m.CreateIntConstant r) |]
            
        /// Infix "strictly greater than" for integer terms
        static member ( >>>> ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Greater [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix "strictly greater than" for integer terms
        static member ( >>>> ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.Greater  [| (m.CreateIntConstant l) ; (r :> SfsIntTerm<'u>) |]
        /// Infix "strictly greater than" for integer terms
        static member ( >>>> ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.Greater  [| (l :> SfsIntTerm<'u>) ; (m.CreateIntConstant r) |]
            
        /// Infix "greater or equal than" for integer terms
        static member ( >>== ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.GreaterEqual [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix "greater or equal than" for integer terms
        static member ( >>== ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.GreaterEqual  [| (m.CreateIntConstant l) ;  (r :> SfsIntTerm<'u>) |]
        /// Infix "greater or equal than" for integer terms
        static member ( >>== ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.GreaterEqual  [| (l :> SfsIntTerm<'u>) ; (m.CreateIntConstant r) |]
            
        /// Infix equality for integer terms
        static member ( ==== ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Equal [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix equality for integer terms
        static member ( ==== ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.Equal  [| (m.CreateIntConstant l) ;  (r :> SfsIntTerm<'u>) |]
        /// Infix equality for integer terms
        static member ( ==== ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.Equal  [| (l :> SfsIntTerm<'u>) ; (m.CreateIntConstant r) |]
            
        /// Infix inequality for integer terms
        static member ( <<>> ) (l: #SfsIntTerm<'u>, r: #SfsIntTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Equal [| (l :> SfsIntTerm<'u>) ; (r :> SfsIntTerm<'u>) |]
        /// Infix inequality for integer terms
        static member ( <<>> ) (l: int<'u>, r: #SfsIntTerm<'u>) =
            let m = r.Model 
            m.Equal  [| (m.CreateIntConstant l) ;  (r :> SfsIntTerm<'u>) |]
        /// Infix inequality for integer terms
        static member ( <<>> ) (l: #SfsIntTerm<'u>, r: int<'u>) =
            let m = l.Model 
            m.Equal  [| (l :> SfsIntTerm<'u>) ; (m.CreateIntConstant r) |]
           
           
    /// Describes a Solver Foundation Services variable that takes on integer values.
    /// Value will later determined by the solver.
    and SfsIntVariable<[<Measure>] 'u> (m : SfsModel, d: Decision) =
        inherit SfsIntTerm<'u>(m, d)
        /// The name of the variable
        member this.Name with get () = d.Name
        /// The value of the integer variable
        member this.Value =
            Convert.ToInt32(Math.Round(d.GetDouble())) 
            |> unbox<int<'u>>
        /// Returns the value of the integer variable, or None if it has not been assigned yet
        member this.TryGetValue () =        
            try 
                this.Value |> Some
            with
            | :? KeyNotFoundException -> None
            
        
    /// Describes a Solver Foundation Services term that takes on real (float) values.
    and SfsRealTerm<[<Measure>]'u> (m : SfsModel, d : Term) =
        
        inherit SfsTerm(m, d)
        
        /// Infix addition for real (float) terms
        static member ( + ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            l.Model.Sum [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix addition for real (float) terms
        static member ( + )(ll: float<'u>, r: #SfsRealTerm<'u>) =
            let l = r.Model.CreateRealConstant ll
            r.Model.Sum [| l; (r :> SfsRealTerm<'u>) |]
        /// Infix addition for real (float) terms
        static member ( + ) (l: #SfsRealTerm<'u>, rr: float<'u>) =
            let r = l.Model.CreateRealConstant rr
            l.Model.Sum [| (l :> SfsRealTerm<'u>) ; r |]

        /// Infix subtraction for real (float) terms
        static member ( - ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            l.Model.Difference ((l :> SfsRealTerm<'u>) , (r :> SfsRealTerm<'u>))
        /// Infix subtraction for real (float) terms
        static member ( - ) (ll: float<'u>, r: #SfsRealTerm<'u>) =
            let l = r.Model.CreateRealConstant ll
            r.Model.Difference (l, (r :> SfsRealTerm<'u>))
        /// Infix subtraction for real (float) terms
        static member ( - ) (l: #SfsRealTerm<'u>, rr: float<'u>) =
            let r = l.Model.CreateRealConstant rr
            l.Model.Difference ((l :> SfsRealTerm<'u>), r)

        /// Infix product for real (float) terms
        static member ( * ) (l: SfsRealTerm<'v>, r: #SfsRealTerm<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (l: SfsRealVariable<'v>, r: SfsRealTerm<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (l: SfsRealVariable<'v>, r: SfsRealVariable<'w>) =
            SfsTerm.CheckModels (l, r)
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (ll: float<'v>, r: SfsRealTerm<'w>)  =
            let l = r.Model.CreateRealConstant ll
            new SfsRealTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (ll: float<'v>, r: SfsRealVariable<'w>)  =
            let l = r.Model.CreateRealConstant ll
            new SfsRealTerm<'v 'w>(r.Model, r.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (l: SfsRealTerm<'v>, rr : float<'w>) =
            let r = l.Model.CreateRealConstant rr
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
        /// Infix product for real (float) terms
        static member ( * ) (l: SfsRealVariable<'v>, rr : float<'w>) =
            let r = l.Model.CreateRealConstant rr
            new SfsRealTerm<'v 'w>(l.Model, l.Model.Product (l.Term, r.Term))
            
        /// Infix "strictly less than" for real (float) terms
        static member ( <<<< ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Less [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix "strictly less than" for real (float) terms
        static member ( <<<< ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.Less  [| (m.CreateRealConstant l) ;  (r :> SfsRealTerm<'u>) |]
        /// Infix "strictly less than" for real (float) terms
        static member ( <<<< ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.Less  [| (l :> SfsRealTerm<'u>) ; (m.CreateRealConstant r) |]
            
        /// Infix "less or equal than" for real (float) terms
        static member ( <<== ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.LessEqual [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix "less or equal than" for real (float) terms
        static member ( <<== ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.LessEqual  [| (m.CreateRealConstant l) ;  (r :> SfsRealTerm<'u>) |]
        /// Infix "less or equal than" for real (float) terms
        static member ( <<== ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.LessEqual  [| (l :> SfsRealTerm<'u> ); (m.CreateRealConstant r) |]
            
        /// Infix "greater than" for real (float) terms
        static member ( >>>> ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Greater [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix "greater than" for real (float) terms
        static member ( >>>> ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.Greater  [| (m.CreateRealConstant l) ; (r :> SfsRealTerm<'u>) |]
        /// Infix "greater than" for real (float) terms
        static member ( >>>> ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.Greater  [| (l :> SfsRealTerm<'u>) ; (m.CreateRealConstant r) |]
            
        /// Infix "greater or equal than" for real (float) terms
        static member ( >>== ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.GreaterEqual [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix "greater or equal than" for real (float) terms
        static member ( >>== ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.GreaterEqual  [| (m.CreateRealConstant l) ;  (r :> SfsRealTerm<'u>) |]
        /// Infix "greater or equal than" for real (float) terms
        static member ( >>== ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.GreaterEqual  [| (l :> SfsRealTerm<'u>) ; (m.CreateRealConstant r) |]
            
        /// Infix equality for real (float) terms
        static member ( ==== ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Equal [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix equality for real (float) terms
        static member ( ==== ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.Equal  [| (m.CreateRealConstant l) ;  (r :> SfsRealTerm<'u>) |]
        /// Infix equality for real (float) terms
        static member ( ==== ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.Equal  [| (l :> SfsRealTerm<'u>) ; (m.CreateRealConstant r) |]
            
        /// Infix inequality for real (float) terms
        static member ( <<>> ) (l: #SfsRealTerm<'u>, r: #SfsRealTerm<'u>) =
            SfsTerm.CheckModels (l, r)
            let m = l.Model 
            m.Equal [| (l :> SfsRealTerm<'u>) ; (r :> SfsRealTerm<'u>) |]
        /// Infix inequality for real (float) terms
        static member ( <<>> ) (l: float<'u>, r: #SfsRealTerm<'u>) =
            let m = r.Model 
            m.Equal  [| (m.CreateRealConstant l) ;  (r :> SfsRealTerm<'u>) |]
        /// Infix inequality for real (float) terms
        static member ( <<>> ) (l: #SfsRealTerm<'u>, r: float<'u>) =
            let m = l.Model 
            m.Equal  [| (l :> SfsRealTerm<'u>) ; (m.CreateRealConstant r) |]
            
          
    /// Describes a Solver Foundation Services variable that takes on real (float) values.
    /// Value will later determined by the solver.
    and SfsRealVariable<[<Measure>] 'u> (m : SfsModel, d: Decision) =
        inherit SfsRealTerm<'u>(m, d)
        /// The name of the variable
        member this.Name with get () = d.Name
        /// Returns the value of the real variable
        member this.Value =
            d.GetDouble()
            |> unbox<float<'u>>
        /// Returns the value of the integer variable, or None if it has not been assigned yet
        member this.TryGetValue () =        
            try 
                this.Value |> Some
            with
            | :? KeyNotFoundException -> None
            

    /// Describes a Solver Foundation model, i.e., a problem description with
    /// variables, constraints, objectives, etc.
    and SfsModel (context : SolverContext) = 

        /// The actual SFS model that is wrapped
        let model =  context.CreateModel()
        /// Counter for generating variable names
        let varCounter = ref 0
        /// Counter for generating goal names
        let goalCounter = ref 0
        /// Counter for generating constraint names
        let constraintCounter = ref 0
        /// The constant "true" cached
        let cstTrue = ref None
        /// The constant "false" cached
        let cstFalse = ref None
        /// Cached float constants as terms
        let mutable floatTermCache = new Dictionary<float,Term>()
        /// Cached integer constants as terms
        let mutable intTermCache = new Dictionary<int,Term>()
        
        /// Creates a new (unused) variable name
        let CreateFreshVarName() =
            incr varCounter
            @"SfsWrapperVar_" + (!varCounter).ToString()
        /// Creates a new (unused) goal name
        let CreateFreshGoalName() =
            incr goalCounter
            @"SfsWrapperGoal_" + (!goalCounter).ToString()
        /// Creates a new (unused) constraint name
        let CreateFreshConstraintName() =
            incr goalCounter
            @"SfsWrapperConstraint_" + (!goalCounter).ToString()
        /// Returns the array of wrapped SFS terms
        let TermArray (array : #SfsTerm[]) =
            array
            |> Array.map (fun t -> t.Term)
        
        /// Returns the wrapped SFS model
        member this.Model with get() = model
        
        /// Saves the Model
        member this.SaveModel(format, writer) =
            context.SaveModel(format, writer)
        
        /// Returns the constant "true"
        member this.True 
            with get() =
                match !cstTrue with
                | None -> 
                    let t = Term.op_Implicit (true)
                    let result = new SfsBooleanTerm (this, t)
                    cstTrue := Some (result); 
                    result
                | Some(x) -> x
        
        /// Returns the constant "false"
        member this.False 
            with get() =
                match !cstFalse with 
                | None -> 
                    let f = Term.op_Implicit (false)
                    let result = new SfsBooleanTerm (this, f)
                    cstFalse := Some (result); 
                    result
                | Some(x) -> x
        
        /// Creates a real valued (float) constant with unit-of-measure
        member this.CreateRealConstant<[<Measure>] 'u> (x: float<'u>) : SfsRealTerm<'u> =
            let cachedTerm = ref (Term.op_Implicit 0.0)
            /// The constant bar the unit-of-measure
            let stripped = x |> float
            if floatTermCache.TryGetValue(stripped, cachedTerm) then
                new SfsRealTerm<'u>(this, !cachedTerm)
            else
                let term = stripped |> Term.op_Implicit
                floatTermCache.Add(stripped, term)
                new SfsRealTerm<'u>(this, term)
        
        /// Creates an integer constant with unit-of-measure
        member this.CreateIntConstant<[<Measure>] 'u> (x: int<'u>) : SfsIntTerm<'u>=
            let cachedTerm = ref (Term.op_Implicit 0.0)
            /// The constant bar the unit-of-measure
            let stripped = x |> int
            if intTermCache.TryGetValue(stripped, cachedTerm) then
                new SfsIntTerm<'u>(this, !cachedTerm)
            else
                let term = stripped |> float |> Term.op_Implicit
                intTermCache.Add(stripped, term)
                new SfsIntTerm<'u>(this, term)
            
        /// Creates a Boolean decision variable and adds it to the model
        member this.CreateBooleanVariable name =
            let result = new Decision(Domain.Boolean, name)
            model.AddDecision result
            new SfsBooleanVariable(this, result)
        /// Creates a Boolean decision variable and adds it to the model
        member this.CreateBooleanVariable () = 
            this.CreateBooleanVariable (CreateFreshVarName())

        /// Creates a real valued (float) decision variable with unit-of-measure, and
        /// adds it to the model
        member this.CreateRealVariable<[<Measure>] 'u> (name) = 
            let result = new Decision(Domain.Real, name)
            model.AddDecision result
            new SfsRealVariable<'u>(this, result)
        /// Creates a real valued (float) decision variable with unit-of-measure, and
        /// adds it to the model
        member this.CreateRealVariable<[<Measure>] 'u> () =
            this.CreateRealVariable<'u>(CreateFreshVarName()) 
            
                    
        /// Creates a non-negative real valued (float) decision variable with
        /// unit-of-measure, and adds it to the model
        member this.CreateRealNonnegativeVariable<[<Measure>] 'u> (name) = 
            let result = new Decision(Domain.RealNonnegative, name)
            model.AddDecision result
            new SfsRealVariable<'u>(this, result)
        /// Creates a non-negative real valued (float) decision variable with
        /// unit-of-measure, and adds it to the model
        member this.CreateRealNonnegativeVariable<[<Measure>] 'u> () = 
            this.CreateRealNonnegativeVariable<'u> (CreateFreshVarName())
            
        /// Creates a real valued (float) decision variable that can take on values in
        /// in a closed interval, and adds it to the model
        member this.CreateRealRangeVariable<[<Measure>] 'u> (min: float<'u>, max: float<'u>, name)= 
            let minR = min |> float |> Rational.op_Implicit
            let maxR = max |> float |> Rational.op_Implicit
            let result = new Decision(Domain.RealRange(minR, maxR), name)
            model.AddDecision result
            new SfsRealVariable<'u>(this, result)
        /// Creates a real valued (float) decision variable that can take on values in
        /// in a closed interval, and adds it to the model
        member this.CreateRealRangeVariable<[<Measure>] 'u> (min, max) =
            this.CreateRealRangeVariable<'u>(min, max, CreateFreshVarName())
        
        /// Creates a real valued (float) decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateRealSetVariable(allowedValues: seq<Rational>, name) = 
            let result = new Decision(Domain.Set (allowedValues |> Seq.toArray), name)
            model.AddDecision result
            new SfsRealVariable<1>(this, result)
        /// Creates a real valued (float) decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateRealSetVariable(allowedValues: seq<Rational>) = 
            this.CreateRealSetVariable(allowedValues, CreateFreshVarName())
                        
        /// Creates a real valued (float) decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateRealSetVariable<[<Measure>] 'u> (allowedValues: Set<float<'u>>, name) = 
            let values = 
                allowedValues
                |> Set.toArray
                |> Array.map (float >> Rational.op_Implicit)
            let result = new Decision(Domain.Set values, name)
            model.AddDecision result
            new SfsRealVariable<'u>(this, result)
        /// Creates a real valued (float) decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateRealSetVariable<[<Measure>] 'u> (allowedValues: Set<float<'u>>) = 
            this.CreateRealSetVariable<'u>(allowedValues, CreateFreshVarName())
                        
        /// Creates an integer decision variable with units-of-measure, and adds it to the model
        member this.CreateIntVariable<[<Measure>] 'u> name = 
            let result = new Decision(Domain.Integer, name)
            model.AddDecision result
            new SfsIntVariable<'u>(this, result)
        /// Creates an integer decision variable with units-of-measure, and adds it to the model
        member this.CreateIntVariable<[<Measure>] 'u> () = 
            this.CreateIntVariable<'u>(CreateFreshVarName())
                        
        /// Creates a non-negative integer decision variable with units-of-measure,
        /// and adds it to the model
        member this.CreateIntNonnegativeVariable<[<Measure>] 'u> name = 
            let result = new Decision(Domain.IntegerNonnegative, name)
            model.AddDecision result
            new SfsIntVariable<'u>(this, result)
        /// Creates a non-negative integer decision variable with units-of-measure,
        /// and adds it to the model
        member this.CreateIntNonnegativeVariable<[<Measure>] 'u> ()= 
            this.CreateIntNonnegativeVariable<'u> (CreateFreshVarName())

        /// Creates an integer decision variable that can take on values in
        /// a closed interval, and adds it to the model
        member this.CreateIntRangeVariable<[<Measure>] 'u> (min: int<'u>, max: int<'u>, name) = 
            let minR = min |> int |> Rational.op_Implicit
            let maxR = max |> int |> Rational.op_Implicit
            let result = new Decision(Domain.IntegerRange(minR, maxR), name)
            model.AddDecision result
            new SfsIntVariable<'u>(this, result)
        /// Creates an integer decision variable that can take on values in
        /// a closed interval, and adds it to the model
        member this.CreateIntRangeVariable<[<Measure>] 'u>(min, max) = 
            this.CreateIntRangeVariable<'u>(min, max, CreateFreshVarName())

        /// Creates an integer decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateIntSetVariable<[<Measure>] 'u> (allowedValues: Set<int<'u>>, name) = 
            let values = 
                allowedValues 
                |> Set.toArray 
                |> Array.map int
            let result = new Decision(Domain.Set (values), name)
            model.AddDecision result
            new SfsIntVariable<'u>(this, result)
        /// Creates an integer decision variable that can take on values in
        /// a given set, and adds it to the model
        member this.CreateIntSetVariable<[<Measure>] 'u> allowedValues = 
            this.CreateIntSetVariable<'u>(allowedValues, CreateFreshVarName())
                        
        /// Creates a symbolic decision variable from an F# discriminated
        /// union type, and adds it to the model
        member this.CreateSymbolicVariable<'a> name =
            assert (Object.ReferenceEquals(SfsSymbolicVariable<'a>.Domain, SfsSymbolicVariable<'a>.Domain))
            let result = new Decision(SfsSymbolicVariable<'a>.Domain, name)
            model.AddDecision result
            new SfsSymbolicVariable<'a>(this, result)
        /// Creates a symbolic decision variable from an F# discriminated
        /// union type, and adds it to the model
        member this.CreateSymbolicVariable<'a> () =
            this.CreateSymbolicVariable<'a> (CreateFreshVarName())
        
        //// (1): numerical terms
        
        /// Creates a term that is the sum of a list of terms
        member this.Sum (args: SfsRealTerm<'u> array) =
            let t = Model.Sum (args |> TermArray)
            new SfsRealTerm<'u>(this, t)
        /// Creates a term that is the sum of a list of terms
        member this.Sum  (args: SfsIntTerm<'u> array) =
            let t = Model.Sum (args |> TermArray)
            new SfsIntTerm<'u>(this, t)
        /// Creates a term that is the sum of a list of terms
        member this.Sum (args: SfsRealVariable<'u> array) =
            let t = Model.Sum (args |> TermArray)
            new SfsRealTerm<'u>(this, t)
        /// Creates a term that is the sum of a list of terms
        member this.Sum (args: SfsIntVariable<'u> array) =
            let t = Model.Sum (args |> TermArray)
            new SfsIntTerm<'u>(this, t)

        /// Creates a term representing the absolute value of a term
        member this.Abs (x : SfsRealTerm<'u>) =
            let t = Model.Abs (x.Term)
            new SfsRealTerm<'u>(this, t)
        /// Creates a term representing the absolute value of a term
        member this.Abs (x : SfsIntTerm<'u>) =
            let t = Model.Abs (x.Term)
            new SfsIntTerm<'u>(this, t)
            
        /// Creates a term representing a term multiplied by itself
        member this.Square (x : SfsRealTerm<'u>) =
            let t = Model.Power (x.Term, Term.op_Implicit (2.0))
            new SfsRealTerm<'u*'u>(this, t)
        /// Creates a term representing a term multiplied by itself
        member this.Square (x : SfsIntTerm<'u>) =
            let t = Model.Power (x.Term, Term.op_Implicit (2.0))
            new SfsIntTerm<'u*'u>(this, t)
            
        /// Creates a term representing the negative value (unary minus) of a term
        member this.Negate (x : SfsRealTerm<'u>) =
            let t = Model.Negate x.Term
            new SfsRealTerm<'u>(this, t)
        /// Creates a term representing the negative value (unary minus) of a term
        member this.Negate (x : SfsIntTerm<'u>) =
            let t = Model.Negate x.Term
            new SfsIntTerm<'u>(this, t)
           
        /// Creates a term representing the difference of two terms ( l - r )
        member this.Difference (l: SfsRealTerm<'u>, r: SfsRealTerm<'u>) =
            let diff = Model.Difference(l.Term, r.Term)
            new SfsRealTerm<'u>(this, diff)
        /// Creates a term representing the difference of two terms ( l - r )
        member this.Difference (l: SfsIntTerm<'u>, r: SfsIntTerm<'u>) =
            let diff = Model.Difference(l.Term, r.Term)
            new SfsIntTerm<'u>(this, diff)
        
        /// Product of two SFS terms.
        // Not exposed as the product is difficult to handle with units-of-measure, and we have
        // all that complexity in the operator definitions, not at this level   
        member internal this.Product (l: Term, r: Term) =
            Model.Product [| l; r|]
            
        //// (2): Boolean terms
        
        /// Creates a term that is true iff all terms in a list are equal
        member this.Equal (args: SfsRealTerm<_>[]) =
            let t = Model.Equal (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in a list are equal
        member this.Equal (args: SfsIntTerm<_>[]) =
            let t = Model.Equal (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in a list are equal
        member this.Equal (args: SfsSymbolicVariable<_>[]) =
            let t = Model.Equal (TermArray args)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true iff all terms in a list are pairwise different
        member this.AllDifferent (args: SfsRealTerm<_>[]) =
            let t = Model.AllDifferent (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in a list are pairwise different
        member this.AllDifferent (args: SfsIntTerm<_>[]) =
            let t = Model.AllDifferent (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in a list are pairwise different
        member this.AllDifferent (args: SfsSymbolicVariable<_>[]) =
            let t = Model.AllDifferent (TermArray args)
            new SfsBooleanTerm(this, t)

        /// Creates a term that is true iff all terms in the list are 
        /// ordered in strictly increasing values
        member this.Less (args: SfsRealTerm<_>[]) =
            let t = Model.Less (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in strictly increasing values
        member this.Less (args: SfsIntTerm<_>[]) =
            let t = Model.Less (TermArray args)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in non-decreasing values
        member this.LessEqual (args: SfsRealTerm<_>[]) =
            let t = Model.LessEqual (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in non-decreasing values
        member this.LessEqual (args: SfsIntTerm<_>[]) =
            let t = Model.LessEqual (TermArray args)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in strictly decreasing values
        member this.Greater (args: SfsRealTerm<_>[]) =
            let t = Model.Greater (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in strictly decreasing values
        member this.Greater (args: SfsIntTerm<_>[]) =
            let t = Model.Greater (TermArray args)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in non-increasing values
        member this.GreaterEqual (args: SfsRealTerm<_>[]) =
            let t = Model.GreaterEqual (TermArray args)
            new SfsBooleanTerm(this, t)
        /// Creates a term that is true iff all terms in the list are 
        /// ordered in non-increasing values
        member this.GreaterEqual (args: SfsIntTerm<_>[]) =
            let t = Model.GreaterEqual (TermArray args)
            new SfsBooleanTerm(this, t)
            
        /// Creates a term that is true iff all its arguments are true
        member this.And args =
            let t = Model.And (TermArray args)
            new SfsBooleanTerm(this, t)
            
        /// Creates a term true that is true iff at least one of its arguments is true
        member this.Or args =
            let t = Model.Or (TermArray args)
            new SfsBooleanTerm(this, t)
            
        /// Creates a term that is true iff at least one of its arguments is false
        member this.Not (arg : SfsBooleanTerm) =
            let t = Model.Not arg.Term
            new SfsBooleanTerm(this, t)

        /// Creates a term that is true iff at most M of the terms in the array are true
        member this.AtMostMofN (m, args : SfsBooleanTerm array) =
            let t = Model.AtMostMofN(m, args |> TermArray)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true iff exactly M of the terms in the array are true
        member this.ExactlyMofN (m, args : SfsBooleanTerm array) =
            let t = Model.ExactlyMofN(m, args |> TermArray)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true the function f returns true when applied to each array element
        /// Note that this function may behave differently to Model.ForEach in how
        /// it calls the function f
        member this.ForEach (args: 'a array, f: 'a -> SfsBooleanTerm) =
            let t = Model.And(args |> Array.map f |> TermArray)
            new SfsBooleanTerm(this, t)
        
        /// Creates a term that is true the function f returns true when applied to each array elements
        /// where the predicate holds
        /// Note that this function may behave differently to Model.ForEachWhere in how
        /// it calls the function f
        member this.ForEachWhere (args: 'a array, predicate: 'a -> SfsBooleanTerm, f: 'a -> SfsBooleanTerm) =
            let t = Model.And(args |> Array.map (fun x -> (predicate x) ==>> (f x)) |> TermArray)
            new SfsBooleanTerm(this, t)
            
        //////////////////////////////////////////////////////////////////////
        // specification of constraints / objectives / solutions
        
        /// Adds a list of boolean terms as constraints
        member this.AddConstraints(name, terms) =
            let c = model.AddConstraints(name, terms |> TermArray)
            new SfsConstraint(c)
        /// Adds a list of boolean terms as constraints
        member this.AddConstraints terms = 
            this.AddConstraints(CreateFreshConstraintName(), terms)
        /// Adds a single boolean term as a constraint
        member this.AddConstraint(name, term) = 
            this.AddConstraints(name, [| term |])
        /// Adds a single boolean term as a constraint
        member this.AddConstraint term = 
            this.AddConstraints(CreateFreshConstraintName(), [| term |])
                    
        /// Removes a constraint from the model
        member this.RemoveConstraint (c: SfsConstraint) =
            model.RemoveConstraint (c.Constraint)
                    
        /// Adds a numerical term as an objective function (goal)
        member this.AddGoal (name, goalKind, objective : SfsIntTerm<'u>) =
            // NOTE: goals are added one by one for simplicity
            // to allow potentially different units
            let goal = model.AddGoal(name, goalKind, objective.Term) 
            new SfsIntGoal<'u> (goal)
        /// Adds a numerical term as an objective function (goal)
        member this.AddGoal (goalKind, objective : SfsIntTerm<'u>) =
            this.AddGoal(CreateFreshGoalName(), goalKind, objective)
                    
        /// Adds a numerical term as an objective function (goal)
        member this.AddGoal (name, goalKind, objective : SfsRealTerm<'u>) =
            // NOTE: goals are added one by one for simplicity
            // to allow potentially different units
            let goal = model.AddGoal(name, goalKind, objective.Term)
            new SfsRealGoal<'u> (goal)
        /// Adds a numerical term as an objective function (goal)
        member this.AddGoal (goalKind, objective : SfsRealTerm<'u>) =
            this.AddGoal(CreateFreshGoalName(), goalKind, objective)
            
        /// Removes an objective function (goal) from the model
        member this.RemoveGoal (g: #SfsGoal) =
            model.RemoveGoal (g.Goal)
            
        /// Solves the program, with a given solver or a set of solvers in parallel.
        /// Use this when solvers need to be parameterized
        member this.Solve directives =
            context.Solve directives
            
        /// Solves the program, with a given solver in its default configuration
        member this.Solve directive =
            let d = 
                match directive with
                | Simplex                   -> new SimplexDirective() :> Directive
                | ConstraintProgramming     -> new ConstraintProgrammingDirective() :> Directive
                | InteriorPointMethod       -> new InteriorPointMethodDirective() :> Directive
            this.Solve [| d |]                
        /// Solves the program using a simplex solver            
        member this.Solve() = this.Solve Simplex

