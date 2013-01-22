#r "Microsoft.Solver.Foundation.dll"

#load "DSL.fs"
#load "Compile.fs"
#load "Query.fs"

open Microsoft.SolverFoundation.FSharpDSL.Language
open Microsoft.SolverFoundation.FSharpDSL.Query

// Units-of-measure declarations used throughout the examples
[<Measure>] type Dollar
[<Measure>] type Barrel
[<Measure>] type Day

/// The Petrochem example from the MSF documentation, here annotated with the correct units-of-measure.
// In this example, we annotate each and every expression with its unit-of-measure. However, many of those annotations
// can be done automatically by F#'s type inference. In subsequent examples, we will drop many of those annotations.
// To get a feeling of how the type inference for units-of-measures works, try deleting or modifying some
// of the type annotations.
let petrochem () =   
    opt { let! sa = var<Barrel/Day>()
          let! vz = var<_>()
          assume (0.3 * sa + 0.4 * vz >= 2000.<_>)
          assume (0.4 * sa + 0.2 * vz >= 1500.<_>)
          assume (0.2 * sa + 0.3 * vz >= 500.<_>)
          assume (sa <= 9000.<_> && sa >= 0.<_>)
          assume (vz <= 6000.<_> && vz >= 0.<_>)   
          minimise (20.0<Dollar/Barrel> * sa + 15.0<_> * vz)
    }

/// The Petrochem example from the MSF documentation, now with free parameters for the coefficients
/// in the objective function. This illustrates how information external to the DSL part can be used 
/// in modelling.
let petrochemAsFunction (a:float<Dollar/Barrel>, b:float<_>) =   
    opt { let! sa = var<Barrel/Day>()
          let! vz = var<_>()
          assume (0.3 * sa + 0.4 * vz >= 2000.<_>)
          assume (0.4 * sa + 0.2 * vz >= 1500.<_>)
          assume (0.2 * sa + 0.3 * vz >= 500.<_>)
          assume (sa <= 9000.<_> && sa >= 0.<_>)
          assume (vz <= 6000.<_> && vz >= 0.<_>)   
          minimise (a * sa + b * vz)
    }

/// A toy example that shows how to create arrays of variables (decisions), and how to 
/// access constants from inside the DSL.
let arrayExample1 ((coefficients: float[]), (upperBounds: float[])) =
    /// An array of indices. 
    // Note that these must be declared outside the DSL part!
    // Also, make sure that the index arrays go from 0 to N - 1
    let indices = [|0 .. coefficients.Length-1|] 
    opt { let! sa = vararray1 (coefficients.Length-1)
          assume (foreach indices (fun i -> sa.[i] <= upperBounds.[i]))
          maximise (sum indices (fun i -> coefficients.[i] * sa.[i]))
    }

/// This simplified portfolio selection problem illustrates integrality constraints: 
/// We have real valued variables, but they can only take on values that are integers.
let integerProgrammingExample() =
    /// List of available investments
    // We will be using that as indices later, thus the list of investments
    // must be integers from 0 to N-1
    let portfolio  = [|0; 1; 2|]
    /// Expected return for each investment
    let ret        = [| 20.0; 12.0; 17.0|]
    /// Cost of each investment
    let cost       = [| 10.0; 12.0; 12.0|]
    /// Overall budget limit
    let budget     = 25.0
    
    opt { /// Decisions whether to buy a specific item in the portfolio
          let! select = vararray1 (3)

          // All decisions are "boolean": integral and in 0/1
          assume (foreach portfolio (fun p -> integral (select.[p])))
          assume (foreach portfolio (fun p -> 0.0 <= select.[p]))
          assume (foreach portfolio (fun p -> select.[p] <= 1.0))
                    
          // Budget constraint
          assume (sum portfolio (fun p -> cost.[p]*select.[p]) <= budget)

          // Additionally we may have dependencies between the investments:
          // Here, items 1 and 2 are incompatible for some reason and can't
          // be bought together
          assume (select.[1] + select.[2] <= 1.0)
           
          // We want to optimise for the best possible return
          maximise (sum portfolio (fun p -> ret.[p] * select.[p]))
    }

#time "on";;

let result = integerProgrammingExample();;