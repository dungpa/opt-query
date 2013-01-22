// Copyright © Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)
module ODSLSamples

open Microsoft.SolverFoundation.Common
open Microsoft.SolverFoundation.FSharpDSL.Language
open Microsoft.SolverFoundation.FSharpDSL.Compiler

// Units-of-measure declarations used throughout the examples
[<Measure>] type Dollar
[<Measure>] type Barrel
[<Measure>] type Day
[<Measure>] type ProductionRate = Barrel/Day
[<Measure>] type Meter
[<Measure>] type Click
[<Measure>] type Impression

/// Describes a slot on a web page that can hold an advertisement
type AdvertisingSlot =
    | Slot1
    | Slot2
    | Slot3

/// The data that describes an advertisement: Bid and click-through rates when the ad 
/// is displayed in a specific slot
type Ad = 
    {
        Bid                 : float<Dollar/Click>
        ClickThroughRates   : Map<AdvertisingSlot, float<Click/Impression>>
    }

/// Template for samples: compile the expression, print out variables and objective function before
/// and after solving the linear program
let SampleTemplate expr =   
    let solver = Solver expr
    printfn "Objective function before solving = %f" (solver.ObjectiveFunction |> Rational.op_Explicit)
    solver.Variables 
    |> Seq.iter (fun v -> printfn "%s = %f" (v.ToString()) (solver.[v] |> Rational.op_Explicit))
    solver.Solve ()
    printfn "Objective function after solving = %f" (solver.ObjectiveFunction |> Rational.op_Explicit)
    solver.Variables 
    |> Seq.iter (fun v -> printfn "%s = %f" (v.ToString()) (solver.[v] |> Rational.op_Explicit))
    
/// The Petrochem example from the MSF documentation, here annotated with the correct units-of-measure.
// In this example, we annotate each and every expression with its unit-of-measure. However, many of those annotations
// can be done automatically by F#'s type inference. In subsequent examples, we will drop many of those annotations.
// To get a feeling of how the type inference for units-of-measures works, try deleting or modifying some
// of the type annotations.
let Petrochem () =   
    SampleTemplate 
        <@
            let sa = var<Barrel/Day>()
            let vz = var<Barrel/Day>()
            
            minimise (20.0<Dollar/Barrel> * sa + 15.0<Dollar/Barrel> * vz)
            
            where
                [
                    0.3 * sa + 0.4 * vz >= 2000.<Barrel/Day>;
                    0.4 * sa + 0.2 * vz >= 1500.<Barrel/Day>;
                    0.2 * sa + 0.3 * vz >= 500.<Barrel/Day>;
                    sa <= 9000.<Barrel/Day>;
                    vz <= 6000.<Barrel/Day>;
                    sa >= 0.<Barrel/Day>;
                    vz >= 0.<Barrel/Day>  
                ]
        @>
  
/// The Petrochem example from the MSF documentation, now with free parameters for the coefficients
/// in the objective function. This illustrates how information external to the DSL part can be used 
/// in modelling.
let PetrochemAsFunction (a:float<Dollar/Barrel>,b:float<Dollar/Barrel>) =   
    SampleTemplate
        <@
            let sa = var<Barrel/Day>()
            // Note that here we don't need to declare the unit-of-measure anymore - just
            // by the nature of the objective function, the compiler can figure out that vz needs to have the same
            // unit-of-measure as sa
            let vz = var<_>()
            
            minimise (a * sa + b * vz)
            
            where
                [
                    // We use the same constraints as above, but leave the complete unit-of-measure annotation
                    // to the type checker
                    0.3 * sa + 0.4 * vz >= 2000.<_>;
                    0.4 * sa + 0.2 * vz >= 1500.<_>;
                    0.2 * sa + 0.3 * vz >= 500.<_>;
                    sa <= 9000.<_>;
                    vz <= 6000.<_>;
                    sa >= 0.<_>;
                    vz >= 0.<_>  
                ]
        @>

/// The Petrochem example from the MSF documentation, now with output data binding to save the MSF results.
/// To achieve that, a variable in the DSL (an SFS decision) can be linked to a reference cell,
/// into which the result will be written.
let PetrochemWithDataBinding (a:float<Dollar/Barrel>, b:float<Dollar/Barrel>) =   
    let saudiArabia = ref 0.0<_>      
    let venezuela = ref 0.0<_>
    let objectiveFunction = ref 0.0<_>
    let solver =
        Solver 
            <@
                // This declares a Solver Foundation variable that is directly linked to
                // an reference cell. Once the simplex has been solved, the value that has been
                // assigned by Solver Foundation will be written out into the reference cell.
                // Note that this is the only way of reading out a Solver Foundation variable while
                // retaining the unit-of-measure!
                let sa = varinto (saudiArabia)
                let vz = varinto (venezuela)
                
                // Note here the minimiseinto keyword:
                // The first argument here is a reference cell into which the objective function
                // will be written. Similarly to the varinto keyword above, minimizeinto
                // is the only way of reading out the objective function while
                // retaining its unit-of-measure!
                minimiseinto objectiveFunction (a * sa + b * vz)
                
                where
                    [
                        0.3 * sa + 0.4 * vz >= 2000.<Barrel/Day>;
                        0.4 * sa + 0.2 * vz >= 1500.<_>;
                        0.2 * sa + 0.3 * vz >= 500.<_>;
                        sa <= 9000.<_>;
                        vz <= 6000.<_>;
                        sa >= 0.<_>;
                        vz >= 0.<_>  
                    ]
            @>
    solver.Solve()
    // When printing out a value that has a unit-of-measure annotation, we need to 
    // either divide that out, or strip it off using the float function
    printfn "Objective function after solving = %f" (!objectiveFunction/1.0<Dollar/Day>)
    printfn "Saudi Arabia = %f barrels/day" (!saudiArabia/1.0<Barrel/Day>)
    printfn "Venezuela    = %f barrels/day" (!venezuela/1.0<Barrel/Day>)

/// A toy example that shows how to create arrays of variables (decisions), and how to 
/// access constants from inside the DSL.
let ArrayExample1 ((coefficients: float[]), (upperBounds: float[])) =
    /// An array of indices. 
    // Note that these must be declared outside the DSL part!
    // Also, make sure that the index arrays go from 0 to N - 1
    let indices = [ 0 .. coefficients.Length-1 ] 
    SampleTemplate
        <@
            let sa = vararray1(indices)
            
            maximise (sum indices (fun i -> coefficients.[i] * sa.[i]))
            
            where
                [
                    foreach indices (fun i -> sa.[i] <= upperBounds.[i])
                ]
        @>

/// A more complex example to illustrate the use of arrays in the DSL.
/// The example is based on the integer programming example in the example code for the 
/// Solver Foundation Services wrapper with units-of-measure: Assignment of advertisements
/// to slots, where the goal is to maximize advertiser welfare.
let ArrayExample2 () =
    // Assignment problem: our goods are advertising slots on a search engine result page.
    // Advertisers can buy these slots, by specifying their valuation in terms of 
    // a bid "I'm willing to pay x $ per click". However, different advertisers
    // attract a different number of clicks in different slots.
    // Our goal is to maximize advertiser welfare, that is, overall value * number of clicks.
    /// Advertiser 1 bids a lot of money. His ad only performs well on the top slot
    let ad1 = { 
        Bid = 10.0<Dollar/Click>; 
        ClickThroughRates = Map.ofList [ (Slot1, 0.8<_>); (Slot2, 0.05<_>); (Slot3, 0.05<_>) ] }
    /// Advertiser 2 bids a moderate amount of money. The ad performs reasonably well on all 3 slots
    let ad2 = { 
        Bid = 4.99<Dollar/Click>; 
        ClickThroughRates = Map.ofList [ (Slot1, 0.4<_>); (Slot2, 0.2<_>); (Slot3, 0.2<_>) ] }
    /// Advertiser 3 bids a moderate amount of money. The ad performs reasonably well on all 3 slots
    let ad3 = { 
        Bid = 4.0<Dollar/Click>; 
        ClickThroughRates = Map.ofList [ (Slot1, 0.4<_>); (Slot2, 0.3<_>); (Slot3, 0.3<_>) ] }
    /// Advertiser 4 bids a high amount of money, but the ads are spam, and hardly attract clicks.
    let ad4 = { 
        Bid = 10.0<Dollar/Click>; 
        ClickThroughRates = Map.ofList [ (Slot1, 0.01<_>); (Slot2, 0.005<_>); (Slot3, 0.005<_>) ] }
    /// Info about all available ads
    let ads = [| ad1; ad2; ad3; ad4 |]
    /// All the advertising slots we consider
    let slots = [| Slot1; Slot2; Slot3 |]
    
    /// An array that stores all the average valuations of each advertiser in all slots
    /// (average valuation is the value an ad would create per impression)
    let w = 
        Array2D.init (ads.Length) (slots.Length) (fun i j -> 
            let ad = ads.[i]
            ad.ClickThroughRates.[slots.[j]] * ad.Bid
        )
    // Note that the index arrays must be declared outside the DSL part!
    // Also, make sure that these go from 0 to N - 1
    let ind1 = [ 0 .. ads.Length - 1 ] 
    let ind2 = [ 0 .. slots.Length - 1 ]
    let welfare = ref 0.0<_>
    let solver = 
        Solver
            <@
                let xij = vararray2<1>(ind1,ind2)
                
                maximiseinto welfare (sum ind1 (fun i -> sum ind2 (fun j -> (xij.[i,j] * w.[i,j]))))
                
                where
                    [
                        foreach ind1 (fun i -> foreach ind2 (fun j -> xij.[i,j] <= 1.0))
                        foreach ind1 (fun i -> foreach ind2 (fun j -> xij.[i,j] >= 0.0))
                        foreach ind1 (fun i -> sum ind2 (fun j -> xij.[i,j]) <= 1.0)
                        foreach ind2 (fun j -> sum ind1 (fun i -> xij.[i,j]) <= 1.0)
                    ]
            @>
    solver.Solve()
    printfn "Objective function after solving = %f" (solver.ObjectiveFunction |> Rational.op_Explicit)
    printfn "Objective function after solving, read out via a reference = %f" (!welfare / 1.0<Dollar/Impression>)
    printfn "Assignment variables:"
    solver.Variables
    |> Seq.iter (fun v -> printfn "%s = %f" (v.ToString()) (solver.[v] |> Rational.op_Explicit))
            

/// This simplified portfolio selection problem illustrates integrality constraints: 
/// We have real valued variables, but they can only take on values that are integers.
let IntegerProgrammingExample() =
    /// List of available investments
    // We will be using that as indices later, thus the list of investments
    // must be integers from 0 to N-1
    let portfolio  = [0; 1; 2]
    /// Expected return for each investment
    let ret        = [| 20.0; 12.0; 17.0|]
    /// Cost of each investment
    let cost       = [| 10.0; 12.0; 12.0|]
    /// Overall budget limit
    let budget     = 25.0
    
    SampleTemplate    
        <@
            /// Decisions whether to buy a specific item in the portfolio
            let select = vararray1(portfolio)
            
            // We want to optimise for the best possible return
            maximise (sum portfolio (fun p -> ret.[p] * select.[p]))
            
            where
                [
                    // All decisions are "boolean": integral and in 0/1
                    foreach portfolio (fun p ->  integral (select.[p]))
                    foreach portfolio (fun p ->  0.0 <= select.[p])
                    foreach portfolio (fun p ->         select.[p] <= 1.0)
                    
                    // Budget constraint
                    sum portfolio (fun p -> cost.[p]*select.[p]) <= budget

                    // Additionally we may have dependencies between the investments:
                    // Here, items 1 and 2 are incompatible for some reason and can't
                    // be bought together
                    select.[1] + select.[2] <= 1.0
                ]
        @>

do
    printfn "--------------------------------"
    printfn "Petrochem example: Basic functionality"
    Petrochem ()
    printfn "--------------------------------"
    printfn "Petrochem example with parameter"
    PetrochemAsFunction (20.0<_>, 15.0<_>)
    printfn "--------------------------------"
    printfn "Petrochem example with output data binding"
    PetrochemWithDataBinding (20.0<_>, 15.0<_>)
    printfn "--------------------------------"
    printfn "Array example: parametrised objective function"
    ArrayExample1 ([| 1.0; 0.5 |], [| 20.0; 30.0 |])
    printfn "--------------------------------"
    printfn "Assignment game: working with 2D arrays"
    ArrayExample2 ()
    printfn "--------------------------------"
    printfn "Portfolio selection: Integer programming"
    IntegerProgrammingExample()
    printf"Done. Press any key to end the demo."
    System.Console.ReadKey() |> ignore
    
    