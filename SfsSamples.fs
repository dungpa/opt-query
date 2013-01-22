// Copyright © Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)

module SfsSamples

open Microsoft.SolverFoundation.Services
open Microsoft.SolverFoundation.Common
open System.Collections.Generic
open Microsoft.SolverFoundation.SfsWrapper

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

/// An F# discriminated union type for colors
/// (for use in the 4-color coding example)
type Color = 
    | Red
    | Green
    | Blue
    | Yellow
    override this.ToString() = 
        match this with
        | Red       -> "Red"
        | Green     -> "Green"
        | Blue      -> "Blue"
        | Yellow    -> "Yellow"
       
do

    /// Solver context
    // Note that we can only have one context, and only one model per context
    let context = SolverContext.GetContext()

    // ===================================================================
    // Example 1: Linear Programming
    // This is the Petrochem example from the MSF documentation
    // ===================================================================

    printfn "--------------------------------"
    printfn "Petrochem example: "
    /// Model for the linear programming example (Petrochem)
    let petrochem = new SfsModel(context)
    
    /// Optimization variable: Production in Saudi-Arabia
    let buyfromSA = petrochem.CreateRealVariable<ProductionRate>()
    /// Optimization variable: Production in Venezuela
    let buyfromVZ = petrochem.CreateRealVariable<ProductionRate>()
    
    /// Maximum production in Saudi-Arabia
    // Note that we don't have to specify the unit-of-measure anymore, and just can write <_>
    // The type inference will figure out that the maxium production has the same unit of measure
    // as the production, that is Barrel/Day
    let maxProductionSA = 9000.0<_>
    /// Maximum production in Venezuela
    let maxProductionVZ = 6000.0<_>

    // Add the maximum production constraints to the model
    petrochem.AddConstraints [|
        0.0<_> <<== buyfromVZ; buyfromVZ <<== maxProductionVZ;
        0.0<_> <<== buyfromSA ; buyfromSA <<== maxProductionSA 
    |]
    |> ignore

    // Add the production constraints: How much of gasoline, jet fuel and machine lubricants
    // can we refine from the oil from the two supplier countries?
    let c1 = petrochem.AddConstraint (0.3*buyfromSA + 0.4*buyfromVZ >>== 2000.0<Barrel/Day>)
    let c2 = petrochem.AddConstraint (0.4*buyfromSA + 0.2*buyfromVZ >>== 1500.0<Barrel/Day>)
    let c3 = petrochem.AddConstraint (0.2*buyfromSA + 0.3*buyfromVZ >>== 500.0<Barrel/Day>)
    
    /// Business goal: minimize the running costs
    // Note that running cost has the unit Dollar/Day, as all input is also in Barrel/Day
    // Due to the type inference, the unit Dollar/Day may be written as
    // Dollar productionRate / Barrel, which simplifies to Dollar/Day
    let runningCost = petrochem.AddGoal (GoalKind.Minimize, 20.0<Dollar/Barrel>*buyfromSA + 15.0<Dollar/Barrel>*buyfromVZ)
    
    /// Solution to the petrochem example
    let petrochemSolution = petrochem.Solve()
    System.Console.WriteLine("Solution quality: {0}", petrochemSolution.Quality)
    
    // Note that we have to strip off the unit-of-measure before we can output it in printf
    printfn "vz: %f, sa: %f" (buyfromVZ.Value |> float) (buyfromSA.Value |> float)
    printfn "Goal value: %f" (runningCost.Value |> float)
    
    // Remove constraint and re-solve:
    petrochem.RemoveConstraint c1
    petrochem.Solve() |> ignore
    printfn "Solution after removing constraint 1:"    
    printfn "vz: %f, sa: %f" (buyfromVZ.Value |> float) (buyfromSA.Value |> float)
    printfn "Goal value: %f" (runningCost.Value |> float)
    
    // ===================================================================
    // Example 2: Discrete combinatorial optimization
    // This is the CubicHypotenuse example from the MSF code samples
    // ===================================================================
    // the OML original is:
    //      Model[
    //        Decisions[Integers, a, b, c, d],
    //        Constraints[
    //          1 <= a <= 20,
    //          0 < d,
    //          d <= c <= b,
    //          a*a == b*b + c*c + d*d
    //        ]
    //      ];

    printfn "--------------------------------"
    printfn "Cubic hypotenuse example:"
    // MSF does not allow multiple model to be created in a context. Before we can 
    // create a new model, we need to clear the old model from the context.
    context.ClearModel()
    /// Model for the cubic hypotenuse example
    let cubicHypo = new SfsModel(context)
    
    // We add 4 integer variables. At the time of declaration, the units of measure are left 
    // open. Later, when we add the constraints, F#s type inference will figure out 
    // that each of the 4 variables are in fact meters
    // In addition, we give each variable a string name here. This will come in handy when we
    // later print out the solution report - if we omit the names, the variables in the report
    // will just bear dummy names like SfsWrapperVar#1
    let varA = cubicHypo.CreateIntVariable<_> "a"
    let varB = cubicHypo.CreateIntVariable<_> "b"
    let varC = cubicHypo.CreateIntVariable<_> "c"
    let varD = cubicHypo.CreateIntVariable<_> "d"
    /// Note that the term a^2 has the unit of measure Meter*Meter
    let surfaceOfA = varA * varA

    // Note that here only minimal annotation with units of measure is required.
    cubicHypo.AddConstraints ("Bounds", 
        [| 
            1<_> <<== varA ; 
            varA <<== 20<Meter> ;
            0<_> <<<< varD;
            varD <<== varC; 
            varC <<== varB
        |]
    )
    |> ignore
        
    cubicHypo.AddConstraints ("Surface", [| surfaceOfA ==== varB * varB + varC * varC + varD * varD |] )
    |> ignore
    
    let cubicHypoSolution = cubicHypo.Solve(ConstraintProgramming)
    
    System.Console.WriteLine("Solution quality: {0}", cubicHypoSolution.Quality)
    printfn "Solution report:"
    System.Console.WriteLine("{0}", cubicHypoSolution.GetReport())
    
    printfn "a: %i, b: %i, c: %i, d: %i" (varA.Value |> int) (varB.Value |> int) (varC.Value |> int) (varD.Value |> int)
    
    // ===================================================================
    // Example 3: Integer programming
    // Assignment problem: We have a number of goods that we can sell to
    // different buyers. Each buyer has a different valuation for the goods.
    // How can we assign goods to buyers to optimize buyer welfare?
    // ===================================================================

    printfn "--------------------------------"
    printfn "Integer programming example: Assignment game"
    context.ClearModel()
        
    // Concretely, our goods are advertising slots on a search engine result page.
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
        ads
        |> Array.map (fun ad -> 
            slots |> Array.map (fun slot -> ad.ClickThroughRates.[slot] * ad.Bid )
        )  
    /// Model for the assignment game (integer programming)
    let assignment = new SfsModel(context)
    /// Assignment variables: x_ij = 1 if ad i is assigned to slot j
    let x = w |> Array.map (Array.map (fun _ -> assignment.CreateIntVariable()))
    /// For arrays of arrays, this returns a "column slice" at column j
    let ColumnSlice j (a: 'a array array) = a |> Array.map (fun xi -> xi.[j])
    /// Map for arrays of arrays
    let Map2 f = Array.map (Array.map f)
    /// Collect for arrays of arrays
    let Collect2 f = Array.map (Array.collect f) >> Array.concat
    /// Constraint 1: Each ad can at most be assigned to one slot: for all i: sum_j x_ij <= 1
    let adConstraints = 
        x |> Array.map (fun xi -> (assignment.Sum xi) <<== 1)
    assignment.AddConstraints adConstraints |> ignore
    /// Constraint 2: Each slot can have at most one ad: for all j: sum_i x_ij <= 1
    let slotConstraints = 
        slots 
        |> Array.mapi (fun j _ -> ColumnSlice j x) 
        |> Array.map (fun s -> assignment.Sum s <<== 1)
    assignment.AddConstraints slotConstraints |> ignore
    /// Constraint 3: Assignment variables can only be 0 or 1
    let boundConstraints = 
        x |> Collect2 (fun xij -> [| 0 <<== xij; xij <<== 1 |])
    assignment.AddConstraints boundConstraints |> ignore
    /// Objective function: sum_i sum_j x_ij w_ij
    // Computed by flattening out the arrays of arrays for x and w, multiplying and summing
    let objectiveFunction = 
        Array.map2 (fun wij xij -> wij*xij) (Array.concat w) (Array.concat x)
        |> assignment.Sum
    /// SFS goal: maximize the welfare
    let welfareGoal = assignment.AddGoal(GoalKind.Maximize, objectiveFunction)

    printfn "Variables x_ij before optimization:"
    x |> Array.iteri (fun i xi -> xi |> Array.iteri (fun j xij -> printfn "x(%i,%i) = %A" i j (xij.TryGetValue())))
    printfn "Objective function before optimization: %A" (welfareGoal.Value)
    /// Solution to the assignment game
    let assignmentSolution = assignment.Solve(Simplex)
    
    System.Console.WriteLine("Solution quality: {0}", assignmentSolution.Quality)
    printfn "Variables x_ij after optimization:"
    x |> Array.iteri (fun i xi -> xi |> Array.iteri (fun j xij -> printfn "x(%i,%i) = %i" i j (xij.Value)))
    printfn "Objective function after optimization: %A" (welfareGoal.Value)

    // Solving the same model as above, but now relaxed as a linear program, 
    // and with constraints written with ForEach operators
    printfn "Solving the assignment problem with linear relaxation, ForEach operators:"
    context.ClearModel()
    /// The ad assignment problem, this time solved via relaxation and with variables that are automatically
    /// constrained to be from a given interval
    let assignment2 = new SfsModel(context)
    /// assignment2 variables: x_ij = 1 if ad i is assigned to slot j
    let x = w |> Array.map (Array.map (fun _ -> assignment2.CreateRealRangeVariable(0.0, 1.0)))
    // Constraint 1: Each ad can at most be assigned to one slot: for all i: sum_j x_ij <= 1
    assignment2.ForEach (x, fun xi -> ((assignment2.Sum xi) <<== 1.0))
    |> assignment2.AddConstraint
    |> ignore
    // Constraint 2: Each slot can have at most one ad: for all j: sum_i x_ij <= 1
    let columns = 
        slots 
        |> Array.mapi (fun j _ -> ColumnSlice j x)
    let slotConstraints = 
        assignment2.ForEach(columns, fun s -> assignment2.Sum s <<== 1.0)
        |> assignment2.AddConstraint
        |> ignore
    /// Objective function: sum_i sum_j x_ij w_ij
    /// Computed by flattening out the arrays of arrays for x and w, multiplying and summing
    let objectiveFunction = 
        Array.map2 (fun wij xij -> wij*xij) (Array.concat w) (Array.concat x)
        |> assignment2.Sum
    let welfareGoal2 = assignment2.AddGoal(GoalKind.Maximize, objectiveFunction)

    let assignment2Solution = assignment2.Solve(Simplex)
    
    System.Console.WriteLine("Solution quality: {0}", assignment2Solution.Quality)
    printfn "Variables x_ij after optimization:"
    x |> Array.iteri (fun i xi -> xi |> Array.iteri (fun j xij -> printfn "x(%i,%i) = %f" i j (xij.Value)))
    printfn "Objective function after optimization: %A" (welfareGoal2.Value)

    // ===================================================================
    // Example 4: Constraint programming, coloring a map
    // Can we color a simple map with Belgium, Netherlands, France and Italy such that
    // no two neighboring countries have the same color?
    // ===================================================================

    printfn "--------------------------------"
    printfn "Constraint programming example: Coloring a map"
    
    context.ClearModel()
    /// Model for the constraint programming example (coloring a map)
    let colorMap = new SfsModel(context)
    
    /// Discrete optimization variable: Color for Belgium
    // Note that we create the enumeration variable from an F# enum type
    let be = colorMap.CreateSymbolicVariable<Color>()
    /// Discrete optimization variable: Color for Deutschland
    let de = colorMap.CreateSymbolicVariable<Color>()
    /// Discrete optimization variable: Color for France
    let fr = colorMap.CreateSymbolicVariable<Color>()
    /// Discrete optimization variable: Color for Netherlands
    let nl = colorMap.CreateSymbolicVariable<Color>()

    // Add the constraints that neighboring countries don't have the same color
    colorMap.AddConstraints [|
        be <<>> de ;
        be <<>> fr ;
        be <<>> nl ;
        de <<>> fr ;
        de <<>> nl
    |]
    |> ignore
    
    /// Solution to the map coloring problem
    let colorMapSolution = colorMap.Solve(ConstraintProgramming)
    
    printfn "Variables after optimization:"
    printfn "be: %s" (be.Value.ToString())
    printfn "de: %s" (de.Value.ToString())
    printfn "fr: %s" (fr.Value.ToString())
    printfn "nl: %s" (nl.Value.ToString())

    printfn "Demo finished, press any key to end."
    System.Console.ReadKey() |> ignore

    ()