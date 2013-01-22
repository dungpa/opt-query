module Microsoft.SolverFoundation.FSharpDSL.Query

open Microsoft.FSharp.Quotations
open Microsoft.SolverFoundation.FSharpDSL.Language
open Microsoft.SolverFoundation.FSharpDSL.Compiler
    
type Query<'T> = Query of (unit -> 'T)

let var<[<Measure>] 'T>() = Query var<'T>
let vararray1<[<Measure>] 'T>(n) = Query (fun () -> vararray1<'T>(Seq.empty))

type OptQueryBuilder() = 
    member __.Bind (source: Query<'T>, body: 'T -> Query<'U>) = match source with Query f -> body (f())
    member __.Yield (x: 'T) = Query (fun () -> x)
    member __.Return (x: 'T) = Query (fun () -> x)
    
    [<CustomOperation("assume", MaintainsVariableSpaceUsingBind=true)>]
    member __.Where (x: Query<'T>, [<ProjectionParameter>] body: 'T -> bool) = 
        match x with Query f -> Query (fun() -> body (f()) |> ignore; f())
    [<CustomOperation("minimise", MaintainsVariableSpaceUsingBind=true)>]
    member __.Minimise (x: Query<'T>, [<ProjectionParameter>] body: 'T -> 'U) = 
        match x with Query f -> Query (fun () -> f(), body (f()))
    [<CustomOperation("maximise", MaintainsVariableSpaceUsingBind=true)>]
    member __.Maximise (x: Query<'T>, [<ProjectionParameter>] body: 'T -> 'U) = 
        match x with Query f -> Query (fun () -> f(), body (f()))
    
    member __.Quote (q: Quotations.Expr<_>) = q 
    member __.Run (q: Quotations.Expr<_>) = q

let opt = OptQueryBuilder()

let assume = seq
