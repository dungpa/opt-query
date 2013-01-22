// Taken from http://stackoverflow.com/questions/14110532/extended-computation-expressions-without-for-in-do
// for the purpose of exprimentating with new features
type Command = Left | Right 
type Commands = Commands of Command list

type MovesBuilder() =
  member x.Yield( () ) = 
      Commands[]

  member x.Zero() = Commands []

  member x.Bind(Commands c1, f) = 
    let (Commands c2) = f () in Commands(c1 @ c2)
  member x.For(c, f) = x.Bind(c, f)
  member x.Return(a) = x.Yield(a)

  member x.Combine(Commands c1, Commands c2) = Commands (c1 @ c2)

  [<CustomOperation("left")>]
  member x.Left(Commands c) = Commands(c @ [Left])
  [<CustomOperation("right")>]
  member x.Right(Commands c) = Commands(c @ [Right])

let moves = MovesBuilder()

let lr = 
  moves { left
          right
           }  

let res =
  moves { left
          do! lr
          left 
          do! lr }
  