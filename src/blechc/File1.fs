namespace Blech.Compiler 

module Server =
    type private Bla = private {bla: bool}

    type private S = 
        private {a: int; b: int}
    
    type private Number = int

    let v: S = {a = 1; b = 2}

    [<Literal>]
    let n: Number = 1

    let private x = n


module Client =

    [<Literal>]
    let i = Server.n
    let s = Server.v

    let show () = if i = 1 then printfn "V is: %s" <| string Server.n