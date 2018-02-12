signature MAIN =
sig
  val go : string -> unit
end

structure Main : MAIN =
struct

  structure P = PrintAbsyn

  fun go filename =
    let
      val ast = Parse.parse filename
      val explicitAST = Decorate.decorateProg ast
      val () = P.print(TextIO.stdOut, explicitAST);
    in
      ()
    end

end
