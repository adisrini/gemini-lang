signature MAIN =
sig
  val go : string -> unit
end

structure Main : MAIN =
struct

  structure P = PrintAbsyn
  structure E = Env

  fun go filename =
    let
      val ast = Parse.parse filename
      val (menv, explicitAST) = Decorate.decorateProg ast
      val () = print("===== AST =====\n")
      val () = P.print(TextIO.stdOut, explicitAST)
      val () = print("===== MENV =====\n")
      val () = E.print(TextIO.stdOut, menv, Types.toString)
    in
      ()
    end

end
