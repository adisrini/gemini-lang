signature MAIN =
sig
  val go : string -> unit
end

structure Main : MAIN =
struct

  structure P = PrintAbsyn
  structure E = Env
  structure S = Symbol

  fun go filename =
    let
      val ast = Parse.parse filename
      val (menv, explicitAST) = Decorate.decorateProg ast
      val () = print("===== AST =====\n")
      val () = P.print(TextIO.stdOut, explicitAST)
      val () = print("===== MENV =====\n")
      val () = S.print(TextIO.stdOut, menv, Types.toString)
      (* val smap = Infer.inferProg (menv, explicitAST)
      val () = print("===== SMAP =====\n")
      val () = S.print(TextIO.stdOut, smap, Types.toString) *)
    in
      ()
    end

end
