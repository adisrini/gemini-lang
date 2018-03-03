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
      val (smap, explicitAST) = Decorate.decorateProg ast
      val () = print("===== AST =====\n")
      val () = P.print(TextIO.stdOut, ast)
      val () = print("===== EXPLICIT AST =====\n")
      val () = P.print(TextIO.stdOut, explicitAST)
      val () = print("===== SMAP =====\n")
      val () = S.print(TextIO.stdOut, smap, Types.toString)
      val smap' = Infer.inferProg (smap, explicitAST)
      val () = print("===== SMAP POST-INFERENCE =====\n")
      val () = S.print(TextIO.stdOut, smap', Types.toString)
    in
      ()
    end

end
