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
      val (smap', inferredAST) = Infer.inferProg (smap, explicitAST)
      val () = print("===== SMAP POST-INFERENCE =====\n")
      val () = S.print(TextIO.stdOut, smap', Types.toString)
      (* monomorphize 
          * pull modules out into "toplevel" with everything monomorphized
          * module_123_g_int_int
          * rewrite module body and replace module call with new name
          * symbol table: map from symbol module names -> (definition of module * ref map from list of types -> name of monomorphic version of that module)
      *)
      val evalValue = Evaluate.evalProg inferredAST
      val () = case evalValue of
                    Value.ModuleVal(m, namedArgs) => print(Value.toString(m(namedArgs)) ^ "\n")
                  | _ => ()
    in
      ()
    end

end
