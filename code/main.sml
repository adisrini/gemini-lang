signature MAIN =
sig
  val go : string -> unit
end

structure Main : MAIN =
struct

  structure P = PrintAbsyn
  structure E = Env
  structure S = Symbol

  exception TopLevelError

  val debug = true

  fun go filename =
    let
      val () = if not (String.isSuffix ".gm" filename) then (raise Fail "cannot compile file without .gm extension") else ()

      (* PARSING *)
      val ast = Parse.parse filename

      (* DECORATING *)
      val (smap, explicitAST) = Decorate.decorateProg ast
      val () = if debug then print("===== AST =====\n") else ()
      val () = if debug then P.print(TextIO.stdOut, ast) else ()
      val () = if debug then print("===== EXPLICIT AST =====\n") else ()
      val () = if debug then P.print(TextIO.stdOut, explicitAST) else ()
      val () = if debug then print("===== SMAP =====\n") else ()
      val () = if debug then S.print(TextIO.stdOut, smap, Types.toString) else ()

      (* INFERRING *)
      val (smap', inferredAST) = Infer.inferProg (smap, explicitAST)
      val () = if debug then print("===== SMAP POST-INFERENCE =====\n") else ()
      val () = if debug then S.print(TextIO.stdOut, smap', Types.toString) else ()

      (* EVALUATING *)
      val evalValue = Evaluate.evalProg inferredAST
      val (hwTree, namedArgs) = case evalValue of
                                     Value.ModuleVal(m, namedArgs) => (m(namedArgs), namedArgs)
                                   | _ => (ErrorMsg.error 0 "return value of program must be a module"; raise TopLevelError)
      val () = if debug then print("===== MODULE BODY =====\n") else ()
      val () = if debug then print(Value.toString(hwTree) ^ "\n") else ()

      (* GENERATING *)
      val () = if debug then print("===== VERILOG =====\n") else ()
      val () = Generate.genProg(String.substring(filename, 0, size(filename) - 3), namedArgs, hwTree)
    in
      ()
    end

end
