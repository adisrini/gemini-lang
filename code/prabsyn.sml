structure PrintAbsyn :
     sig val print : TextIO.outstream * Absyn.exp -> unit end =
struct

  structure A = Absyn

fun print (outstream, e0) =
 let
  fun say s =  TextIO.output(outstream,s)

  fun sayln s = (say s; say "\n")

  fun indent 0 = ()
    | indent i = (say " "; indent(i - 1))

  fun opname A.IntPlusOp = "IntPlusOp"
    | opname A.IntMinusOp = "IntMinusOp"
    | opname A.IntTimesOp = "IntTimesOp"
    | opname A.IntDivideOp = "IntDivideOp"
    | opname A.IntModOp = "IntModOp"
    | opname A.RealPlusOp = "RealPlusOp"
    | opname A.RealMinusOp = "RealMinusOp"
    | opname A.RealTimesOp = "RealTimesOp"
    | opname A.RealDivideOp = "RealDivideOp"
    | opname A.BitNotOp = "BitNotOp"
    | opname A.BitAndOp = "BitAndOp"
    | opname A.BitOrOp = "BitOrOp"
    | opname A.BitXorOp = "BitXorOp"
    | opname A.BitDoubleAndOp = "BitDoubleAndOp"
    | opname A.BitDoubleOrOp = "BitDoubleOrOp"
    | opname A.BitDoubleXorOp = "BitDoubleXorOp"
    | opname A.BitSLLOp = "BitSLLOp"
    | opname A.BitSRLOp = "BitSRLOp"
    | opname A.BitSRAOp = "BitSRAOp"
    | opname A.BitOrReduceOp = "BitOrReduceOp"
    | opname A.BitAndReduceOp = "BitAndReduceOp"
    | opname A.BitXorReduceOp = "BitXorReduceOp"
    | opname A.EqOp = "EqOp"
    | opname A.NeqOp = "NeqOp"
    | opname A.LtOp = "LtOp"
    | opname A.LeOp = "LeOp"
    | opname A.GtOp = "GtOp"
    | opname A.GeOp = "GeOp"
    | opname A.ConsOp = "ConsOp"

  fun dolist d f [a] = (sayln ""; f(a, d + 1))
    | dolist d f (a::r) = (sayln ""; f(a, d + 1); say ","; dolist d f r)
    | dolist d f nil = ()

  fun f((name, e, pos), d) = (indent d; say "("; say(Symbol.name name); sayln ":"; exp(e, d + 1); say ")")

  and print_field({name, escape, ty = tyopt, pos}, d) =
      (indent d; sayln "Field(";
       indent (d + 1); say(Symbol.name name); sayln ",";
       indent (d + 1); say(Bool.toString(!escape)); sayln ",";
       case tyopt of NONE => (indent (d + 1); say "NONE") | SOME t => ty(t, d + 1); sayln "";
       indent d; say ")")

  and print_param(A.NoParam, d) = (indent d; say "NoParam")
    | print_param(A.SingleParam(fld), d) = (indent d; sayln "SingleParam("; print_field(fld, d + 1); sayln ""; indent d; say ")")
    | print_param(A.MultiParams(flds), d) = (indent d; say "MultiParams["; dolist d print_field flds; sayln "]")

  and m({match, result, pos}, d) = (indent d; sayln "("; exp(match, d + 1); sayln "=>"; exp(result, d + 1); sayln ""; indent d; say ")")

  and exp(A.StructsSigsExp(structsigs), d) = (indent d; say "StructsSigsExp["; dolist d ss structsigs; say "]")
    | exp(A.VarExp(sym, pos), d) = (indent d; say "VarExp("; say(Symbol.name sym); say ")")
    | exp(A.IntExp(i, pos), d) = (indent d; say "IntExp("; say(Int.toString i); say ")")
    | exp(A.StringExp(s, pos), d) = (indent d; say "StringExp(\""; say s; say "\")")
    | exp(A.RealExp(r, pos), d) = (indent d; say "RealExp("; say(Real.toString r); say ")")
    | exp(A.BitExp(b, pos), d) = (indent d; say "BitExp("; say(GeminiBit.toString b); say ")")
    | exp(A.ApplyExp(e1, e2, pos), d) = (indent d; sayln "ApplyExp("; exp(e1, d + 1); sayln ","; exp(e2, d + 1); sayln ""; indent d; say ")")
    | exp(A.NilExp(p), d) = (indent d; say "NilExp")
    | exp(A.BinOpExp{left, oper, right, pos}, d) = (indent d; sayln "BinOpExp("; indent (d + 1); say(opname oper); sayln ","; exp(left, d + 1); sayln ","; exp(right, d + 1); sayln ""; indent d; say ")")
    | exp(A.UnOpExp{exp = e, oper, pos}, d) = (indent d; sayln "UnOpExp("; indent (d + 1); say(opname oper); sayln ","; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.LetExp{decs, body, pos}, d) = (indent d; say "LetExp(["; dolist d dec decs; sayln "],"; exp(body, d + 1); sayln ""; indent d; say ")")
    | exp(A.AssignExp{lhs, rhs, pos}, d) = (indent d; sayln "AssignExp("; exp(lhs, d + 1); sayln ","; exp(rhs, d + 1); sayln ""; indent d; say ")")
    | exp(A.SeqExp(exps), d) = (indent d; say "SeqExp["; dolist d exp (map #1 exps); sayln ""; indent d; say "]")
    | exp(A.IfExp{test, then', else', pos}, d) = (indent d; sayln "IfExp("; exp(test, d + 1); sayln ","; exp(then', d + 1); case else' of NONE => () | SOME e => (sayln ","; exp(e, d + 1)); sayln ""; indent d; say ")")
    | exp(A.ListExp(exps), d) = (indent d; say "ListExp["; dolist d exp (map #1 exps); sayln ""; indent d; say "]")
    | exp(A.ArrayExp(exps), d) = (indent d; say "ArrayExp["; dolist d exp (map #1 (Vector.toList(exps))); sayln ""; indent d; say "]")
    | exp(A.RefExp(e, p), d) = (indent d; sayln "RefExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.SWRecordExp{fields, pos}, d) = (indent d; say "SWRecordExp(["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.HWRecordExp{fields, pos}, d) = (indent d; say "HWRecordExp(["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.SWExp(e, p), d) = (indent d; sayln "SWExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.WithExp{exp = e, fields, pos}, d) = (indent d; sayln "WithExp("; exp(e, d + 1); sayln ","; indent (d + 1); say "["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.DerefExp{exp = e, pos}, d) = (indent d; sayln "DerefExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.StructAccExp{name, field, pos}, d) = (indent d; say "StructAccExp("; say(Symbol.name name); say ", "; say (Symbol.name field); say ")")
    | exp(A.RecordAccExp{exp = e, field, pos}, d) = (indent d; sayln "RecordAccExp("; indent (d + 1); say(Symbol.name field); sayln ","; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.ArrayAccExp{exp = e, index, pos}, d) = (indent d; sayln "ArrayAccExp("; exp(e, d + 1); sayln ","; exp(index, d + 1); sayln ""; indent d; say ")")
    | exp(A.PatternMatchExp{exp = e, cases, pos}, d) = (indent d; sayln "PatternMatchExp("; exp(e, d + 1); sayln ","; indent (d + 1); say "["; dolist (d + 1) m cases; sayln "]"; indent d; say ")")
    | exp(A.BitArrayExp{size, result, spec}, d) = (indent d; sayln "BitArrayExp("; exp(size, d + 1); sayln ","; exp(result, d + 1); case spec of NONE => () | SOME s => (sayln ","; indent (d + 1); say s); sayln ""; indent d; say ")")
    | exp(A.ZeroExp, d) = (indent d; say "ZeroExp")

  and ss(A.StructExp({name, signat, decs, pos}), d) = (indent d; sayln "StructExp("; indent (d + 1); say(Symbol.name name); sayln ","; case signat of NONE => () | SOME (s, _) => (ss(s, d + 1); sayln ","); indent (d + 1); say "["; dolist d dec decs; sayln "]"; indent d; say ")")
    | ss(A.SigExp({name, defs}), d) = (indent d; sayln "SigExp("; indent (d + 1); say(Symbol.name name); sayln ","; indent (d + 1); say "["; dolist d def defs; sayln "]"; indent d; say ")")
    | ss(A.NamedSigExp(sym), d) = (indent d; say "NamedSigExp("; say(Symbol.name sym); say ")")
    | ss(A.AnonSigExp(defs), d) = (indent d; say "AnonSigExp["; dolist d def defs; say "]")

  and def(A.ValDef{name, ty = (t, p), pos}, d) = (indent d; sayln "ValDef("; indent (d + 1); say(Symbol.name name); sayln ","; ty(t, d + 1); sayln ""; indent d; say ")")
    | def(A.TypeDef{name, pos}, d) = (indent d; say "TypeDef("; say(Symbol.name name); say ")")
    | def(A.ModuleDef{name, input_ty, output_ty, pos}, d) = (indent d; sayln "ModuleDef("; indent (d + 1); say(Symbol.name name); sayln ","; ty(input_ty, d + 1); sayln " -> "; ty(output_ty, d + 1); say ")")

  and dec(A.DatatypeDec(datatydecs), d) =
      let
          fun print_datacon({datacon, ty = t, pos}, d) =
            (indent d; sayln "Datacon(";
             indent (d + 1); say (Symbol.name datacon); sayln ",";
             ty(t, d + 1); sayln "";
             indent d; say ")")
          fun print_dataty({name, datacons}, d) =
            (indent d; say(Symbol.name name); say "(";
             dolist d print_datacon datacons; sayln "";
             indent d; say ")")
      in
          indent d; say "DatatyDec["; dolist d print_dataty datatydecs; say "]"
      end
    | dec(A.ModuleDec(moddecs), d) =
      let
          fun print_mod({name, arg, result, body, pos}, d) =
            (indent d; say (Symbol.name name); say "(";
             dolist d print_param [arg]; sayln ",";
             indent (d + 1);
             case result of NONE => say "NONE"
                          | SOME(t, _) => (sayln "SOME("; ty(t, d + 1); sayln ""; indent d; say ")");
             sayln ",";
             exp(body, d + 1); sayln "";
             indent d; say ")")
      in
        indent d; say "ModuleDec["; dolist d print_mod moddecs; say "]"
      end
    | dec(A.FunctionDec(fundecs), d) =
	    let
          fun func({name, params, result, body, pos}, d) =
              (indent d; say (Symbol.name name); say "([";
		           dolist d print_param params; sayln "],";
               indent (d + 1);
		           case result of NONE => say "NONE"
			                      | SOME(t, _) => (sayln "SOME("; ty(t, d + 1); sayln ""; indent d; say ")");
               sayln ",";
               exp(body, d + 1); sayln "";
               indent d; say ")")
	    in
          indent d; say "FunctionDec["; dolist d func fundecs; say "]"
	    end
    | dec(A.ValDec(valdecs), d) =
      let
          fun vald({name, init, ty = tyo, escape, pos}, d) =
            (indent d; say(Symbol.name name); sayln "(";
             indent d; say(Bool.toString (!escape)); sayln ",";
             indent d; case tyo of NONE => say "NONE"
                                       | SOME(t, p)=> (sayln "SOME("; ty(t, d + 1); sayln ""; indent d; say ")");
             sayln ",";
             exp(init, d); sayln "";
             indent d; say ")")
      in
          indent d; say "ValDec["; dolist d vald valdecs; say "]"
      end
    | dec(A.TypeDec(tydecs), d) =
	    let
          fun opd({oper, param_a, param_b, body, pos}, d) =
              (indent d; sayln "Opdef(";
               indent (d + 1); say(opname oper); sayln ",";
               indent (d + 1); say(Symbol.name param_a); sayln ",";
               indent (d + 1); say(Symbol.name param_b); sayln ",";
               exp(body, d + 1); sayln "";
               indent d; say ")")
          fun tdec({name, ty = t, opdef, pos}, d) =
              (indent d; say(Symbol.name name); sayln "(";
					     ty(t, d + 1); sayln ",";
               case opdef of NONE => ()
                           | SOME(opds) => (indent (d + 1); say "["; dolist d opd opds; sayln "]");
               indent d; say ")")
      in
          indent d; say "TypeDec["; dolist d tdec tydecs; say "]"
      end

  and ty(A.NameTy(s, p), d) = (indent d; say "NameTy("; say(Symbol.name s); say ")")
    | ty(A.GenericTy(s, p), d) = (indent d; say "GenericTy("; say(Symbol.name s); say ")")
    | ty(A.SWRecordTy(fields, p), d) = (indent d; say "SWRecordTy["; dolist d print_field fields; sayln ""; indent d; say "]")
    | ty(A.HWRecordTy(fields, p), d) = (indent d; say "HWRecordTy["; dolist d print_field fields; sayln ""; indent d; say "]")
    | ty(A.ArrayTy(t, e, p), d) = (indent d; sayln "ArrayTy("; ty(t, d + 1); sayln ","; exp(e, d + 1); sayln ""; indent d; say ")")
    | ty(A.ListTy(t, p), d) = (indent d; sayln "ListTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.TemporalTy(t, e, p), d) = (indent d; sayln "TemporalTy("; ty(t, d + 1); sayln " @ "; exp(e, d + 1); sayln ""; indent d; say ")")
    | ty(A.RefTy(t, p), d) = (indent d; sayln "RefTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.SWTy(t, p), d) = (indent d; sayln "SWTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.FunTy(t1, t2, p), d) = (indent d; sayln "FunTy("; ty(t1, d + 1); sayln " -> "; ty(t2, d + 1); sayln ""; indent d; say ")")
    | ty(A.GroupedTy(t, p), d) = (indent d; sayln "GroupedTy("; ty(t, d + 1); sayln ""; indent d; say ")")
 in
    exp(e0, 0); sayln ""; TextIO.flushOut outstream
 end

end
