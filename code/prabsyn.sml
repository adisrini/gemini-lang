structure PrintAbsyn :
     sig val print : TextIO.outstream * Absyn.exp -> unit end =
struct

  structure A = Absyn
  structure T = Types

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

  and print_field({name, escape, ty = t, pos}, d) =
      (indent d; sayln "Field(";
       indent (d + 1); say(Symbol.name name); sayln ",";
       indent (d + 1); say(Bool.toString(!escape)); sayln ",";
       ty(t, d + 1); sayln "";
       indent d; say ")")

  and print_param(A.NoParam, d) = (indent d; say "NoParam")
    | print_param(A.SingleParam(fld), d) = (indent d; sayln "SingleParam("; print_field(fld, d + 1); sayln ""; indent d; say ")")
    | print_param(A.TupleParams(flds), d) = (indent d; say "TupleParams["; dolist d print_field flds; sayln "]")
    | print_param(A.RecordParams(flds), d) = (indent d; say "RecordParams["; dolist d print_field flds; sayln "]")

  and m({match, result, pos}, d) = (indent d; sayln "("; exp(match, d + 1); sayln "=>"; exp(result, d + 1); sayln ""; indent d; say ")")

  and exp(A.StructsSigsExp(structsigs), d) = (indent d; say "StructsSigsExp["; dolist d ss structsigs; say "]")
    | exp(A.VarExp(sym, pos), d) = (indent d; say "VarExp("; say(Symbol.name sym); say ")")
    | exp(A.IntExp(i, pos), d) = (indent d; say "IntExp("; say(Int.toString i); say ")")
    | exp(A.StringExp(s, pos), d) = (indent d; say "StringExp(\""; say s; say "\")")
    | exp(A.RealExp(r, pos), d) = (indent d; say "RealExp("; say(Real.toString r); say ")")
    | exp(A.BitExp(b, pos), d) = (indent d; say "BitExp("; say(GeminiBit.toString b); say ")")
    | exp(A.ApplyExp(e1, e2, pos), d) = (indent d; sayln "ApplyExp("; exp(e1, d + 1); sayln ","; exp(e2, d + 1); sayln ""; indent d; say ")")
    | exp(A.ParameterApplyExp(e1, e2, pos), d) = (indent d; sayln "ParameterApplyExp("; exp(e1, d + 1); sayln ","; exp(e2, d + 1); sayln ""; indent d; say ")")
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
    | exp(A.UnSWExp(e, p), d) = (indent d; sayln "UnSWExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.WithExp{exp = e, fields, pos}, d) = (indent d; sayln "WithExp("; exp(e, d + 1); sayln ","; indent (d + 1); say "["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.DerefExp{exp = e, pos}, d) = (indent d; sayln "DerefExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.StructAccExp{name, field, pos}, d) = (indent d; say "StructAccExp("; say(Symbol.name name); say ", "; say (Symbol.name field); say ")")
    | exp(A.RecordAccExp{exp = e, field, pos}, d) = (indent d; sayln "RecordAccExp("; indent (d + 1); say(Symbol.name field); sayln ","; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.ArrayAccExp{exp = e, index, pos}, d) = (indent d; sayln "ArrayAccExp("; exp(e, d + 1); sayln ","; exp(index, d + 1); sayln ""; indent d; say ")")
    | exp(A.PatternMatchExp{exp = e, cases, pos}, d) = (indent d; sayln "PatternMatchExp("; exp(e, d + 1); sayln ","; indent (d + 1); say "["; dolist (d + 1) m cases; sayln "]"; indent d; say ")")
    | exp(A.BitArrayGenExp{size, counter, genfun, pos}, d) = (indent d; sayln "BitArrayGenExp("; exp(size, d + 1); sayln ","; indent (d + 1); sayln (Symbol.name(counter) ^ ","); exp(genfun, d + 1); indent d; say ")")
    | exp(A.BitArrayConvExp{size, value, spec, pos}, d) = (indent d; sayln "BitArrayConvExp("; exp(size, d + 1); sayln ","; exp(value, d + 1); indent (d + 1); sayln (spec ^ ","); indent d; say ")")

  and ss(A.StructExp({name, signat, decs, pos}), d) = (indent d; sayln "StructExp("; indent (d + 1); say(Symbol.name name); sayln ","; case signat of NONE => () | SOME (s, _) => (ss(s, d + 1); sayln ","); indent (d + 1); say "["; dolist d dec decs; sayln "]"; indent d; say ")")
    | ss(A.SigExp({name, defs}), d) = (indent d; sayln "SigExp("; indent (d + 1); say(Symbol.name name); sayln ","; indent (d + 1); say "["; dolist d def defs; sayln "]"; indent d; say ")")
    | ss(A.NamedSigExp(sym), d) = (indent d; say "NamedSigExp("; say(Symbol.name sym); say ")")
    | ss(A.AnonSigExp(defs), d) = (indent d; say "AnonSigExp["; dolist d def defs; say "]")

  and def(A.ValDef{name, ty = (t, p), pos}, d) = (indent d; sayln "ValDef("; indent (d + 1); say(Symbol.name name); sayln ","; ty(t, d + 1); sayln ""; indent d; say ")")
    | def(A.TypeDef{name, pos}, d) = (indent d; say "TypeDef("; say(Symbol.name name); say ")")
    | def(A.ModuleDef{name, input_ty, output_ty, pos}, d) = (indent d; sayln "ModuleDef("; indent (d + 1); say(Symbol.name name); sayln ","; ty(input_ty, d + 1); sayln " -> "; ty(output_ty, d + 1); say ")")

  and dec(A.SWDatatypeDec(datatydecs), d) =
      let
          fun print_datacon({datacon, ty = t, pos}, d) =
            (indent d; sayln "Datacon(";
             indent (d + 1); say (Symbol.name datacon); sayln ",";
             ty(t, d + 1); sayln "";
             indent d; say ")")
          fun print_dataty({name, tyvars, datacons}, d) =
            (indent d; say(Symbol.name name); say "(";
            case tyvars of
                 SOME(xs) => (sayln ""; indent (d + 1); say "TYVARS["; dolist (d + 1) (fn(s, d) => (indent d; say(Symbol.name(s)))) xs; sayln ""; indent (d + 1); say "],")
               | NONE => ();
             dolist d print_datacon datacons; sayln "";
             indent d; say ")")
      in
          indent d; say "SWDatatyDec["; dolist d print_dataty datatydecs; say "]"
      end
    | dec(A.HWDatatypeDec(datatydecs), d) =
        let
            fun print_datacon({datacon, ty = t, pos}, d) =
              (indent d; sayln "Datacon(";
               indent (d + 1); say (Symbol.name datacon); sayln ",";
               ty(t, d + 1); sayln "";
               indent d; say ")")
            fun print_dataty({name, tyvars, datacons}, d) =
              (indent d; say(Symbol.name name); say "(";
               case tyvars of
                    SOME(xs) => (sayln ""; indent (d + 1); say "TYVARS["; dolist (d + 1) (fn(s, d) => (indent d; say(Symbol.name(s)))) xs; sayln ""; indent (d + 1); say "],")
                  | NONE => ();
               dolist d print_datacon datacons; sayln "";
               indent d; say ")")
        in
            indent d; say "HWDatatyDec["; dolist d print_dataty datatydecs; say "]"
        end
    | dec(A.ModuleDec(moddecs), d) =
      let
          fun print_mod({name, arg, sw_arg, result = (t, p), body, pos}, d) =
            (indent d; say (Symbol.name name); say "(";
             dolist d print_param [arg]; sayln ",";
             case sw_arg of
                SOME(x) => (dolist d print_param [x]; sayln",")
              | _ => ();
             ty(t, d + 1);
             sayln ",";
             exp(body, d + 1); sayln "";
             indent d; say ")")
      in
        indent d; say "ModuleDec["; dolist d print_mod moddecs; say "]"
      end
    | dec(A.FunctionDec(fundecs), d) =
	    let
          fun func({name, params, result = (t, p), body, pos}, d) =
              (indent d; say (Symbol.name name); say "([";
		           dolist d print_param params; indent d; sayln "],";
		           ty(t, d + 1);
               sayln ",";
               exp(body, d + 1); sayln "";
               indent d; say ")")
	    in
          indent d; say "FunctionDec["; dolist d func fundecs; say "]"
	    end
    | dec(A.ValDec(valdecs), d) =
      let
          fun vald({name, init, ty = (t, p), escape, pos}, d) =
            (indent d; say(Symbol.name name); sayln "(";
             indent d; say(Bool.toString (!escape)); sayln ",";
             ty(t, d);
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
          fun tdec({name, ty = t, tyvars, opdef, pos}, d) =
              (indent d; say(Symbol.name name); sayln "(";
              case tyvars of NONE => ()
                           | SOME(tyvs) => (indent (d + 1); say "TYVARS["; dolist (d + 1) (fn(s, d) => (indent d; say(Symbol.name(s)))) tyvs; sayln ""; indent (d + 1); sayln "],");
					     ty(t, d + 1); sayln ",";
               case opdef of NONE => ()
                           | SOME(opds) => (indent (d + 1); say "["; dolist d opd opds; sayln "]");
               indent d; say ")")
      in
          indent d; say "TypeDec["; dolist d tdec tydecs; say "]"
      end

  and ty(A.NameTy(s, p), d) = (indent d; say "NameTy("; say(Symbol.name s); say ")")
    | ty(A.ParameterizedTy(s, tys, p), d) = (indent d; sayln "ParameterizedTy("; indent(d + 1); say(Symbol.name s); sayln ",";  dolist (d + 1) ty tys; sayln ""; indent d; say ")")
    | ty(A.TyVar(s, p), d) = (indent d; say "TyVar("; say(Symbol.name s); say ")")
    | ty(A.SWRecordTy(fields, p), d) = (indent d; say "SWRecordTy["; dolist d print_field fields; sayln ""; indent d; say "]")
    | ty(A.HWRecordTy(fields, p), d) = (indent d; say "HWRecordTy["; dolist d print_field fields; sayln ""; indent d; say "]")
    | ty(A.ArrayTy(t, i, p), d) = (indent d; sayln "ArrayTy("; ty(t, d + 1); sayln ","; say (Int.toString(i)); sayln ""; indent d; say ")")
    | ty(A.ListTy(t, p), d) = (indent d; sayln "ListTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.TemporalTy(t, i, p), d) = (indent d; sayln "TemporalTy("; ty(t, d + 1); sayln " @ "; say (Int.toString(i)); sayln ""; indent d; say ")")
    | ty(A.RefTy(t, p), d) = (indent d; sayln "RefTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.SWTy(t, p), d) = (indent d; sayln "SWTy("; ty(t, d + 1); sayln ""; indent d; say ")")
    | ty(A.FunTy(t1, t2, p), d) = (indent d; sayln "FunTy("; ty(t1, d + 1); sayln " -> "; ty(t2, d + 1); sayln ""; indent d; say ")")
    | ty(A.PlaceholderTy(_), d) = (indent d; say "PlaceholderTy()")
    | ty(A.NoTy, d) = (indent d; say "NoTy")
    | ty(A.ExplicitTy(t), d) = (indent d; sayln "ExplicitTy("; realTy(t, d + 1); sayln ""; indent d; say ")")

  and realTy(t, d) =
    let
      fun sfield((tyv, s), d) = (indent d; say (Symbol.name(tyv)); say ": "; sty(s, d+1))
      and saytyvar(tyv, d) = (indent d; say (Symbol.name(tyv)))
      and stycon((tyv, s_opt), d) = (indent d; say (Symbol.name(tyv)); (case s_opt of SOME(s) => (sayln ": "; sty(s, d+1)) | NONE => ()))
      and htycon((tyv, h_opt), d) = (indent d; say (Symbol.name(tyv)); (case h_opt of SOME(h) => (sayln ": "; hty(h, d+1)) | NONE => ()))
      and sty(T.INT, d) = (indent d; say "INT")
        | sty(T.STRING, d) = (indent d; say "STRING")
        | sty(T.REAL, d) = (indent d; say "REAL")
        | sty(T.ARROW(s1, s2), d) = (indent d; sayln "ARROW("; sty(s1, d + 1); sayln "->"; sty(s2, d + 1); sayln ""; indent d; say ")")
        | sty(T.LIST(s), d) = (indent d; sayln "LIST("; sty(s, d + 1); sayln ""; indent d; say ")")
        | sty(T.SW_H(h), d) = (indent d; sayln "SW_H("; hty(h, d + 1); sayln ""; indent d; say ")")
        | sty(T.SW_M(m), d) = (indent d; sayln "SW_M("; mty(m, d + 1); sayln ""; indent d; say ")")
        | sty(T.S_RECORD(fields), d) = (indent d; say "S_RECORD(["; dolist (d + 1) sfield fields; say "])")
        | sty(T.REF(s), d) = (indent d; sayln "REF("; sty(s, d + 1); sayln ""; indent d; say ")")
        | sty(T.S_DATATYPE(tycons, u), d) = (indent d; say "S_DATATYPE(["; dolist (d + 1) stycon tycons; say "])")
        | sty(T.S_META(tyv), d) = (indent d; say "S_META("; say (Symbol.name(tyv)); say ")")
        | sty(T.S_TOP, d) = (indent d; say "S_TOP")
        | sty(T.S_BOTTOM, d) = (indent d; say "S_BOTTOM")
        | sty(T.S_MU(tyvars, s), d) = (indent d; say "S_MU(["; dolist (d + 1) saytyvar tyvars; sayln "],"; sty(s, d + 1); sayln ""; indent d; say ")")
        | sty(T.S_POLY(tyvars, s), d) = (indent d; say "S_POLY(["; dolist (d + 1) saytyvar tyvars; sayln "],"; sty(s, d + 1); sayln ""; indent d; say ")")
      and hfield((tyv, h), d) = (indent d; say (Symbol.name(tyv)); say ": "; hty(h, 0))
      and hty(T.BIT, d) = (indent d; say "BIT")
        | hty(T.ARRAY{ty, size}, d) = (indent d; sayln "ARRAY("; hty(ty, d + 1); sayln ","; indent (d + 1); say (Int.toString(!size)); sayln ""; indent d; say ")")
        | hty(T.H_RECORD(fields), d) = (indent d; sayln "H_RECORD(["; dolist (d + 1) hfield fields; say "])")
        | hty(T.TEMPORAL{ty, time}, d) = (indent d; sayln "TEMPORAL("; hty(ty, d + 1); sayln ","; indent (d + 1); say (Int.toString(!time)); sayln ""; indent d; say ")")
        | hty(T.H_DATATYPE(tycons, u), d) = (indent d; sayln "H_DATATYPE(["; dolist (d + 1) htycon tycons; say "])")
        | hty(T.H_META(tyv), d) = (indent d; say "H_META("; say (Symbol.name(tyv)); say ")")
        | hty(T.H_TOP, d) = (indent d; say "H_TOP")
        | hty(T.H_BOTTOM, d) = (indent d; say "H_BOTTOM")
        | hty(T.H_POLY(tyvars, h), d) = (indent d; say "H_POLY(["; dolist (d + 1) saytyvar tyvars; sayln "],"; hty(h, d + 1); sayln ""; indent d; say ")")

      and mty(T.MODULE(h1, h2), d) = (indent d; sayln "MODULE("; hty(h1, d + 1); sayln "~>"; hty(h2, d + 1); sayln ""; indent d; say ")")
        | mty(T.PARAMETERIZED_MODULE(s, h1, h2), d) = (indent d; sayln "MODULE("; sty(s, d + 1); sayln "->"; hty(h1, d + 1); sayln "~>"; hty(h2, d + 1); sayln ""; indent d; say ")")
        | mty(T.M_POLY(tyvars, m), d) = (indent d; say "M_POLY(["; dolist (d + 1) saytyvar tyvars; sayln "],"; mty(m, d + 1); sayln ""; indent d; say ")")
        | mty(T.M_BOTTOM, d) = (indent d; say "M_BOTTOM")
    in
      case t of
           T.S_TY(s) => (indent d; sayln "S_TY("; sty(s, d + 1); sayln ""; indent d; say ")")
         | T.H_TY(h) => (indent d; sayln "H_TY("; hty(h, d + 1); sayln ""; indent d; say ")")
         | T.M_TY(m) => (indent d; sayln "M_TY("; mty(m, d + 1); sayln ""; indent d; say ")")
         | T.META(m) => (indent d; say "META("; say (Symbol.name(m)); say ")")
         | T.EMPTY => (indent d; say "EMPTY")
         | T.TOP => (indent d; say "TOP")
         | T.BOTTOM => (indent d; say "BOTTOM")
    end

 in
    exp(e0, 0); sayln ""; TextIO.flushOut outstream
 end

end
