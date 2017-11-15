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
    | opname A.TimesOp = "IntTimesOp"
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
    | opname A.BitSLLOp = "BitSLLOp"
    | opname A.BitSRLOp = "BitSRLOp"
    | opname A.BitSRAOp = "BitSRAOp"
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

  (*

  datatype exp =
          | PatternMatchExp of {exp: exp, cases: match list, pos: pos}

  *)

  and f((name, e, pos), d) = (indent d; say "("; say(Symbol.name name); sayln ":"; exp(e, d + 1); say ")")

  and m({match, result, pos}, d) = (indent d; sayln "("; exp(match, d + 1); sayln "=>"; exp(result, d + 1); sayln ""; indent d; say ")")

  and exp(A.StructsSigsExp(structsigs), d) = (indent d; say "StructsSigsExp["; dolist d structsig structsigs; say "]")
    | exp(A.VarExp(sym, pos), d) = (indent d; say "VarExp("; say(Symbol.name sym); say ")")
    | exp(A.IntExp(i, pos), d) = (indent d; say "IntExp("; say(Int.toString i); say ")")
    | exp(A.StringExp(s, pos), d) = (indent d; say "StringExp(\""; say s; say "\")")
    | exp(A.RealExp(r, pos), d) = (indent d; say "RealExp("; say(Real.toString r); say ")")
    | exp(A.BitExp(b, pos), d) = (indent d; say "BitExp("; say(Bit.toString b); say ")")
    | exp(A.ApplyExp(e1, e2, pos), d) = (indent d; sayln "ApplyExp("; exp(e1, d + 1); sayln ","; exp(e2, d + 1); sayln ""; indent d; say ")")
    | exp(A.NilExp, d) = (indent d; say "NilExp")
    | exp(A.OpExp{left, oper, right, pos}, d) = (indent d; sayln "OpExp("; indent (d + 1); say(opname oper); sayln ","; exp(left, d + 1); sayln ","; exp(right, d + 1); sayln ""; indent d; say ")")
    | exp(A.NegExp{e, p}, d) = (indent d; sayln "NegExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.LetExp{decs, body, pos}, d) = (indent d; say "LetExp(["; dolist d dec decs; sayln "],"; exp(body, d + 1); sayln ""; indent d; say ")")
    | exp(A.AssignExp{lhs, rhs, pos}, d) = (indent d; sayln "AssignExp("; exp(lhs, d + 1); sayln "," exp(rhs, d + 1); sayln ""; indent d; say ")")
    | exp(A.SeqExp(exps), d) = (indent d; say "SeqExp["; dolist d exp (map #1 exps); sayln ""; indent d; say "]")
    | exp(A.IfExp{test, then', else', pos}, d) = (indent d; sayln "IfExp("; exp(test, d + 1); sayln ","; exp(then', d + 1); case else' of NONE => () | SOME e => (sayln ","; exp(e, d + 1)); sayln ""; indent d; say ")")
    | exp(A.ListExp(exps), d) = (indent d; say "ListExp["; dolist d exp (map #1 exps); sayln ""; indent d; say "]")
    | exp(A.ArrayExp(exps), d) = (indent d; say "ArrayExp["; dolist d exp (map #1 (Vector.toList(exps))); sayln ""; indent d; say "]")
    | exp(A.RefExp(e, p)) = (indent d; sayln "RefExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.RecordExp{fields, pos}, d) = (indent d; say "RecordExp(["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.HWTupleExp(exps)) = (indent d; say "HWTupleExp["; dolist d exp (map #1 exps); sayln ""; indent d; say "]")
    | exp(A.WithExp{exp = e, fields, pos}) = (indent d; sayln "WithExp("; exp(e, d + 1); sayln ","; indent (d + 1); say "["; dolist d f fields; sayln "]"; indent d; say ")")
    | exp(A.DerefExp{exp = e, pos}) = (indent d; sayln "DerefExp("; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.StructAccExp{name, field, pos}) = (indent d; say "StructAccExp("; say(Symbol.name name); say (Symbol.name field); say ")")
    | exp(A.RecordAccExp{exp = e, field, pos}) = (indent d; sayln "RecordAccExp("; indent (d + 1); say(Symbol.name field); sayln ","; exp(e, d + 1); sayln ""; indent d; say ")")
    | exp(A.ArrayAccExp{exp = e, index, pos}) = (indent d; sayln "ArrayAccExp("; exp(e, d + 1); sayln ","; exp(index, d + 1); sayln ""; indent d; say ")")
    | exp(A.PatternMatchExp{exp = e, cases, pos}) = (indent d; sayln "PatternMatchExp("; exp(e, d + 1); sayln ","; say "["; dolist d m cases; sayln "]"; indent d; say ")")
    | exp(A.BitArrayExp{size, result, spec}) = (indent d; sayln "BitArrayExp("; exp(size, d + 1); sayln ","; exp(result, d + 1); case spec of NONE => () | SOME s => (sayln ","; indent (d + 1); say s); sayln ""; indent d; say ")")
    | exp(A.ZeroExp) = (indent d; say "ZeroExp")

  (* TODO *)
  and structsig StructExp({name, signat, decs, pos}) = ()
    | structsig SigExp({name, defs}) = ()
    | structsig NamedSigExp(sym) = ()
    | structsig AnonSigExp(defs) = ()

  and dec(A.FunctionDec l, d) =
	    let fun field({name,escape,typ,pos},d) =
			(indent d; say "("; say(Symbol.name name);
			 say ","; say(Bool.toString(!escape));
			 say ","; say(Symbol.name typ); say ")")
		fun f({name,params,result,body,pos},d) =
		   (indent d; say "("; say (Symbol.name name); say ",[";
		    dolist d field params; sayln "],";
		    case result of NONE => say "NONE"
			 | SOME(s,_) => (say "SOME("; say(Symbol.name s); say ")");
		    sayln ","; exp(body,d+1); say ")")
	     in indent d; say "FunctionDec["; dolist d f l; say "]"
	    end
    | dec(A.VarDec{name,escape,typ,init,pos},d) =
	   (indent d; say "VarDec("; say(Symbol.name name); say ",";
	    say(Bool.toString (!escape)); say ",";
	    case typ of NONE => say "NONE"
		      | SOME(s,p)=> (say "SOME("; say(Symbol.name s); say ")");
            sayln ","; exp(init,d+1); say ")")
    | dec(A.TypeDec l, d) =
	 let fun tdec({name,ty=t,pos},d) = (indent d; say"(";
				  	    say(Symbol.name name); sayln ",";
					    ty(t,d+1); say ")")
	  in indent d; say "TypeDec["; dolist d tdec l; say "]"
         end

  and ty(A.NameTy(s,p), d) = (indent d; say "NameTy("; say(Symbol.name s);
			      say ")")
    | ty(A.RecordTy l, d) =
		let fun f({name,escape,typ,pos},d) =
			(indent d; say "("; say (Symbol.name name);
		         say ","; say (Bool.toString (!escape)); say ",";
			 say (Symbol.name typ); say ")")
	         in indent d; say "RecordTy["; dolist d f l; say "]"
		end
    | ty(A.ArrayTy(s,p),d) = (indent d; say "ArrayTy("; say(Symbol.name s);
			      say ")")

 in
    exp(e0, 0); sayln ""; TextIO.flushOut outstream
 end

end
