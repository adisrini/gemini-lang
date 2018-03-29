structure SWEvaluate : 
sig
  
  type vstore

  val evalProg : Absyn.exp -> unit
  val evalExp  : vstore * Absyn.exp -> SWValue.value
  val evalDec  : vstore * Absyn.dec -> vstore

end = 
struct

  structure A = Absyn
  structure V = SWValue
  structure S = Symbol

  type vstore = V.value S.table

  exception TypeError

  (* value getting functions *)
  fun getInt(V.IntVal x) = x
    | getInt(_) = raise TypeError

  fun getString(V.StringVal x) = x
    | getString(_) = raise TypeError

  fun getReal(V.RealVal x) = x
    | getReal(_) = raise TypeError

  fun getList(V.ListVal x) = x
    | getList(_) = raise TypeError

  fun getRef(V.RefVal x) = x
    | getRef(_) = raise TypeError
  

  (* evaluation functions *)
  fun evalProg(prog) = 
    let
      val progVal = evalExp(V.base_store, prog)
      val () = print(V.toString(progVal) ^ "\n")
    in
      ()
    end

  and evalExp(vstore, exp) =
      let fun evexp(A.StructsSigsExp(_)) = V.NoVal
            | evexp(A.VarExp(sym, pos)) = (case Symbol.look(vstore, sym) of
                                                SOME(value) => value
                                              | NONE => (ErrorMsg.error pos "unknown value"; V.NoVal))
            | evexp(A.IntExp(num, pos)) = V.IntVal num
            | evexp(A.StringExp(str, pos)) = V.StringVal str
            | evexp(A.RealExp(num, pos)) = V.RealVal num
            | evexp(A.BitExp(bit, pos)) = V.NoVal (* TODO *)
            | evexp(A.ApplyExp(e1, e2, pos)) = V.NoVal (* TODO *)
            | evexp(A.BinOpExp({left, oper, right, pos})) =
              let
                val leftVal = evexp(left)
                val rightVal = evexp(right)
              in
                case oper of
                     A.IntPlusOp => V.IntVal(getInt(leftVal) + getInt(rightVal))
                   | A.IntMinusOp => V.IntVal(getInt(leftVal) - getInt(rightVal))
                   | A.IntTimesOp => V.IntVal(getInt(leftVal) * getInt(rightVal))
                   | A.IntDivideOp => V.IntVal(getInt(leftVal) div getInt(rightVal))
                   | A.IntModOp => V.IntVal(getInt(leftVal) mod getInt(rightVal))
                   | A.RealPlusOp => V.RealVal(getReal(leftVal) + getReal(rightVal))
                   | A.RealMinusOp => V.RealVal(getReal(leftVal) - getReal(rightVal))
                   | A.RealTimesOp => V.RealVal(getReal(leftVal) * getReal(rightVal))
                   | A.RealDivideOp => V.RealVal(getReal(leftVal) / getReal(rightVal))
                   | _ => V.NoVal (* TODO: handle other ops *)
              end
            | evexp(A.UnOpExp({exp, oper, pos})) =
              let
                val expVal = evexp(exp)
              in
                case oper of
                     A.IntMinusOp => V.IntVal(~(getInt(expVal)))
                   | _ => V.NoVal (* TODO: handle other ops *)
              end
            | evexp(A.LetExp{decs, body, pos}) =
              let
                val vstore' = foldl (fn(dec, vs) => evalDec(vs, dec)) vstore decs
              in
                evalExp(vstore', body)
              end
            | evexp(A.AssignExp{lhs, rhs, pos}) =
              let
                val lhsVal = evexp(lhs)
                val rhsVal = evexp(rhs)
                val lhsRef = getRef(lhsVal)
                val () = lhsRef := rhsVal
              in
                V.RecordVal [] (* unit *)
              end
            | evexp(A.SeqExp(exps)) =
              let
                fun foldExp((exp, pos), (opt_val)) =
                  let
                    val expVal = evexp(exp)
                  in
                    SOME(expVal)
                  end
                val opt_val = foldl foldExp NONE exps
              in
                (case opt_val of
                      NONE => V.RecordVal [] (* unit *)
                    | SOME(v) => v)
              end
            | evexp(A.IfExp{test, then', else' = SOME(elseExp), pos}) =
              let
                val testVal = evexp(test)
              in
                if (getInt(testVal)) <> 0
                then evexp(then')
                else evexp(elseExp)
              end
            | evexp(A.IfExp{test, then', else' = NONE, pos}) =
              let
                val testVal = evexp(test)
              in
                if (getInt(testVal)) <> 0
                then evexp(then')
                else V.RecordVal [] (* unit *)
              end
            | evexp(A.ListExp(elems)) =
              let
                val vals = map (fn (exp, _) => evexp(exp)) elems
              in
                V.ListVal vals
              end
            | evexp(A.ArrayExp(elems)) = V.NoVal (* TODO *)
            | evexp(A.RefExp(exp, pos)) =
              let
                val expVal = evexp(exp)
              in
                V.RefVal (ref expVal)
              end
            | evexp(A.SWRecordExp({fields, pos})) =
              let
                fun makeVal(sym, exp, pos) = (sym, evexp(exp))
                val fs = map makeVal fields
              in
                V.RecordVal fs
              end
            | evexp(A.HWRecordExp({fields, pos})) = V.NoVal (* TODO *)
            | evexp(A.SWExp(exp, pos)) = V.NoVal (* TODO *)
            | evexp(A.WithExp{exp, fields, pos}) = V.NoVal (* TODO *)
            | evexp(A.DerefExp{exp, pos}) =
              let
                val expVal = evexp(exp)
              in
                !(getRef(expVal))
              end
            | evexp(_) = V.NoVal
      in
        evexp(exp)
      end

  and evalDec(vstore, dec) =
    let fun evdec(A.FunctionDec(fundecs)) = vstore
          | evdec(A.ValDec(valdecs)) = vstore
          | evdec(A.TypeDec(tydecs)) = vstore
          | evdec(A.ModuleDec(moddecs)) = vstore
          | evdec(A.SWDatatypeDec(datatydecs)) = vstore
          | evdec(A.HWDatatypeDec(datatydecs)) = vstore
    in
      evdec(dec)
    end
(*

eval(FunDef(params, body), vs) =
  fn(value) => 
    let
        valuestore' = valuestore[params |-> value]
    in
        eval(body, vs')
    end


*)

end