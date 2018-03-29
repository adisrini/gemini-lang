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
  
  fun getRecord(V.RecordVal x) = x
    | getRecord(_) = raise TypeError

  fun getFun(V.FunVal x) = x
    | getFun(_) = raise TypeError

  (* comparison operators *)
  fun compareEq(V.IntVal l, V.IntVal r) = l = r
    | compareEq(V.StringVal l, V.StringVal r) = l = r
    | compareEq(V.RealVal l, V.RealVal r) = Real.==(l, r)
    | compareEq(V.ListVal l, V.ListVal r) = if length(l) = length(r)
                                            then foldl (fn((lv, rv), isequal) => isequal andalso compareEq(lv, rv)) true (ListPair.zipEq(l, r))
                                            else false
    | compareEq(V.RefVal l, V.RefVal r) = l = r
    | compareEq(V.RecordVal l, V.RecordVal r) = if length(l) = length(r)
                                                then foldl (fn(((lsym, lv), (rsym, rv)), isequal) => isequal andalso (Symbol.name(lsym) = Symbol.name(rsym)) andalso compareEq(lv, rv)) true (ListPair.zipEq(l, r))
                                                else false
    | compareEq(_) = raise TypeError

  (* evaluation functions *)
  fun evalProg(prog) = 
    let
      val progVal = evalExp(V.base_store, prog)
      val () = print("===== PROGRAM RESULT =====\n")
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
            | evexp(A.ApplyExp(e1, e2, pos)) =
              let
                val e1Val = evexp(e1)
                val e2Val = evexp(e2)

                val e1Fun = !(getFun(e1Val))
                val retVal = e1Fun e2Val
              in
                retVal
              end
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
                   | A.EqOp => if compareEq(leftVal, rightVal)
                               then V.IntVal 1
                               else V.IntVal 0
                   | A.NeqOp => if compareEq(leftVal, rightVal)
                                then V.IntVal 1
                                else V.IntVal 0
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
                val refVal = evexp(exp)
              in
                !(getRef(refVal))
              end
            | evexp(A.StructAccExp{name, field, pos}) = V.NoVal (* TODO *)
            | evexp(A.RecordAccExp{exp, field, pos}) =
              let
                val recVal = evexp(exp)
                val (_, fieldVal) = valOf(List.find (fn (sym, _) => Symbol.name(sym) = Symbol.name(field)) (getRecord(recVal)))
              in
                fieldVal
              end
            | evexp(A.ArrayAccExp{exp, index, pos}) = V.NoVal (* TODO *)
            | evexp(A.PatternMatchExp{exp, cases, pos}) = V.NoVal (* TODO *)
            | evexp(A.BitArrayGenExp{size, counter, genfun, pos}) = V.NoVal (* TODO *)
            | evexp(A.BitArrayConvExp{size, value, spec, pos}) = V.NoVal (* TODO *)
      in
        evexp(exp)
      end

  and evalDec(vstore, dec) =
    let fun evdec(A.FunctionDec(fundecs)) =
            let
              fun foldDec({name, params, result, body, pos}, vs) = 
                let
                  fun augmentParam(A.NoParam, vs, value) = vs
                    | augmentParam(A.SingleParam{name, ty, escape, pos}, vs, value) = Symbol.enter(vs, name, value)
                    | augmentParam(A.TupleParams(fs), vs, value) =
                      let
                        fun foldField(({name, ty, escape, pos}, (sym, value)), vs) = Symbol.enter(vs, name, value)
                      in
                        foldl foldField vs (ListPair.zipEq(fs, getRecord(value)))
                      end
                    | augmentParam(A.RecordParams(fs), vs, value) =
                      let
                        fun foldField(({name, ty, escape, pos}, (sym, value)), vs) = Symbol.enter(vs, name, value)
                      in
                        foldl foldField vs (ListPair.zipEq(fs, getRecord(value)))
                      end

                  val vs' = Symbol.enter(vs, name, V.FunVal (ref (fn(v) => V.NoVal)))

                  fun genFunVal(params, vs) =
                      fn(value) =>
                        case params of
                             [param] => evalExp(augmentParam(param, vs, value), body)
                           | param::rest => V.FunVal(ref (genFunVal(rest, augmentParam(param, vs, value))))
                           | [] => raise Match

                  val funVal = genFunVal(params, vs')
                  val () = case Symbol.look(vs', name) of
                                SOME(V.FunVal(funref)) => funref := funVal
                              | _ => ()
                in
                  vs'
                end
              val vstore' = foldl foldDec vstore fundecs
            in
              vstore'
            end
          | evdec(A.ValDec(valdecs)) =
            let
              fun foldDec({name, escape, ty, init, pos}, vs) =
                let
                  val value = evalExp(vs, init)
                  val vs' = Symbol.enter(vs, name, value)
                in
                  vs'
                end
              val vstore' = foldl foldDec vstore valdecs
            in
              vstore'
            end
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