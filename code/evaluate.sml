structure Evaluate : 
sig
  
  type vstore

  val evalProg : Absyn.exp -> Value.value
  val evalExp  : vstore * Absyn.exp -> Value.value
  val evalDec  : vstore * Absyn.dec -> vstore

end = 
struct

  structure GBA = GeminiBitArray(Vector)
  structure A = Absyn
  structure V = Value
  structure S = Symbol
  structure T = Types

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

  fun getHWRecord(V.HWRecordVal x) = x
    | getHWRecord(_) = raise TypeError

  fun getFun(V.FunVal x) = x
    | getFun(_) = raise TypeError

  fun getBit(V.BitVal x) = x
    | getBit(_) = raise TypeError

  fun getArray(V.ArrayVal x) = x
    | getArray(_) = raise TypeError

  fun getBitArray(V.ArrayVal bs) = Vector.map getBit bs
    | getBitArray(_) = raise TypeError

  fun getSWInner(V.SWVal x) = x
    | getSWInner(_) = raise TypeError

  fun getExplicitTy(A.ExplicitTy t) = t
    | getExplicitTy(_) = raise TypeError

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

  fun compareLt(V.IntVal l, V.IntVal r) = l < r
    | compareLt(V.StringVal l, V.StringVal r) = l < r
    | compareLt(V.RealVal l, V.RealVal r) = l < r
    | compareLt(_) = raise TypeError

  fun compareGt(V.IntVal l, V.IntVal r) = l > r
    | compareGt(V.StringVal l, V.StringVal r) = l > r
    | compareGt(V.RealVal l, V.RealVal r) = l > r
    | compareGt(_) = raise TypeError

  fun evalBinaryBitOp(V.AndOp, b1, b2) = GeminiBit.andb b1 b2
    | evalBinaryBitOp(V.OrOp, b1, b2) = GeminiBit.orb b1 b2
    | evalBinaryBitOp(V.XorOp, b1, b2) = GeminiBit.xorb b1 b2
    | evalBinaryBitOp(_) = raise Match

  fun evalUnaryBitOp(V.NotOp, b) = GeminiBit.notb b
    | evalUnaryBitOp(_) = raise Match

  fun evalShortcutBitOp(V.AndOp, V.BitVal GeminiBit.ZERO, _) = V.BitVal GeminiBit.ZERO
    | evalShortcutBitOp(V.AndOp, _, V.BitVal GeminiBit.ZERO) = V.BitVal GeminiBit.ZERO
    | evalShortcutBitOp(V.AndOp, V.BitVal GeminiBit.ONE, x) = x
    | evalShortcutBitOp(V.AndOp, x, V.BitVal GeminiBit.ONE) = x
    | evalShortcutBitOp(V.OrOp, V.BitVal GeminiBit.ONE, _) = V.BitVal GeminiBit.ONE
    | evalShortcutBitOp(V.OrOp, _, V.BitVal GeminiBit.ONE) = V.BitVal GeminiBit.ONE
    | evalShortcutBitOp(V.OrOp, V.BitVal GeminiBit.ZERO, x) = x
    | evalShortcutBitOp(V.OrOp, x, V.BitVal GeminiBit.ZERO) = x
    | evalShortcutBitOp(bitop, leftVal, rightVal) = V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}

  fun evalBinaryBitwiseOp(bitop, leftVal, rightVal) = case (leftVal, rightVal) of
                                                     (V.BitVal b1, V.BitVal b2) => V.BitVal (evalBinaryBitOp(bitop, b1, b2))
                                                   | (V.BitVal b, _) => evalShortcutBitOp(bitop, leftVal, rightVal)
                                                   | (_, V.BitVal b) => evalShortcutBitOp(bitop, leftVal, rightVal)
                                                   | (V.ArrayVal vals1, V.ArrayVal vals2) => V.ArrayVal(Vector.map (fn (v1, v2) => evalBinaryBitwiseOp(bitop, v1, v2)) (Utils.vectorZipEq(vals1, vals2)))
                                                   | (V.HWRecordVal vals1, V.HWRecordVal vals2) => V.HWRecordVal(map (fn ((s1, v1), (s2, v2)) => if Symbol.name(s1) = Symbol.name(s2) then (s1, evalBinaryBitwiseOp(bitop, v1, v2)) else raise TypeError) (ListPair.zipEq(vals1, vals2)))
                                                   | (V.NamedVal _, _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (_, V.NamedVal _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (V.BinOpVal _, _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (_, V.BinOpVal _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (V.UnOpVal _, _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (_, V.UnOpVal _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (V.ArrayAccVal _, _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | (_, V.ArrayAccVal _) => V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}
                                                   | _ => raise TypeError

  fun evalUnaryBitwiseOp(bitop, expVal) = case expVal of
                                               V.BitVal(b) => V.BitVal (evalUnaryBitOp(bitop, b))
                                             | V.ArrayVal(vals) => V.ArrayVal(Vector.map (fn (v) => evalUnaryBitwiseOp(bitop, v)) vals)
                                             | V.HWRecordVal(vals) => V.HWRecordVal(map (fn (s, v) => (s, evalUnaryBitwiseOp(bitop, v))) vals)
                                             | V.NamedVal _ => V.UnOpVal{value = expVal, oper = bitop}
                                             | V.BinOpVal _ => V.UnOpVal{value = expVal, oper = bitop}
                                             | V.UnOpVal _ => V.UnOpVal{value = expVal, oper = bitop}
                                             | V.ArrayAccVal _ => V.UnOpVal{value = expVal, oper = bitop}
                                             | _ => raise TypeError

  fun evalShiftOp(bitop, leftVal, rightVal) = V.BinOpVal{left = leftVal, oper = bitop, right = rightVal}

  fun reduceToBitOp(V.AndReduceOp) = V.AndOp
    | reduceToBitOp(V.OrReduceOp) = V.OrOp
    | reduceToBitOp(V.XorReduceOp) = V.XorOp
    | reduceToBitOp(_) = raise Match

  fun bitToReduceOp(V.AndOp) = V.AndReduceOp
    | bitToReduceOp(V.OrOp) = V.OrReduceOp
    | bitToReduceOp(V.XorOp) = V.XorReduceOp
    | bitToReduceOp(_) = raise Match

  fun evalReduceOp(bitop, expVal) =
    case expVal of
         V.ArrayVal(arr) => foldl (fn (v, acc) => evalBinaryBitwiseOp(reduceToBitOp(bitop), v, acc)) (Vector.sub(arr, 0)) (List.drop(Vector.toList(arr), 1))
       | _ => V.UnOpVal{value = expVal, oper = bitop}

  fun evalDoubleBitOp(bitop, leftVal, rightVal) =
    let
      val leftBit  = evalReduceOp(V.OrReduceOp, leftVal)
      val rightBit = evalReduceOp(V.OrReduceOp, rightVal)
      val result = evalBinaryBitwiseOp(bitop, leftBit, rightBit)
    in
      result
    end

  (* evaluation functions *)
  fun evalProg(prog) = 
    let
      val progVal = evalExp(V.base_store, prog)
    in
      progVal
    end

  and evalExp(vstore, exp) =
      let fun evexp(A.StructsSigsExp(_)) = V.NoVal
            | evexp(A.VarExp(sym, pos)) = (case Symbol.look(vstore, sym) of
                                                SOME(value) => value
                                              | NONE => (ErrorMsg.error pos "unknown value"; V.NoVal))
            | evexp(A.IntExp(num, pos)) = V.IntVal num
            | evexp(A.StringExp(str, pos)) = V.StringVal str
            | evexp(A.RealExp(num, pos)) = V.RealVal num
            | evexp(A.BitExp(bit, pos)) = V.BitVal bit
            | evexp(A.ApplyExp(e1, e2, pos)) =
              let
                val e1Val = evexp(e1)
                val e2Val = evexp(e2)
              in
                case e1Val of
                     V.FunVal f => !f e2Val
                   | V.ModuleVal(m, _) => m e2Val
                   | _ => raise TypeError
              end
            | evexp(A.ParameterApplyExp(e1, e2, pos)) =
              let
                val e1Val = evexp(e1)
                val e2Val = evexp(e2)
              in
                case e1Val of
                     V.PreParameterizedModuleVal(f, args) => V.ModuleVal(f e2Val, args)
                   | _ => raise TypeError
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
                                then V.IntVal 0
                                else V.IntVal 1
                   | A.LtOp => if compareLt(leftVal, rightVal)
                               then V.IntVal 1
                               else V.IntVal 0
                   | A.GeOp => if compareLt(leftVal, rightVal)
                               then V.IntVal 0
                               else V.IntVal 1
                   | A.GtOp => if compareGt(leftVal, rightVal)
                               then V.IntVal 1
                               else V.IntVal 0
                   | A.LeOp => if compareGt(leftVal, rightVal)
                               then V.IntVal 0
                               else V.IntVal 1
                   | A.ConsOp => (V.ListVal (leftVal::getList(rightVal)))
                   | A.BitAndOp => evalBinaryBitwiseOp(V.AndOp, leftVal, rightVal)
                   | A.BitOrOp  => evalBinaryBitwiseOp(V.OrOp, leftVal, rightVal)
                   | A.BitXorOp => evalBinaryBitwiseOp(V.XorOp, leftVal, rightVal)
                   | A.BitSLLOp => evalShiftOp(V.SLLOp, leftVal, rightVal)
                   | A.BitSRLOp => evalShiftOp(V.SRLOp, leftVal, rightVal)
                   | A.BitSRAOp => evalShiftOp(V.SRAOp, leftVal, rightVal)
                   | A.BitDoubleAndOp => evalDoubleBitOp(V.AndOp, leftVal, rightVal)
                   | A.BitDoubleOrOp => evalDoubleBitOp(V.OrOp, leftVal, rightVal)
                   | A.BitDoubleXorOp => evalDoubleBitOp(V.XorOp, leftVal, rightVal)
                   | _ => V.NoVal
              end
            | evexp(A.UnOpExp({exp, oper, pos})) =
              let
                val expVal = evexp(exp)
              in
                case oper of
                     A.IntMinusOp => V.IntVal(~(getInt(expVal)))
                   | A.BitNotOp => evalUnaryBitwiseOp(V.NotOp, expVal)
                   | A.BitAndReduceOp => evalReduceOp(V.AndReduceOp, expVal)
                   | A.BitOrReduceOp => evalReduceOp(V.OrReduceOp, expVal)
                   | A.BitXorReduceOp => evalReduceOp(V.XorReduceOp, expVal)
                   | _ => V.NoVal
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
            | evexp(A.ArrayExp(elems)) =
              let
                val vals = Vector.map (fn (exp, _) => evexp(exp)) elems
              in
                V.ArrayVal vals
              end
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
            | evexp(A.HWRecordExp({fields, pos})) =
              let
                fun makeVal(sym, exp, pos) = (sym, evexp(exp))
                val fs = map makeVal fields
              in
                V.HWRecordVal fs
              end
            | evexp(A.SWExp(exp, pos)) =
              let
                val innerVal = evexp(exp)
              in
                V.SWVal innerVal
              end
            | evexp(A.UnSWExp(exp, pos)) =
              let
                val innerVal = evexp(exp)
              in
                getSWInner(innerVal)
              end
            | evexp(A.WithExp{exp, fields, pos}) = V.NoVal (* TODO *)
            | evexp(A.DerefExp{exp, pos}) =
              let
                val refVal = evexp(exp)
              in
                !(getRef(refVal))
              end
            | evexp(A.StructAccExp{name, field, pos}) = (case Symbol.look(Env.base_senv, name) of
                                                              SOME(struct_vstore) => (case Symbol.look(struct_vstore, field) of
                                                                                           SOME(_, v) => v
                                                                                         | NONE => (ErrorMsg.error pos ("unbound path in structure: " ^ Symbol.name(field) ^ "\n"); V.NoVal))
                                                            | NONE => (ErrorMsg.error pos ("unbound structure: " ^ Symbol.name(name) ^ "\n"); V.NoVal))
            | evexp(A.RecordAccExp{exp, field, pos}) =
              let
                val recVal = evexp(exp)
              in
                case recVal of
                      V.RecordVal vs => #2(valOf(List.find (fn (sym, _) => Symbol.name(sym) = Symbol.name(field)) vs))
                    | V.HWRecordVal vs => #2(valOf(List.find (fn (sym, _) => Symbol.name(sym) = Symbol.name(field)) vs))
                    | _ => V.HWRecordAccVal {record = recVal, field = field}
              end
            | evexp(A.ArrayAccExp{exp, index, pos}) =
              let
                val expVal = evexp(exp)
                val idx = getInt(evexp(index))
              in
                case expVal of
                     V.ArrayVal vals => Vector.sub(vals, Vector.length(vals) - 1 - idx)
                   | _ => V.ArrayAccVal{arr = expVal, index = idx}
              end
            | evexp(A.PatternMatchExp{exp, cases, pos}) =
              let
                val expVal = evexp(exp)
                fun foldCase({match, result, pos}, res as SOME(_)) = res
                  | foldCase({match, result, pos}, NONE) =
                    let
                      (* takes in match and vstore and returns whether match and augmented vstore *)
                      fun checkMatch(A.VarExp(sym, _), expVal, vs) =
                        (case Symbol.look(vs, sym) of
                              SOME(V.DatatypeVal(datatypeSym, datatypeU, datatypeVal)) => (case expVal of
                                                                                                V.DatatypeVal(expSym, expU, expVal) => (if Symbol.name(datatypeSym) = Symbol.name(expSym)
                                                                                                                                        then (true, vs)
                                                                                                                                        else (false, vs))
                                                                                              | _ => (false, vs))
                            | _ => (true, Symbol.enter(vs, sym, expVal)))
                        | checkMatch(A.IntExp(n1, _), V.IntVal n2, vs) = (n1 = n2, vs)
                        | checkMatch(A.StringExp(s1, _), V.StringVal s2, vs) = (s1 = s2, vs)
                        | checkMatch(A.RealExp(r1, _), V.RealVal r2, vs) = (Real.==(r1, r2), vs)
                        | checkMatch(A.ListExp(exps), V.ListVal vals, vs) =
                          if length(exps) = length(vals)
                          then (foldl (fn (((e, _), v), (sofar, vs')) =>
                              let
                                val (isMatch', vs'') = checkMatch(e, v, vs')
                              in
                                (sofar andalso isMatch', vs'')
                              end) (true, vs) (ListPair.zipEq(exps, vals)))
                          else (false, vs)
                        | checkMatch(A.SWRecordExp{fields = exps, pos}, V.RecordVal vals, vs) =
                          if length(exps) = length(vals)
                          then (foldl (fn (((s1, e, _), (s2, v)), (sofar, vs')) =>
                              let
                                val (isMatch', vs'') = checkMatch(e, v, vs')
                              in
                                (sofar andalso isMatch' andalso (Symbol.name(s1) = Symbol.name(s2)), vs'')
                              end) (true, vs) (ListPair.zipEq(exps, vals)))
                          else (false, vs)
                        | checkMatch(A.BinOpExp{left, oper = A.ConsOp, right, pos}, V.ListVal vals, vs) =
                          (case vals of
                                [] => (false, vs)
                              | hd::tl =>  (let
                                              val (isMatch', vs') = checkMatch(left, hd, vs)
                                              val (isMatch'', vs'') = checkMatch(right, V.ListVal tl, vs')
                                            in
                                              (isMatch' andalso isMatch'', vs'')
                                            end))
                        | checkMatch(A.ApplyExp(A.VarExp(consym, _), param, _), V.DatatypeVal(sym, unique, value), vs) =
                          if Symbol.name(consym) = Symbol.name(sym)
                          then checkMatch(param, value, vs)
                          else (false, vs)
                        | checkMatch(_, _, vs) = (false, vs)
                      val (isMatch, vstore_with_vars) = checkMatch(match, expVal, vstore)
                    in
                      if isMatch
                      then SOME(evalExp(vstore_with_vars, result))
                      else NONE
                    end
                val resVal = foldl foldCase NONE cases
              in
                case resVal of 
                     SOME(x) => x
                   | NONE => (ErrorMsg.runtime pos ("no case matched, actual value was " ^ V.toString(expVal)); V.NoVal)
              end
            | evexp(A.BitArrayGenExp{size, counter, genfun, pos}) =
              let
                val sizeInt = getInt(evexp(size))
                fun gen(i, acc) = if i >= sizeInt
                                  then acc
                                  else (let
                                          (* add counter *)
                                          val vstore' = Symbol.enter(vstore, counter, V.IntVal i)
                                          val genexp = evalExp(vstore', genfun)
                                        in
                                          gen(i + 1, genexp::acc)
                                        end)
                val valList = gen(0, [])
              in
                V.ArrayVal (Vector.fromList(valList))
              end
            | evexp(A.BitArrayConvExp{size, value, spec, pos}) =
              case spec of
                   "'r" => 
                      let
                        val sizes = getRecord(evexp(size))
                        val valueReal = getReal(evexp(value))
                      in
                        V.NoVal (* TODO *)
                      end
                  | _ =>
                      let
                        val sizeInt = getInt(evexp(size))
                        val valueInt = getInt(evexp(value))
                      in
                        case spec of
                             "'u" => V.ArrayVal (Vector.map (fn(b) => V.BitVal b) (GBA.fromUnsignedInt valueInt sizeInt pos))
                           | "'s" => V.ArrayVal (Vector.map (fn(b) => V.BitVal b) (GBA.fromSignedInt valueInt sizeInt pos))
                           | _ => raise Match
                      end
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
                (* if init is BitArrayGenExp, then need to handle specially *)
                case init of
                     A.BitArrayGenExp({size, counter, genfun, pos}) =>
                      let
                        val sizeInt = getInt(evalExp(vs, size))
                        fun gen(i, acc) = if i >= sizeInt
                                          then acc
                                          else (let
                                                  (* add counter *)
                                                  val vs' = Symbol.enter(vs, counter, V.IntVal i)
                                                  (* add current array *)
                                                  val vs'' = Symbol.enter(vs', name, V.ArrayVal (Vector.fromList(acc)))
                                                  val genexp = evalExp(vs'', genfun)
                                                in
                                                  gen(i + 1, genexp::acc)
                                                end)
                        val valList = gen(0, [])
                        val value = V.ArrayVal (Vector.fromList(valList))
                        val vs' = Symbol.enter(vs, name, value)
                      in
                        vs'
                      end
                   | _ => let
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
          | evdec(A.ModuleDec(moddecs)) =
            let
              fun augmentParam(A.NoParam, vs, value) = vs
                | augmentParam(A.SingleParam{name, ty, escape, pos}, vs, value) = Symbol.enter(vs, name, value)
                | augmentParam(A.TupleParams(fs), vs, value) =
                  let
                    fun foldField(({name, ty, escape, pos}, (sym, value)), vs) = Symbol.enter(vs, name, value)
                  in
                    foldl foldField vs (ListPair.zipEq(fs, getHWRecord(value)))
                  end
                | augmentParam(A.RecordParams(fs), vs, value) =
                  let
                    fun foldField(({name, ty, escape, pos}, (sym, value)), vs) = Symbol.enter(vs, name, value)
                  in
                    foldl foldField vs (ListPair.zipEq(fs, getHWRecord(value)))
                  end

              fun makeNamedArgs(A.NoParam) = raise Match
                | makeNamedArgs(A.SingleParam{name, ty, escape, pos}) = V.NamedVal(name, getExplicitTy(ty))
                | makeNamedArgs(A.TupleParams(fs)) = V.HWRecordVal (List.rev(#2(foldl (fn ({name, ty, escape, pos}, (i, acc)) => (i + 1, (Symbol.symbol(Int.toString(i)), V.NamedVal(name, getExplicitTy(ty)))::acc)) (1, []) fs)))
                | makeNamedArgs(A.RecordParams(fs)) = V.HWRecordVal (map (fn {name, ty, escape, pos} => (name, V.NamedVal(name, getExplicitTy(ty)))) fs)

              fun foldDec({name, arg, sw_arg = SOME(sw), result, body, pos}, vs) =
                let
                  val namedArgs = makeNamedArgs(arg)
                  val mfun = fn(swv) => fn(hwv) => evalExp(augmentParam(arg, augmentParam(sw, vs, swv), hwv), body)
                  val vs' = Symbol.enter(vs, name, V.PreParameterizedModuleVal(mfun, namedArgs))
                in
                  vs'
                end
                | foldDec({name, arg, sw_arg = NONE, result, body, pos}, vs) =
                let
                  val namedArgs = makeNamedArgs(arg)
                  val mfun = fn(v) => evalExp(augmentParam(arg, vs, v), body)
                  val vs' = Symbol.enter(vs, name, V.ModuleVal(mfun, namedArgs))
                in
                  vs'
                end
              val vstore' = foldl foldDec vstore moddecs
            in
              vstore'
            end
          | evdec(A.SWDatatypeDec(datatydecs)) =
            let
              fun foldDec({name, tyvars, datacons}, vs) = 
                let
                  fun foldDatacon({datacon, ty, pos}, vs') = case ty of 
                                                                  A.ExplicitTy(T.S_TY(T.ARROW(_))) => Symbol.enter(vs', datacon, V.FunVal (ref (fn(v) => V.DatatypeVal(datacon, ref (), v))))
                                                                | _ => Symbol.enter(vs', datacon, V.DatatypeVal(datacon, ref (), V.NoVal))
                in
                  foldl foldDatacon vs datacons
                end
              val vstore' = foldl foldDec vstore datatydecs
            in
              vstore'
            end
          | evdec(A.HWDatatypeDec(datatydecs)) = vstore
    in
      evdec(dec)
    end

end