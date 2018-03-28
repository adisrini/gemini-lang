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
                   | _ => V.NoVal
              end
            | evexp(_) = V.NoVal
      in
        evexp(exp)
      end

  and evalDec(vstore, dec) = vstore
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