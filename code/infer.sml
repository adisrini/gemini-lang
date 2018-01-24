signature INFER =
sig

  val inferProg: Absyn.exp -> (Types.ty Symbol.table * Env.enventry Symbol.table)

end

structure Infer : INFER =
struct

  structure A = Absyn

  fun inferProg(exp) = inferExp(Env.base_tenv, Env.base_venv, exp)

  (* TODO *)
  and inferExp(tenv, venv, A.StructsSigsExp(structsigs)) = (tenv, venv)
    | inferExp(tenv, venv, A.VarExp(sym, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.IntExp(num, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.StringExp(num, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.RealExp(num, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.BitExp(bit, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.ApplyExp(e1, e2, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.NilExp(pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.BinOpExp({left, oper, right, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.UnOpExp({exp, oper, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.LetExp({decs, body, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.AssignExp({lhs, rhs, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.SeqExp(exps)) = (tenv, venv)
    | inferExp(tenv, venv, A.IfExp({test, then', else', pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.ListExp(exps)) = (tenv, venv)
    | inferExp(tenv, venv, A.ArrayExp(exps)) = (tenv, venv)
    | inferExp(tenv, venv, A.RefExp(exp, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.SWRecordExp({fields, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.HWRecordExp({fields, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.SWExp(exp, pos)) = (tenv, venv)
    | inferExp(tenv, venv, A.WithExp({exp, fields, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.DerefExp({exp, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.StructAccExp({name, field, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.RecordAccExp({exp, field, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.ArrayAccExp({exp, index, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.PatternMatchExp({exp, cases, pos})) = (tenv, venv)
    | inferExp(tenv, venv, A.BitArrayExp({size, result, spec})) = (tenv, venv)

end
