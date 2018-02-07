signature INFER =
sig

  type menv
  type tenv
  type venv

  type expty


  val inferProg :                      Absyn.exp -> Absyn.exp     (* returns explicit poly tree *)
  val inferExp  : menv * tenv * venv * Absyn.exp -> expty         (* returns expression and its type *)
  val inferTy   : menv * tenv * venv * Absyn.ty  -> Types.ty      (* returns explicit type *)
  val inferDec  : menv * tenv * venv * Absyn.dec -> { menv: menv, (* returns augmented environments and *)
                                                      tenv: tenv, (* Absyn.dec with explicit types      *)
                                                      venv: venv,
                                                      dec: Absyn.dec }

end

structure Infer : INFER =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env

  type menv = T.ty Symbol.table
  type tenv = T.ty Symbol.table
  type venv = E.enventry Symbol.table

  type expty = { exp: A.exp, ty: T.ty }

  fun getTypeFromEnv(env, sym) =
    case Symbol.look(env, sym) of
         SOME(t) => t
       | NONE => T.TOP (* TODO: error message (symbol not found) *)

  fun inferProg(e) =
    let
      val {exp, ty} = inferExp(E.base_menv, E.base_tenv, E.base_venv, e)
    in
      exp
    end

  and inferExp(menv, tenv, venv, expression) =
    let infexp(A.StructsSigsExp(structsigs))

  and inferTy(menv, tenv, venv, ty) =
    let fun infty(A.NameTy(sym, pos)) = getTypeFromEnv(tenv, sym)
          | infty(A.TyVar(sym, pos)) = getTypeFromEnv(menv, sym)
          | infty(A.SWRecordTy(fields, pos)) =
            let
              fun absynToTy({name, ty, escape, pos}) =
                let
                  val realTy = case Symbol.look(tenv, name) of
                                    SOME(t) => t
                                  | NONE => (case Symbol.look(menv, name) of
                                                  SOME(t) => t
                                                | NONE => T.S_TOP) (* TODO: error message (symbol not found) *)
                  val retTy = case realTy of
                                   T.S_TY(t) => t
                                 | _ => T.S_TOP (* TODO: error message (sw type expected) *)
                in
                  (name, retTy)
                end
              fun processFields fs = foldl (fn(f, l) => l @ [absynToTy(f)]) [] fs
              fun checkDuplicateFields [] = ()
                | checkDuplicateFields ({name, ty, escape, pos}::rest) =
                let
                  val () = if (List.exists (fn r => (Symbol.name name) = (Symbol.name (#name r))) rest)
                           then () (* TODO: error message (duplicate field name) *)
                           else ()
                in
                  checkDuplicateFields(rest)
                end
              val () = checkDuplicateFields(fields)
            in
              T.S_TY(T.S_RECORD(processFields(fields)))
            end
          | infty(A.HWRecordTy(fields, pos)) =
            let
              fun absynToTy({name, ty, escape, pos}) =
                let
                  val realTy = case Symbol.look(tenv, name) of
                                    SOME(t) => t
                                  | NONE => (case Symbol.look(menv, name) of
                                                  SOME(t) => t
                                                | NONE => T.H_TOP) (* TODO: error message (symbol not found) *)
                  val retTy = case realTy of
                                   T.H_TY(t) => t
                                 | _ => T.H_TOP (* TODO: error message (hw type expected) *)
                in
                  (name, retTy)
                end
              fun processFields fs = foldl (fn(f, l) => l @ [absynToTy(f)]) [] fs
              fun checkDuplicateFields [] = ()
                | checkDuplicateFields ({name, ty, escape, pos}::rest) =
                let
                  val () = if (List.exists (fn r => (Symbol.name name) = (Symbol.name (#name r))) rest)
                           then () (* TODO: error message (duplicate field name) *)
                           else ()
                in
                  checkDuplicateFields(rest)
                end
              val () = checkDuplicateFields(fields)
            in
              T.H_TY(T.H_RECORD(processFields(fields)))
            end
          | infty(A.ArrayTy(ty, size, pos)) =
            let
              val realTy = infty(ty)
              val retTy = case realTy of
                               T.H_TY(t) => t
                             | _ => T.H_TOP (* TODO: error message (hw type expected) *)
              val {exp = sizeExp, ty = sizeTy} = inferExp(menv, tenv, venv, size)
              val () = case sizeTy of
                            T.S_TY(T.INT) => ()
                          | _ => () (* TODO: error message (int type expected) *)
            in
              T.H_TY(T.ARRAY({ty = retTy, size = int}))
            end
          | infty(A.ListTy(ty, pos)) =
            let
              val realTy = infty(ty)
              val retTy = case realTy of
                               T.S_TY(t) => t
                             | _ => T.S_TOP (* TODO: error message (sw type expected) *)
            in
              T.S_TY(T.LIST(retTy))
            end
          | infty(A.TemporalTy(ty, time, pos)) =
          | infty(A.RefTy(ty, pos)) =
          | infty(A.SWTy(ty, pos)) =
          | infty(A.FunTy(ty1, ty2, pos)) = T.S_TY(T.ARROW(infty(ty1), infty(ty2)))
          | infty(A.PlaceholderTy(u)) =
          | infty(A.ExplicitTy(t)) = t
    in
      infty(ty)
    end

  (*
  and inferExp(tenv, venv, A.StructsSigsExp(structsigs)) =
      let

      in
      end
    | inferExp(tenv, venv, A.VarExp(sym, pos)) = { polytree: A.VarExp(sym, pos), tenv: tenv, venv: venv }
    | inferExp(tenv, venv, A.IntExp(num, pos)) = { polytree: A.IntExp(num, pos), tenv: tenv, venv: venv }
    | inferExp(tenv, venv, A.StringExp(str, pos)) = { polytree: A.StringExp(str, pos), tenv: tenv, venv: venv }
    | inferExp(tenv, venv, A.RealExp(num, pos)) = { polytree: A.RealExp(num, pos), tenv: tenv, venv: venv }
    | inferExp(tenv, venv, A.BitExp(bit, pos)) = { polytree: A.BitExp(bit, pos), tenv: tenv, venv: venv }
    | inferExp(tenv, venv, A.ApplyExp(e1, e2, pos)) =
      let
        val e1_polytree = #polytree(inferExp(tenv, venv, e1))
        val e2_polytree = #polytree(inferExp(tenv, venv, e2))
      in
        { polytree: A.ApplyExp(e1_polytree, e2_polytree) }
      end
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
  *)

end