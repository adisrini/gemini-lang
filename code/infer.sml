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

(* rename this to decorate

- should keep track of a substitution mapping
- after this is done, should go through once more and do substitutions


*)

(* UNIFY

take in two types and try to UNIFY
if variable and something, substitute (v -> s)
if something and variable, substitute (v -> s)
otherwise, check outermost tycon and if match, recurse (do left first, then apply substitution to right and do right)
if not match, report error

 *)

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

  and inferExp(menv, tenv, venv, exp) =
    let fun infexp(A.StructsSigsExp(structsigs)) =
          | infexp(A.VarExp(sym, pos)) =
          | infexp(A.IntExp(num, pos)) =
          | infexp(A.StringExp(str, pos)) =
          | infexp(A.RealExp(num, pos)) =
          | infexp(A.BitExp(bit, pos)) =
          | infexp(A.ApplyExp(e1, e2, pos)) =
          | infexp(A.NilExp(pos)) = {exp = A.NilExp(pos), ty = T.S_TY(T.LIST(T.S_META))}
          | infexp(A.BinOpExp({left, oper, right, pos})) =
          | infexp(A.UnOpExp({exp, oper, pos})) =
          | infexp(A.LetExp({decs, body, pos})) =
          | infexp(A.AssignExp({lhs, rhs, pos})) =
          | infexp(A.SeqExp(exps)) =
          | infexp(A.IfExp({test, then', else', pos})) =
          | infexp(A.ListExp(exps)) =
          | infexp(A.ArrayExp(exps)) =
          | infexp(A.RefExp(exp, pos)) =
          | infexp(A.SWRecordExp({fields, pos})) =
          | infexp(A.HWRecordExp({fields, pos})) =
          | infexp(A.SWExp(exp, pos)) =
          | infexp(A.WithExp({exp, fields, pos})) =
          | infexp(A.DerefExp({exp, pos})) =
          | infexp(A.StructAccExp({name, field, pos})) =
          | infexp(A.RecordAccExp({exp, field, pos})) =
          | infexp(A.ArrayAccExp({exp, index, pos})) =
          | infexp(A.PatternMatchExp({exp, cases, pos})) =
          | infexp(A.BitArrayExp({size, result, spec})) =
    in
      infexp(exp)
    end

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
            let
              val realTy = infty(ty)
              val retTy = case realTy of
                               T.H_TY(t) => t
                             | _ => T.H_TOP (* TODO: error message (expected hw type) *)
              val {exp = timeExp, ty = timeTy} = inferExp(menv, tenv, venv, time)
              val () = case timeTy of
                            T.S_TY(T.INT) => ()
                          | _ => () (* TODO: error message (expected int type) *)
            in
              T.H_TY(T.TEMPORAL({ty = retTy, time = timeExp}))
            end
          | infty(A.RefTy(ty, pos)) =
            let
              val realTy = infty(ty)
              val retTy = case realTy of
                               T.S_TY(t) => t
                             | _ => T.S_TOP (* TODO: error message (expected sw type) *)
            in
              T.S_TY(T.REF(retTy))
            end
          | infty(A.SWTy(ty, pos)) =
            let
              val realTy = infty(ty)
              val ret = case realTy of
                             T.H_TY(t) => T.S_TY(T.SW_H(t))
                           | T.M_TY(t) => T.S_TY(T.SW_M(t))
                           | _ => T.S_TY(T.S_TOP) (* TODO: error message (expected hw/m type ) *)
            in
              ret
            end
          | infty(A.FunTy(ty1, ty2, pos)) =
            let
              val realArgTy = infty(ty1)
              val realResTy = infty(ty2)

              val retArgTy = case realArgTy of
                                  T.S_TY(t) => t
                                | _ => T.S_TOP (* TODO: error message (expected sw type) *)
              val retResTy = case realResTy of
                                  T.S_TY(t) => t
                                | _ => T.S_BOTTOM (* TODO: error message (expected sw type) *)
            in
              T.S_TY(T.ARROW(infty(ty1), infty(ty2)))
            end
          | infty(A.PlaceholderTy(u)) = T.META(E.newMeta())
          | infty(A.ExplicitTy(t)) = t
    in
      infty(ty)
    end

end
