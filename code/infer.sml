signature INFER =
sig

  type sub

  val unify     : Types.ty * Types.ty -> sub list

  val inferProg :                                  Env.menv * Absyn.exp -> Env.smap              (* returns substitution mapping *)
  val inferExp  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.exp -> Env.smap * Types.ty   (* returns mapping and expression type *)
  (* val inferTy   : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.ty  -> Types.ty          (* returns explicit type *) *)
  (* val inferDec  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.dec -> { menv: Env.menv,     (* returns augmented environments *)
                                                             venv: Env.venv,
                                                             smap: Env.smap } *)

end

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

  datatype sub = SUB of (Symbol.symbol * T.ty)
               | EMPTY
               | ERROR

  fun apply(sub, ty1, ty2)

  fun unify(smap, ty1, ty2) = case ty1 of
                                   T.META(m) => [SOME(m, ty2)]
                                 | T.H_TY(T.H_META(hm)) => [SOME(hm, ty2)]
                                 | T.S_TY(T.S_META(sm)) => [SOME(sm, ty2)]
                                 | _ => case ty2 of
                                             T.META(m) => [SOME(m, ty1)]
                                           | T.H_TY(T.H_META(hm)) => [SOME(hm, ty1)]
                                           | T.S_TY(T.S_META(sm)) => [SOME(sm, ty1)]
                                           | _ => case (ty1, ty2) of
                                                       (T.H_TY(h1), T.H_TY(h2)) => unifyHty(h1, h2)
                                                     | (T.S_TY(s1), T.S_TY(s2)) => unifySty(s1, s2)
                                                     | (T.M_TY(m1), T.M_TY(m2)) => unifyMty(m1, m2)
                                                     | _ => [NONE]

  and unifyHty(hty1, hty2) = case (hty1, hty2) of
                                  (T.ARRAY{ty = ty1, size}, T.ARRAY{ty = ty2, size}) => unifyHty(ty1, ty2)
                                | (T.H_RECORD(recs1), T.H_RECORD(recs2)) = let
  and unifySty(sty1, sty2) = [NONE]
  and unifyMty(mty1, mty2) = [NONE]

  fun inferProg(menv, e) =
    let
      val (smap, ty) = inferExp(E.base_menv, E.base_tenv, E.base_venv, E.base_smap, e)
    in
      smap
    end

  and inferExp(menv, tenv, venv, smap, exp) =
    let fun infexp(A.StructsSigsExp(structsigs)) = (smap, T.EMPTY)
          | infexp(A.VarExp(sym, pos)) = (smap, case Symbol.look(venv, sym) of
                                                     SOME(t) => t
                                                   | _ => T.BOTTOM (* error *))
          | infexp(A.IntExp(num, pos)) = (smap, T.S_TY(T.INT))
          | infexp(A.StringExp(str, pos)) = (smap, T.S_TY(T.STRING))
          | infexp(A.RealExp(num, pos)) = (smap, T.S_TY(T.REAL))
          | infexp(A.BitExp(bit, pos)) = (smap, T.H_TY(T.BIT))
          | infexp(A.ApplyExp(e1, e2, pos)) = (smap, T.EMPTY)
          | infexp(A.BinOpExp({left, oper, right, pos})) =
            let

            in
              (smap, T.EMPTY)
            end
          | infexp(A.UnOpExp({exp, oper, pos})) = (smap, T.EMPTY)
          | infexp(A.LetExp({decs, body, pos})) = (smap, T.EMPTY)
          | infexp(A.AssignExp({lhs, rhs, pos})) = (smap, T.EMPTY)
          | infexp(A.SeqExp(exps)) = (smap, T.EMPTY)
          | infexp(A.IfExp({test, then', else', pos})) = (smap, T.EMPTY)
          | infexp(A.ListExp(exps)) = (smap, T.EMPTY)
          | infexp(A.ArrayExp(exps)) = (smap, T.EMPTY)
          | infexp(A.RefExp(exp, pos)) = (smap, T.EMPTY)
          | infexp(A.SWRecordExp({fields, pos})) = (smap, T.EMPTY)
          | infexp(A.HWRecordExp({fields, pos})) = (smap, T.EMPTY)
          | infexp(A.SWExp(exp, pos)) = (smap, T.EMPTY)
          | infexp(A.WithExp({exp, fields, pos})) = (smap, T.EMPTY)
          | infexp(A.DerefExp({exp, pos})) = (smap, T.EMPTY)
          | infexp(A.StructAccExp({name, field, pos})) = (smap, T.EMPTY)
          | infexp(A.RecordAccExp({exp, field, pos})) = (smap, T.EMPTY)
          | infexp(A.ArrayAccExp({exp, index, pos})) = (smap, T.EMPTY)
          | infexp(A.PatternMatchExp({exp, cases, pos})) = (smap, T.EMPTY)
          | infexp(A.BitArrayExp({size, result, spec})) = (smap, T.EMPTY)
    in
      infexp(exp)
    end

  (*
  and inferTy(menv, tenv, venv, smap, ty) =
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
    end *)

end
