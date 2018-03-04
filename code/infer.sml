signature INFER =
sig

  val inferProg :                                  Env.smap * Absyn.exp -> Env.smap              (* returns substitution mapping *)
  val inferExp  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.exp -> Env.smap * Types.ty   (* returns mapping and expression type *)
  (* val inferTy   : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.ty  -> Types.ty          (* returns explicit type *) *)
  val inferDec  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.dec -> { menv: Env.menv,     (* returns augmented environments *)
                                                                             tenv: Env.tenv,
                                                                             venv: Env.venv,
                                                                             smap: Env.smap }

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
  structure U = Unify
  structure S = Substitute

  (* unifies all types in list with given type and substitues into smap *)
  fun unifyAndSubstitute(smap, ty, typos_list) =
    let
      fun foldSub((uty, pos), (smap, subs)) =
        let
          val sub = U.unify(ty, uty, pos)
        in
          (case sub of
                S.SUB(SOME((sym, nty))) => Symbol.enter(smap, sym, nty)
              | _ => (smap),
           sub::subs)
        end
      val (smap', subs') = foldl foldSub (smap, []) typos_list
    in
      (smap', List.rev(subs'))
    end

  fun getExplicitType(A.ExplicitTy(ty), _) = ty
    | getExplicitType(_, default) = default

  fun inferProg(smap, e) =
    let
      val (smap', ty) = inferExp(E.base_menv, E.base_tenv, E.base_venv, smap, e)
    in
      smap'
    end

  and inferExp(menv, tenv, venv, smap, exp) =
    let fun infexp(A.StructsSigsExp(structsigs)) = (smap, T.EMPTY)
          | infexp(A.VarExp(sym, pos)) = (smap, case Symbol.look(venv, sym) of
                                                     SOME(t) => t
                                                   | _ => T.BOTTOM (* TODO: error *))
          | infexp(A.IntExp(num, pos)) = (smap, T.S_TY(T.INT))
          | infexp(A.StringExp(str, pos)) = (smap, T.S_TY(T.STRING))
          | infexp(A.RealExp(num, pos)) = (smap, T.S_TY(T.REAL))
          | infexp(A.BitExp(bit, pos)) = (smap, T.H_TY(T.BIT))
          | infexp(A.ApplyExp(e1, e2, pos)) = (smap, T.EMPTY)
          | infexp(A.BinOpExp({left, oper, right, pos})) =
            let
              val (smap', leftTy) = inferExp(menv, tenv, venv, smap, left)
              val (smap'', rightTy) = inferExp(menv, tenv, venv, smap', right)
              val ((smap''', subs), retTy) = case oper of
                              A.IntPlusOp => (unifyAndSubstitute(smap'', T.S_TY(T.INT), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.INT))
                            | A.IntMinusOp => (unifyAndSubstitute(smap'', T.S_TY(T.INT), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.INT))
                            | A.IntTimesOp => (unifyAndSubstitute(smap'', T.S_TY(T.INT), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.INT))
                            | A.IntDivideOp => (unifyAndSubstitute(smap'', T.S_TY(T.INT), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.INT))
                            | A.IntModOp => (unifyAndSubstitute(smap'', T.S_TY(T.INT), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.INT))
                            | A.RealPlusOp => (unifyAndSubstitute(smap'', T.S_TY(T.REAL), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.REAL))
                            | A.RealMinusOp => (unifyAndSubstitute(smap'', T.S_TY(T.REAL), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.REAL))
                            | A.RealTimesOp => (unifyAndSubstitute(smap'', T.S_TY(T.REAL), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.REAL))
                            | A.RealDivideOp => (unifyAndSubstitute(smap'', T.S_TY(T.REAL), [(leftTy, pos), (rightTy, pos)]), T.S_TY(T.REAL))
                            (* | A.BitAndOp =>
                            | A.BitOrOp =>
                            | A.BitXorOp =>
                            | A.BitSLLOp =>
                            | A.BitSRLOp =>
                            | A.BitSRAOp =>
                            | A.BitDoubleAndOp =>
                            | A.BitDoubleOrOp =>
                            | A.BitDoubleXorOp => *)
                            | A.EqOp =>
                              let
                                val (sub, retTy) = U.unifyEqualityType(leftTy, rightTy, pos)
                                val smap' = case sub of
                                                 S.SUB(SOME((sym, ty))) => Symbol.enter(smap, sym, ty)
                                               | _ => smap
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.NeqOp =>
                              let
                                val (sub, retTy) = U.unifyEqualityType(leftTy, rightTy, pos)
                                val smap' = case sub of
                                                 S.SUB(SOME((sym, ty))) => Symbol.enter(smap, sym, ty)
                                               | _ => smap
                              in
                                ((smap', [sub]), retTy)
                              end
                            (* | A.LtOp =>
                            | A.GtOp =>
                            | A.LeOp =>
                            | A.GeOp => *)
                            | A.ConsOp =>
                              let
                                val (sub, retTy) = U.unifyList(leftTy, rightTy, pos)
                                val smap' = case sub of
                                                 S.SUB(SOME((sym, ty))) => Symbol.enter(smap, sym, ty)
                                               | _ => smap
                              in
                                ((smap', [sub]), retTy)
                              end
                            | _ => raise Match
            in
              (smap''', retTy)
            end
          | infexp(A.UnOpExp({exp, oper, pos})) = (smap, T.EMPTY)
          | infexp(A.LetExp({decs, body, pos})) =
            let
              fun foldDec(dec, {menv, tenv, venv, smap}) = inferDec(menv, tenv, venv, smap, dec)
              val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldDec {menv = menv, tenv = tenv, venv = venv, smap = smap} decs
            in
              inferExp(menv', tenv', venv', smap', body)
            end
          | infexp(A.AssignExp({lhs, rhs, pos})) = (smap, T.EMPTY)
          | infexp(A.SeqExp(exps)) = (smap, T.EMPTY)
          | infexp(A.IfExp({test, then', else', pos})) =
            let
              val (smap', thenTy) = inferExp(menv, tenv, venv, smap, then')
              val (smap'', elseTy) = case else' of
                                          SOME(elseExp) => inferExp(menv, tenv, venv, smap', elseExp)
                                        | _ => (smap', case thenTy of
                                                     T.S_TY(_) => T.S_TY(T.S_RECORD([]))
                                                   | T.H_TY(_) => T.H_TY(T.H_RECORD([]))
                                                   | _ => T.BOTTOM)
              val sub = U.unify(thenTy, elseTy, pos)
              val retTy = case sub of
                               S.SUB(x) => thenTy
                             | S.ERROR(m) => T.BOTTOM
            in
              (smap'', retTy)
            end
          | infexp(A.ListExp(exps)) = (smap, T.S_TY(T.LIST(T.INT))) (* TODO *)
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

  and inferDec(menv, tenv, venv, smap, dec) =
    let
      fun infdec(A.FunctionDec(fundecs)) =
        let
          fun foldFunDec({name, params, result = (resultTy, resultPos), body, pos}, {menv, tenv, venv, smap}) =
            let
              (* enter params into venv *)
              fun foldParam(A.NoParam, venv) = venv
                | foldParam(A.SingleParam{name, ty, escape, pos}, venv) = Symbol.enter(venv, name, getExplicitType(ty, T.S_TY(T.S_BOTTOM)))
                | foldParam(A.MultiParams(fs), venv) = foldl (fn({name, ty, escape, pos}, v) => Symbol.enter(v, name, getExplicitType(ty, T.S_TY(T.S_BOTTOM)))) venv fs
              val venv' = foldl foldParam venv params
              (* process body with augmented venv' *)
              val (smap', bodyTy) = inferExp(menv, tenv, venv', smap, body)
              (* add function to tenv *)
            in
              {menv = menv,
               tenv = tenv,
               venv = venv',
               smap = smap'}
            end
        in
          foldl foldFunDec {menv = menv, tenv = tenv, venv = venv, smap = smap} fundecs
        end
        | infdec(_) = {menv = menv, tenv = tenv, venv = venv, smap = smap}
    in
      infdec(dec)
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
