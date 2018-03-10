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

structure Infer : INFER =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env
  structure U = Unify
  structure S = Substitute

  (* augments smap if substitution is defined, else returns original *)
  fun augmentSmap(smap, subs, pos) =
    let
      fun tryEnter(sub, smap') = case sub of
                                      S.SUB(SOME(sym, ty)) => let
                                                                val lookup = Symbol.look(smap', sym)
                                                              in
                                                                case lookup of
                                                                     SOME(existingTy) => (case U.unify(existingTy, ty, pos) of (* try unifying *)
                                                                                               S.SUB(SOME(_, ty2)) => smap' (* can this case happen? *)
                                                                                             | _ => smap')
                                                                   | _ => Symbol.enter(smap', sym, ty) (* if doesn't exist, add as usual *)
                                                              end
                                    | _ => smap'
    in
      foldl tryEnter smap subs
    end

  (* unifies all types in list with given type and substitues into smap *)
  fun unifyAndSubstitute(smap, ty, typos_list) =
    let
      fun foldSub((uty, pos), (smap, subs)) =
        let
          val sub = U.unify(ty, uty, pos)
        in
          (augmentSmap(smap, [sub], pos), sub::subs)
        end
      val (smap', subs') = foldl foldSub (smap, []) typos_list
    in
      (smap', List.rev(subs'))
    end

  fun getSWType(T.S_TY(sty)) = sty
    | getSWType(T.META(m)) = T.S_META(m)
    | getSWType(_) = T.S_BOTTOM

  fun getExplicitType(A.ExplicitTy(ty), _) = ty
    | getExplicitType(_, default) = default

  fun getExplicitSWType(A.ExplicitTy(ty), _) = getSWType(ty)
    | getExplicitSWType(_, default) = default

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
          | infexp(A.ApplyExp(e1, e2, pos)) =
            let
              val (smap', e1Ty) = inferExp(menv, tenv, venv, smap, e1)
              val (smap'', e2Ty) = inferExp(menv, tenv, venv, smap', e2)
            in
              case e1Ty of
                   T.S_TY(T.ARROW(sty1, sty2)) =>
                    let
                      val sub = U.unify(T.S_TY(sty1), e2Ty, pos)
                    in
                      (augmentSmap(smap'', [sub], pos), T.S_TY(sty2))
                    end
                 | _ => case e2Ty of
                             T.S_TY(e2Sty) =>
                              let
                                val retTy = T.S_META(E.newMeta())
                                val sub = U.unify(T.S_TY(T.ARROW(e2Sty, retTy)), e1Ty, pos)
                              in
                                (augmentSmap(smap'', [sub], pos), T.S_TY(retTy))
                              end
                           | T.BOTTOM => (smap'', T.S_TY(T.S_META(E.newMeta())))
                           | _ => (ErrorMsg.error pos "cannot apply function to non-sw type"; (smap'', T.S_TY(T.S_META(E.newMeta()))))
            end
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
                              let
                                val (sub, retTy) = U.unifyBitwiseOperator(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
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
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.NeqOp =>
                              let
                                val (sub, retTy) = U.unifyEqualityType(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.LtOp =>
                              let
                                val (sub, retTy) = U.unifyInequalityType(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.GtOp =>
                              let
                                val (sub, retTy) = U.unifyInequalityType(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.LeOp =>
                              let
                                val (sub, retTy) = U.unifyInequalityType(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.GeOp =>
                              let
                                val (sub, retTy) = U.unifyInequalityType(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.ConsOp =>
                              let
                                val (sub, retTy) = U.unifyList(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
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

              val venv'' = S.substitute(smap', venv')
              val () = print("===== VENV =====\n")
              val () = Symbol.print(TextIO.stdOut, venv'', Types.toString)

            in
              inferExp(menv', tenv', venv'', smap', body)
            end
          | infexp(A.AssignExp({lhs, rhs, pos})) =
            let
              val (smap', leftTy) = inferExp(menv, tenv, venv, smap, lhs)
              val (smap'', rightTy) = inferExp(menv, tenv, venv, smap', rhs)
              val (sub, retTy) = U.unifyAssign(leftTy, rightTy, pos)
              val smap''' = augmentSmap(smap'', [sub], pos)
            in
              (smap''', retTy)
            end
          | infexp(A.SeqExp(exps)) =
            let
              fun foldExp((exp, pos), (smap, ty_opt)) =
                let
                  val (smap', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (smap', SOME(expTy))
                end
              val (smap', retTy_opt) = foldl foldExp (smap, NONE) exps
            in
              (smap', case retTy_opt of
                           NONE => T.S_TY(T.S_RECORD([])) (* unit *)
                         | SOME(retTy) => retTy)
            end
          | infexp(A.IfExp({test, then', else', pos})) =
            let
              val (smap', testTy) = inferExp(menv, tenv, venv, smap, test)
              val sub1 = U.unify(T.S_TY(T.INT), testTy, pos)
              val (smap'', thenTy) = inferExp(menv, tenv, venv, smap', then')
              val (smap''', elseTy) = case else' of
                                          SOME(elseExp) => inferExp(menv, tenv, venv, smap'', elseExp)
                                        | _ => (smap'', case thenTy of
                                                     T.S_TY(_) => T.S_TY(T.S_RECORD([]))
                                                   | T.H_TY(_) => T.H_TY(T.H_RECORD([]))
                                                   | _ => T.BOTTOM)
              val sub2 = U.unify(thenTy, elseTy, pos)
              val smap'''' = augmentSmap(smap''', [sub1, sub2], pos)
              val retTy = case sub2 of
                               S.SUB(x) => thenTy
                             | S.ERROR(m) => T.BOTTOM
            in
              (smap'''', retTy)
            end
          | infexp(A.ListExp(exps)) = (smap, T.S_TY(T.LIST(T.INT))) (* TODO *)
          | infexp(A.ArrayExp(exps)) = (smap, T.EMPTY)
          | infexp(A.RefExp(exp, pos)) =
            let
              val (smap', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(s) => s
                               | T.META(m) => T.S_META(m)
                               | _ => T.S_BOTTOM
            in
              (smap', T.S_TY(T.REF(innerTy)))
            end
          | infexp(A.SWRecordExp({fields, pos})) = (smap, T.EMPTY)
          | infexp(A.HWRecordExp({fields, pos})) = (smap, T.EMPTY)
          | infexp(A.SWExp(exp, pos)) = (smap, T.EMPTY)
          | infexp(A.WithExp({exp, fields, pos})) = (smap, T.EMPTY)
          | infexp(A.DerefExp({exp, pos})) =
            let
              val (smap', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(T.REF(s)) => s
                               | T.S_TY(T.S_META(m)) => T.S_META(m)
                               | T.META(m) => T.S_META(m)
                               | _ => T.S_BOTTOM
              val newInnerTy = T.S_META(E.newMeta()) (* NOTE: should be creating new meta here? *)
              val sub = case innerTy of
                             T.S_META(m) => U.unify(expTy, T.S_TY(T.REF(newInnerTy)), pos)
                           | _ => S.SUB(NONE)
              val smap'' = augmentSmap(smap', [sub], pos)
              val retTy = case sub of
                               S.SUB(x) => (case innerTy of
                                                 T.S_META(m) => T.S_TY(newInnerTy)
                                               | _ => T.S_TY(innerTy))
                             | S.ERROR(m) => T.BOTTOM
            in
              (smap'', retTy)
            end
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
                | foldParam(A.TupleParams(fs), venv) = foldl (fn({name, ty, escape, pos}, v) => Symbol.enter(v, name, getExplicitType(ty, T.S_TY(T.S_BOTTOM)))) venv fs
                | foldParam(A.RecordParams(fs), venv) = foldl (fn({name, ty, escape, pos}, v) => Symbol.enter(v, name, getExplicitType(ty, T.S_TY(T.S_BOTTOM)))) venv fs
              val venv' = foldl foldParam venv params

              (* process body with augmented venv' *)
              val (smap', bodyTy) = inferExp(menv, tenv, venv', smap, body)

              (* unify bodyTy with resultTy *)
              val sub = U.unify(getExplicitType(resultTy, T.S_TY(T.S_BOTTOM)), bodyTy, resultPos)
              val smap'' = augmentSmap(smap', [sub], resultPos)

              (* TODO: add function to tenv *)
              fun getParamTy(A.NoParam) = T.S_RECORD([])
                | getParamTy(A.SingleParam({name, ty, escape, pos})) = getExplicitSWType(ty, T.S_BOTTOM)
                | getParamTy(A.TupleParams(fs)) =
                  let
                    fun makeTupleParamTy([], SOME(sty), _) = sty
                      | makeTupleParamTy({name, ty, escape, pos}::fs, NONE, i) = makeTupleParamTy(fs, SOME(T.S_RECORD([(Symbol.symbol(Int.toString(i)), getExplicitSWType(ty, T.S_BOTTOM))])), i + 1)
                      | makeTupleParamTy({name, ty, escape, pos}::fs, SOME(T.S_RECORD(rs)), i) = makeTupleParamTy(fs, SOME(T.S_RECORD(rs @ [(Symbol.symbol(Int.toString(i)), getExplicitSWType(ty, T.S_BOTTOM))])), i + 1)
                      | makeTupleParamTy(_) = raise Match
                  in
                    makeTupleParamTy(fs, NONE, 1)
                  end
                | getParamTy(A.RecordParams(fs)) =
                  let
                    fun makeRecordParamTy([], SOME(sty)) = sty
                      | makeRecordParamTy({name, ty, escape, pos}::fs, NONE) = makeRecordParamTy(fs, SOME(T.S_RECORD([(name, getExplicitSWType(ty, T.S_BOTTOM))])))
                      | makeRecordParamTy({name, ty, escape, pos}::fs, SOME(T.S_RECORD(rs))) = makeRecordParamTy(fs, SOME(T.S_RECORD(rs @ [(name, getExplicitSWType(ty, T.S_BOTTOM))])))
                      | makeRecordParamTy(_) = raise Match
                  in
                    makeRecordParamTy(fs, NONE)
                  end

              fun makeParamTy([], SOME(sty)) = sty
                | makeParamTy(p::ps, NONE) = makeParamTy(ps, SOME(getParamTy(p)))
                | makeParamTy(p::ps, SOME(sty)) = makeParamTy(ps, SOME(T.ARROW(sty, getParamTy(p))))
                | makeParamTy(_) = raise Match

              val paramTy = makeParamTy(params, NONE)
              val venv'' = Symbol.enter(venv, name, T.S_TY(T.ARROW(paramTy, getSWType(bodyTy))))
            in
              {menv = menv,
               tenv = tenv,
               venv = venv'',
               smap = smap''}
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
