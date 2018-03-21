signature INFER =
sig

  val inferProg :                                  Env.smap * Absyn.exp -> Env.smap                         (* returns substitution mapping *)
  val inferExp  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.exp -> Env.smap * Env.venv * Types.ty   (* returns mapping, substituted venv and expression type *)
  val inferDec  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.dec -> { menv: Env.menv,                (* returns augmented environments *)
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
                                      S.SUB(innersubs) => let
                                                            fun foldInnersub((sym, ty), smap'') =
                                                              case Symbol.look(smap'', sym) of
                                                                   SOME(existingTy) => smap''
                                                                 | _ => Symbol.enter(smap'', sym, ty) (* if doesn't exist, add as usual *)
                                                          in
                                                              foldl foldInnersub smap' innersubs
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
      val (smap', venv', ty) = inferExp(E.base_menv, E.base_tenv, E.base_venv, smap, e)
    in
      smap'
    end

  and inferExp(menv, tenv, venv, smap, exp) =
    let fun infexp(A.StructsSigsExp(structsigs)) = (smap, venv, T.EMPTY)
          | infexp(A.VarExp(sym, pos)) = (smap, venv, case Symbol.look(venv, sym) of
                                                           SOME(t) => t
                                                         | _ => (ErrorMsg.error pos ("unbound variable or constructor: " ^ Symbol.name(sym)); T.BOTTOM))
          | infexp(A.IntExp(num, pos)) = (smap, venv, T.S_TY(T.INT))
          | infexp(A.StringExp(str, pos)) = (smap, venv, T.S_TY(T.STRING))
          | infexp(A.RealExp(num, pos)) = (smap, venv, T.S_TY(T.REAL))
          | infexp(A.BitExp(bit, pos)) = (smap, venv, T.H_TY(T.BIT))
          | infexp(A.ApplyExp(e1, e2, pos)) =
            let
              val (smap', venv', e1Ty) = inferExp(menv, tenv, venv, smap, e1)
              val (smap'', venv'', e2Ty) = inferExp(menv, tenv, venv', smap', e2)
            in
              case e1Ty of
                   T.S_TY(T.ARROW(sty1, sty2)) =>
                    let
                      val sub = U.unify(T.S_TY(sty1), e2Ty, pos)
                    in
                      (augmentSmap(smap'', [sub], pos), venv'', T.S_TY(sty2))
                    end
                 | T.S_TY(T.S_POLY(tyvars, T.ARROW(sty1, sty2))) =>
                    let
                      val sub = U.unifyPolyApp(T.S_TY(sty1), e2Ty, pos)
                    in
                      (augmentSmap(smap'', [sub], pos), venv'', S.substituteType(T.S_TY(sty2), S.makeMap(sub), ref false)) (* return original smap but substitute on return type *)
                    end
                 | _ => case e2Ty of
                             T.S_TY(e2Sty) =>
                              let
                                val retTy = T.S_META(E.newMeta())
                                val sub = U.unify(T.S_TY(T.ARROW(e2Sty, retTy)), e1Ty, pos)
                              in
                                (augmentSmap(smap'', [sub], pos), venv'', T.S_TY(retTy))
                              end
                           | T.BOTTOM => (smap'', venv'', T.S_TY(T.S_META(E.newMeta())))
                           | _ => (ErrorMsg.error pos "cannot apply function to non-sw type"; (smap'', venv'', T.S_TY(T.S_META(E.newMeta()))))
            end
          | infexp(A.BinOpExp({left, oper, right, pos})) =
            let
              val (smap', venv', leftTy) = inferExp(menv, tenv, venv, smap, left)
              val (smap'', venv'', rightTy) = inferExp(menv, tenv, venv', smap', right)
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
              (smap''', venv'', retTy)
            end
          | infexp(A.UnOpExp({exp, oper, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.LetExp({decs, body, pos})) =
            let
              fun foldDec(dec, {menv, tenv, venv, smap}) = inferDec(menv, tenv, venv, smap, dec)
              val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldDec {menv = menv, tenv = tenv, venv = venv, smap = smap} decs
              val () = print("====== VENV ======\n")
              val () = Symbol.print(TextIO.stdOut, venv', Types.toString)
            in
              inferExp(menv', tenv', venv', smap', body)
            end
          | infexp(A.AssignExp({lhs, rhs, pos})) =
            let
              val (smap', venv', leftTy) = inferExp(menv, tenv, venv, smap, lhs)
              val (smap'', venv'', rightTy) = inferExp(menv, tenv, venv', smap', rhs)
              val (sub, retTy) = U.unifyAssign(leftTy, rightTy, pos)
              val smap''' = augmentSmap(smap'', [sub], pos)
            in
              (smap''', venv'', retTy)
            end
          | infexp(A.SeqExp(exps)) =
            let
              fun foldExp((exp, pos), (smap, venv, ty_opt)) =
                let
                  val (smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (smap', S.substitute(smap', venv'), SOME(expTy))
                end
              val (smap', venv', retTy_opt) = foldl foldExp (smap, venv, NONE) exps
            in
              (smap', venv', case retTy_opt of
                                 NONE => T.S_TY(T.S_RECORD([])) (* unit *)
                               | SOME(retTy) => retTy)
            end
          | infexp(A.IfExp({test, then', else', pos})) =
            let
              val (smap', venv', testTy) = inferExp(menv, tenv, venv, smap, test)
              val sub1 = U.unify(T.S_TY(T.INT), testTy, pos)
              val (smap'', venv'', thenTy) = inferExp(menv, tenv, venv', smap', then')
              val (smap''', venv''', elseTy) = case else' of
                                                    SOME(elseExp) => inferExp(menv, tenv, venv'', smap'', elseExp)
                                                  | _ => (smap'', venv'', case thenTy of
                                                                               T.S_TY(_) => T.S_TY(T.S_RECORD([]))
                                                                             | T.H_TY(_) => T.H_TY(T.H_RECORD([]))
                                                                             | _ => T.BOTTOM)
              val sub2 = U.unify(thenTy, elseTy, pos)
              val smap'''' = augmentSmap(smap''', [sub1, sub2], pos)
              val retTy = case sub2 of
                               S.SUB(_) => thenTy
                             | S.ERROR(_) => T.BOTTOM
            in
              (smap'''', venv''', retTy)
            end
          | infexp(A.ListExp(exps)) = (smap, venv, T.S_TY(T.LIST(T.INT))) (* TODO *)
          | infexp(A.ArrayExp(exps)) = (smap, venv, T.EMPTY)
          | infexp(A.RefExp(exp, pos)) =
            let
              val (smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(s) => s
                               | T.META(m) => T.S_META(m)
                               | _ => T.S_BOTTOM
            in
              (smap', venv', T.S_TY(T.REF(innerTy)))
            end
          | infexp(A.SWRecordExp({fields, pos})) =
            let
              fun foldField((sym, exp, pos), (smap, venv, tyfields)) =
                let
                  val (smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (smap', venv', (sym, getSWType(expTy))::tyfields)
                end
              val (smap', venv', tyfields) = foldl foldField (smap, venv, []) fields
            in
              (smap', venv', T.S_TY(T.S_RECORD(List.rev(tyfields))))
            end
          | infexp(A.HWRecordExp({fields, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.SWExp(exp, pos)) = (smap, venv, T.EMPTY)
          | infexp(A.WithExp({exp, fields, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.DerefExp({exp, pos})) =
            let
              val (smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(T.REF(s)) => s
                               | T.S_TY(T.S_META(m)) => T.S_META(m)
                               | T.META(m) => T.S_META(m)
                               | _ => T.S_BOTTOM
              val newInnerTy = T.S_META(E.newMeta()) (* NOTE: should be creating new meta here? *)
              val sub = case innerTy of
                             T.S_META(m) => U.unify(expTy, T.S_TY(T.REF(newInnerTy)), pos)
                           | _ => S.SUB([])
              val smap'' = augmentSmap(smap', [sub], pos)
              val retTy = case sub of
                               S.SUB(x) => (case innerTy of
                                                 T.S_META(m) => T.S_TY(newInnerTy)
                                               | _ => T.S_TY(innerTy))
                             | S.ERROR(m) => T.BOTTOM
            in
              (smap'', venv', retTy)
            end
          | infexp(A.StructAccExp({name, field, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.RecordAccExp({exp, field, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.ArrayAccExp({exp, index, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.PatternMatchExp({exp, cases, pos})) = (smap, venv, T.EMPTY)
          | infexp(A.BitArrayExp({size, result, spec})) = (smap, venv, T.EMPTY)
    in
      let
        val (smap', venv', ty) = infexp(exp)
      in
        (smap', S.substitute(smap', venv'), ty)
      end
    end

  and inferDec(menv, tenv, venv, smap, dec) =
    let
      fun infdec(A.FunctionDec(fundecs)) =
        let
          fun foldFunDec({name, params, result = (resultTy, resultPos), body, pos}, {menv, tenv, venv, smap}) =
            let
              val () = print("=== MENV IN " ^ Symbol.name(name) ^ " ===\n")
              val () = Symbol.print(TextIO.stdOut, menv, T.toString)
              (* enter params into venv and menv *)
              fun foldParam(A.NoParam, (venv, menv)) = (venv, menv)
                | foldParam(A.SingleParam{name, ty, escape, pos}, (venv, menv)) =
                  let
                    val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
                    val menv' = case paramTy of
                                     T.S_TY(T.S_META(sm)) => Symbol.enter(menv, sm, paramTy)
                                   | _ => menv
                  in
                    (Symbol.enter(venv, name, paramTy), menv')
                  end
                | foldParam(A.TupleParams(fs), (venv, menv)) = 
                  foldl (fn({name, ty, escape, pos}, v) => (let
                                                              val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
                                                              val menv' = case paramTy of
                                                                               T.S_TY(T.S_META(sm)) => Symbol.enter(menv, sm, paramTy)
                                                                             | _ => menv
                                                            in
                                                              (Symbol.enter(venv, name, paramTy), menv')
                                                            end)) (venv, menv) fs
                | foldParam(A.RecordParams(fs), (venv, menv)) =
                  foldl (fn({name, ty, escape, pos}, v) => (let
                                                              val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
                                                              val menv' = case paramTy of
                                                                               T.S_TY(T.S_META(sm)) => Symbol.enter(menv, sm, paramTy)
                                                                             | _ => menv
                                                            in
                                                              (Symbol.enter(venv, name, paramTy), menv')
                                                            end)) (venv, menv) fs
              val (venv', menv') = foldl foldParam (venv, menv) params

              (* process body with augmented venv' *)
              val (smap', _, bodyTy) = inferExp(menv', tenv, venv', smap, body)

              (* unify bodyTy with resultTy *)
              val sub = U.unify(getExplicitType(resultTy, T.S_TY(T.S_BOTTOM)), bodyTy, resultPos)
              val smap'' = augmentSmap(smap', [sub], resultPos)

              (* add function to venv *)
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

              fun makeFunTy([], SOME(sty)) = sty
                | makeFunTy(t::ts, NONE) = makeFunTy(ts, SOME(t))
                | makeFunTy(t::ts, SOME(sty)) = makeFunTy(ts, SOME(T.ARROW(t, sty)))
                | makeFunTy(_) = raise Match

              val funTy = makeFunTy(getSWType(bodyTy)::List.rev(map getParamTy params), NONE)
              val venv'' = Symbol.enter(venv, name, T.S_TY(funTy))
              val venv''' = S.substitute(smap'', venv'')

              val subbedFunTy = valOf(Symbol.look(venv''', name))
              (* find metas part of substituted function parameters and POLY based on those *)
              val params' = case subbedFunTy of
                                 T.S_TY(T.ARROW(params, _)) => params
                               | _ => (ErrorMsg.error pos ("unbound function: " ^ Symbol.name(name)); T.S_BOTTOM)

              fun flattenMetas(T.S_META(sm)) = (case Symbol.look(menv, sm) of
                                                    SOME(_) => []
                                                  | _ => [sm] (* only add if not in menv *))
                | flattenMetas(T.S_RECORD(fs)) = List.rev(foldl (fn((tyv, sty), metas)  => flattenMetas(sty) @ metas) [] fs)
                | flattenMetas(T.ARROW(s1, s2)) = flattenMetas(s1) @ flattenMetas(s2)
                | flattenMetas(T.LIST(s)) = flattenMetas(s)
                | flattenMetas(T.SW_H(h)) = flattenHWMetas(h)
                | flattenMetas(T.SW_M(m)) = flattenModMetas(m)
                | flattenMetas(T.REF(s)) = flattenMetas(s)
                | flattenMetas(T.S_DATATYPE(tys, u)) = List.rev(foldl (fn((tyv, sty_opt), metas)  => case sty_opt of SOME(s) => flattenMetas(s) @ metas | NONE => metas) [] tys)
                | flattenMetas(_) = []
              and flattenHWMetas(T.H_META(hm)) = (case Symbol.look(menv, hm) of
                                                      SOME(_) => []
                                                    | _ => [hm] (* only add if not in menv *))
                | flattenHWMetas(T.ARRAY{ty, size}) = flattenHWMetas(ty)
                | flattenHWMetas(T.TEMPORAL{ty, time}) = flattenHWMetas(ty)
                | flattenHWMetas(T.H_RECORD(fs)) = List.rev(foldl (fn((tyv, hty), metas)  => flattenHWMetas(hty) @ metas) [] fs)
                | flattenHWMetas(T.H_DATATYPE(tys, u)) = List.rev(foldl (fn((tyv, hty_opt), metas)  => case hty_opt of SOME(h) => flattenHWMetas(h) @ metas | NONE => metas) [] tys)
                | flattenHWMetas(_) = []
              and flattenModMetas(T.MODULE(h1, h2)) = flattenHWMetas(h1) @ flattenHWMetas(h2)
              val paramMetas = flattenMetas params'

              val funTy' = case paramMetas of
                                [] => subbedFunTy
                               | _ => T.S_TY(T.S_POLY(paramMetas, getSWType(subbedFunTy)))

              val venv'''' = Symbol.enter(venv''', name, funTy')
            in
              {menv = menv,
               tenv = tenv,
               venv = venv'''',
               smap = smap''}
            end
        in
          foldl foldFunDec {menv = menv, tenv = tenv, venv = venv, smap = smap} fundecs
        end
      | infdec(A.ValDec(valdecs)) =
        let
          fun foldValDec({name, escape, ty = (ty, tyPos), init, pos}, {menv, tenv, venv, smap}) =
            let
              (* infer type of initializing expression *)
              val (smap', venv', initTy) = inferExp(menv, tenv, venv, smap, init)

              (* unify initializing expression with value type *)
              val sub = U.unify(getExplicitType(ty, T.BOTTOM), initTy, tyPos)

              (* add to substitution mapping *)
              val smap'' = augmentSmap(smap', [sub], tyPos)

              (* add name to variable environment *)
              val venv'' = Symbol.enter(venv', name, initTy)

              (* perform substitution *)
              val venv''' = S.substitute(smap'', venv'')
            in
              {menv = menv, tenv = tenv, venv = venv''', smap = smap''}
            end
        in
          foldl foldValDec {menv = menv, tenv = tenv, venv = venv, smap = smap} valdecs
        end
      | infdec(_) = {menv = menv, tenv = tenv, venv = venv, smap = smap}
    in
      infdec(dec)
    end

end
