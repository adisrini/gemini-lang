signature INFER =
sig

  val inferProg :                                  Env.smap * Absyn.exp -> Env.smap * Absyn.exp                         (* returns substitution mapping *)
  val inferExp  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.exp -> Absyn.exp * Env.smap * Env.venv * Types.ty   (* returns mapping, substituted venv and expression type *)
  val inferDec  : Env.menv * Env.tenv * Env.venv * Env.smap * Absyn.dec -> { menv: Env.menv,                            (* returns augmented environments *)
                                                                             tenv: Env.tenv,
                                                                             venv: Env.venv,
                                                                             dec': Absyn.dec,
                                                                             smap: Env.smap }

end

structure Infer : INFER =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env
  structure U = Unify
  structure S = Substitute
  structure M = Meta

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

  fun getHWType(T.H_TY(hty)) = hty
    | getHWType(T.META(m)) = T.H_META(m)
    | getHWType(_) = T.H_BOTTOM

  fun getModType(T.M_TY(mty)) = mty
    | getModType(_) = T.M_BOTTOM

  fun getExplicitType(A.ExplicitTy(ty), _) = ty
    | getExplicitType(_, default) = default

  fun getExplicitSWType(A.ExplicitTy(ty), _) = getSWType(ty)
    | getExplicitSWType(_, default) = default

  fun getExplicitHWType(A.ExplicitTy(ty), _) = getHWType(ty)
    | getExplicitHWType(_, default) = default

  (* enter params into venv and menv *)
  fun foldSWParam(A.NoParam, (venv, menv)) = (venv, menv)
    | foldSWParam(A.SingleParam{name, ty, escape, pos}, (venv, menv)) =
      let
        val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
        val menv' = case paramTy of
                         T.S_TY(T.S_META(sm)) => Symbol.enter(menv, sm, paramTy)
                       | _ => menv
      in
        (Symbol.enter(venv, name, paramTy), menv')
      end
    | foldSWParam(A.TupleParams(fs), (venv, menv)) = 
      foldl (fn({name, ty, escape, pos}, (v, m)) => (let
                                                  val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
                                                  val menv' = case paramTy of
                                                                   T.S_TY(T.S_META(sm)) => Symbol.enter(m, sm, paramTy)
                                                                 | _ => m
                                                  val venv' = Symbol.enter(v, name, paramTy)
                                                in
                                                  (venv', menv')
                                                end)) (venv, menv) fs
    | foldSWParam(A.RecordParams(fs), (venv, menv)) =
      foldl (fn({name, ty, escape, pos}, (v, m)) => (let
                                                  val paramTy = getExplicitType(ty, T.S_TY(T.S_BOTTOM))
                                                  val menv' = case paramTy of
                                                                   T.S_TY(T.S_META(sm)) => Symbol.enter(m, sm, paramTy)
                                                                 | _ => m
                                                  val venv' = Symbol.enter(v, name, paramTy)
                                                in
                                                  (venv', menv')
                                                end)) (venv, menv) fs

  (* enter params into venv and menv *)
  fun foldHWParam(A.NoParam, (venv, menv)) = (venv, menv)
    | foldHWParam(A.SingleParam{name, ty, escape, pos}, (venv, menv)) =
      let
        val paramTy = T.H_TY(getExplicitHWType(ty, T.H_BOTTOM))
        val menv' = case paramTy of
                         T.H_TY(T.H_META(hm)) => Symbol.enter(menv, hm, paramTy)
                       | _ => menv
      in
        (Symbol.enter(venv, name, paramTy), menv')
      end
    | foldHWParam(A.TupleParams(fs), (venv, menv)) = 
      foldl (fn({name, ty, escape, pos}, (v, m)) => (let
                                                  val paramTy = T.H_TY(getExplicitHWType(ty, T.H_BOTTOM))
                                                  val menv' = case paramTy of
                                                                   T.H_TY(T.H_META(hm)) => Symbol.enter(m, hm, paramTy)
                                                                 | _ => m
                                                  val venv' = Symbol.enter(v, name, paramTy)
                                                in
                                                  (venv', menv')
                                                end)) (venv, menv) fs
    | foldHWParam(A.RecordParams(fs), (venv, menv)) =
      foldl (fn({name, ty, escape, pos}, (v, m)) => (let
                                                  val paramTy = T.H_TY(getExplicitHWType(ty, T.H_BOTTOM))
                                                  val menv' = case paramTy of
                                                                   T.H_TY(T.H_META(hm)) => Symbol.enter(m, hm, paramTy)
                                                                 | _ => m
                                                  val venv' = Symbol.enter(v, name, paramTy)
                                                in
                                                  (venv', menv')
                                                end)) (venv, menv) fs

  fun getSWParamTy(A.NoParam) = T.S_RECORD([])
    | getSWParamTy(A.SingleParam({name, ty, escape, pos})) = getExplicitSWType(ty, T.S_BOTTOM)
    | getSWParamTy(A.TupleParams(fs)) =
      let
        fun makeTupleParamTy([], SOME(sty), _) = sty
          | makeTupleParamTy({name, ty, escape, pos}::fs, NONE, i) = makeTupleParamTy(fs, SOME(T.S_RECORD([(Symbol.symbol(Int.toString(i)), getExplicitSWType(ty, T.S_BOTTOM))])), i + 1)
          | makeTupleParamTy({name, ty, escape, pos}::fs, SOME(T.S_RECORD(rs)), i) = makeTupleParamTy(fs, SOME(T.S_RECORD(rs @ [(Symbol.symbol(Int.toString(i)), getExplicitSWType(ty, T.S_BOTTOM))])), i + 1)
          | makeTupleParamTy(_) = raise Match
      in
        makeTupleParamTy(fs, NONE, 1)
      end
    | getSWParamTy(A.RecordParams(fs)) =
      let
        fun makeRecordParamTy([], SOME(sty)) = sty
          | makeRecordParamTy({name, ty, escape, pos}::fs, NONE) = makeRecordParamTy(fs, SOME(T.S_RECORD([(name, getExplicitSWType(ty, T.S_BOTTOM))])))
          | makeRecordParamTy({name, ty, escape, pos}::fs, SOME(T.S_RECORD(rs))) = makeRecordParamTy(fs, SOME(T.S_RECORD(rs @ [(name, getExplicitSWType(ty, T.S_BOTTOM))])))
          | makeRecordParamTy(_) = raise Match
      in
        makeRecordParamTy(fs, NONE)
      end

  fun getHWParamTy(A.NoParam) = T.H_RECORD([])
    | getHWParamTy(A.SingleParam({name, ty, escape, pos})) = getExplicitHWType(ty, T.H_BOTTOM)
    | getHWParamTy(A.TupleParams(fs)) =
      let
        fun makeTupleParamTy([], SOME(hty), _) = hty
          | makeTupleParamTy({name, ty, escape, pos}::fs, NONE, i) = makeTupleParamTy(fs, SOME(T.H_RECORD([(Symbol.symbol(Int.toString(i)), getExplicitHWType(ty, T.H_BOTTOM))])), i + 1)
          | makeTupleParamTy({name, ty, escape, pos}::fs, SOME(T.H_RECORD(rs)), i) = makeTupleParamTy(fs, SOME(T.H_RECORD(rs @ [(Symbol.symbol(Int.toString(i)), getExplicitHWType(ty, T.H_BOTTOM))])), i + 1)
          | makeTupleParamTy(_) = raise Match
      in
        makeTupleParamTy(fs, NONE, 1)
      end
    | getHWParamTy(A.RecordParams(fs)) =
      let
        fun makeRecordParamTy([], SOME(hty)) = hty
          | makeRecordParamTy({name, ty, escape, pos}::fs, NONE) = makeRecordParamTy(fs, SOME(T.H_RECORD([(name, getExplicitHWType(ty, T.H_BOTTOM))])))
          | makeRecordParamTy({name, ty, escape, pos}::fs, SOME(T.H_RECORD(rs))) = makeRecordParamTy(fs, SOME(T.H_RECORD(rs @ [(name, getExplicitHWType(ty, T.H_BOTTOM))])))
          | makeRecordParamTy(_) = raise Match
      in
        makeRecordParamTy(fs, NONE)
      end


  fun inferProg(smap, e) =
    let
      val (prog, smap', venv', ty) = inferExp(E.base_menv, E.base_tenv, E.base_venv, smap, e)
    in
      (smap', prog)
    end

  and inferExp(menv, tenv, venv, smap, exp) =
    let fun infexp(A.StructsSigsExp(structsigs)) = (exp, smap, venv, T.EMPTY)
          | infexp(A.VarExp(sym, pos)) = (exp, smap, venv, case Symbol.look(venv, sym) of
                                                           SOME(t) => t
                                                         | _ => (ErrorMsg.error pos ("unbound variable or constructor: " ^ Symbol.name(sym)); T.BOTTOM))
          | infexp(A.IntExp(num, pos)) = (exp, smap, venv, T.S_TY(T.INT))
          | infexp(A.StringExp(str, pos)) = (exp, smap, venv, T.S_TY(T.STRING))
          | infexp(A.RealExp(num, pos)) = (exp, smap, venv, T.S_TY(T.REAL))
          | infexp(A.BitExp(bit, pos)) = (exp, smap, venv, T.H_TY(T.BIT))
          | infexp(A.ApplyExp(e1, e2, pos)) =
            let
              val (e1', smap', venv', e1Ty) = inferExp(menv, tenv, venv, smap, e1)
              val (e2', smap'', venv'', e2Ty) = inferExp(menv, tenv, venv', smap', e2)
            in
              case e1Ty of
                   T.S_TY(T.ARROW(sty1, sty2)) =>
                    let
                      val sub = U.unify(T.S_TY(sty1), e2Ty, pos)
                    in
                      (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', T.S_TY(sty2))
                    end
                 | T.M_TY(T.MODULE(hty1, hty2)) =>
                    let
                      val sub = U.unify(T.H_TY(hty1), e2Ty, pos)
                    in
                      (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', T.H_TY(hty2))
                    end
                 | T.S_TY(T.S_POLY(tyvars, T.ARROW(sty1, sty2))) =>
                    let
                      val sub = U.unifyPolyFunApp(T.S_TY(sty1), e2Ty, pos)
                    in
                      (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', S.substituteType(T.S_TY(sty2), S.makeMap(sub), ref false)) (* return original smap but substitute on return type *)
                    end
                 | T.M_TY(T.M_POLY(tyvars, T.MODULE(hty1, hty2))) =>
                    let
                      val sub = U.unifyPolyModApp(T.H_TY(hty1), e2Ty, pos)
                    in
                      (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', S.substituteType(T.H_TY(hty2), S.makeMap(sub), ref false)) (* return original smap but substitute on return type *)
                    end
                 | _ => case e2Ty of
                             T.S_TY(e2Sty) =>
                              let
                                val retTy = T.S_META(M.newMeta())
                                val sub = U.unify(T.S_TY(T.ARROW(e2Sty, retTy)), e1Ty, pos)
                              in
                                (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', T.S_TY(retTy))
                              end
                           | T.H_TY(e2Hty) =>
                              let
                                val retTy = T.H_META(M.newMeta())
                                val sub = U.unify(T.M_TY(T.MODULE(e2Hty, retTy)), e1Ty, pos)
                              in
                                (A.ApplyExp(e1', e2', pos), augmentSmap(smap'', [sub], pos), venv'', T.H_TY(retTy))
                              end
                           | T.BOTTOM => (A.ApplyExp(e1', e2', pos), smap'', venv'', T.S_TY(T.S_META(M.newMeta())))
                           | _ => (ErrorMsg.error pos "cannot apply function to non-sw type"; (A.ApplyExp(e1', e2', pos), smap'', venv'', T.S_TY(T.S_META(M.newMeta()))))
            end
          | infexp(A.ParameterApplyExp(e1, e2, pos)) = (exp, smap, venv, T.EMPTY)
          | infexp(A.BinOpExp({left, oper, right, pos})) =
            let
              val (left', smap', venv', leftTy) = inferExp(menv, tenv, venv, smap, left)
              val (right', smap'', venv'', rightTy) = inferExp(menv, tenv, venv', smap', right)
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
                            | A.BitAndOp =>
                              let
                                val (sub, retTy) = U.unifyBitOp(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.BitOrOp =>
                              let
                                val (sub, retTy) = U.unifyBitOp(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.BitXorOp =>
                              let
                                val (sub, retTy) = U.unifyBitOp(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub], pos)
                              in
                                ((smap', [sub]), retTy)
                              end
                            | A.BitSLLOp =>
                              let
                                val (subs, retTy) = U.unifyShift(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', subs, pos)
                              in
                                  ((smap', subs), retTy)
                              end
                            | A.BitSRLOp =>
                              let
                                val (subs, retTy) = U.unifyShift(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', subs, pos)
                              in
                                  ((smap', subs), retTy)
                              end
                            | A.BitSRAOp =>
                              let
                                val (subs, retTy) = U.unifyShift(leftTy, rightTy, pos)
                                val smap' = augmentSmap(smap'', subs, pos)
                              in
                                  ((smap', subs), retTy)
                              end
                            | A.BitDoubleAndOp =>
                              let
                                val sub1 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), leftTy, pos)
                                val sub2 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub1, sub2], pos)
                              in
                                ((smap', [sub1, sub2]), T.H_TY(T.BIT))
                              end
                            | A.BitDoubleOrOp =>
                              let
                                val sub1 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), leftTy, pos)
                                val sub2 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub1, sub2], pos)
                              in
                                ((smap', [sub1, sub2]), T.H_TY(T.BIT))
                              end
                            | A.BitDoubleXorOp =>
                              let
                                val sub1 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), leftTy, pos)
                                val sub2 = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), rightTy, pos)
                                val smap' = augmentSmap(smap'', [sub1, sub2], pos)
                              in
                                ((smap', [sub1, sub2]), T.H_TY(T.BIT))
                              end
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
              (A.BinOpExp{left = left', oper = oper, right = right', pos = pos}, smap''', venv'', retTy)
            end
          | infexp(A.UnOpExp({exp, oper, pos})) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val (smap'', retTy) = case oper of
                              A.IntMinusOp =>
                                let
                                  val (smap''', subs) = unifyAndSubstitute(smap', T.S_TY(T.INT), [(expTy, pos)])
                                in
                                  (smap''', T.S_TY(T.INT))
                                end
                            | A.BitNotOp =>
                                (smap', case expTy of
                                             T.H_TY(_) => expTy
                                           | T.META(m) => T.H_TY(T.H_META(m))
                                           | _ => (ErrorMsg.error pos "expected hw type"; T.H_TY(T.H_BOTTOM)))
                            | A.BitOrReduceOp =>
                                let
                                  val sub = U.unify(T.H_TY(T.ARRAY({ty = T.BIT, size = ref ~1})), expTy, pos)
                                  val smap''' = augmentSmap(smap', [sub], pos)
                                in
                                  (smap''', T.H_TY(T.BIT))
                                end
                            | A.BitAndReduceOp =>
                                let
                                  val sub = U.unify(T.H_TY(T.ARRAY({ty = T.BIT, size = ref ~1})), expTy, pos)
                                  val smap''' = augmentSmap(smap', [sub], pos)
                                in
                                  (smap''', T.H_TY(T.BIT))
                                end
                            | A.BitXorReduceOp =>
                                let
                                  val sub = U.unify(T.H_TY(T.ARRAY({ty = T.BIT, size = ref ~1})), expTy, pos)
                                  val smap''' = augmentSmap(smap', [sub], pos)
                                in
                                  (smap''', T.H_TY(T.BIT))
                                end
                            | _ => raise Match
            in
              (A.UnOpExp{exp = exp', oper = oper, pos = pos}, smap'', venv', retTy)
            end
          | infexp(A.LetExp({decs, body, pos})) =
            let
              fun foldDec(dec, {menv, tenv, venv, augmented_decs, smap}) =
                let
                  val {menv = menv', tenv = tenv', venv = venv', dec' = dec', smap = smap'} = inferDec(menv, tenv, venv, smap, dec)
                in
                  {menv = menv',
                   tenv = tenv',
                   venv = venv',
                   augmented_decs = augmented_decs @ [dec'],
                   smap = smap'}
                end

              val {menv = menv', tenv = tenv', venv = venv', augmented_decs = decs', smap = smap'} = foldl foldDec {menv = menv, tenv = tenv, venv = venv, augmented_decs = decs, smap = smap} decs
              val () = print("====== VENV ======\n")
              val () = Symbol.print(TextIO.stdOut, venv', Types.toString)
              val () = print("====== TENV ======\n")
              val () = Symbol.print(TextIO.stdOut, tenv', Types.toString)
              val (body', smap'', venv'', bodyTy) = inferExp(menv', tenv', venv', smap', body)
            in
              (A.LetExp{decs = decs', body = body', pos = pos}, smap'', venv'', bodyTy)
            end
          | infexp(A.AssignExp({lhs, rhs, pos})) =
            let
              val (lhs', smap', venv', leftTy) = inferExp(menv, tenv, venv, smap, lhs)
              val (rhs', smap'', venv'', rightTy) = inferExp(menv, tenv, venv', smap', rhs)
              val (sub, retTy) = U.unifyAssign(leftTy, rightTy, pos)
              val smap''' = augmentSmap(smap'', [sub], pos)
            in
              (A.AssignExp{lhs = lhs', rhs = rhs', pos = pos}, smap''', venv'', retTy)
            end
          | infexp(A.SeqExp(exps)) =
            let
              fun foldExp((exp, pos), (exps, smap, venv, ty_opt)) =
                let
                  val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (exps @ [(exp', pos)], smap', S.substitute(smap', venv'), SOME(expTy))
                end
              val (exps', smap', venv', retTy_opt) = foldl foldExp ([], smap, venv, NONE) exps
            in
              (A.SeqExp(exps'), smap', venv', case retTy_opt of
                                 NONE => T.S_TY(T.S_RECORD([])) (* unit *)
                               | SOME(retTy) => retTy)
            end
          | infexp(A.IfExp({test, then', else', pos})) =
            let
              val (test', smap', venv', testTy) = inferExp(menv, tenv, venv, smap, test)
              val sub1 = U.unify(T.S_TY(T.INT), testTy, pos)
              val (then'', smap'', venv'', thenTy) = inferExp(menv, tenv, venv', smap', then')
              val (else'', smap''', venv''', elseTy) = case else' of
                                                    SOME(elseExp) => let val (elseExp', elseSmap, elseVenv, elseExpTy) = inferExp(menv, tenv, venv'', smap'', elseExp)
                                                                     in (SOME(elseExp'), elseSmap, elseVenv, elseExpTy)
                                                                     end
                                                  | _ => (NONE, smap'', venv'', case thenTy of
                                                                               T.S_TY(_) => T.S_TY(T.S_RECORD([]))
                                                                             | T.H_TY(_) => T.H_TY(T.H_RECORD([]))
                                                                             | _ => T.BOTTOM)
              val sub2 = U.unify(thenTy, elseTy, pos)
              val smap'''' = augmentSmap(smap''', [sub1, sub2], pos)
              val retTy = case sub2 of
                               S.SUB(_) => thenTy
                             | S.ERROR(_) => T.BOTTOM
            in
              (A.IfExp{test = test', then' = then'', else' = else'', pos = pos}, smap'''', venv''', retTy)
            end
          | infexp(A.ListExp(exps)) =
            let
              fun foldElem((exp, pos), (exps', smap, venv, elemTy)) =
                let
                  val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                  val sub = U.unify(elemTy, expTy, pos)
                  val smap'' = augmentSmap(smap', [sub], pos)

                  val strongerTy = case elemTy of
                                        T.S_TY(T.S_META(_)) => expTy
                                      | _ => elemTy
                in
                  (exps' @ [(exp', pos)], smap'', S.substitute(smap'', venv'), strongerTy)
                end

              val (exps', smap', venv', retTy) = foldl foldElem ([], smap, venv, T.S_TY(T.S_META(M.newMeta()))) exps
            in
              (A.ListExp(exps'), smap', venv', T.S_TY(T.LIST(getSWType(retTy))))
            end
          | infexp(A.ArrayExp(exps)) =
            let
              fun foldElem((exp, pos), (exps', smap, venv, elemTy)) =
                let
                  val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                  val sub = U.unify(elemTy, expTy, pos)
                  val smap'' = augmentSmap(smap', [sub], pos)

                  val strongerTy = case elemTy of
                                        T.H_TY(T.H_META(_)) => expTy
                                      | _ => elemTy
                in
                  (exps' @ [(exp', pos)], smap'', S.substitute(smap'', venv'), strongerTy)
                end

              val (exps', smap', venv', retTy) = foldl foldElem ([], smap, venv, T.H_TY(T.H_META(M.newMeta()))) (Vector.toList(exps))
            in
              (A.ArrayExp(Vector.fromList(exps')), smap', venv', T.H_TY(T.ARRAY({ty = getHWType(retTy), size = ref (Vector.length(exps))})))
            end
          | infexp(A.RefExp(exp, pos)) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(s) => s
                               | T.META(m) => T.S_META(m)
                               | _ => (ErrorMsg.error pos "expected 'sw type"; T.S_BOTTOM)
            in
              (A.RefExp(exp', pos), smap', venv', T.S_TY(T.REF(innerTy)))
            end
          | infexp(A.SWRecordExp({fields, pos})) =
            let
              fun foldField((sym, exp, pos), (fields', smap, venv, tyfields)) =
                let
                  val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (fields' @ [(sym, exp', pos)], smap', venv', (sym, getSWType(expTy))::tyfields)
                end
              val (fields', smap', venv', tyfields) = foldl foldField ([], smap, venv, []) fields
            in
              (A.SWRecordExp{fields = fields', pos = pos}, smap', venv', T.S_TY(T.S_RECORD(List.rev(tyfields))))
            end
          | infexp(A.HWRecordExp({fields, pos})) =
            let
              fun foldField((sym, exp, pos), (fields', smap, venv, tyfields)) =
                let
                  val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
                in
                  (fields' @ [(sym, exp', pos)], smap', venv', (sym, getHWType(expTy))::tyfields)
                end
              val (fields', smap', venv', tyfields) = foldl foldField ([], smap, venv, []) fields
            in
              (A.HWRecordExp{fields = fields', pos = pos}, smap', venv', T.H_TY(T.H_RECORD(List.rev(tyfields))))
            end
          | infexp(A.SWExp(exp, pos)) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val retTy = case expTy of
                              T.H_TY(h) => T.SW_H(h)
                            | T.META(m) => T.SW_H(T.H_META(m))
                            | T.M_TY(m) => T.SW_M(m)
                            | _ => (ErrorMsg.error pos "expected hw or module type"; T.S_BOTTOM)
            in
              (A.SWExp(exp', pos), smap', venv', T.S_TY(retTy))
            end
          | infexp(A.UnSWExp(exp, pos)) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(T.SW_H(h)) => h
                               | T.S_TY(T.S_META(m)) => T.H_META(M.newMeta())
                               | T.META(m) => T.H_META(M.newMeta())
                               | _ => T.H_BOTTOM
              val newInnerTy = T.H_META(M.newMeta()) (* NOTE: should be creating new meta here? *)
              val sub = case innerTy of
                             T.H_META(m) => U.unify(expTy, T.S_TY(T.SW_H(newInnerTy)), pos)
                           | _ => S.SUB([])
              val smap'' = augmentSmap(smap', [sub], pos)
              val retTy = case sub of
                               S.SUB(x) => (case innerTy of
                                                 T.H_META(m) => T.H_TY(newInnerTy)
                                               | _ => T.H_TY(innerTy))
                             | S.ERROR(m) => T.BOTTOM
            in
              (A.UnSWExp(exp', pos), smap'', venv', retTy)
            end
          | infexp(A.WithExp({exp, fields, pos})) = (exp, smap, venv, T.EMPTY)
          | infexp(A.DerefExp({exp, pos})) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val innerTy = case expTy of
                                 T.S_TY(T.REF(s)) => s
                               | T.S_TY(T.S_META(m)) => T.S_META(m)
                               | T.META(m) => T.S_META(m)
                               | _ => T.S_BOTTOM
              val newInnerTy = T.S_META(M.newMeta()) (* NOTE: should be creating new meta here? *)
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
              (A.DerefExp{exp = exp', pos = pos}, smap'', venv', retTy)
            end
          | infexp(A.StructAccExp({name, field, pos})) = (exp, smap, venv, case Symbol.look(E.base_senv, name) of
                                                                           SOME(stenv) => (case Symbol.look(stenv, field) of
                                                                                                SOME(t, _) => t
                                                                                              | _ => (ErrorMsg.error pos ("unbound path in structure: " ^ Symbol.name(field)); T.BOTTOM))
                                                                         | _ => (ErrorMsg.error pos ("unbound structure: " ^ Symbol.name(name)); T.BOTTOM))
          | infexp(A.RecordAccExp({exp, field, pos})) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val retTy = case expTy of
                               T.S_TY(T.S_RECORD(fields)) => (case List.find (fn((sym, _)) => Symbol.name(sym) = Symbol.name(field)) fields of
                                                                   SOME(_, x) => T.S_TY(x)
                                                                 | _ => (ErrorMsg.error pos ("unknown field " ^ Symbol.name(field)); T.S_TY(T.S_BOTTOM)))
                             | T.H_TY(T.H_RECORD(fields)) => (case List.find (fn((sym, _)) => Symbol.name(sym) = Symbol.name(field)) fields of
                                                                   SOME(_, x) => T.H_TY(x)
                                                                 | _ => (ErrorMsg.error pos ("unknown field " ^ Symbol.name(field)); T.H_TY(T.H_BOTTOM)))
                             | T.S_TY(T.S_META(sm)) => (ErrorMsg.error pos ("unresolved flex record (can't tell what fields there are besides #" ^ Symbol.name(field) ^ ")"); T.S_TY(T.S_BOTTOM))
                             | T.H_TY(T.H_META(hm)) => (ErrorMsg.error pos ("unresolved flex record (can't tell what fields there are besides #" ^ Symbol.name(field) ^ ")"); T.H_TY(T.H_BOTTOM))
                             | _ => (ErrorMsg.error pos ("cannot access field of non-record type"); T.S_TY(T.S_BOTTOM))
            in
              (A.RecordAccExp{exp = exp', field = field, pos = pos}, smap', venv', retTy)
            end
          | infexp(A.ArrayAccExp({exp, index, pos})) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)
              val (index', smap'', venv'', indexTy) = inferExp(menv, tenv, venv', smap', index)
              val sub = U.unify(T.S_TY(T.INT), indexTy, pos)
              val smap''' = augmentSmap(smap'', [sub], pos)

              val retTy = case expTy of
                               T.H_TY(T.ARRAY({ty, size})) => T.H_TY(ty)
                             | T.H_TY(T.H_META(hm)) => (T.H_TY(T.H_META(M.newMeta())))
                             | _ => (ErrorMsg.error pos ("cannot index element of non-array type"); T.H_TY(T.H_BOTTOM))
            in
              (A.ArrayAccExp{exp = exp', index = index', pos = pos}, smap''', venv'', retTy)
            end
          | infexp(A.PatternMatchExp({exp, cases, pos})) =
            let
              val (exp', smap', venv', expTy) = inferExp(menv, tenv, venv, smap, exp)

              fun foldCase({match, result, pos}, (cases', smap, venv, ty_opt)) =
                let
                  fun addMatchVars(A.VarExp(sym, pos), venv) = Symbol.enter(venv, sym, T.S_TY(T.S_META(M.newMeta())))
                    | addMatchVars(A.ApplyExp(func, arg, pos), venv) = addMatchVars(arg, venv)
                    | addMatchVars(A.SWRecordExp({fields, pos}), venv) = foldl (fn((sym, exp, pos), venv) => addMatchVars(exp, venv)) venv fields
                    | addMatchVars(A.HWRecordExp({fields, pos}), venv) = foldl (fn((sym, exp, pos), venv) => addMatchVars(exp, venv)) venv fields
                    | addMatchVars(A.ListExp(elems), venv) = foldl (fn((exp, pos), venv) => addMatchVars(exp, venv)) venv elems
                    | addMatchVars(A.ArrayExp(elems), venv) = foldl (fn((exp, pos), venv) => addMatchVars(exp, venv)) venv (Vector.toList(elems))
                    | addMatchVars(A.BinOpExp{left, oper = A.ConsOp, right, pos}, venv) = addMatchVars(right, addMatchVars(left, venv))
                    | addMatchVars(_, venv) = venv (* int, string, bit, real *)

                  val venv_with_match_vars = addMatchVars(match, venv)

                  val (match', smap', venv', matchTy) = inferExp(menv, tenv, venv_with_match_vars, smap, match)
                  val sub = U.unify(expTy, matchTy, pos)
                  val smap'' = augmentSmap(smap', [sub], pos)

                  val (result', smap''', venv'', resultTy) = inferExp(menv, tenv, venv', smap'', result)

                  val sub' = case ty_opt of
                                  SOME(prevTy) => U.unify(prevTy, resultTy, pos)
                                | _ => S.SUB([])
                  val smap'''' = augmentSmap(smap''', [sub'], pos)
                in
                  (cases' @ [{match = match', result = result', pos = pos}], 
                        smap'''', S.substitute(smap'''', venv), case ty_opt of
                                                                SOME(prevTy) => ty_opt
                                                              | _ => SOME(resultTy))
                end

              val (cases', smap', venv', retTy_opt) = foldl foldCase ([], smap, venv, NONE) cases
            in
              (A.PatternMatchExp{exp = exp', cases = cases', pos = pos}, smap', venv', case retTy_opt of
                                                                                            SOME(x) => x
                                                                                          | _ => raise Match (* should never have empty cases*))
            end
          | infexp(A.BitArrayGenExp({size, counter, genfun, pos})) =
            let
              (* process size expression *)
              val (size', smap', venv', sizeTy) = inferExp(menv, tenv, venv, smap, size)
              val sub = U.unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), sizeTy, pos)
              val smap'' = augmentSmap(smap', [sub], pos)

              (* add counter variable to venv *)
              val venv'' = Symbol.enter(venv', counter, T.S_TY(T.INT))

              (* process genfun body with new venv *)
              val (genfun', smap''', venv''', genfunTy) = inferExp(menv, tenv, venv'', smap'', genfun)

              (* final venv *)
              val venv'''' = S.substitute(smap''', venv')

              val elemTy = case genfunTy of
                                T.H_TY(h) => h
                              | T.META(m) => T.H_META(m)
                              | _ => (ErrorMsg.error pos "return type of generation function must be 'hw"; T.H_BOTTOM)
            in
              (A.BitArrayGenExp{size = size', counter = counter, genfun = genfun', pos = pos}, smap''', venv'''', T.H_TY(T.ARRAY{ty = elemTy, size = ref ~1}))
            end
          | infexp(A.BitArrayConvExp({size, value, spec, pos})) =
            case spec of
              "'r" => 
                let
                  (* process size expression *)
                  val (size', smap', venv', sizeTy) = inferExp(menv, tenv, venv, smap, size)
                  val sub = U.unify(T.S_TY(T.S_RECORD([(Symbol.symbol("1"), T.INT), (Symbol.symbol("2"), T.INT)])), sizeTy, pos)
                  val smap'' = augmentSmap(smap', [sub], pos)

                  (* process value expression *)
                  val (value', smap''', venv'', valueTy) = inferExp(menv, tenv, venv', smap', value)
                  val sub' = U.unify(T.S_TY(T.REAL), valueTy, pos)
                  val smap'''' = augmentSmap(smap''', [sub'], pos)
                in
                  (A.BitArrayConvExp{size = size', value = value', spec = spec, pos = pos}, smap'''', venv'', T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}))
                end
            | _ =>
                let
                  (* process size expression *)
                  val (size', smap', venv', sizeTy) = inferExp(menv, tenv, venv, smap, size)
                  val sub = U.unify(T.S_TY(T.INT), sizeTy, pos)
                  val smap'' = augmentSmap(smap', [sub], pos)

                  (* process value expression *)
                  val (value', smap''', venv'', valueTy) = inferExp(menv, tenv, venv', smap', value)
                  val sub' = U.unify(T.S_TY(T.INT), valueTy, pos)
                  val smap'''' = augmentSmap(smap''', [sub'], pos)
                in
                  (A.BitArrayConvExp{size = size', value = value', spec = spec, pos = pos}, smap'''', venv'', T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}))
                end
    in
      let
        val (exp', smap', venv', ty) = infexp(exp)
      in
        (exp', smap', S.substitute(smap', venv'), ty)
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
              
              val (venv', menv') = foldl foldSWParam (venv, menv) params

              (* enter function header with 'a -> 'b type *)
              val funHeaderTy = T.S_TY(T.ARROW(T.S_META(M.newMeta()), T.S_META(M.newMeta())))
              val venvWithHeader = Symbol.enter(venv', name, funHeaderTy)

              (* process body with augmented venv' *)
              val (body', smap', _, bodyTy) = inferExp(menv', tenv, venvWithHeader, smap, body)

              (* unify bodyTy with resultTy *)
              val sub = U.unify(getExplicitType(resultTy, T.S_TY(T.S_BOTTOM)), bodyTy, resultPos)
              val smap'' = augmentSmap(smap', [sub], resultPos)

              fun makeFunTy([], SOME(sty)) = sty
                | makeFunTy(t::ts, NONE) = makeFunTy(ts, SOME(t))
                | makeFunTy(t::ts, SOME(sty)) = makeFunTy(ts, SOME(T.ARROW(t, sty)))
                | makeFunTy(_) = raise Match

              val funTy = makeFunTy(getSWType(bodyTy)::List.rev(map getSWParamTy params), NONE)
              val venv'' = Symbol.enter(venv, name, T.S_TY(funTy))
              val venv''' = S.substitute(smap'', venv'')

              val subbedFunTy = valOf(Symbol.look(venv''', name))
              (* find metas part of substituted function parameters and POLY based on those *)
              fun getParams(T.ARROW(s1, s2)) = (case s2 of
                                                     T.ARROW(s3, s4) => T.ARROW(s1, getParams(s2))
                                                   | _ => s1)
                | getParams(_) = raise Match

              val params' = case subbedFunTy of
                                 T.S_TY(arrowTy as T.ARROW(_)) => getParams(arrowTy)
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
                | flattenMetas(T.S_MU(tyvs, s)) = flattenMetas(s)
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
                | flattenModMetas(T.PARAMETERIZED_MODULE(s, h1, h2)) = flattenMetas(s) @ flattenHWMetas(h1) @ flattenHWMetas(h2)
                | flattenModMetas(_) = []
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
          val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldFunDec {menv = menv, tenv = tenv, venv = venv, smap = smap} fundecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec' = A.FunctionDec(fundecs), smap = smap'}
        end
      | infdec(A.ValDec(valdecs)) =
        let
          fun foldValDec({name, escape, ty = (ty, tyPos), init, pos}, {menv, tenv, venv, smap}) =
            let
              (* add variable in case of BitArrayGenExp since can be defined recursively *)
              val venv = case init of
                              A.BitArrayGenExp (_) => Symbol.enter(venv, name, T.H_TY(T.H_META(M.newMeta())))
                            | _ => venv
              (* infer type of initializing expression *)
              val (init', smap', venv', initTy) = inferExp(menv, tenv, venv, smap, init)

              (* unify initializing expression with value type *)
              val sub = U.unify(S.substituteType(getExplicitType(ty, T.BOTTOM), smap', ref false), initTy, tyPos)

              (* add to substitution mapping *)
              val smap'' = augmentSmap(smap', [sub], tyPos)

              (* add name to variable environment *)
              val venv'' = Symbol.enter(venv', name, initTy)

              (* perform substitution *)
              val venv''' = S.substitute(smap'', venv'')
            in
              {menv = menv, tenv = tenv, venv = venv''', smap = smap''}
            end
          val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldValDec {menv = menv, tenv = tenv, venv = venv, smap = smap} valdecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec' = A.ValDec(valdecs), smap = smap'}
        end
      | infdec(A.TypeDec(tydecs)) =
        let
          fun foldTyDec({name, ty, tyvars, opdef, pos}, {menv, tenv, venv, smap}) =
            let
              (* enter in type environment *)
              val tenv' = Symbol.enter(tenv, name, getExplicitType(ty, T.TOP))

              fun checkOpdef({oper, param_a, param_b, body, pos}) =
                let
                  (* add params into venv *)
                  val venv' = Symbol.enter(venv, param_a, getExplicitType(ty, T.BOTTOM))
                  val venv'' = Symbol.enter(venv', param_b, getExplicitType(ty, T.BOTTOM))
                  val (_, _, _, bodyTy) = inferExp(menv, tenv', venv'', smap, body)
                  val _ = U.unify(T.S_TY(T.INT), bodyTy, pos)
                in
                  ()
                end

              val () = app checkOpdef (case opdef of SOME(x) => x | _ => [])
            in
              {menv = menv, tenv = tenv', venv = venv, smap = smap}
            end
          val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldTyDec {menv = menv, tenv = tenv, venv = venv, smap = smap} tydecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec' = A.TypeDec(tydecs), smap = smap'}
        end
      | infdec(A.SWDatatypeDec(datatydecs)) =
        let
          fun foldDatatyDec({name, tyvars, datacons}, {menv, tenv, venv, smap}) =
            let
              (* at this point, type should already be in SMAP and all datacons have function types to construct *)

              (* add all datacons to venv *)
              fun foldDatacon({datacon, ty, pos}, venv) =
                let
                  val venv' = Symbol.enter(venv, datacon, getExplicitType(ty, T.S_TY(T.S_BOTTOM)))
                in
                  venv'
                end

              val venv' = foldl foldDatacon venv datacons
            in
              {menv = menv, tenv = tenv, venv = venv', smap = smap}
            end
          val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldDatatyDec {menv = menv, tenv = tenv, venv = venv, smap = smap} datatydecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec' = A.SWDatatypeDec(datatydecs), smap = smap'}
        end
      | infdec(A.HWDatatypeDec(datatydecs)) =
        let
          fun foldDatatyDec({name, tyvars, datacons}, {menv, tenv, venv, smap}) =
            let
              (* at this point, type should already be in SMAP and all datacons have function types to construct *)

              (* add all datacons to venv *)
              fun foldDatacon({datacon, ty, pos}, venv) =
                let
                  val venv' = Symbol.enter(venv, datacon, getExplicitType(ty, T.H_TY(T.H_BOTTOM)))
                in
                  venv'
                end

              val venv' = foldl foldDatacon venv datacons
            in
              {menv = menv, tenv = tenv, venv = venv', smap = smap}
            end
            val {menv = menv', tenv = tenv', venv = venv', smap = smap'} = foldl foldDatatyDec {menv = menv, tenv = tenv, venv = venv, smap = smap} datatydecs
        in
            {menv = menv', tenv = tenv', venv = venv', dec' = A.HWDatatypeDec(datatydecs), smap = smap'}
        end
      | infdec(A.ModuleDec(moddecs)) =
        let
          fun foldModDec({name, arg, sw_arg, result = (resultTy, resultPos), body, pos}, {menv, tenv, venv, decs, smap}) =
            let
              
              val (venv1, menv1) = foldl foldSWParam (venv, menv) (case sw_arg of SOME(a) => [a] | _ => [])
              val (venv', menv') = foldl foldHWParam (venv1, menv1) [arg]

              (* process body *)
              val (body', smap', _, bodyTy) = inferExp(menv', tenv, venv', smap, body)

              (* unify bodyTy with resultTy *)
              val sub = U.unify(getExplicitType(resultTy, T.H_TY(T.H_BOTTOM)), bodyTy, resultPos)
              val smap'' = augmentSmap(smap', [sub], resultPos)

              val modTy = case sw_arg of 
                               SOME(a) => T.PARAMETERIZED_MODULE(getSWParamTy a, getHWParamTy arg, getHWType(bodyTy))
                             | NONE => T.MODULE(getHWParamTy arg, getHWType(bodyTy))
              val venv'' = Symbol.enter(venv, name, T.M_TY(modTy))
              val venv''' = S.substitute(smap'', venv'')

              val subbedModTy = valOf(Symbol.look(venv''', name))

              (* find metas part of substituted module parameters and POLY based on those *)
              val (param', swParam) = case subbedModTy of
                                           T.M_TY(T.MODULE(pTy, _)) => (pTy, NONE)
                                         | T.M_TY(T.PARAMETERIZED_MODULE(swPty, pTy, _)) => (pTy, SOME(swPty))
                                         | _ => (ErrorMsg.error pos ("unbound module: " ^ Symbol.name(name)); (T.H_BOTTOM, NONE))

              fun flattenSWMetas(T.S_META(sm)) = (case Symbol.look(menv, sm) of
                                                    SOME(_) => []
                                                  | _ => [sm] (* only add if not in menv *))
                | flattenSWMetas(T.S_RECORD(fs)) = List.rev(foldl (fn((tyv, sty), metas)  => flattenSWMetas(sty) @ metas) [] fs)
                | flattenSWMetas(T.ARROW(s1, s2)) = flattenSWMetas(s1) @ flattenSWMetas(s2)
                | flattenSWMetas(T.LIST(s)) = flattenSWMetas(s)
                | flattenSWMetas(T.SW_H(h)) = flattenHWMetas(h)
                | flattenSWMetas(T.SW_M(m)) = flattenModMetas(m)
                | flattenSWMetas(T.REF(s)) = flattenSWMetas(s)
                | flattenSWMetas(T.S_DATATYPE(tys, u)) = List.rev(foldl (fn((tyv, sty_opt), metas)  => case sty_opt of SOME(s) => flattenSWMetas(s) @ metas | NONE => metas) [] tys)
                | flattenSWMetas(T.S_MU(tyvs, s)) = flattenSWMetas(s)
                | flattenSWMetas(_) = []
              and flattenHWMetas(T.H_META(hm)) = (case Symbol.look(menv, hm) of
                                                      SOME(_) => []
                                                    | _ => [hm] (* only add if not in menv *))
                | flattenHWMetas(T.ARRAY{ty, size}) = flattenHWMetas(ty)
                | flattenHWMetas(T.TEMPORAL{ty, time}) = flattenHWMetas(ty)
                | flattenHWMetas(T.H_RECORD(fs)) = List.rev(foldl (fn((tyv, hty), metas)  => flattenHWMetas(hty) @ metas) [] fs)
                | flattenHWMetas(T.H_DATATYPE(tys, u)) = List.rev(foldl (fn((tyv, hty_opt), metas)  => case hty_opt of SOME(h) => flattenHWMetas(h) @ metas | NONE => metas) [] tys)
                | flattenHWMetas(_) = []
              and flattenModMetas(T.MODULE(h1, h2)) = flattenHWMetas(h1) @ flattenHWMetas(h2)
                | flattenModMetas(T.PARAMETERIZED_MODULE(s, h1, h2)) = flattenSWMetas(s) @ flattenHWMetas(h1) @ flattenHWMetas(h2)
                | flattenModMetas(_) = []

              val paramMetas = (flattenHWMetas param') @ (case swParam of SOME(a) => flattenSWMetas a | _ => [])

              val modTy' = case paramMetas of
                                [] => subbedModTy
                              | _ => T.M_TY(T.M_POLY(paramMetas, getModType(subbedModTy)))

              fun substituteArgTypes(arg, NONE) = arg
                | substituteArgTypes(A.SingleParam{name, ty, escape, pos}, SOME(hty)) = A.SingleParam{name = name, ty = A.ExplicitTy(T.H_TY(hty)), escape = escape, pos = pos}
                | substituteArgTypes(A.TupleParams fs1, SOME(T.H_RECORD(fs2))) =
                  A.TupleParams (map (fn ({name, ty, escape, pos}, (sym, hty)) => {name = name, ty = A.ExplicitTy(T.H_TY(hty)), escape = escape, pos = pos}) (ListPair.zipEq(fs1, fs2)))
                | substituteArgTypes(A.RecordParams fs1, SOME(T.H_RECORD(fs2))) =
                  A.RecordParams (map (fn ({name, ty, escape, pos}, (sym, hty)) => {name = name, ty = A.ExplicitTy(T.H_TY(hty)), escape = escape, pos = pos}) (ListPair.zipEq(fs1, fs2)))
                | substituteArgTypes(_) = raise Match

              val arg' = substituteArgTypes(arg, case getModType(subbedModTy) of
                                                      T.MODULE(h1, _) => SOME(h1)
                                                    | T.PARAMETERIZED_MODULE(_, h1, _) => SOME(h1)
                                                    | _ => NONE)

              val venv'''' = Symbol.enter(venv''', name, modTy')
            in
              {menv = menv,
               tenv = tenv,
               venv = venv'''',
               decs = decs @ [{name = name, arg = arg', sw_arg = sw_arg, result = (resultTy, resultPos), body = body, pos = pos}],
               smap = smap''}
            end
          val {menv = menv', tenv = tenv', venv = venv', decs = decs', smap = smap'} = foldl foldModDec {menv = menv, tenv = tenv, venv = venv, decs = [], smap = smap} moddecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec' = A.ModuleDec(decs'), smap = smap'}
        end
    in
      infdec(dec)
    end

end
