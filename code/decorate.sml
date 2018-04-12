signature DECORATE =
sig

  val decorateProg :                       Absyn.exp -> Env.menv * Absyn.exp  (* returns explicit poly tree *)
  val decorateExp  : Env.menv * Env.tenv * Absyn.exp -> Env.menv * Absyn.exp  (* returns expression with types made explicit *)
  val decorateTy   : Env.menv * Env.tenv * Absyn.ty  -> Types.ty              (* returns explicit type *)
  val decorateDec  : Env.menv * Env.tenv * Absyn.dec -> { menv: Env.menv,     (* returns augmented environments and *)
                                                          tenv: Env.tenv,     (* Absyn.dec with explicit types      *)
                                                          dec: Absyn.dec }

end

structure Decorate : DECORATE =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env
  structure S = Substitute
  structure M = Meta

  (* attach information/context to TOP in order to make warnings/errors more clearn
  potentially number warnings and refer to others based on whether error is propagated *)

  fun getSWType(T.S_TY(sty)) = sty
    | getSWType(T.META(m)) = T.S_META(m)
    | getSWType(_) = T.S_BOTTOM

  fun getHWType(T.H_TY(hty)) = hty
    | getHWType(T.META(m)) = T.H_META(m)
    | getHWType(_) = T.H_BOTTOM

  fun extractMetas(ty) =
    let
      fun extractSWMetas(T.S_RECORD(fs)) = foldl (fn((_, sty), metas) => extractSWMetas(sty) @ metas) [] fs
        | extractSWMetas(T.ARROW(s1, s2)) = extractSWMetas(s1) @ extractSWMetas(s2)
        | extractSWMetas(T.LIST(s)) = extractSWMetas(s)
        | extractSWMetas(T.SW_H(h)) = extractHWMetas(h)
        | extractSWMetas(T.SW_M(m)) = extractMDMetas(m)
        | extractSWMetas(T.REF(s)) = extractSWMetas(s)
        | extractSWMetas(T.S_DATATYPE(xs, u)) = foldl (fn((_, sty_opt), metas) => (case sty_opt of SOME(sty) => extractSWMetas(sty) | _ => []) @ metas) [] xs
        | extractSWMetas(T.S_POLY(tyvars, s)) = extractSWMetas(s)
        | extractSWMetas(T.S_MU(tyvars, s)) = extractSWMetas(s)
        | extractSWMetas(T.S_META(sm)) = [sm]
        | extractSWMetas(T.INT) = []
        | extractSWMetas(T.STRING) = []
        | extractSWMetas(T.REAL) = []
        | extractSWMetas(T.S_TOP) = []
        | extractSWMetas(T.S_BOTTOM) = []
      and extractHWMetas(T.H_META(hm)) = [hm]
        | extractHWMetas(T.BIT) = []
        | extractHWMetas(T.ARRAY{ty, size}) = extractHWMetas(ty)
        | extractHWMetas(T.H_RECORD(xs)) = foldl (fn((_, hty), metas) => extractHWMetas(hty) @ metas) [] xs
        | extractHWMetas(T.TEMPORAL{ty, time}) = extractHWMetas(ty)
        | extractHWMetas(T.H_DATATYPE(xs, u)) = foldl (fn((_, hty_opt), metas) => (case hty_opt of SOME(hty) => extractHWMetas(hty) | _ => []) @ metas) [] xs
        | extractHWMetas(T.H_POLY(tyvars, h)) = extractHWMetas(h)
        | extractHWMetas(T.H_TOP) = []
        | extractHWMetas(T.H_BOTTOM) = []
      and extractMDMetas(T.MODULE(h1, h2)) = extractHWMetas(h1) @ extractHWMetas(h2)
        | extractMDMetas(T.M_POLY(tyvars, m)) = extractMDMetas(m)
        | extractMDMetas(T.M_BOTTOM) = []
    in
      case ty of
           T.S_TY(s) => extractSWMetas(s)
         | T.H_TY(h) => extractHWMetas(h)
         | T.M_TY(m) => extractMDMetas(m)
         | _ => []
    end

  fun decorateProg(e) = decorateExp(E.base_menv, E.base_tenv, e)

  and decorateExp(menv, tenv, exp) =
    let fun decorexp(A.StructsSigsExp(structsigs)) = (menv, A.StructsSigsExp(structsigs)) (* TODO *)
    (* struct/sig environment in same env with StructEntry and SigEntry *)
            (* let
              fun processStructSig(A.StructExp({name, signat, decs, pos}), {structsigs, menv, tenv, venv}) =
                let
                  val (s, pos') = signat
                  val signat' = processStructSig(s)
                  val structsig = A.StructExp({name = name, signat = (signat', pos') pos = pos})
                in
                  {structsigs = structsig::structsigs, menv = menv', tenv = tenv', venv = venv'}
                end
                | processStructSig(A.SigExp({name, defs}), {structsigs, menv, tenv, venv})
                | processStructSig(A.NamedSigExp(sym), {structsigs, menv, tenv, venv}) = {structsigs = A.NamedSigExp(sym)::structsigs, menv = menv, tenv = tenv, venv = venv} (* NO-OP *)
                | processStructSig(A.AnonSigExp(defs), {structsigs, menv, tenv, venv})
            in
              foldl processStructSig {structsigs = [], menv = menv, tenv = tenv, venv = venv} structsigs
            end *)
          | decorexp(A.VarExp(sym, pos)) = (menv, A.VarExp(sym, pos)) (* NO-OP *)
          | decorexp(A.IntExp(num, pos)) = (menv, A.IntExp(num, pos)) (* NO-OP *)
          | decorexp(A.StringExp(str, pos)) = (menv, A.StringExp(str, pos)) (* NO-OP *)
          | decorexp(A.RealExp(num, pos)) = (menv, A.RealExp(num, pos)) (* NO-OP *)
          | decorexp(A.BitExp(bit, pos)) = (menv, A.BitExp(bit, pos)) (* NO-OP *)
          | decorexp(A.ApplyExp(e1, e2, pos)) =
            let
              val (menv', e1') = decorateExp(menv, tenv, e1)
              val (menv'', e2') = decorateExp(menv', tenv, e2)
            in
              (menv'', A.ApplyExp(e1', e2', pos))
            end
          | decorexp(A.BinOpExp({left, oper, right, pos})) =
            let
              val (menv', left') = decorateExp(menv, tenv, left)
              val (menv'', right') = decorateExp(menv', tenv, right)
            in
              (menv'', A.BinOpExp({left = left',
                                   oper = oper,
                                   right = right',
                                   pos = pos }))
            end
          | decorexp(A.UnOpExp({exp, oper, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.UnOpExp({ exp = exp',
                                  oper = oper,
                                  pos = pos }))
            end
          | decorexp(A.LetExp({decs, body, pos})) =
            let
              fun processDecs(dec, {decs, menv, tenv}) =
                let
                  val {menv = menv', tenv = tenv', dec = dec'} = decorateDec(menv, tenv, dec)
                in
                  {decs = dec'::decs, menv = menv', tenv = tenv'}
                end
              val {decs = decs',
                   menv = menv',
                   tenv = tenv'} = foldl processDecs {decs = [], menv = menv, tenv = tenv} decs
              val (menv'', body') = decorateExp(menv', tenv', body)
            in
              (menv'', A.LetExp({decs = List.rev(decs'),
                                 body = body',
                                 pos = pos }))
            end
          | decorexp(A.AssignExp({lhs, rhs, pos})) =
            let
              val (menv', lhs') = decorateExp(menv, tenv, lhs)
              val (menv'', rhs') = decorateExp(menv', tenv, rhs)
            in
              (menv'', A.AssignExp({ lhs = lhs',
                                     rhs = rhs',
                                     pos = pos }))
            end
          | decorexp(A.SeqExp(exps)) =
            let
              fun foldSeq((e, p), {menv, exps}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', exps = (e', p)::exps}
                end
              val {menv = menv', exps = exps'} = foldl foldSeq {menv = menv, exps = []} exps
            in
              (menv', A.SeqExp(List.rev(exps')))
            end
          | decorexp(A.IfExp({test, then', else', pos})) =
            let
              val (menv', test') = decorateExp(menv, tenv, test)
              val (menv'', then'') = decorateExp(menv', tenv, then')
              val ret = Option.map (fn(x) => decorateExp(menv'', tenv, x)) else'
            in
              case ret of
                   SOME(menv''', else'') => (menv''', A.IfExp({ test = test', then' = then'', else' = SOME(else''), pos = pos}))
                 | NONE => (menv'', A.IfExp({ test = test', then' = then'', else' = NONE, pos = pos}))
            end
          | decorexp(A.ListExp(exps)) =
            let
              fun foldList((e, p), {menv, exps}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', exps = (e', p)::exps}
                end
              val {menv = menv', exps = exps'} = foldl foldList {menv = menv, exps = []} exps
            in
              (menv', A.ListExp(List.rev(exps')))
            end
          | decorexp(A.ArrayExp(exps)) =
            let
              fun vectorToList(l) = Vector.foldr (fn(a, b) => a::b) [] l
              fun foldArray((e, p), {menv, exps}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', exps = (e', p)::exps}
                end
              val {menv = menv', exps = exps'} = foldl foldArray {menv = menv, exps = []} (vectorToList(exps))
            in
              (menv', A.ArrayExp(Vector.fromList(List.rev(exps'))))
            end
          | decorexp(A.RefExp(exp, pos)) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.RefExp(exp', pos))
            end
          | decorexp(A.SWRecordExp({fields, pos})) =
            let
              fun foldField((s, e, p), {menv, fields}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', fields = (s, e', p)::fields}
                end
              val {menv = menv', fields = fields'} = foldl foldField {menv = menv, fields = []} fields
            in
              (menv', A.SWRecordExp({fields = List.rev(fields'), pos = pos}))
            end
          | decorexp(A.HWRecordExp({fields, pos})) =
            let
              fun foldField((s, e, p), {menv, fields}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', fields = (s, e', p)::fields}
                end
              val {menv = menv', fields = fields'} = foldl foldField {menv = menv, fields = []} fields
            in
              (menv', A.HWRecordExp({fields = List.rev(fields'), pos = pos}))
            end
          | decorexp(A.SWExp(exp, pos)) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.SWExp(exp', pos))
            end
          | decorexp(A.UnSWExp(exp, pos)) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.UnSWExp(exp', pos))
            end
          | decorexp(A.WithExp({exp, fields, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
              fun foldField((s, e, p), {menv, fields}) =
                let
                  val (menv', e') = decorateExp(menv, tenv, e)
                in
                  {menv = menv', fields = (s, e', p)::fields}
                end
              val {menv = menv'', fields = fields'} = foldl foldField {menv = menv', fields = []} fields
            in
              (menv'', A.WithExp({ exp = exp',
                                   fields = List.rev(fields'),
                                   pos = pos }))
            end
          | decorexp(A.DerefExp({exp, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.DerefExp({ exp = exp',
                                   pos = pos }))
            end
          | decorexp(A.StructAccExp({name, field, pos})) = (menv, A.StructAccExp({name = name, field = field, pos = pos})) (* NO-OP *)
          | decorexp(A.RecordAccExp({exp, field, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
            in
              (menv', A.RecordAccExp({ exp = exp',
                                       field = field,
                                       pos = pos }))
            end
          | decorexp(A.ArrayAccExp({exp, index, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
              val (menv'', index') = decorateExp(menv', tenv, index)
            in
              (menv'', A.ArrayAccExp({ exp = exp',
                                       index = index',
                                       pos = pos }))
            end
          | decorexp(A.PatternMatchExp({exp, cases, pos})) =
            let
              val (menv', exp') = decorateExp(menv, tenv, exp)
              fun foldField({match, result, pos}, {menv, cases}) =
                let
                  val (menv', match') = decorateExp(menv, tenv, match)
                  val (menv'', result') = decorateExp(menv', tenv, result)
                  val c' = {match = match', result = result', pos = pos}
                in
                  {menv = menv'', cases = c'::cases}
                end
              val {menv = menv'', cases = cases'} = foldl foldField {menv = menv', cases = []} cases
            in
              (menv'', A.PatternMatchExp({exp = exp', cases = List.rev(cases'), pos = pos}))
            end
          | decorexp(A.BitArrayGenExp({size, counter, genfun, pos})) =
            let
              val (menv', size') = decorateExp(menv, tenv, size)
              val (menv'', genfun') = decorateExp(menv', tenv, genfun)
            in
              (menv'', A.BitArrayGenExp({ size = size',
                                       counter = counter,
                                       genfun = genfun',
                                       pos = pos }))
            end
          | decorexp(A.BitArrayConvExp({size, value, spec, pos})) =
            let
              val (menv', size') = decorateExp(menv, tenv, size)
              val (menv'', value') = decorateExp(menv', tenv, value)
            in
              (menv'', A.BitArrayConvExp({ size = size',
                                       value = value',
                                       spec = spec,
                                       pos = pos }))
            end
    in
      decorexp(exp)
    end

  and decorateTy(menv, tenv, ty) =
    let fun getSWTy(t) = (case t of
                               T.S_TY(x) => x
                             | T.META(x) => T.S_META(x)
                             | _ => T.S_TOP)  (* NOTE: error? *)
        fun getHWTy(t) = (case t of
                               T.H_TY(x) => x
                             | T.META(x) => T.H_META(x)
                             | _ => T.H_TOP)  (* NOTE: error? *)
        fun substitute(tyvars, tyargs, ty) =
          let
            fun makeMap((tyvar, tyarg), varmap) = Symbol.enter(varmap, tyvar, tyarg)
            val varmap = foldl makeMap Symbol.empty (ListPair.zipEq(tyvars, tyargs))
          in
            S.substituteType(ty, varmap, ref false)
          end
        fun unpoly(tyvars, tyargs, ty, sym, pos) =
          let
            val defaultTy = case ty of T.S_TY(_) => T.S_TY(T.S_TOP) | T.H_TY(_) => T.H_TY(T.H_TOP) | _ => T.TOP
          in
            if length(tyvars) <> length(tyargs)
            then (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), length(tyargs), length(tyvars)); defaultTy)
            else substitute(tyvars, tyargs, ty)
          end
        fun decoty(A.NameTy(sym, pos)) = (case Symbol.look(tenv, sym) of
                                               SOME(t) => (case t of
                                                                T.S_TY(T.S_POLY(tyvars, sty)) => (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), 0, length(tyvars)); T.S_TY(T.S_TOP))
                                                              | T.H_TY(T.H_POLY(tyvars, hty)) => (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), 0, length(tyvars)); T.H_TY(T.H_TOP))
                                                              | _ => t)
                                             | NONE => (ErrorMsg.error pos ("unbound type: " ^ Symbol.name(sym)); T.TOP))
          | decoty(A.ParameterizedTy(sym, typarams, pos)) =
            let
              val mainTy = (case Symbol.look(tenv, sym) of
                                 SOME(t) => (case t of
                                                  T.S_TY(T.S_POLY(tyvars, sty)) => t
                                                | T.H_TY(T.H_POLY(tyvars, hty)) => t
                                                | T.S_TY(T.S_META(sm)) => (case Symbol.look(menv, sm) of
                                                                                SOME(t') => t'
                                                                              | _ => (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), length(typarams), 0); T.S_TY(T.S_TOP)))
                                                | T.H_TY(T.H_META(hm)) => (case Symbol.look(menv, hm) of
                                                                                SOME(t') => t'
                                                                              | _ => (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), length(typarams), 0); T.H_TY(T.H_TOP)))
                                                | _ => (ErrorMsg.typeNumArgsError(pos, Symbol.name(sym), length(typarams), 0); T.TOP))
                               | _ => (ErrorMsg.error pos ("unbound type: " ^ Symbol.name(sym)); T.TOP))
              val mainTy' = case mainTy of
                                 T.S_TY(T.S_META(sm)) => (case Symbol.look(menv, sm) of
                                                               SOME(otherTy) => otherTy
                                                             | _ => mainTy)
                               | T.H_TY(T.H_META(hm)) => (case Symbol.look(menv, hm) of
                                                               SOME(otherTy) => otherTy
                                                             | _ => mainTy)
                               | _ => mainTy
            in
              case mainTy' of
                   T.S_TY(T.S_POLY(tyvars, sty)) => unpoly(tyvars, map decoty typarams, T.S_TY(sty), sym, pos)
                 | T.H_TY(T.H_POLY(tyvars, hty)) => unpoly(tyvars, map decoty typarams, T.H_TY(hty), sym, pos)
                 | _ => mainTy' (* NOTE: error? *)
            end
          | decoty(A.TyVar(sym, pos)) = (case Symbol.look(menv, sym) of
                                              SOME(t) => t
                                            | NONE => (ErrorMsg.error pos ("unbound type variable: " ^ Symbol.name(sym)); T.TOP))
          | decoty(A.SWRecordTy(fields, pos)) =
            let
              fun mapFields({name, ty, escape, pos}) = (name, getSWTy(decoty(ty)))
            in
              T.S_TY(T.S_RECORD(map mapFields fields))
            end
          | decoty(A.HWRecordTy(fields, pos)) =
            let
              fun mapFields({name, ty, escape, pos}) = (name, getHWTy(decoty(ty)))
            in
              T.H_TY(T.H_RECORD(map mapFields fields))
            end
          | decoty(A.ArrayTy(ty, size, pos)) =
            let
              val realTy1 = getHWTy(decoty(ty))
            in
              T.H_TY(T.ARRAY({ty = realTy1, size = ref ~1}))
            end
          | decoty(A.ListTy(ty, pos)) =
            let
              val realTy = getSWTy(decoty(ty))
            in
              T.S_TY(T.LIST(realTy))
            end
          | decoty(A.TemporalTy(ty, time, pos)) =
            let
              val realTy1 = getHWTy(decoty(ty))
            in
              T.H_TY(T.TEMPORAL({ty = realTy1, time = ref ~1}))
            end
          | decoty(A.RefTy(ty, pos)) =
            let
              val realTy = getSWTy(decoty(ty))
            in
              T.S_TY(T.REF(realTy))
            end
          | decoty(A.SWTy(ty, pos)) =
            let
              val exTy = decoty(ty)
              val retTy = (case exTy of
                                T.H_TY(h) => T.S_TY(T.SW_H(h))
                              | T.M_TY(m) => T.S_TY(T.SW_M(m))
                              | T.META(x) => T.S_TY(T.SW_H(T.H_META(x)))
                              | _ => T.S_TY(T.S_TOP))
              val () = print(T.toString(exTy) ^ "\n")
            in
              retTy
            end
          | decoty(A.FunTy(ty1, ty2, pos)) =
            let
              val argTy = getSWTy(decoty(ty1))
              val resTy = getSWTy(decoty(ty2))
              (* if either errors, return BOTTOM type instead of ARROW *)
              (* tell them error in decorate phase and won't go on*)
              (* in next phase, don't error if it is applied or passed (BOTTOM is subtype of everything) *)
            in
              case argTy of
                   T.S_TOP => T.BOTTOM
                 | _ => (case resTy of
                              T.S_TOP => T.BOTTOM
                            | _ => T.S_TY(T.ARROW(argTy, resTy)))
            end
          | decoty(A.PlaceholderTy(u)) = T.META(M.newMeta())
          | decoty(A.NoTy) = T.EMPTY
          | decoty(A.ExplicitTy(t)) = t
    in
      decoty(ty)
    end

  and decorateDec(menv, tenv, dec) =
    let
      (* TODO: mutually recursive *)
      fun decodec(A.FunctionDec(fundecs)) =
        let
          (* NOTE: tenv is never altered *)
          fun foldFunDec({name, params, result = (ty, typos), body, pos}, {menv, fdecs}) =
            let
              fun mapField({name, ty, escape, pos}) =
                let
                  val ty' = decorateTy(menv, tenv, ty)
                  val ty'' = case ty' of
                                  T.S_TY(x) => ty'
                                | T.META(x) => T.S_TY(T.S_META(x))
                                | _ => T.S_TY(T.S_BOTTOM)
                in
                  {name = name, ty = A.ExplicitTy(ty''), escape = escape, pos = pos}
                end

              fun mapParam(A.NoParam) = A.NoParam
                | mapParam(A.SingleParam(f)) = A.SingleParam(mapField(f))
                | mapParam(A.TupleParams(fs)) = A.TupleParams(map mapField fs)
                | mapParam(A.RecordParams(fs)) = A.RecordParams(map mapField fs)

              val params' = map mapParam params

              val resultTy = decorateTy(menv, tenv, ty)
              val resultTy' = case resultTy of
                                   T.S_TY(x) => resultTy
                                 | T.META(x) => T.S_TY(T.S_META(x))
                                 | _ => T.S_TY(T.S_BOTTOM)

              val (menv', body') = decorateExp(menv, tenv, body)
              val fdec' = {name = name, params = params', result = (A.ExplicitTy(resultTy'), typos), body = body', pos = pos}
            in
              {menv = menv', fdecs = fdec'::fdecs}
            end

          val {menv = menv', fdecs = fdecs'} = foldl foldFunDec {menv = menv, fdecs = []} fundecs
        in
          {menv = menv', tenv = tenv, dec = A.FunctionDec(List.rev(fdecs'))}
        end
        | decodec(A.TypeDec(tydecs)) =
          let
            (* menv is only altered in context of type body *)
            (* tenv is altered and passed on to future decs *)
            fun processTyDec({name, ty, tyvars, opdef, pos}, {menv, tenv, tydecs}) =
              let
                fun foldMenv(tyv, (menv, metamap)) =
                  let
                    val newMeta = M.newMeta()
                  in
                    (Symbol.enter(menv, tyv, T.META(newMeta)),
                     Symbol.enter(metamap, tyv, newMeta))
                  end
                val (menv', metamap) = case tyvars of SOME(tyvs) => foldl foldMenv (menv, Symbol.empty) tyvs
                                                    | _ => (menv, Symbol.empty)
                val realTy = case tyvars of
                                  SOME(tyvs) => (case decorateTy(menv', tenv, ty) of
                                                      T.S_TY(sty) => T.S_TY(T.S_POLY(map (fn(tyv) => valOf(Symbol.look(metamap, tyv))) tyvs, sty))
                                                    | T.H_TY(hty) => T.H_TY(T.H_POLY(map (fn(tyv) => valOf(Symbol.look(metamap, tyv))) tyvs, hty))
                                                    | x => x)
                                | _ => decorateTy(menv', tenv, ty)
                val tenv' = Symbol.enter(tenv, name, realTy)
                fun foldDef({oper, param_a, param_b, body, pos}, {menv, defs}) =
                  let
                    val (menv', body') = decorateExp(menv, tenv, body)
                    val def' = {oper = oper, param_a = param_a, param_b = param_b, body = body', pos = pos}
                  in
                    {menv = menv', defs = def'::defs}
                  end
                val {menv = menv'', defs = defs'} = case opdef of
                                                         SOME(defs) => (foldl foldDef {menv = menv, defs = []} defs)
                                                       | NONE => {menv = menv, defs = []}
                val opdef' = case opdef of
                                  SOME(_) => SOME(defs')
                                | NONE => NONE
                val tydec' = {name = name, ty = A.ExplicitTy(realTy), tyvars = tyvars, opdef = opdef', pos = pos}
              in
                 {menv = menv'',
                  tenv = tenv',
                  tydecs = tydec'::tydecs}
              end
            val {menv = menv', tenv = tenv', tydecs = tydecs'} = foldl processTyDec {menv = menv, tenv = tenv, tydecs = []} tydecs
          in
            {menv = menv', tenv = tenv', dec = A.TypeDec(List.rev(tydecs'))}
          end
        (* moddec: {name: symbol, arg: param, result: ty * pos, body: exp, pos: pos} *)
        | decodec(A.ModuleDec(moddecs)) =
        let
          (* NOTE: tenv is never altered *)
          fun foldModDec({name, arg, result = (ty, typos), body, pos}, {menv, mdecs}) =
            let
              fun mapField({name, ty, escape, pos}) = {name = name, ty = A.ExplicitTy(decorateTy(menv, tenv, ty)), escape = escape, pos = pos}

              fun mapArg(A.NoParam) = A.NoParam
                | mapArg(A.SingleParam(f)) = A.SingleParam(mapField(f))
                | mapArg(A.TupleParams(fs)) = A.TupleParams(map mapField fs)
                | mapArg(A.RecordParams(fs)) = A.RecordParams(map mapField fs)

              val arg' = mapArg arg

              val resultTy = decorateTy(menv, tenv, ty)
              val resultTy' = case resultTy of
                                   T.H_TY(x) => resultTy
                                 | T.META(x) => T.H_TY(T.H_META(x))
                                 | _ => T.H_TY(T.H_BOTTOM)

              val (menv', body') = decorateExp(menv, tenv, body)
              val mdec' = {name = name, arg = arg', result = (A.ExplicitTy(resultTy'), typos), body = body', pos = pos}
            in
              {menv = menv', mdecs = mdec'::mdecs}
            end

          val {menv = menv', mdecs = mdecs'} = foldl foldModDec {menv = menv, mdecs = []} moddecs
        in
          {menv = menv, tenv = tenv, dec = A.ModuleDec(List.rev(mdecs'))}
        end
        (* dataty: {name: symbol, tyvar: symbol option, datacons: datacon list} *)
        (* datacon: {datacon: symbol, ty: ty, pos: pos} *)
        | decodec(A.SWDatatypeDec(datatydecs)) =
        (*
          datatype ilist = EMPTY | LIST of int * ilist

          first in tenv, do ilist -> m42
          then after processing tycons, do m42 -> DATATYPE(...)
        *)
          let
            (* menv is altered if tyvar and passed only to body of dec *)
            (* tenv is altered to point to temp meta *)
            (* menv is altered to point from temp meta to real type *)
            (* both tenv and menv are passed on *)
            fun processDatatype({name, tyvars, datacons}, {menv, tenv, datatydecs}) =
              let
                fun foldMenv(tyvar, (menv, metamap)) =
                  let
                    val newmeta = M.newMeta()
                  in
                    (Symbol.enter(menv, tyvar, T.META(newmeta)),
                     Symbol.enter(metamap, tyvar, newmeta))
                  end
                (* if tyvar, add to menv *)
                val (menv', metamap) = case tyvars of
                                            SOME(tyvs) => foldl foldMenv (menv, Symbol.empty) tyvs
                                          | _ => (menv, Symbol.empty)
                (* add datatype as META in tenv *)
                val tempMeta = M.newMeta()
                val tenv' = Symbol.enter(tenv, name, T.S_TY(T.S_META(tempMeta)))
                (* map datacons to explicit types *)
                fun mapDatacon({datacon, ty, pos}) =
                  let
                    val dataconTy = decorateTy(menv', tenv', ty)
                    val dataconTyvars = List.rev(extractMetas(dataconTy))
                    val argTy = case dataconTyvars of
                                      [] => dataconTy
                                    | _ => T.S_TY(T.S_POLY(dataconTyvars, getSWType(dataconTy)))
                    val retTy = T.S_META(tempMeta)
                    val realTy = case argTy of
                                      T.S_TY(s) => T.S_TY(T.ARROW(s, retTy))
                                    | T.EMPTY => T.S_TY(retTy)
                                    | _ => (T.S_TY(T.S_TOP))
                  in
                    {datacon = datacon, ty = A.ExplicitTy(realTy), pos = pos}
                  end
                val datacons' = map mapDatacon datacons
                val datatydec' = {name = name, tyvars = tyvars, datacons = datacons'}
                (* map from meta to computed datatype type *)
                fun mapDataconForType({datacon, ty = A.ExplicitTy(t), pos}) = (datacon, (case t of
                                                                                              T.S_TY(s) => SOME(s)
                                                                                            | _ => raise Match))
                  | mapDataconForType(_) = raise Match

                val sty = T.S_MU([tempMeta], T.S_DATATYPE(map mapDataconForType datacons', ref ()))
                val retTy = case tyvars of
                                 SOME(tyvs) => T.S_TY(T.S_POLY(map (fn(tyv) => valOf(Symbol.look(metamap, tyv))) tyvs, sty))
                               | _ => T.S_TY(sty)
                val menv'' = Symbol.enter(menv, tempMeta, retTy)
              in
                {menv = menv'', tenv = tenv', datatydecs = datatydec'::datatydecs}
              end
            val {menv = menv', tenv = tenv', datatydecs = datatydecs'} = foldl processDatatype {menv = menv, tenv = tenv, datatydecs = []} datatydecs
          in
            (* other declarations should see the new type and meta environments *)
            {menv = menv', tenv = tenv', dec = A.SWDatatypeDec(List.rev(datatydecs'))}
          end
        | decodec(A.HWDatatypeDec(datatydecs)) =
        (*
          datatype ilist = EMPTY | LIST of int * ilist

          first in tenv, do ilist -> m42
          then after processing tycons, do m42 -> DATATYPE(...)
        *)
          let
            (* menv is altered if tyvar and passed only to body of dec *)
            (* tenv is altered to point to temp meta *)
            (* menv is altered to point from temp meta to real type *)
            (* both tenv and menv are passed on *)
            fun processDatatype({name, tyvars, datacons}, {menv, tenv, datatydecs}) =
              let
                fun foldMenv(tyvar, (menv, metamap)) =
                  let
                    val newmeta = M.newMeta()
                  in
                    (Symbol.enter(menv, tyvar, T.META(newmeta)),
                     Symbol.enter(metamap, tyvar, newmeta))
                  end
                (* if tyvar, add to menv *)
                val (menv', metamap) = case tyvars of
                                            SOME(tyvs) => foldl foldMenv (menv, Symbol.empty) tyvs
                                          | _ => (menv, Symbol.empty)
                (* add datatype as META in tenv *)
                val tempMeta = M.newMeta()
                val tenv' = Symbol.enter(tenv, name, T.H_TY(T.H_META(tempMeta)))
                (* map datacons to explicit types *)
                fun mapDatacon({datacon, ty, pos}) =
                  let
                    val dataconTy = decorateTy(menv', tenv', ty)
                    val dataconTyvars = List.rev(extractMetas(dataconTy))
                    val argTy = case dataconTyvars of
                                      [] => dataconTy
                                    | _ => T.H_TY(T.H_POLY(dataconTyvars, getHWType(dataconTy)))
                    val retTy = T.H_META(tempMeta)
                    val realTy = case argTy of
                                      T.H_TY(h) => T.M_TY(T.MODULE(h, retTy))
                                    | T.EMPTY => T.M_TY(T.MODULE(T.H_DATATYPE([], ref ()), retTy))
                                    | _ => T.H_TY(T.H_TOP)
                  in
                    {datacon = datacon, ty = A.ExplicitTy(realTy), pos = pos}
                  end
                val datacons' = map mapDatacon datacons
                val datatydec' = {name = name, tyvars = tyvars, datacons = datacons'}
                (* map from meta to computed datatype type *)
                fun mapDataconForType({datacon, ty = A.ExplicitTy(t), pos}) = (datacon, (case t of
                                                                                              T.H_TY(h) => SOME(h)
                                                                                            | _ => raise Match))
                  | mapDataconForType(_) = raise Match

                val hty = T.H_DATATYPE(map mapDataconForType datacons', ref ())
                val retTy = case tyvars of
                                 SOME(tyvs) => T.H_TY(T.H_POLY(map (fn(tyv) => valOf(Symbol.look(metamap, tyv))) tyvs, hty))
                               | _ => T.H_TY(hty)
                val menv'' = Symbol.enter(menv, tempMeta, retTy)
              in
                {menv = menv'', tenv = tenv', datatydecs = datatydec'::datatydecs}
              end
            val {menv = menv', tenv = tenv', datatydecs = datatydecs'} = foldl processDatatype {menv = menv, tenv = tenv, datatydecs = []} datatydecs
          in
            (* other declarations should see the new type and meta environments *)
            {menv = menv', tenv = tenv', dec = A.SWDatatypeDec(List.rev(datatydecs'))}
          end
        | decodec(A.ValDec(valdecs)) =
          let
            fun processValDec({name, escape, ty = (ty, typos), init, pos}, {menv, valdecs}) =
              let
                val (menv', init') = decorateExp(menv, tenv, init)
                val realTy = decorateTy(menv, tenv, ty)
                val valdec' = {name = name,
                               escape = escape,
                               ty = (A.ExplicitTy(realTy), typos),
                               init = init',
                               pos = pos}
              in
                {menv = menv', valdecs = valdec'::valdecs}
              end
            val {menv = menv', valdecs = valdecs'} = foldl processValDec {menv = menv, valdecs = []} valdecs
          in
            {menv = menv', tenv = tenv, dec = A.ValDec(List.rev(valdecs'))}
          end
    in
      decodec(dec)
    end

end
