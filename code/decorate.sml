signature DECORATE =
sig

  val decorateProg :                       Absyn.exp -> Absyn.exp         (* returns explicit poly tree *)
  val decorateExp  : Env.menv * Env.tenv * Absyn.exp -> Absyn.exp         (* returns expression with types made explicit *)
  val decorateTy   : Env.menv * Env.tenv * Absyn.ty  -> Types.ty          (* returns explicit type *)
  val decorateDec  : Env.menv * Env.tenv * Absyn.dec -> { menv: Env.menv, (* returns augmented environments and *)
                                                          tenv: Env.tenv, (* Absyn.dec with explicit types      *)
                                                          dec: Absyn.dec }

end

structure Decorate : DECORATE =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env

  (* attach information/context to TOP in order to make warnings/errors more clearn
  potentially number warnings and refer to others based on whether error is propagated *)

  fun decorateProg(e) = decorateExp(E.base_menv, E.base_tenv, e)

  and decorateExp(menv, tenv, exp) =
    let fun decorexp(A.StructsSigsExp(structsigs)) = A.StructsSigsExp(structsigs) (* TODO *)
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
          | decorexp(A.VarExp(sym, pos)) = A.VarExp(sym, pos) (* NO-OP *)
          | decorexp(A.IntExp(num, pos)) = A.IntExp(num, pos) (* NO-OP *)
          | decorexp(A.StringExp(str, pos)) = A.StringExp(str, pos) (* NO-OP *)
          | decorexp(A.RealExp(num, pos)) = A.RealExp(num, pos) (* NO-OP *)
          | decorexp(A.BitExp(bit, pos)) = A.BitExp(bit, pos) (* NO-OP *)
          | decorexp(A.ApplyExp(e1, e2, pos)) = A.ApplyExp(decorexp(e1), decorexp(e2), pos)
          | decorexp(A.BinOpExp({left, oper, right, pos})) = A.BinOpExp({ left = decorexp(left),
                                                                          oper = oper,
                                                                          right = decorexp(right),
                                                                          pos = pos })
          | decorexp(A.UnOpExp({exp, oper, pos})) = A.UnOpExp({ exp = decorexp(exp),
                                                                oper = oper,
                                                                pos = pos })
          | decorexp(A.LetExp({decs, body, pos})) =
            let
              fun processDecs(dec, {decs, menv, tenv}) =
                let
                  val {menv = menv', tenv = tenv', dec = dec'} = decorateDec(menv, tenv, dec)
                in
                  {decs = dec'::decs, menv = menv', tenv = tenv'}
                end
              val {decs = newDecs,
                   menv = newMenv,
                   tenv = newTenv} = foldl processDecs {decs = [], menv = menv, tenv = tenv} decs
              val newBody = decorateExp(newMenv, newTenv, body)
            in
              A.LetExp({decs = List.rev(newDecs),
                        body = newBody,
                        pos = pos })
            end
          | decorexp(A.AssignExp({lhs, rhs, pos})) = A.AssignExp({ lhs = decorexp(lhs),
                                                                   rhs = decorexp(rhs),
                                                                   pos = pos })
          | decorexp(A.SeqExp(exps)) = A.SeqExp(map (fn(e, p) => (decorexp(e), p)) exps)
          | decorexp(A.IfExp({test, then', else', pos})) = A.IfExp({ test = decorexp(test),
                                                                     then' = decorexp(then'),
                                                                     else' = Option.map (fn(x) => decorexp(x)) else',
                                                                     pos = pos })
          | decorexp(A.ListExp(exps)) = A.ListExp(map (fn(e, p) => (decorexp(e), p)) exps)
          | decorexp(A.ArrayExp(exps)) = A.ArrayExp(Vector.map (fn(e, p) => (decorexp(e), p)) exps)
          | decorexp(A.RefExp(exp, pos)) = A.RefExp(decorexp(exp), pos)
          | decorexp(A.SWRecordExp({fields, pos})) = A.SWRecordExp({ fields = map (fn((s, e, p)) => (s, decorexp(e), p)) fields,
                                                                     pos = pos })
          | decorexp(A.HWRecordExp({fields, pos})) = A.HWRecordExp({ fields = map (fn((s, e, p)) => (s, decorexp(e), p)) fields,
                                                                     pos = pos })
          | decorexp(A.SWExp(exp, pos)) = A.SWExp(decorexp(exp), pos)
          | decorexp(A.WithExp({exp, fields, pos})) = A.WithExp({ exp = decorexp(exp),
                                                                  fields = map (fn((s, e, p)) => (s, decorexp(e), p)) fields,
                                                                  pos = pos })
          | decorexp(A.DerefExp({exp, pos})) = A.DerefExp({ exp = decorexp(exp),
                                                            pos = pos })
          | decorexp(A.StructAccExp({name, field, pos})) = A.StructAccExp({name = name, field = field, pos = pos}) (* NO-OP *)
          | decorexp(A.RecordAccExp({exp, field, pos})) = A.RecordAccExp({ exp = decorexp(exp),
                                                                           field = field,
                                                                           pos = pos })
          | decorexp(A.ArrayAccExp({exp, index, pos})) = A.ArrayAccExp({ exp = decorexp(exp),
                                                                         index = decorexp(index),
                                                                         pos = pos })
          | decorexp(A.PatternMatchExp({exp, cases, pos})) = A.PatternMatchExp({ exp = decorexp(exp),
                                                                                 cases = map (fn({match, result, pos}) => {match = decorexp(match), result = decorexp(result), pos = pos}) cases,
                                                                                 pos = pos })
          | decorexp(A.BitArrayExp({size, result, spec})) = A.BitArrayExp({ size = decorexp(size),
                                                                            result = decorexp(result),
                                                                            spec = spec })
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
        fun decoty(A.NameTy(sym, pos)) = (case Symbol.look(tenv, sym) of
                                               SOME(t) => t
                                             | NONE => T.TOP) (* NOTE: error? *)
          | decoty(A.TyVar(sym, pos)) = (case Symbol.look(menv, sym) of
                                              SOME(t) => t
                                            | NONE => T.META(E.newMeta()))
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
          | decoty(A.PlaceholderTy(u)) = T.META(E.newMeta())
          | decoty(A.NoTy) = T.EMPTY
          | decoty(A.ExplicitTy(t)) = t
    in
      decoty(ty)
    end

  (* NOTE: CHECK THESE! *)
  (* NOTE: mainly check which environments are being passed where, and which things are being entered *)
  and decorateDec(menv, tenv, dec) =
    let
      fun decodec(A.FunctionDec(fundecs)) =
        let
          (* NOTE: menv and tenv are never altered *)
          fun mapFunDec({name, params, result = (ty, typos), body, pos}) =
            let
              fun mapField({name, ty, escape, pos}) = {name = name, ty = A.ExplicitTy(decorateTy(menv, tenv, ty)), escape = escape, pos = pos}

              fun mapParam(A.NoParam) = A.NoParam
                | mapParam(A.SingleParam(f)) = A.SingleParam(mapField(f))
                | mapParam(A.MultiParams(fs)) = A.MultiParams(map mapField fs)

              val params' = map mapParam params

              val resultTy = decorateTy(menv, tenv, ty)
              val resultTy' = case resultTy of
                                   T.S_TY(x) => resultTy
                                 | _ => T.S_TY(T.S_BOTTOM)

              val body' = decorateExp(menv, tenv, body)
            in
              {name = name, params = params', result = (A.ExplicitTy(resultTy'), typos), body = body', pos = pos}
            end

          val fdecs' = map mapFunDec fundecs
        in
          {menv = menv, tenv = tenv, dec = A.FunctionDec(fdecs')}
        end
        | decodec(A.TypeDec(tydecs)) =
          let
            (* menv is only altered in context of type body *)
            (* tenv is altered and passed on to future decs *)
            fun processTyDec({name, ty, tyvar, opdef, pos}, {tenv, tydecs}) =
              let
                val menv' = case tyvar of
                                 SOME(tyv) => Symbol.enter(menv, tyv, T.META(E.newMeta()))
                               | _ => menv
                val realTy = decorateTy(menv', tenv, ty)
                val tenv' = Symbol.enter(tenv, name, realTy)
                val opdef' = Option.map (fn(defs) => map (fn({oper, param_a, param_b, body, pos}) => {oper = oper, param_a = param_a, param_b = param_b, body = decorateExp(menv, tenv', body), pos = pos}) defs) opdef
                val tydec' = {name = name, ty = A.ExplicitTy(realTy), tyvar = tyvar, opdef = opdef', pos = pos}
              in
                 {tenv = tenv',
                 tydecs = tydec'::tydecs}
              end
            val {tenv = tenv', tydecs = tydecs'} = foldl processTyDec {tenv = tenv, tydecs = []} tydecs
          in
            {menv = menv, tenv = tenv', dec = A.TypeDec(List.rev(tydecs'))}
          end
        (* moddec: {name: symbol, arg: param, result: ty * pos, body: exp, pos: pos} *)
        | decodec(A.ModuleDec(moddecs)) =
        let
          (* NOTE: menv and tenv are never altered *)
          fun mapModDec({name, arg, result = (ty, typos), body, pos}) =
            let
              fun mapField({name, ty, escape, pos}) = {name = name, ty = A.ExplicitTy(decorateTy(menv, tenv, ty)), escape = escape, pos = pos}

              fun mapArg(A.NoParam) = A.NoParam
                | mapArg(A.SingleParam(f)) = A.SingleParam(mapField(f))
                | mapArg(A.MultiParams(fs)) = A.MultiParams(map mapField fs)

              val arg' = mapArg arg

              val resultTy = decorateTy(menv, tenv, ty)
              val resultTy' = case resultTy of
                                   T.H_TY(x) => resultTy
                                 | _ => T.H_TY(T.H_BOTTOM)

              val body' = decorateExp(menv, tenv, body)
            in
              {name = name, arg = arg', result = (A.ExplicitTy(resultTy'), typos), body = body', pos = pos}
            end

          val mdecs' = map mapModDec moddecs
        in
          {menv = menv, tenv = tenv, dec = A.ModuleDec(mdecs')}
        end
        (* dataty: {name: symbol, tyvar: symbol option, datacons: datacon list} *)
        (* datacon: {datacon: symbol, ty: ty, pos: pos} *)
        | decodec(A.DatatypeDec(datatydecs)) =
        (* TODO: mutually recursive datatypes *)
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
            fun processDatatype({name, tyvar, datacons}, {menv, tenv, datatydecs}) =
              let
                (* if tyvar, add to menv *)
                val menv' = case tyvar of
                                 SOME(tyv) => Symbol.enter(menv, tyv, T.META(E.newMeta()))
                               | _ => menv
                (* add datatype as META in tenv *)
                val tempMeta = E.newMeta()
                val tenv' = Symbol.enter(tenv, name, T.META(tempMeta))
                (* map datacons to explicit types *)
                fun mapDatacon({datacon, ty, pos}) =
                  let
                    val realTy = decorateTy(menv', tenv', ty)
                  in
                    {datacon = datacon, ty = A.ExplicitTy(realTy), pos = pos}
                  end
                val datacons' = map mapDatacon datacons
                val datatydec' = {name = name, tyvar = tyvar, datacons = datacons'}
                (* map from meta to computed datatype type *)
                fun mapDataconForType({datacon, ty = A.ExplicitTy(t), pos}) = (datacon, (case t of
                                                                                              T.S_TY(s) => SOME(s)
                                                                                            | T.EMPTY => NONE
                                                                                            | _ => SOME(T.S_TOP)))
                  | mapDataconForType(_) = raise Match
                (* NOTE: what to do with menv''? *)
                val menv'' = Symbol.enter(menv, name, T.S_TY(T.DATATYPE(map mapDataconForType datacons', ref ())))
              in
                {menv = menv'', tenv = tenv', datatydecs = datatydec'::datatydecs}
              end
            val {menv = menv', tenv = tenv', datatydecs = datatydecs'} = foldl processDatatype {menv = menv, tenv = tenv, datatydecs = []} datatydecs
          in
            (* other declarations should see the new type and meta environments *)
            {menv = menv', tenv = tenv', dec = A.DatatypeDec(List.rev(datatydecs'))}
          end
        | decodec(A.ValDec(valdecs)) =
          let
            fun processValDec({name, escape, ty = (ty, typos), init, pos}, valdecs) =
              let
                val init' = decorateExp(menv, tenv, init)
                val realTy = decorateTy(menv, tenv, ty)
                val valdec' = {name = name,
                               escape = escape,
                               ty = (A.ExplicitTy(realTy), typos),
                               init = init',
                               pos = pos}
              in
                valdec'::valdecs
              end
            val valdecs' = foldl processValDec [] valdecs
          in
            {menv = menv, tenv = tenv, dec = A.ValDec(List.rev(valdecs'))}
          end
    in
      decodec(dec)
    end

end
