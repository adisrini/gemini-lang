signature DECORATE =
sig

  val decorateProg :                                  Absyn.exp -> Absyn.exp         (* returns explicit poly tree *)
  val decorateExp  : Env.menv * Env.tenv * Env.venv * Absyn.exp -> Absyn.exp         (* returns expression with types made explicit *)
  val decorateTy   : Env.menv * Env.tenv * Env.venv * Absyn.ty  -> Types.ty          (* returns explicit type *)
  val decorateDec  : Env.menv * Env.tenv * Env.venv * Absyn.dec -> { menv: Env.menv, (* returns augmented environments and *)
                                                                     tenv: Env.tenv, (* Absyn.dec with explicit types      *)
                                                                     venv: Env.venv,
                                                                     dec: Absyn.dec }

end

structure Decorate : DECORATE =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env

  fun decorateProg(e) = decorateExp(E.base_menv, E.base_tenv, E.base_venv, e)

  and decorateExp(menv, tenv, venv, exp) =
    let fun decorexp(A.StructsSigsExp(structsigs)) = A.StructsSigsExp(structsigs) (* TODO *)
            (* NOTE: double check this! *)
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
              foldr processStructSig {structsigs = [], menv = menv, tenv = tenv, venv = venv} structsigs
            end *)
          | decorexp(A.VarExp(sym, pos)) = A.VarExp(sym, pos) (* NO-OP *)
          | decorexp(A.IntExp(num, pos)) = A.IntExp(num, pos) (* NO-OP *)
          | decorexp(A.StringExp(str, pos)) = A.StringExp(str, pos) (* NO-OP *)
          | decorexp(A.RealExp(num, pos)) = A.RealExp(num, pos) (* NO-OP *)
          | decorexp(A.BitExp(bit, pos)) = A.BitExp(bit, pos) (* NO-OP *)
          | decorexp(A.ApplyExp(e1, e2, pos)) = A.ApplyExp(decorexp(e1), decorexp(e2), pos)
          | decorexp(A.NilExp(pos)) = A.NilExp(pos) (* NO-OP *)
          | decorexp(A.BinOpExp({left, oper, right, pos})) = A.BinOpExp({ left = decorexp(left),
                                                                          oper = oper,
                                                                          right = decorexp(right),
                                                                          pos = pos })
          | decorexp(A.UnOpExp({exp, oper, pos})) = A.UnOpExp({ exp = decorexp(exp),
                                                                oper = oper,
                                                                pos = pos })
          | decorexp(A.LetExp({decs, body, pos})) =
            let
              fun processDecs(dec, {decs, menv, tenv, venv}) =
                let
                  val {menv = menv', tenv = tenv', venv = venv', dec = dec'} = decorateDec(menv, tenv, venv, dec)
                in
                  {decs = dec'::decs, menv = menv', tenv = tenv', venv = venv'}
                end
              val {decs = newDecs,
                   menv = newMenv,
                   tenv = newTenv,
                   venv = newVenv} = foldr processDecs {decs = [], menv = menv, tenv = tenv, venv = venv} decs
              val newBody = decorateExp(newMenv, newTenv, newVenv, body)
            in
              A.LetExp({ decs = newDecs,
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

  and decorateTy(menv, tenv, venv, ty) =
    let fun getSWTy(t) = (case t of
                               T.S_TY(x) => x
                             | _ => T.S_TOP)  (* NOTE: error? *)
        fun getHWTy(t) = (case t of
                               T.H_TY(x) => x
                             | _ => T.H_TOP)  (* NOTE: error? *)
        fun decoty(A.NameTy(sym, pos)) = (case Symbol.look(tenv, sym) of
                                               SOME(t) => t
                                             | NONE => (case Symbol.look(menv, sym) of
                                                        SOME(t) => t
                                                      | NONE => T.TOP)) (* NOTE: error? *)
          | decoty(A.TyVar(sym, pos)) = T.META(E.newMeta())
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
                              | _ => T.S_TY(T.S_TOP))
            in
              retTy
            end
          | decoty(A.FunTy(ty1, ty2, pos)) =
            let
              val realTy1 = getSWTy(decoty(ty1))
              val realTy2 = getSWTy(decoty(ty2))
            in
              T.S_TY(T.ARROW(realTy1, realTy2))
            end
          | decoty(A.PlaceholderTy(u)) = T.META(E.newMeta())
          | decoty(A.NoTy) = T.EMPTY
          | decoty(A.ExplicitTy(t)) = t
    in
      decoty(ty)
    end

  (* NOTE: CHECK THESE! *)
  (* NOTE: mainly check which environments are being passed where, and which things are being entered *)
  and decorateDec(menv, tenv, venv, dec) =
    let
      fun decodec(A.FunctionDec(fundecs)) =
        let
          fun processFunDec({name, params, result = (ty, typos), body, pos}, {menv, tenv, venv, fdecs}) =
            let
              fun foldParams(A.NoParam, {menv, tenv, venv, params}) = {menv = menv, tenv = tenv, venv = venv, params = A.NoParam::params}
                | foldParams(A.SingleParam({name, ty, escape, pos}), {menv, tenv, venv, params}) =
                  let
                    val realTy = decorateTy(menv, tenv, venv, ty)
                    val venv' = Symbol.enter(venv, name, realTy)
                    (* NOTE: should add to menv if ty is A.TyVar(_)? *)
                  in
                    {menv = menv,
                     tenv = tenv,
                     venv = venv',
                     params = A.SingleParam({name = name, ty = A.ExplicitTy(realTy), escape = escape, pos = pos})::params}
                  end
                | foldParams(A.MultiParams(fs), {menv, tenv, venv, params}) =
                  let
                    fun foldField({name, ty, escape, pos}, {menv, tenv, venv, fields}) =
                      let
                        val realTy = decorateTy(menv, tenv, venv, ty)
                        val venv' = Symbol.enter(venv, name, realTy)
                        (* NOTE: should add to menv if ty is A.TyVar(_)? *)
                      in
                        {menv = menv,
                         tenv = tenv,
                         venv = venv',
                         fields = {name = name, ty = A.ExplicitTy(realTy), escape = escape, pos = pos}::fields}
                      end
                    val {menv = menvWithFields,
                         tenv = tenvWithFields,
                         venv = venvWithFields,
                         fields = fs'} = foldr foldField {menv = menv, tenv = tenv, venv = venv, fields = []} fs
                  in
                    {menv = menvWithFields,
                     tenv = tenvWithFields,
                     venv = venvWithFields,
                     params = A.MultiParams(fs')::params}
                  end

              val {menv = menvWithParams,
                   tenv = tenvWithParams,
                   venv = venvWithParams,
                   params = params'} = foldr foldParams {menv = menv, tenv = tenv, venv = venv, params = []} params

              val resultTy = decorateTy(menvWithParams, tenvWithParams, venvWithParams, ty)
              val resultTy' = case resultTy of
                                   T.S_TY(x) => x
                                 | _ => T.S_TOP (* NOTE: check if top or bottom *)

              val venv' = Symbol.enter(venvWithParams, name, T.S_TY(T.ARROW(T.S_TOP, resultTy')))

              val bodyExp = decorateExp(menvWithParams, tenvWithParams, venv', body)

              val fdec' = {name = name, params = params', result = (A.ExplicitTy(resultTy), typos), body = bodyExp, pos = pos}
            in
              {menv = menvWithParams,
               tenv = tenvWithParams,
               venv = venv',
               fdecs = fdec'::fdecs}
            end

          val {menv = menv', tenv = tenv', venv = venv', fdecs = fdecs'} = foldr processFunDec {menv = menv, tenv = tenv, venv = venv, fdecs = []} fundecs
        in
          {menv = menv', tenv = tenv', venv = venv', dec = A.FunctionDec(fdecs')}
        end
        | decodec(A.TypeDec(tydecs)) =
          let
            fun processTyDec({name, ty, tyvar = tyvar_opt, opdef = opdef_opt, pos}, {menv, tenv, venv, tydecs}) =
              let
                val menv' = case tyvar_opt of
                                 SOME(s) => Symbol.enter(menv, s, T.META(E.newMeta()))
                               | _ => menv
                val realTy = decorateTy(menv', tenv, venv, ty)
                val tenv' = Symbol.enter(tenv, name, realTy)
                val opdefs' = Option.map (fn(opds) => map (fn({oper, param_a, param_b, body, pos}) => (
                  let
                    val venv' = Symbol.enter(venv, param_a, realTy)
                    val venv'' = Symbol.enter(venv', param_b, realTy)
                    val body' = decorateExp(menv, tenv, venv'', body)
                  in
                    {oper = oper, param_a = param_a, param_b = param_b, body = body', pos = pos}
                  end
                  )) opds) opdef_opt
                val tydec' = {name = name, ty = A.ExplicitTy(realTy), tyvar = tyvar_opt, opdef = opdefs', pos = pos}
              in
                {menv = menv',
                 tenv = tenv',
                 venv = venv,
                 tydecs = tydec'::tydecs}
              end
            val {menv = menv', tenv = tenv', venv = venv', tydecs = tydecs'} = foldr processTyDec {menv = menv, tenv = tenv, venv = venv, tydecs = []} tydecs
          in
            {menv = menv', tenv = tenv', venv = venv', dec = A.TypeDec(tydecs')}
          end
        (* moddec: {name: symbol, arg: param, result: ty * pos, body: exp, pos: pos} *)
        | decodec(A.ModuleDec(moddecs)) =
          let
            fun processModDec({name, arg, result = (ty, typos), body, pos}, {menv, tenv, venv, moddecs}) =
              let
                val {venv', arg'} = case arg of
                                         A.NoParam => {venv' = venv, arg' = A.NoParam}
                                       | A.SingleParam(f) =>
                                          (let
                                             val {name, ty, escape, pos} = f
                                             val realTy = decorateTy(menv, tenv, venv, ty)
                                           in
                                            {venv' = Symbol.enter(venv, name, realTy), arg' = A.SingleParam({name = name, ty = A.ExplicitTy(realTy), escape = escape, pos = pos})}
                                           end)
                                       | A.MultiParams(fs) =>
                                          (let
                                             fun foldField({name, ty, escape, pos}, {venv', fs'}) =
                                               let
                                                 val realTy = decorateTy(menv, tenv, venv', ty)
                                                 val f' = {name = name, ty = A.ExplicitTy(realTy), escape = escape, pos = pos}
                                               in
                                                 {venv' = Symbol.enter(venv, name, realTy), fs' = f'::fs'}
                                               end
                                             val {venv', fs'} = foldr foldField {venv' = venv, fs' = []} fs
                                           in
                                             {venv' = venv', arg' = A.MultiParams(fs')}
                                           end)
                val realTy = decorateTy(menv, tenv, venv, ty)
                val body' = decorateExp(menv, tenv, venv', body)
                val moddec' = {name = name, arg = arg', result = (A.ExplicitTy(realTy), typos), body = body', pos = pos}
              in
                {menv = menv,
                 tenv = tenv,
                 venv = venv,
                 moddecs = moddec'::moddecs}
              end
            val {menv = menv', tenv = tenv', venv = venv', moddecs = moddecs'} = foldr processModDec {menv = menv, tenv = tenv, venv = venv, moddecs = []} moddecs
          in
            {menv = menv', tenv = tenv', venv = venv', dec = A.ModuleDec(moddecs')}
          end
          (* dataty: {name: symbol, tyvar: symbol option, datacons: datacon list} *)
          (* datacon: {datacon: symbol, ty: ty, pos: pos} *)
        | decodec(A.DatatypeDec(datatydecs)) =
        (* TODO: recursive datatypes *)
          let
            fun processDatatyDec({name, tyvar = tyvar_opt, datacons}, {menv, tenv, venv, datatydecs}) =
              let
                val menv' = case tyvar_opt of
                                 SOME(s) => Symbol.enter(menv, s, T.META(E.newMeta()))
                               | _ => menv
                val datacons' = map (fn({datacon, ty, pos}) => {datacon = datacon, ty = A.ExplicitTy(decorateTy(menv', tenv, venv, ty)), pos = pos}) datacons
                val datatydec' = {name = name, tyvar = tyvar_opt, datacons = datacons'}
                fun mapDatacons({datacon, ty = A.ExplicitTy(t), pos}) = (datacon, case t of T.S_TY(x) => SOME(x) | T.EMPTY => NONE | _ => SOME(T.S_TOP))
                  | mapDatacons(_) = raise Match
                val tenv' = Symbol.enter(tenv, name, T.S_TY(T.DATATYPE(map mapDatacons datacons', ref())))
              in
                {menv = menv', tenv = tenv', venv = venv, datatydecs = datatydec'::datatydecs}
              end
            val {menv = menv', tenv = tenv', venv = venv', datatydecs = datatydecs'} = foldr processDatatyDec {menv = menv, tenv = tenv, venv = venv, datatydecs = []} datatydecs
          in
            {menv = menv', tenv = tenv', venv = venv', dec = A.DatatypeDec(datatydecs')} (* TODO *)
          end
        | decodec(A.ValDec(valdecs)) = {menv = menv, tenv = tenv, venv = venv, dec = A.ValDec(valdecs)} (* TODO *)
    in
      decodec(dec)
    end

end
