signature DECORATE =
sig

  type menv
  type tenv
  type venv

  type expty


  val decorateProg :                      Absyn.exp -> Absyn.exp     (* returns explicit poly tree *)
  val decorateExp  : menv * tenv * venv * Absyn.exp -> Absyn.exp     (* returns expression with types made explicit *)
  val decorateTy   : menv * tenv * venv * Absyn.ty  -> Types.ty      (* returns explicit type *)
  val decorateDec  : menv * tenv * venv * Absyn.dec -> { menv: menv, (* returns augmented environments and *)
                                                         tenv: tenv, (* Absyn.dec with explicit types      *)
                                                         venv: venv,
                                                         dec: Absyn.dec }

end

structure Decorate : DECORATE =
struct

  structure A = Absyn
  structure T = Types
  structure E = Env

  type menv = T.ty Symbol.table
  type tenv = T.ty Symbol.table
  type venv = E.enventry Symbol.table

  fun decorateProg(e) = decorateExp(E.base_menv, E.base_tenv, E.base_venv, e)

  and decorateExp(menv, tenv, venv, exp) =
    let fun decorexp(A.StructsSigsExp(structsigs)) =
            (* NOTE: double check this! *)
            let
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
            end
          | decorexp(A.VarExp(sym, pos)) = A.VarExp(sym, pos) (* NO-OP *)
          | decorexp(A.IntExp(num, pos)) = A.IntExp(num, pos) (* NO-OP *)
          | decorexp(A.StringExp(str, pos)) = A.StringExp(str, pos) (* NO-OP *)
          | decorexp(A.RealExp(num, pos)) = A.RealExp(num, pos) (* NO-OP *)
          | decorexp(A.BitExp(bit, pos)) = A.BitExp(bit, pos) (* NO-OP *)
          | decorexp(A.ApplyExp(e1, e2, pos)) = A.ApplyExp(decorexp(e1), decorexp(e2))
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
                  {menv = menv', tenv = tenv', venv = venv', dec = dec'} = decorateDec(menv, tenv, venv, dec)
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
          | decorexp(A.SeqExp(exps)) = A.SeqExp(map decorexp exps)
          | decorexp(A.IfExp({test, then', else', pos})) = A.IfExp({ test = decorexp(test),
                                                                     then' = decorexp(then'),
                                                                     else' = decorexp(else'),
                                                                     pos = pos })
          | decorexp(A.ListExp(exps)) = A.ListExp(map decorexp exps)
          | decorexp(A.ArrayExp(exps)) = A.ArrayExp(Vector.map decorexp exps)
          | decorexp(A.RefExp(exp, pos)) = A.RefExp(decorexp(exp, pos))
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
          | decorexp(A.StructAccExp({name, field, pos})) = A.StructAccExp({name = name field = field, pos = pos}) (* NO-OP *)
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
    let fun getSWTy(t) = case t of
                              T.S_TY(x) => x
                            | _ => T.S_TOP  (* NOTE: error? *)
        fun getHWTy(t) = case t of
                              T.H_TY(x) => x
                            | _ => T.H_TOP  (* NOTE: error? *)
        fun decoty(A.NameTy(sym, pos)) = case Symbol.look(tenv, sym) of
                                              SOME(t) => t
                                            | NONE => case Symbol.look(menv, sym) of
                                                      SOME(t) => t
                                                    | NONE => T.TOP (* NOTE: error? *)
          | decoty(A.TyVar(sym, pos)) = T.META(E.newMeta())
          | decoty(A.SWRecordTy(fields, pos)) =
            let
              fun mapFields({name, ty, escape, pos}) = (name, getSWTy(decoty(ty)))
            in
              A.S_TY(A.S_RECORD(map mapFields fields))
            end
          | decoty(A.HWRecordTy(fields, pos)) =
            let
              fun mapFields({name, ty, escape, pos}) = (name, getHWTy(decoty(ty)))
            in
              A.H_TY(A.H_RECORD(map mapFields fields))
            end
          | decoty(A.ArrayTy(ty, size, pos)) =
            let
              val realTy1 = getHWTy(decoty(ty))
            in
              A.H_TY(A.ARRAY({ty = realTy1, size = size}))
            end
          | decoty(A.ListTy(ty, pos)) =
            let
              val realTy = getSWTy(decoty(ty))
            in
              A.S_TY(A.LIST(realTy))
            end
          | decoty(A.TemporalTy(ty, time, pos)) =
            let
              val realTy1 = getHWTy(decoty(ty))
            in
              A.H_TY(A.TEMPORAL({ty = realTy1, time = time}))
            end
          | decoty(A.RefTy(ty, pos)) =
            let
              val realTy = getSWTy(decoty(ty))
            in
              A.S_TY(A.REF(realTy))
            end
          | decoty(A.SWTy(ty, pos)) =
            let
              val exTy = decoty(ty)
              val retTy = case exTy of
                               T.H_TY(h) => T.S_TY(T.SW_H(h))
                             | T.M_TY(m) => T.S_TY(T.SW_M(m))
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
          | decoty(A.ExplicitTy(t)) = t
    in
      decoty(ty)
    end

end
