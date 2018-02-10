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
            let
              fun processStructSig(A.StructExp({name, signat, decs, pos}))
                | processStructSig(A.SigExp({name, defs}))
                | processStructSig(A.NamedSigExp(sym)) = A.NamedSigExp(sym) (* NO-OP *)
                | processStructSig(A.AnonSigExp(defs))
            in
              (* NOTE: not sure if fold is appropriate *)
              foldr processStructSig [] structsigs
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
    let fun decoty(A.NameTy(sym, pos)) = getTypeFromEnv(tenv, sym)
          | decoty(A.TyVar(sym, pos)) = getTypeFromEnv(menv, sym)
          | decoty(A.SWRecordTy(fields, pos)) =
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
          | decoty(A.HWRecordTy(fields, pos)) =
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
          | decoty(A.ArrayTy(ty, size, pos)) =
            let
              val realTy = decoty(ty)
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
          | decoty(A.ListTy(ty, pos)) =
            let
              val realTy = decoty(ty)
              val retTy = case realTy of
                               T.S_TY(t) => t
                             | _ => T.S_TOP (* TODO: error message (sw type expected) *)
            in
              T.S_TY(T.LIST(retTy))
            end
          | decoty(A.TemporalTy(ty, time, pos)) =
            let
              val realTy = decoty(ty)
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
          | decoty(A.RefTy(ty, pos)) =
            let
              val realTy = decoty(ty)
              val retTy = case realTy of
                               T.S_TY(t) => t
                             | _ => T.S_TOP (* TODO: error message (expected sw type) *)
            in
              T.S_TY(T.REF(retTy))
            end
          | decoty(A.SWTy(ty, pos)) =
            let
              val realTy = decoty(ty)
              val ret = case realTy of
                             T.H_TY(t) => T.S_TY(T.SW_H(t))
                           | T.M_TY(t) => T.S_TY(T.SW_M(t))
                           | _ => T.S_TY(T.S_TOP) (* TODO: error message (expected hw/m type ) *)
            in
              ret
            end
          | decoty(A.FunTy(ty1, ty2, pos)) =
            let
              val realArgTy = decoty(ty1)
              val realResTy = decoty(ty2)

              val retArgTy = case realArgTy of
                                  T.S_TY(t) => t
                                | _ => T.S_TOP (* TODO: error message (expected sw type) *)
              val retResTy = case realResTy of
                                  T.S_TY(t) => t
                                | _ => T.S_BOTTOM (* TODO: error message (expected sw type) *)
            in
              T.S_TY(T.ARROW(decoty(ty1), decoty(ty2)))
            end
          | decoty(A.PlaceholderTy(u)) = T.META(E.newMeta())
          | decoty(A.ExplicitTy(t)) = t
    in
      decoty(ty)
    end

end
