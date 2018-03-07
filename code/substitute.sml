structure Substitute =
struct

  structure T = Types

  datatype sub = SUB of (Symbol.symbol * Types.ty) option
               | ERROR of {expected: Types.ty, received: Types.ty}

  fun substitute(smap, env: T.ty Symbol.table) =
    let
      val hasChanged = ref false
      fun subty(T.S_TY(sty)) = T.S_TY(substy(sty))
        | subty(ty) = ty (* TODO *)
      and substy(T.INT) = T.INT
        | substy(T.REAL) = T.REAL
        | substy(T.STRING) = T.STRING
        | substy(T.ARROW(sty1, sty2)) = T.ARROW(substy(sty1), substy(sty2))
        | substy(T.LIST(sty)) = T.LIST(substy(sty))
        | substy(T.SW_H(hty)) = T.SW_H(subhty(hty))
        | substy(T.SW_M(mty)) = T.SW_M(submty(mty))
        | substy(T.S_RECORD(fs)) = T.S_RECORD(map (fn(sym, sty) => (sym, substy(sty))) fs)
        | substy(T.REF(sty)) = T.REF(substy(sty))
        | substy(T.S_META(sm)) = (case Symbol.look(smap, sm) of
                                       SOME(T.S_TY(newty)) => (hasChanged := true; newty)
                                     | _ => T.S_META(sm))
        | substy(sty) = sty (* TODO: datatype, poly, unpoly, bottom, top *)
      and subhty(T.BIT) = T.BIT
        | subhty(T.ARRAY{ty, size}) = T.ARRAY{ty = subhty(ty), size = size}
        | subhty(T.H_RECORD(fs)) = T.H_RECORD(map (fn(sym, hty) => (sym, subhty(hty))) fs)
        | subhty(T.TEMPORAL{ty, time}) = T.TEMPORAL{ty = subhty(ty), time = time}
        | subhty(T.H_META(hm)) = (case Symbol.look(smap, hm) of
                                       SOME(T.H_TY(newty)) => (hasChanged := true; newty)
                                     | _ => T.H_META(hm))
        | subhty(hty) = hty (* TODO: datatype, poly, unpoly, bottom, top *)
      and submty(mty) = mty (* TODO *)

      fun foldOver((key, ty), env) = Symbol.enter(env, key, subty(ty))

      fun iterate(env) =
        let
          val () = hasChanged := false
          val env' = foldl foldOver env (Symbol.list(env))
        in
          if (!hasChanged)
          then iterate(env')
          else env'
        end
    in
      iterate(env)
    end

end
