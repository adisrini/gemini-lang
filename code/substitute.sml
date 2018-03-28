structure Substitute =
struct

  structure T = Types

  datatype sub = SUB of (Symbol.symbol * Types.ty) list
               | ERROR of {expected: Types.ty, received: Types.ty}

  fun toString(SUB(subs)) = "SUB(" ^ (String.concat(map (fn(sym, ty) => Symbol.name(sym) ^ " |-> " ^ T.toString(ty) ^ ",") subs)) ^ ")"
    | toString(ERROR{expected, received}) = "ERROR({expected: " ^ T.toString(expected) ^ ", received: " ^ T.toString(received) ^ "})"

  fun makeMap(SUB(subs)) = foldl (fn((sym, ty), smap) => Symbol.enter(smap, sym, ty)) Symbol.empty subs 
    | makeMap(_) = Symbol.empty

  fun substituteType(ty, submap, hasChanged) =
    let
      (* the list is a list of tyvars to avoid substituting; it is only added to when encountering a poly so as to avoid substituting things that are part of the poly clause *)
      fun subty(T.S_TY(sty)) = T.S_TY(substy(sty, []))
        | subty(T.H_TY(hty)) = T.H_TY(subhty(hty, []))
        | subty(T.M_TY(mty)) = T.M_TY(submty(mty, []))
        | subty(ty) = ty
      and substy(T.INT, _) = T.INT
        | substy(T.REAL, _) = T.REAL
        | substy(T.STRING, _) = T.STRING
        | substy(T.ARROW(sty1, sty2), tyvars) = T.ARROW(substy(sty1, tyvars), substy(sty2, tyvars))
        | substy(T.LIST(sty), tyvars) = T.LIST(substy(sty, tyvars))
        | substy(T.SW_H(hty), tyvars) = T.SW_H(subhty(hty, tyvars))
        | substy(T.SW_M(mty), tyvars) = T.SW_M(submty(mty, tyvars))
        | substy(T.S_RECORD(fs), tyvars) = T.S_RECORD(map (fn(sym, sty) => (sym, substy(sty, tyvars))) fs)
        | substy(T.REF(sty), tyvars) = T.REF(substy(sty, tyvars))
        | substy(T.S_META(sm), tyvars) = (if (List.exists (fn(x) => x = sm) tyvars)
                                          then T.S_META(sm)
                                          else (case Symbol.look(submap, sm) of
                                                     SOME(T.S_TY(newty)) => (case newty of
                                                                             T.S_META(sm') => if (Symbol.name(sm') <> Symbol.name(sm))
                                                                                              then hasChanged := true
                                                                                              else ()
                                                                           | _ => hasChanged := true; newty)
                                                   | _ => T.S_META(sm)))
        | substy(T.S_POLY(polyvars, sty), tyvars) = T.S_POLY(polyvars, substy(sty, tyvars @ polyvars))
        | substy(T.S_DATATYPE(tycons, u), tyvars) =
          let
            fun mapTycon(tycon, sty_opt) = case sty_opt of
                                                SOME(sty) => (tycon, SOME(substy(sty, tyvars)))
                                              | _ => (tycon, sty_opt)
          in
            T.S_DATATYPE(map mapTycon tycons, u)
          end
        | substy(T.S_MU(muvars, sty), tyvars) = T.S_MU(muvars, substy(sty, tyvars @ muvars))
        | substy(T.S_BOTTOM, _) = T.S_BOTTOM
        | substy(T.S_TOP, _) = T.S_TOP
      and subhty(T.BIT, _) = T.BIT
        | subhty(T.ARRAY{ty, size}, tyvars) = T.ARRAY{ty = subhty(ty, tyvars), size = size}
        | subhty(T.H_RECORD(fs), tyvars) = T.H_RECORD(map (fn(sym, hty) => (sym, subhty(hty, tyvars))) fs)
        | subhty(T.TEMPORAL{ty, time}, tyvars) = T.TEMPORAL{ty = subhty(ty, tyvars), time = time}
        | subhty(T.H_META(hm), tyvars) = (if (List.exists (fn(x) => x = hm) tyvars)
                                          then T.H_META(hm)
                                          else (case Symbol.look(submap, hm) of
                                                     SOME(T.H_TY(newty)) => (case newty of
                                                                             T.H_META(hm') => if (Symbol.name(hm') <> Symbol.name(hm))
                                                                                              then hasChanged := true
                                                                                              else ()
                                                                           | _ => hasChanged := true; newty)
                                                   | _ => T.H_META(hm)))
        | subhty(T.H_POLY(polyvars, hty), tyvars) = T.H_POLY(polyvars, subhty(hty, tyvars @ polyvars))
        | subhty(T.H_DATATYPE(tycons, u), tyvars) =
          let
            fun mapTycon(tycon, hty_opt) = case hty_opt of
                                                SOME(hty) => (tycon, SOME(subhty(hty, tyvars)))
                                              | _ => (tycon, hty_opt)
          in
            T.H_DATATYPE(map mapTycon tycons, u)
          end
        | subhty(T.H_BOTTOM, _) = T.H_BOTTOM
        | subhty(T.H_TOP, _) = T.H_TOP
      and submty(T.MODULE(hty1, hty2), tyvars) = T.MODULE(subhty(hty1, tyvars), subhty(hty2, tyvars))
        | submty(T.M_POLY(polyvars, mty), tyvars) = T.M_POLY(polyvars, submty(mty, tyvars @ polyvars))
        | submty(T.M_BOTTOM, _) = T.M_BOTTOM
    in
      subty(ty)
    end

  fun substitute(smap, env: T.ty Symbol.table) =
    let
      val hasChanged = ref false

      fun foldOver((key, ty), env) = Symbol.enter(env, key, substituteType(ty, smap, hasChanged))

      fun iterate(env) =
        let
          val () = hasChanged := false
          val env' = foldl foldOver env (Symbol.list(env))
        in
          if (!hasChanged)
          then iterate(env')
          else env'
        end
      (*val () = print("=== SUBSTITUTING ===\n")
      val () = Symbol.print(TextIO.stdOut, smap, T.toString)
      val () = Symbol.print(TextIO.stdOut, env, T.toString)*)
    in
      iterate(env)
    end

end
