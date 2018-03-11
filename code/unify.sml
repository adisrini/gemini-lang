structure Unify =
struct

  structure S = Substitute
  structure T = Types


  (* UNIFY

  take in two types and try to UNIFY
  if variable and something, substitute (v -> s)
  if something and variable, substitute (v -> s)
  otherwise, check outermost tycon and if match, recurse (do left first, then apply substitution to right and do right)
  if not match, report error

   *)

  fun error(ty1, ty2, pos) = (ErrorMsg.error pos ("type mismatch!\n" ^
                              "expected:\t" ^ T.toString(ty1) ^ "\n" ^
                              "received:\t" ^ T.toString(ty2) ^ "\n");
                         S.ERROR({expected = ty1,
                                  received = ty2}))

  fun errorSW(expectedTyStr, ty, pos) = (ErrorMsg.error pos ("type mismatch!\n" ^
                              "expected " ^ expectedTyStr ^ " type\n" ^
                              "received:\t" ^ T.toString(ty) ^ "\n");
                     S.ERROR({expected = T.S_TY(T.S_BOTTOM),
                              received = ty}))

  fun unify(ty1, ty2, pos) = case ty1 of
                                   T.META(m) => S.SUB(SOME(m, ty2))
                                 | T.H_TY(T.H_META(hm)) => S.SUB(SOME(hm, ty2))
                                 | T.S_TY(T.S_META(sm)) => S.SUB(SOME(sm, ty2))
                                 | _ => case ty2 of
                                             T.META(m) => S.SUB(SOME(m, ty1))
                                           | T.H_TY(T.H_META(hm)) => S.SUB(SOME(hm, ty1))
                                           | T.S_TY(T.S_META(sm)) => S.SUB(SOME(sm, ty1))
                                           | _ => case (ty1, ty2) of
                                                       (T.H_TY(h1), T.H_TY(h2)) => unifyHty(h1, h2, pos)
                                                     | (T.S_TY(s1), T.S_TY(s2)) => unifySty(s1, s2, pos)
                                                     | (T.M_TY(m1), T.M_TY(m2)) => unifyMty(m1, m2, pos)
                                                     | _ => S.SUB(NONE) (* TODO: error *)

  and unifyHty(hty1, hty2, pos) = case (hty1, hty2) of
                                  (T.H_META(hm), _) => S.SUB(SOME(hm, T.H_TY(hty2)))
                                | (_, T.H_META(hm)) => S.SUB(SOME(hm, T.H_TY(hty1)))
                                | (T.BIT, T.BIT) => S.SUB(NONE)
                                | (T.ARRAY{ty = ty1, size = _}, T.ARRAY{ty = ty2, size = _}) => unifyHty(ty1, ty2, pos)
                                | (T.H_RECORD(recs1), T.H_RECORD(recs2)) =>
                                  let
                                    fun foldSubs(((_, h_ty1), (_, h_ty2)), subs) = unifyHty(h_ty1, h_ty2, pos)::subs
                                    val subs = List.rev(foldl foldSubs [] (ListPair.zipEq(recs1, recs2)))
                                  in
                                    S.SUB(NONE)
                                  end
                                | _ => error(T.H_TY(hty1), T.H_TY(hty2), pos)

  and unifySty(sty1, sty2, pos) = case (sty1, sty2) of
                                  (T.S_META(sm), _) => S.SUB(SOME(sm, T.S_TY(sty2)))
                                | (_, T.S_META(sm)) => S.SUB(SOME(sm, T.S_TY(sty1)))
                                | (T.INT, T.INT) => S.SUB(NONE)
                                | (T.STRING, T.STRING) => S.SUB(NONE)
                                | (T.LIST(listTy1), T.LIST(listTy2)) => unifySty(listTy1, listTy2, pos)
                                | (T.REF(refTy1), T.REF(refTy2)) => unifySty(refTy1, refTy2, pos)
                                | (T.S_POLY(_, polySty), _) => unifySty(polySty, sty2, pos)
                                | (_, T.S_POLY(_, polySty)) => unifySty(polySty, sty1, pos)
                                | _ => error(T.S_TY(sty1), T.S_TY(sty2), pos)
  and unifyMty(mty1, mty2, pos) = S.SUB(NONE)  (* TODO *)

  and unifyList(ty1, ty2, pos) = case (ty1, ty2) of
                                 (T.S_TY(sty1), T.S_TY(sty2)) => let
                                                                   val sub = unifySty(T.LIST(sty1), sty2, pos)
                                                                 in
                                                                   (sub, case sub of
                                                                              S.SUB(SOME(sym, retTy)) => retTy
                                                                            | S.SUB(NONE) => ty2
                                                                            | S.ERROR(_) => T.S_TY(T.S_BOTTOM))
                                                                 end
                               | _ => let
                                        val sub1 = case ty1 of
                                                        T.S_TY(_) => S.SUB(NONE)
                                                      | _ => errorSW("'sw", ty1, pos)
                                        val sub2 = case ty2 of
                                                        T.S_TY(_) => S.SUB(NONE)
                                                      | _ => errorSW("'sw list", ty2, pos)
                                      in
                                        (sub2, T.S_TY(T.S_BOTTOM))
                                      end

   (* TODO: check type being compared? *)
   and unifyEqualityType(ty1, ty2, pos) = (unify(ty1, ty2, pos), T.S_TY(T.INT))

   (* TODO: check type being compared? *)
   and unifyInequalityType(ty1, ty2, pos) = (unify(ty1, ty2, pos), T.S_TY(T.INT))

   and unifyAssign(ty1, ty2, pos) = case (ty1, ty2) of
                                         (T.S_TY(sty1), T.S_TY(sty2)) => let
                                                                           val sub = unifySty(sty1, T.REF(sty2), pos)
                                                                         in
                                                                           (sub, T.S_TY(T.S_RECORD([])))
                                                                         end
                                       | _ => let
                                                val sub1 = case ty1 of
                                                                T.S_TY(_) => errorSW("'sw", ty1, pos)
                                                              | _ => S.SUB(NONE)
                                                val sub2 = case ty2 of
                                                                T.S_TY(_) => errorSW("'sw ref", ty2, pos)
                                                              | _ => S.SUB(NONE)
                                              in
                                                (sub2, T.S_TY(T.S_RECORD([])))
                                              end


end
