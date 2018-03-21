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
                                   T.META(m) => S.SUB([(m, ty2)])
                                 | T.H_TY(T.H_META(hm)) => S.SUB([(hm, ty2)])
                                 | T.S_TY(T.S_META(sm)) => S.SUB([(sm, ty2)])
                                 | _ => case ty2 of
                                             T.META(m) => S.SUB([(m, ty1)])
                                           | T.H_TY(T.H_META(hm)) => S.SUB([(hm, ty1)])
                                           | T.S_TY(T.S_META(sm)) => S.SUB([(sm, ty1)])
                                           | _ => case (ty1, ty2) of
                                                       (T.H_TY(h1), T.H_TY(h2)) => unifyHty(h1, h2, pos)
                                                     | (T.S_TY(s1), T.S_TY(s2)) => unifySty(s1, s2, pos)
                                                     | (T.M_TY(m1), T.M_TY(m2)) => unifyMty(m1, m2, pos)
                                                     | _ => S.SUB([]) (* TODO: error *)

  and unifyHty(hty1, hty2, pos) = case (hty1, hty2) of
                                  (T.H_META(hm), _) => S.SUB([(hm, T.H_TY(hty2))])
                                | (_, T.H_META(hm)) => S.SUB([(hm, T.H_TY(hty1))])
                                | (T.BIT, T.BIT) => S.SUB([])
                                | (T.ARRAY{ty = ty1, size = _}, T.ARRAY{ty = ty2, size = _}) => unifyHty(ty1, ty2, pos)
                                (* TODO: records, temporal, etc. *)
                                | _ => error(T.H_TY(hty1), T.H_TY(hty2), pos)

  and unifySty(sty1, sty2, pos) = case (sty1, sty2) of
                                  (T.S_META(sm), _) => S.SUB([(sm, T.S_TY(sty2))])
                                | (_, T.S_META(sm)) => S.SUB([(sm, T.S_TY(sty1))])
                                | (T.INT, T.INT) => S.SUB([])
                                | (T.STRING, T.STRING) => S.SUB([])
                                | (T.LIST(listTy1), T.LIST(listTy2)) => unifySty(listTy1, listTy2, pos)
                                | (T.REF(refTy1), T.REF(refTy2)) => unifySty(refTy1, refTy2, pos)
                                | (T.S_POLY(_, polySty), _) => unifySty(polySty, sty2, pos)
                                | (_, T.S_POLY(_, polySty)) => unifySty(polySty, sty1, pos)
                                | (T.S_RECORD(recs1), T.S_RECORD(recs2)) => 
                                  let
                                    fun foldSubs(((_, sty1), (_, sty2)), sub) =
                                      let
                                        val innersub = unifySty(sty1, sty2, pos)
                                      in
                                        case sub of
                                          S.ERROR(_) => sub
                                        | S.SUB(subs) => case innersub of
                                                              S.ERROR(_) => innersub
                                                            | S.SUB(innersubs) => S.SUB(subs @ innersubs)
                                      end
                                  in
                                    foldl foldSubs (S.SUB([])) (ListPair.zipEq(recs1, recs2))
                                  end
                                | _ => error(T.S_TY(sty1), T.S_TY(sty2), pos)

  and unifyMty(mty1, mty2, pos) = S.SUB([])  (* TODO *)

  and unifyList(ty1, ty2, pos) = case (ty1, ty2) of
                                 (T.S_TY(sty1), T.S_TY(sty2)) => let
                                                                   val sub = unifySty(T.LIST(sty1), sty2, pos)
                                                                 in
                                                                   (sub, case sub of
                                                                              S.SUB((sym, retTy)::rest) => retTy  (* TODO: test this! *)
                                                                            | S.SUB([]) => ty2
                                                                            | S.ERROR(_) => T.S_TY(T.S_BOTTOM))
                                                                 end
                               | _ => let
                                        val sub1 = case ty1 of
                                                        T.S_TY(_) => S.SUB([])
                                                      | _ => errorSW("'sw", ty1, pos)
                                        val sub2 = case ty2 of
                                                        T.S_TY(_) => S.SUB([])
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
                                                              | _ => S.SUB([])
                                                val sub2 = case ty2 of
                                                                T.S_TY(_) => errorSW("'sw ref", ty2, pos)
                                                              | _ => S.SUB([])
                                              in
                                                (sub2, T.S_TY(T.S_RECORD([])))
                                              end

  (* note: test on case where argTy/paramTy is another poly *)
  and unifyPolyApp(argTy, paramTy, pos) = case (argTy, paramTy) of
                                               (T.S_TY(T.S_POLY(tyvars, T.ARROW(sty1, sty2))), _) => unifyPolyApp(T.S_TY(sty1), paramTy, pos)
                                             | (T.S_TY(_), T.S_TY(_)) => unify(paramTy, argTy, pos)
                                             | (_, T.S_TY(_)) => errorSW("'booga", argTy, pos)
                                             | (_, _) => errorSW(T.toString(argTy) ^ ", " ^ T.toString(paramTy), paramTy, pos)


end
