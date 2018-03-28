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

  fun getSWType(T.META(m)) = T.S_TY(T.S_META(m))
    | getSWType(T.S_TY(s)) = T.S_TY(s)
    | getSWType(_) = T.S_TY(T.S_BOTTOM)

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

  fun kindError(ty1, ty2, pos) = (ErrorMsg.error pos ("kind mismatch!\n" ^
                              "expected:\t" ^ T.toString(ty1) ^ "\n" ^
                              "received:\t" ^ T.toString(ty2) ^ "\n");
                         S.ERROR({expected = ty1,
                                  received = ty2}))

  fun unify(ty1, ty2, pos) = case ty1 of
                                   T.META(m) => S.SUB([(m, ty2)])
                                 | T.H_TY(T.H_META(hm)) => (case ty2 of
                                                                 T.H_TY(_) => S.SUB([(hm, ty2)])
                                                                | _ => kindError(ty1, ty2, pos))
                                 | T.S_TY(T.S_META(sm)) => (case ty2 of
                                                                 T.S_TY(_) => S.SUB([(sm, ty2)])
                                                                | _ => kindError(ty1, ty2, pos))
                                 | T.TOP => S.SUB([])
                                 | T.S_TY(T.S_TOP) => (case ty2 of
                                                            T.S_TY(_) => S.SUB([])
                                                           | _ => kindError(ty1, ty2, pos))
                                 | T.H_TY(T.H_TOP) => (case ty2 of
                                                            T.H_TY(_) => S.SUB([])
                                                           | _ => kindError(ty1, ty2, pos))
                                 | _ => case ty2 of
                                             T.META(m) => S.SUB([(m, ty1)])
                                           | T.H_TY(T.H_META(hm)) => (case ty1 of
                                                                           T.H_TY(_) => S.SUB([(hm, ty1)])
                                                                          | _ => kindError(ty1, ty2, pos))
                                           | T.S_TY(T.S_META(sm)) => (case ty1 of
                                                                           T.S_TY(_) => S.SUB([(sm, ty1)])
                                                                          | _ => kindError(ty1, ty2, pos))
                                           | T.BOTTOM => S.SUB([])
                                           | T.S_TY(T.S_BOTTOM) => (case ty1 of
                                                                         T.S_TY(_) => S.SUB([])
                                                                        | _ => kindError(ty1, ty2, pos))
                                           | T.H_TY(T.H_BOTTOM) => (case ty1 of
                                                                         T.H_TY(_) => S.SUB([])
                                                                        | _ => kindError(ty1, ty2, pos))
                                           | _ => case (ty1, ty2) of
                                                       (T.H_TY(h1), T.H_TY(h2)) => unifyHty(h1, h2, pos)
                                                     | (T.S_TY(s1), T.S_TY(s2)) => unifySty(s1, s2, pos)
                                                     | (T.M_TY(m1), T.M_TY(m2)) => unifyMty(m1, m2, pos)
                                                     | _ => kindError(ty1, ty2, pos)

  and unifyHty(hty1, hty2, pos) = case (hty1, hty2) of
                                  (T.H_TOP, _) => S.SUB([])
                                | (_, T.H_BOTTOM) => S.SUB([])
                                | (T.H_META(hm), _) => S.SUB([(hm, T.H_TY(hty2))])
                                | (_, T.H_META(hm)) => S.SUB([(hm, T.H_TY(hty1))])
                                | (T.BIT, T.BIT) => S.SUB([])
                                | (T.ARRAY{ty = ty1, size = _}, T.ARRAY{ty = ty2, size = _}) => unifyHty(ty1, ty2, pos)
                                | (T.H_RECORD(recs1), T.H_RECORD(recs2)) => 
                                  let
                                    fun foldSubs(((_, hty1), (_, hty2)), sub) =
                                      let
                                        val innersub = unifyHty(hty1, hty2, pos)
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
                                | (T.TEMPORAL{ty = ty1, time = _}, T.TEMPORAL{ty = ty2, time = _}) => unifyHty(ty1, ty2, pos)
                                | _ => error(T.H_TY(hty1), T.H_TY(hty2), pos)

  and unifySty(sty1, sty2, pos) = case (sty1, sty2) of
                                  (T.S_TOP, _) => S.SUB([])
                                | (_, T.S_BOTTOM) => S.SUB([])
                                | (T.S_META(sm), _) => S.SUB([(sm, T.S_TY(sty2))])
                                | (_, T.S_META(sm)) => S.SUB([(sm, T.S_TY(sty1))])
                                | (T.INT, T.INT) => S.SUB([])
                                | (T.STRING, T.STRING) => S.SUB([])
                                | (T.REAL, T.REAL) => S.SUB([])
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
                                | (T.S_MU(_, sty1), T.S_MU(_, sty2)) => unifySty(sty1, sty2, pos)
                                | _ => error(T.S_TY(sty1), T.S_TY(sty2), pos)

  and unifyMty(mty1, mty2, pos) = S.SUB([])  (* TODO *)

  and unifyList(ty1, ty2, pos) = case (getSWType(ty1), getSWType(ty2)) of
                                 (T.S_TY(sty1), T.S_TY(sty2)) => let
                                                                   val sub = unifySty(T.LIST(sty1), sty2, pos)
                                                                 in
                                                                   (sub, case sub of
                                                                              S.SUB((sym, retTy)::rest) => retTy  (* TODO: test this! *)
                                                                            | S.SUB([]) => ty2
                                                                            | S.ERROR(_) => T.S_TY(T.S_BOTTOM))
                                                                 end
                               | _ => let
                                        val sub1 = case getSWType(ty1) of
                                                        T.S_TY(_) => S.SUB([])
                                                      | _ => errorSW("'sw", ty1, pos)
                                        val sub2 = case getSWType(ty2) of
                                                        T.S_TY(_) => S.SUB([])
                                                      | _ => errorSW("'sw list", ty2, pos)
                                      in
                                        (sub2, T.S_TY(T.S_BOTTOM))
                                      end

   (* TODO: check type being compared? *)
   and unifyEqualityType(ty1, ty2, pos) = (unify(ty1, ty2, pos), T.S_TY(T.INT))

   (* TODO: check type being compared? *)
   and unifyInequalityType(ty1, ty2, pos) = (unify(ty1, ty2, pos), T.S_TY(T.INT))

   and unifyAssign(ty1, ty2, pos) = case (getSWType(ty1), getSWType(ty2)) of
                                         (T.S_TY(sty1), T.S_TY(sty2)) => let
                                                                           val sub = unifySty(sty1, T.REF(sty2), pos)
                                                                         in
                                                                           (sub, T.S_TY(T.S_RECORD([])))
                                                                         end
                                       | _ => let
                                                val sub1 = case getSWType(ty1) of
                                                                T.S_TY(_) => errorSW("'sw", ty1, pos)
                                                              | _ => S.SUB([])
                                                val sub2 = case getSWType(ty2) of
                                                                T.S_TY(_) => errorSW("'sw ref", ty2, pos)
                                                              | _ => S.SUB([])
                                              in
                                                (sub2, T.S_TY(T.S_RECORD([])))
                                              end

  and unifyPolyApp(argTy, paramTy, pos) = case (getSWType(argTy), getSWType(paramTy)) of
                                               (T.S_TY(T.S_POLY(tyvars, T.ARROW(sty1, sty2))), _) => unifyPolyApp(T.S_TY(sty1), paramTy, pos)
                                             | (T.S_TY(_), T.S_TY(_)) => unify(paramTy, argTy, pos)
                                             | (_, T.S_TY(_)) => errorSW("'sw", argTy, pos)
                                             | (_, _) => errorSW("'sw", paramTy, pos)


  and unifyShift(arrTy, intTy, pos) =
    let
      val sub1 = unify(T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}), arrTy, pos)
      val sub2 = unify(T.S_TY(T.INT), intTy, pos)
    in
      ([sub1, sub2], T.H_TY(T.ARRAY{ty = T.BIT, size = ref ~1}))
    end

end
