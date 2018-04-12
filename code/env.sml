signature ENV =
sig

  type menv
  type tenv
  type venv
  type smap
  type senv

  val base_menv : menv
  val base_tenv : tenv
  val base_venv : venv
  val base_smap : smap
  val base_senv : senv
  
  val makeEnv : (Symbol.symbol * 'a) list -> 'a Symbol.table

end

structure Env : ENV =
struct

  structure L = Library
  structure S = Symbol
  structure T = Types
  structure V = Value

  type menv = T.ty S.table
  type tenv = T.ty S.table
  type venv = T.ty S.table
  type smap = T.ty S.table
  type senv = ((T.ty * V.value) S.table) S.table

  fun makeEnv (l: (S.symbol * 'a) list) = foldr (fn(x, env) => S.enter(env, #1 x, #2 x)) S.empty l

  val base_menv = S.empty

  val base_tenv = makeEnv [(S.symbol("int"), T.S_TY(T.INT)),
                           (S.symbol("string"), T.S_TY(T.STRING)),
                           (S.symbol("real"), T.S_TY(T.REAL)),
                           (S.symbol("bit"), T.H_TY(T.BIT))]

  val base_venv = S.empty

  val base_smap = S.empty

  val base_senv = makeEnv [
                            (
                              S.symbol("Core"), makeEnv [
                                                         (S.symbol("print"), (L.Core.print_ty, L.Core.print_impl))
                                                       ]
                            ),
                            (
                              S.symbol("BitArray"), makeEnv [
                                                         (S.symbol("twosComp"), (L.BitArray.twosComp_ty, L.BitArray.twosComp_impl))
                                                       ]
                            ),
                            (
                              S.symbol("HW"), makeEnv [
                                                         (S.symbol("dff"), (L.HW.dff_ty, L.HW.dff_impl))
                                                       ]
                            ),
                            (
                              S.symbol("List"), makeEnv [
                                                         (S.symbol("nth"), (L.List.nth_ty, L.List.nth_impl)),
                                                         (S.symbol("length"), (L.List.length_ty, L.List.length_impl)),
                                                         (S.symbol("rev"), (L.List.rev_ty, L.List.rev_impl))
                                                       ]
                            )
                          ]

end
