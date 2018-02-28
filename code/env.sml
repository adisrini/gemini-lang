signature ENV =
sig

  type menv
  type tenv
  type venv
  type smap

  val base_menv : menv
  val base_tenv : tenv
  val base_venv : venv
  val base_smap : smap

  val newMeta   : unit -> Symbol.symbol
  val createEnvironmentWithData : (Symbol.symbol * 'a) list -> 'a Symbol.table

end

structure Env : ENV =
struct

  structure T = Types

  type menv = Types.ty Symbol.table
  type tenv = Types.ty Symbol.table
  type venv = Types.ty Symbol.table
  type smap = Types.ty Symbol.table

  fun createEnvironmentWithData (l: (Symbol.symbol * 'a) list) = foldr (fn(x, env) => Symbol.enter(env, #1 x, #2 x)) Symbol.empty l

  val metaCount = ref 0

  val base_menv = Symbol.empty

  val base_tenv = createEnvironmentWithData [(Symbol.symbol("int"), T.S_TY(T.INT)),
                                             (Symbol.symbol("string"), T.S_TY(T.STRING)),
                                             (Symbol.symbol("real"), T.S_TY(T.REAL)),
                                             (Symbol.symbol("bit"), T.H_TY(T.BIT))]

  val base_venv = Symbol.empty

  val base_smap = Symbol.empty

  fun newMeta () =
    let
      val x = !metaCount;
    in
      metaCount := x + 1;
      Symbol.symbol("m" ^ (Int.toString x))
    end

end
