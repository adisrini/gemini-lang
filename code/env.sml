signature ENV =
sig
  datatype enventry = ValEntry of {ty : Types.ty}
                    | FunEntry of {arg: Types.ty, result: Types.ty}
  val base_tenv : Types.ty Symbol.table
  val base_venv : enventry Symbol.table
  val base_menv : Types.ty Symbol.table
  val new_meta : unit -> Symbol.symbol
  val createEnvironmentWithData : (Symbol.symbol * 'a) list -> 'a Symbol.table
end

structure Env :> ENV =
struct
  datatype enventry = ValEntry of {ty : Types.ty}
                    | FunEntry of {arg: Types.ty, result: Types.ty}

  fun createEnvironmentWithData (l: (Symbol.symbol * 'a) list) = foldr (fn(x, env) => Symbol.enter(env, #1 x, #2 x)) Symbol.empty l

  val meta_count = ref 0

  val base_tenv = Symbol.empty

  val base_venv = Symbol.empty

  val base_menv = Symbol.empty

  fun new_meta () =
    let
      val x = !meta_count;
    in
      meta_count := x + 1;
      Symbol.symbol(Int.toString x)
    end
end
