signature ENV =
sig
  type enventry

  val base_tenv : Types.ty Symbol.table
  val base_venv : enventry Symbol.table
  val base_menv : Types.ty Symbol.table
  val newMeta : unit -> Symbol.symbol
  val createEnvironmentWithData : (Symbol.symbol * 'a) list -> 'a Symbol.table
end

structure Env :> ENV =
struct
  datatype enventry = ValEntry of {ty : Types.ty}
                    | FunEntry of {arg: Types.ty, result: Types.ty}

  fun createEnvironmentWithData (l: (Symbol.symbol * 'a) list) = foldr (fn(x, env) => Symbol.enter(env, #1 x, #2 x)) Symbol.empty l

  val metaCount = ref 0

  val base_tenv = Symbol.empty

  val base_venv = Symbol.empty

  val base_menv = Symbol.empty

  fun newMeta () =
    let
      val x = !metaCount;
    in
      metaCount := x + 1;
      Symbol.symbol("m" ^ (Int.toString x))
    end
end
