signature ENV =
sig
  type access
  datatype enventry = ValEntry of {ty : Types.ty}
                    | FunEntry of {arg: Types.ty, result: Types.ty}
  val base_tenv : Types.ty Symbol.table
  val base_venv : enventry Symbol.table
  val createEnvironmentWithData : (Symbol.symbol * 'a) list -> 'a Symbol.table
end

structure Env :> ENV =
struct
  type access = unit
  datatype enventry = ValEntry of {ty : Types.ty}
                    | FunEntry of {arg: Types.ty, result: Types.ty}

  fun createEnvironmentWithData (l: (Symbol.symbol * 'a) list) = foldr (fn(x, env) => Symbol.enter(env, #1 x, #2 x)) Symbol.empty l

  val base_tenv =
      let
          val data = [(Symbol.symbol "int", Types.INT),
                      (Symbol.symbol "string", Types.STRING)]
      in
          createEnvironmentWithData data
      end

  val base_venv =
      let
          val data = [(Symbol.symbol "flush", FunEntry[{formals = [], result = Types.UNIT}]),
                      (Symbol.symbol "print", FunEntry[{formals = [Types.STRING], result = Types.UNIT}]),
                      (Symbol.symbol "getchar", FunEntry[{formals = [], result = Types.STRING}]),
                      (Symbol.symbol "ord", FunEntry[{formals = [Types.STRING], result = Types.INT}]),
                      (Symbol.symbol "chr", FunEntry[{formals = [Types.INT], result = Types.STRING}]),
                      (Symbol.symbol "size", FunEntry[{formals = [Types.STRING], result = Types.INT}]),
                      (Symbol.symbol "substring", FunEntry[{formals = [Types.STRING, Types.INT, Types.INT], result = Types.STRING}]),
                      (Symbol.symbol "concat", FunEntry[{formals = [Types.STRING, Types.STRING], result = Types.STRING}]),
                      (Symbol.symbol "not", FunEntry[{formals = [Types.INT], result = Types.INT}]),
                      (Symbol.symbol "exit", FunEntry[{formals = [Types.INT], result = Types.UNIT}])]
      in
          createEnvironmentWithData data
      end
end
