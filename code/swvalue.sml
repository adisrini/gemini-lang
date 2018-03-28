structure SWValue = 
struct

  type symbol = Symbol.symbol

  datatype value = IntVal of int
                 | StringVal of string
                 | RealVal of real
                 | ListVal of value list
                 | RecordVal of (symbol * value) list
                 | FunVal of value -> value

  type vstore = value Symbol.table

  val base_store = Symbol.empty

end