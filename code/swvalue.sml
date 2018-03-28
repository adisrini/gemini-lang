structure SWValue = 
struct

  type symbol = Symbol.symbol

  datatype value = IntVal of int
                 | StringVal of string
                 | RealVal of real
                 | ListVal of value list
                 | RefVal of value ref
                 | RecordVal of (symbol * value) list
                 | FunVal of value -> value
                 | NoVal

  fun printlist f lst = case lst of 
                          [] => ""
                        | [x] => f x
                        | x::xs => (f x) ^ ", " ^ (printlist f xs)

  fun toString(IntVal(i)) = "int(" ^ Int.toString(i) ^ ")"
    | toString(StringVal(s)) = "string(" ^ s ^ ")"
    | toString(RealVal(r)) = "real(" ^ Real.toString(r) ^ ")"
    | toString(ListVal(vs)) = "list([" ^ printlist toString vs ^ "])"
    | toString(RefVal(vr)) = "ref(" ^ toString(!vr) ^ ")"
    | toString(RecordVal(fs)) = "record(" ^ (printlist (fn(sym, v) => Symbol.name(sym) ^ ": " ^ toString(v)) fs) ^ ")"
    | toString(FunVal(f)) = "funval"
    | toString(NoVal) = "noval"

  type vstore = value Symbol.table

  val base_store = Symbol.empty

end