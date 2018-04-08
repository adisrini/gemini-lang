structure Value = 
struct

  type symbol = Symbol.symbol

  datatype value = IntVal of int
                 | StringVal of string
                 | RealVal of real
                 | ListVal of value list
                 | RefVal of value ref
                 | RecordVal of (symbol * value) list
                 | FunVal of (value -> value) ref
                 | DatatypeVal of (symbol * unit ref * value)
                 | BitVal of GeminiBit.bit
                 | ArrayVal of value vector
                 | HWRecordVal of (symbol * value) list
                 | OpVal of {left: value, oper: oper, right: value}
                 | ModuleVal of {name: symbol} (* TODO *)
                 | NoVal

  and oper = AndOp | OrOp | XorOp

  fun printlist f lst = case lst of 
                          [] => ""
                        | [x] => f x
                        | x::xs => (f x) ^ ", " ^ (printlist f xs)

  fun operString(AndOp) = "AndOp"
    | operString(OrOp) = "OrOp"
    | operString(XorOp) = "XorOp"

  fun toString(IntVal(i)) = "int(" ^ Int.toString(i) ^ ")"
    | toString(StringVal(s)) = "string(" ^ s ^ ")"
    | toString(RealVal(r)) = "real(" ^ Real.toString(r) ^ ")"
    | toString(ListVal(vs)) = "list([" ^ printlist toString vs ^ "])"
    | toString(RefVal(vr)) = "ref(" ^ toString(!vr) ^ ")"
    | toString(RecordVal(fs)) = "record(" ^ (printlist (fn(sym, v) => Symbol.name(sym) ^ ": " ^ toString(v)) fs) ^ ")"
    | toString(FunVal(f)) = "funval"
    | toString(DatatypeVal(sym, unique, v)) = "data(" ^ Symbol.name(sym) ^ ", " ^ toString(v) ^ ")"
    | toString(BitVal(b)) = "bit(" ^ GeminiBit.toString(b) ^ ")"
    | toString(ArrayVal(vs)) = "array([" ^  printlist toString (Vector.toList(vs)) ^ "])"
    | toString(HWRecordVal(fs)) = "hwrecord(" ^ (printlist (fn(sym, v) => Symbol.name(sym) ^ ": " ^ toString(v)) fs) ^ ")"
    | toString(OpVal{left, oper, right}) = "oper{left: " ^ toString(left) ^ ", right: " ^ toString(right) ^ ", oper: " ^ operString(oper) ^ "}"
    | toString(ModuleVal{name}) = "module{name: " ^ Symbol.name(name) ^ "}"
    | toString(NoVal) = "noval"

  type vstore = value Symbol.table

  val base_store = Symbol.empty

end