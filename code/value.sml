structure Value = 
struct

  type symbol = Symbol.symbol

  datatype value = IntVal of int
                 | StringVal of string
                 | RealVal of real
                 | ListVal of value list
                 | RefVal of value ref
                 | SWVal of value
                 | RecordVal of (symbol * value) list
                 | FunVal of (value -> value) ref
                 | DatatypeVal of (symbol * unit ref * value)

                 | NamedVal of symbol * Types.ty
                 | BitVal of GeminiBit.bit
                 | ArrayVal of value vector
                 | HWRecordVal of (symbol * value) list
                 | BinOpVal of {left: value, oper: binop, right: value}
                 | UnOpVal of {value: value, oper: unop}
                 | ArrayAccVal of {arr: value vector, index: int}
                 (*| DFFVal of int*)
                 | ModuleVal of (value -> value) * value    (* first is module function, second is named arguments value to supply to function when at top-level *)

                 | NoVal

  and binop = AndOp | OrOp | XorOp | SLLOp | SRLOp | SRAOp

  and unop = NotOp | AndReduceOp | OrReduceOp | XorReduceOp

  fun printlist f lst = case lst of 
                          [] => ""
                        | [x] => f x
                        | x::xs => (f x) ^ ", " ^ (printlist f xs)

  fun binopString(AndOp) = "AndOp"
    | binopString(OrOp) = "OrOp"
    | binopString(XorOp) = "XorOp"
    | binopString(SLLOp) = "SLLOp"
    | binopString(SRLOp) = "SRLOp"
    | binopString(SRAOp) = "SRAOp"

  fun unopString(NotOp) = "NotOp"
    | unopString(AndReduceOp) = "AndReduceOp"
    | unopString(OrReduceOp) = "OrReduceOp"
    | unopString(XorReduceOp) = "XorReduceOp"

  fun toString(IntVal(i)) = "int(" ^ Int.toString(i) ^ ")"
    | toString(StringVal(s)) = "string(" ^ s ^ ")"
    | toString(RealVal(r)) = "real(" ^ Real.toString(r) ^ ")"
    | toString(ListVal(vs)) = "list([" ^ printlist toString vs ^ "])"
    | toString(RefVal(vr)) = "ref(" ^ toString(!vr) ^ ")"
    | toString(SWVal(h)) = "sw(" ^ toString(h) ^ ")"
    | toString(RecordVal(fs)) = "record(" ^ (printlist (fn(sym, v) => Symbol.name(sym) ^ ": " ^ toString(v)) fs) ^ ")"
    | toString(FunVal(f)) = "funval"
    | toString(DatatypeVal(sym, unique, v)) = "data(" ^ Symbol.name(sym) ^ ", " ^ toString(v) ^ ")"
    | toString(NamedVal(n, t)) = "named_val(" ^ Symbol.name(n) ^ " : " ^ Types.toString(t) ^ ")"
    | toString(BitVal(b)) = "bit(" ^ GeminiBit.toString(b) ^ ")"
    | toString(ArrayVal(vs)) = "array([" ^  printlist toString (Vector.toList(vs)) ^ "])"
    | toString(HWRecordVal(fs)) = "hwrecord(" ^ (printlist (fn(sym, v) => Symbol.name(sym) ^ ": " ^ toString(v)) fs) ^ ")"
    | toString(BinOpVal{left, oper, right}) = "binop{left: " ^ toString(left) ^ ", right: " ^ toString(right) ^ ", oper: " ^ binopString(oper) ^ "}"
    | toString(UnOpVal{value, oper}) = "unop{value: " ^ toString(value) ^ ", oper: " ^ unopString(oper) ^ "}"
    | toString(ArrayAccVal{arr, index}) = "acc{arr: " ^ toString(ArrayVal(arr)) ^ ", index: " ^ Int.toString(index) ^ "}"
    | toString(ModuleVal(m, namedArgs)) = "moduleval(" ^ toString(namedArgs) ^ ")"
    | toString(NoVal) = "noval"

  type vstore = value Symbol.table

  fun createEnvironmentWithData (l: (Symbol.symbol * 'a) list) = foldr (fn(x, env) => Symbol.enter(env, #1 x, #2 x)) Symbol.empty l

  val base_store = Symbol.empty

end