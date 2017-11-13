structure Absyn =
struct

  type pos = int
  and symbol = Symbol.symbol

  datatype var = SimpleVar of symbol * pos
               | FieldVar of var * symbol * pos

  and dec = FunctionDec of fundec list
          | TypeDec of tydec list
          | ModuleDec of moddec list
          | DatatypeDec of datatydec list
          | ValDec of {name: symbol,
                       escape: bool ref,
                       ty: (symbol * pos) option,
                       init: exp,
                       pos: pos}

  (* TODO *)
  and exp = VarExp of var * pos
          | IntExp of int * pos
          | StringExp of string * pos
          | RealExp of real * pos
          | BitExp of GeminiBit.bit * pos
          | OpExp of {left: exp, oper: oper, right: exp, pos: pos}
          | IfExp of {test: exp, then': exp, else': exp option, pos: pos}
          | AssignExp of {lhs: exp, rhs: exp, pos: pos}

  and oper = IntPlusOp | IntMinusOp | IntTimesOp | IntDivideOp | IntModOp
           | RealPlusOp | RealMinusOp | RealTimesOp | RealDivideOp
           | BitNotOp | BitAndOp | BitOrOp | BitXorOp | BitSLLOp | BitSRLOp | BitSRAOp
           | EqOp | NeqOp | LtOp | GtOp | LeOp | GeOp

  (* TODO *)
  and fundec = Fundec of unit

  (* TODO *)
  and tydec = Tydec of unit

  (* TODO *)
  and moddec = Moddec of unit

  (* TODO *)
  and datatydec = Datatydec of unit

end
