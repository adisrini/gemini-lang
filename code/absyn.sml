structure Absyn =
struct

  type pos = int
  and symbol = Symbol.symbol

  datatype var = SimpleVar of symbol * pos
               | FieldVar of var * symbol * pos

  (* TODO *)
  and exp = VarExp of var * pos
          | IntExp of int * pos
          | StringExp of string * pos
          | RealExp of real * pos
          | BitExp of GeminiBit.bit * pos
          | ApplyExp of (exp * pos) list
          | OpExp of {left: exp, oper: oper, right: exp, pos: pos}
          | LetExp of {decs: dec list, body: exp, pos: pos}
          | AssignExp of {lhs: exp, rhs: exp, pos: pos}
          | SeqExp of (exp * pos) list
          | IfExp of {test: exp, then': exp, else': exp option, pos: pos}

  and oper = IntPlusOp | IntMinusOp | IntTimesOp | IntDivideOp | IntModOp
           | RealPlusOp | RealMinusOp | RealTimesOp | RealDivideOp
           | BitNotOp | BitAndOp | BitOrOp | BitXorOp | BitSLLOp | BitSRLOp | BitSRAOp
           | EqOp | NeqOp | LtOp | GtOp | LeOp | GeOp

 and dec = FunctionDec of fundec list
         | TypeDec of tydec list
         | ModuleDec of moddec list
         | DatatypeDec of datatydec list
         | ValDec of {name: symbol,
                      escape: bool ref,
                      ty: (symbol * pos) option,
                      init: exp,
                      pos: pos}

  and ty = NameTy of symbol * pos
         | GenericTy of symbol * pos
         | RecordTy of field list
         | ArrayTy of ty * int
         | ListTy of ty
         | SWTupleTy of ty * ty
         | HWTupleTy of ty * ty
         | TemporalTy of ty * int
         | RefTy of ty
         | SWTy of ty

  (* TODO *)
  and fundec = Fundec of unit

  (* TODO *)
  and tydec = Tydec of unit

  (* TODO *)
  and moddec = Moddec of unit

  (* TODO *)
  and datatydec = Datatydec of unit

end
