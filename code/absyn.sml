structure Absyn =
struct

  type pos = int
  and symbol = Symbol.symbol

  datatype var = SimpleVar of symbol * pos
               | MemberVar of exp * symbol * pos
               | FieldVar of exp * symbol * pos

  and exp = StructsSigsExp of structsig list
          | VarExp of var * pos
          | IntExp of int * pos
          | StringExp of string * pos
          | RealExp of real * pos
          | BitExp of GeminiBit.bit * pos
          | ApplyExp of (exp * pos) list
          | NilExp of pos
          | OpExp of {left: exp, oper: oper, right: exp, pos: pos}
          | NegExp of {exp: exp, pos: pos}
          | LetExp of {decs: dec list, body: exp, pos: pos}
          | AssignExp of {lhs: exp, rhs: exp, pos: pos}
          | SeqExp of (exp * pos) list
          | IfExp of {test: exp, then': exp, else': exp option, pos: pos}
          | ZeroExp

  and structsig = StructExp of {name: symbol, signat: (structsig * pos) option, decs: dec list, pos: pos}
                | SigExp of {name: symbol, defs: def list}

  and oper = IntPlusOp | IntMinusOp | IntTimesOp | IntDivideOp | IntModOp
           | RealPlusOp | RealMinusOp | RealTimesOp | RealDivideOp
           | BitNotOp | BitAndOp | BitOrOp | BitXorOp | BitSLLOp | BitSRLOp | BitSRAOp
           | EqOp | NeqOp | LtOp | GtOp | LeOp | GeOp
           | ConsOp

  and dec = FunctionDec of fundec list
         | TypeDec of tydec list
         | ModuleDec of moddec list
         | DatatypeDec of datatydec list
         | ValDec of {name: symbol,
                      escape: bool ref,
                      ty: (ty * pos) option,
                      init: exp,
                      pos: pos}

  and def = ValDef of {name: symbol, ty: ty * pos, pos: pos}
          | TypeDef of {name: symbol, pos: pos}
          | DatatypeDef of datatydec
          | ModuleDef of {name: symbol, ty: ty * pos, pos: pos}

  and ty = NameTy of symbol * pos
         | GenericTy of symbol * pos
         | RecordTy of field list * pos
         | ArrayTy of ty * exp * pos
         | ListTy of ty * pos
         | SWTupleTy of ty * ty * pos
         | HWTupleTy of ty * ty * pos
         | TemporalTy of ty * exp * pos
         | RefTy of ty * pos
         | SWTy of ty * pos

  and param = NoParam
            | SingleParam of field
            | MultiParams of field list

  withtype field = {name: symbol, ty: ty option, escape: bool ref, pos: pos}

  and fundec = {name: symbol, params: param list, result: (ty * pos) option, body: exp, pos: pos}

  and tydec = {name: symbol, ty: ty, pos: pos}

  and moddec = {name: symbol, arg: param, result: (ty * pos) option, body: exp, pos: pos}

  and datatydec = {datacon: symbol, ty: ty, pos: pos} list

end
