structure Absyn =
struct

  type pos = int
  and symbol = Symbol.symbol

  datatype var = SimpleVar of symbol * pos
               | FieldVar of var * symbol * pos

  (* TODO *)
  and exp = StructExp of {name: symbol, sigg: (sigg * pos) option, decs: dec list, pos: pos}
          | SigExp of sigg * pos
          | VarExp of var * pos
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
                      ty: (ty * pos) option,
                      init: exp,
                      pos: pos}

  and def = ValDef of {name: symbol, ty: ty * pos, pos: pos}
          | TypeDef of {name: symbol, pos: pos}
          | DatatypeDef of datatydec
          | ModuleDef of {name: symbol, ty: ty * pos, pos: pos}

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

  and param = SingleParam of {name: symbol, ty: ty option, escape: bool ref, pos: pos}
            | MultiParams of {name: symbol, ty: ty option, escape: bool ref, pos: pos} list


  withtype field = {name: symbol, escape: bool ref, ty: ty, pos: pos}

  and sigg = {name: symbol, defs: def list}

  and fundec = {name: symbol, params: param list, result: (ty * pos) option, body: exp, pos: pos}

  and tydec = {name: symbol, ty: ty, pos: pos}

  and moddec = {name: symbol, arg: param, result: (ty * pos) option, body: exp, pos: pos}

  and datatydec = {datacon: symbol, ty: ty, pos: pos} list

end
