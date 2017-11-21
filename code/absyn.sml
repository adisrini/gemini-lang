structure Absyn =
struct

  type pos = int
  and symbol = Symbol.symbol

  datatype exp = StructsSigsExp of structsig list
          | VarExp of symbol * pos
          | IntExp of int * pos
          | StringExp of string * pos
          | RealExp of real * pos
          | BitExp of GeminiBit.bit * pos
          | ApplyExp of (exp * exp * pos)
          | NilExp of pos
          | BinOpExp of {left: exp, oper: oper, right: exp, pos: pos}
          | UnOpExp of {exp: exp, oper: oper, pos: pos}
          | LetExp of {decs: dec list, body: exp, pos: pos}
          | AssignExp of {lhs: exp, rhs: exp, pos: pos}
          | SeqExp of (exp * pos) list
          | IfExp of {test: exp, then': exp, else': exp option, pos: pos}
          | ListExp of (exp * pos) list
          | ArrayExp of (exp * pos) vector
          | RefExp of exp * pos
          | SWRecordExp of {fields: (symbol * exp * pos) list, pos: pos}
          | HWRecordExp of {fields: (symbol * exp * pos) list, pos: pos}
          | SWExp of exp * pos
          | WithExp of {exp: exp, fields: (symbol * exp * pos) list, pos: pos}
          | DerefExp of {exp: exp, pos: pos}
          | StructAccExp of {name: symbol, field: symbol, pos: pos}
          | RecordAccExp of {exp: exp, field: symbol, pos: pos}
          | ArrayAccExp of {exp: exp, index: exp, pos: pos}
          | PatternMatchExp of {exp: exp, cases: match list, pos: pos}
          | BitArrayExp of {size: exp, result: exp, spec: string option}
          | ZeroExp

  and structsig = StructExp of {name: symbol, signat: (structsig * pos) option, decs: dec list, pos: pos}
                | SigExp of {name: symbol, defs: def list}
                | NamedSigExp of symbol
                | AnonSigExp of def list

  and oper = IntPlusOp | IntMinusOp | IntTimesOp | IntDivideOp | IntModOp
           | RealPlusOp | RealMinusOp | RealTimesOp | RealDivideOp
           | BitNotOp | BitAndOp | BitOrOp | BitXorOp | BitSLLOp | BitSRLOp | BitSRAOp
           | BitDoubleAndOp | BitDoubleOrOp | BitDoubleXorOp
           | BitOrReduceOp | BitAndReduceOp | BitXorReduceOp
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
                      pos: pos} list

  and def = ValDef of {name: symbol, ty: ty * pos, pos: pos}
          | TypeDef of {name: symbol, pos: pos}
          | ModuleDef of {name: symbol, input_ty: ty, output_ty: ty, pos: pos}

  and ty = NameTy of symbol * pos
         | GenericTy of symbol * pos
         | SWRecordTy of field list * pos
         | HWRecordTy of field list * pos
         | ArrayTy of ty * exp * pos
         | ListTy of ty * pos
         | TemporalTy of ty * exp * pos
         | RefTy of ty * pos
         | SWTy of ty * pos
         | FunTy of ty * ty * pos
         | GroupedTy of ty * pos

  and param = NoParam
            | SingleParam of field
            | MultiParams of field list

  withtype field = {name: symbol, ty: ty option, escape: bool ref, pos: pos}

  and fundec = {name: symbol, params: param list, result: (ty * pos) option, body: exp, pos: pos}

  and opdef = {oper: oper, param_a: symbol, param_b: symbol, body: exp, pos: pos}

  and tydec = {name: symbol, ty: ty, opdef: (opdef list) option, pos: pos}

  and moddec = {name: symbol, arg: param, result: (ty * pos) option, body: exp, pos: pos}

  and datacon = {datacon: symbol, ty: ty, pos: pos}

  and datatydec = {name: symbol, datacons: datacon list}

  and match = {match: exp, result: exp, pos: pos}

end
