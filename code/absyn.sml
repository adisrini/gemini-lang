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

end
