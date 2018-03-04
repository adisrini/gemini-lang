structure Substitute =
struct

  datatype sub = SUB of (Symbol.symbol * Types.ty) option
               | ERROR of {expected: Types.ty, received: Types.ty}

end
