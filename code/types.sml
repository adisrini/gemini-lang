structure Types =
struct

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty

  datatype h_ty =
            BIT

  datatype s_ty =
            APP of (s_tycon * ty list)
          | VAR of Symbol.symbol
          | POLY of (Symbol.symbol list * s_ty)


  datatype s_tycon =
            INT | REAL | STRING
          | ARROW
          | LIST
          | SW
          | RECORD of (Symbol.symbol * s_ty) list
          | REF of s_ty
          | DATATYPE of {name: Symbol.symbol, cons: (Symbol.symbol * s_ty) list}

end
