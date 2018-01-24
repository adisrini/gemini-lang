structure Types =
struct

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty

  datatype h_ty =
            APP of (h_tycon * ty list)
          | VAR of Symbol.symbol
          | META of Symbol.symbol

  datatype h_tycon =
            BIT
          | ARRAY of int
          | RECORD of (Symbol.symbol * h_ty) list
          | TEMPORAL of int

  datatype s_ty =
            APP of (s_tycon * ty list)
          | VAR of Symbol.symbol
          | META of Symbol.symbol

  datatype s_tycon =
            INT | REAL | STRING
          | ARROW
          | LIST
          | SW
          | RECORD of (Symbol.symbol * s_ty) list
          | REF of s_ty
          | DATATYPE of {name: Symbol.symbol, cons: (Symbol.symbol * s_ty) list}

datatype m_ty =
            MODULE of h_ty * h_ty

end
