structure Types =
struct

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty

  and h_ty =
            H_APP of (h_tycon * ty list)
          | H_VAR of Symbol.symbol
          | H_META of Symbol.symbol

  and h_tycon =
            BIT
          | ARRAY of int
          | H_RECORD of (Symbol.symbol * h_ty) list
          | TEMPORAL of int

  and s_ty =
            S_APP of (s_tycon * ty list)
          | S_VAR of Symbol.symbol
          | S_META of Symbol.symbol

  and s_tycon =
            INT | REAL | STRING
          | ARROW
          | LIST
          | SW
          | S_RECORD of (Symbol.symbol * s_ty) list
          | REF of s_ty
          | DATATYPE of {name: Symbol.symbol, cons: (Symbol.symbol * s_ty) list}

  and m_ty =
            MODULE of h_ty * h_ty

end
