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

  datatype s_tycon =
            INT
          | REAL
          | ARROW
          | LIST
          | SW
          | RECORD of (Symbol.symbol * ty) list
          | TYFUN of ...
          | UNIQUE of (tycon * ???)

end
