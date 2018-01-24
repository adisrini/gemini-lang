structure Types =
struct

(* todo: pull out Symbol.symbol into type tyvar *)

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
            S_APP of (s_tycon * ty list) (* remove this and replace with tycons and arguments *)
          | S_VAR of Symbol.symbol
          | S_POLY of Symbol.symbol list * s_ty
          | S_UNPOLY of s_ty * s_ty list
          | S_META of Symbol.symbol

  and s_tycon =
            INT | REAL | STRING
          | ARROW
          | LIST
          | SW
          | S_RECORD of (Symbol.symbol * s_ty) list
          | REF
          | DATATYPE of (Symbol.symbol * s_ty) list * unit ref

  datatype 'a tree = NODE of 'a | LEAF
tree -> POLY(a, DATATYPE({'a tree, [NODE, META a)]'}))

  and m_ty =
            MODULE of h_ty * h_ty

end
