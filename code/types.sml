structure Types =
struct

  type tyvar = Symbol.symbol

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty

  and h_ty =
            BIT
          | ARRAY of {ty: h_ty, size: int}
          | H_RECORD of (tyvar * h_ty) list
          | TEMPORAL of {ty: h_ty, time: int}
          | H_VAR of tyvar
          | H_POLY of tyvar list * h_ty
          | H_UNPOLY of h_ty * h_ty list
          | H_META of tyvar

  and s_ty =
            INT | REAL | STRING
          | ARROW of (s_ty * s_ty)
          | LIST of s_ty
          | SW of h_ty
          | S_RECORD of (tyvar * s_ty) list
          | REF of s_ty
          | DATATYPE of (tyvar * s_ty) list * unit ref
          | S_VAR of tyvar
          | S_POLY of tyvar list * s_ty
          | S_UNPOLY of s_ty * s_ty list
          | S_META of tyvar

  (* datatype 'a tree = NODE of 'a | LEAF
  tree -> POLY(a, DATATYPE({'a tree, [NODE, META a)]'})) *)

  and m_ty =
            MODULE of h_ty * h_ty

end
