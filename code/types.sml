structure Types =
struct

  type tyvar = Symbol.symbol

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty
          | META of tyvar
          | TOP
          | BOTTOM

  and h_ty =
            BIT
          | ARRAY of {ty: h_ty, size: int ref}    (* type of size? default to max int/-1 *)
          | H_RECORD of (tyvar * h_ty) list
          | TEMPORAL of {ty: h_ty, time: int ref} (* type of time? default to max int/-1 *)
          | H_VAR of tyvar
          | H_POLY of tyvar list * h_ty
          | H_UNPOLY of h_ty * h_ty list
          | H_META of tyvar
          | H_TOP
          | H_BOTTOM

  and s_ty =
            INT | REAL | STRING
          | ARROW of (s_ty * s_ty)
          | LIST of s_ty
          | SW_H of h_ty
          | SW_M of m_ty
          | S_RECORD of (tyvar * s_ty) list
          | REF of s_ty
          | DATATYPE of (tyvar * s_ty option) list * unit ref
          | S_VAR of tyvar
          | S_POLY of tyvar list * s_ty
          | S_UNPOLY of s_ty * s_ty list
          | S_META of tyvar
          | S_TOP
          | S_BOTTOM

  (* datatype 'a tree = NODE of 'a | LEAF
  tree -> POLY(a, DATATYPE([(NODE, SOME(META a)), (LEAF, NONE)], ref ())) *)

  and m_ty =
            MODULE of h_ty * h_ty

end
