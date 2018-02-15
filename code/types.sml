structure Types =
struct

  type tyvar = Symbol.symbol

  datatype ty =
            H_TY of h_ty
          | S_TY of s_ty
          | M_TY of m_ty
          | META of tyvar
          | EMPTY
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

  fun toString(t) =
    let
      fun sty(INT) = "INT"
        | sty(REAL) = "REAL"
        | sty(STRING) = "STRING"
        | sty(ARROW(s1, s2)) = "ARROW(" ^ sty(s1) ^ " -> " ^ sty(s2) ^ ")"
        | sty(LIST(s)) = "LIST(" ^ sty(s) ^ ")"
        | sty(S_META(tyv)) = "S_META(" ^ Symbol.name(tyv) ^ ")"
        | sty(S_TOP) = "S_TOP"
        | sty(S_BOTTOM) = "S_BOTTOM"
        | sty(_) = "STY: UNIMPLEMENTED FOR NOW"

      and hty(h) = "HTY: UNIMPLEMENTED FOR NOW"
      and mty(m) = "MTY: UNIMPLEMENTED FOR NOW"
    in
      case t of
           S_TY(s) => "S_TY(" ^ sty(s) ^ ")"
         | H_TY(h) => "H_TY(" ^ hty(h) ^ ")"
         | M_TY(m) => "M_TY(" ^ mty(m) ^ ")"
         | META(tv) => Symbol.name(tv)
         | EMPTY => "EMPTY"
         | TOP => "TOP"
         | BOTTOM => "BOTTOM"
    end
end
