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
          | H_DATATYPE of (tyvar * h_ty option) list * unit ref
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
          | S_DATATYPE of (tyvar * s_ty option) list * unit ref
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
        | sty(SW_H(h)) = "SW_H(" ^ hty(h) ^ ")"
        | sty(SW_M(m)) = "SW_M(" ^ mty(m) ^ ")"
        | sty(S_RECORD(fs)) = "S_RECORD(" ^ (String.concat(map (fn(tyv, s) => Symbol.name(tyv) ^ ": " ^ sty(s) ^ ", ") fs)) ^ ")"
        | sty(REF(s)) = "REF(" ^ sty(s) ^ ")"
        | sty(S_DATATYPE(fs, _)) =
          let
            fun stringify(tyv, s_opt) =
              let
                val tyvStr = Symbol.name(tyv)
                val s_optStr = case s_opt of SOME(s) => "SOME(" ^ sty(s) ^ ")" | NONE => "NONE"
              in
                tyvStr ^ ": " ^ s_optStr ^ ", "
              end
          in
            "S_DATATYPE(" ^ (String.concat(map stringify fs)) ^ ")"
          end
        | sty(S_META(tyv)) = "S_META(" ^ Symbol.name(tyv) ^ ")"
        | sty(S_TOP) = "S_TOP"
        | sty(S_BOTTOM) = "S_BOTTOM"
        | sty(S_POLY(tyvars, s)) = "S_POLY([" ^ (String.concat(map (fn(tyv) => Symbol.name(tyv) ^ ", ") tyvars)) ^ "], " ^ sty(s) ^ ")"
        | sty(S_UNPOLY(s, args)) = "S_UNPOLY(" ^ sty(s) ^ ", [" ^ (String.concat(map (fn(si) => sty(si) ^ ", ") args)) ^ "])"

      and hty(BIT) = "BIT"
        | hty(ARRAY{ty, size}) = "ARRAY(" ^ hty(ty) ^ ", " ^ Int.toString(!size) ^ ")"
        | hty(H_RECORD(fs)) = "H_RECORD(" ^ (String.concat(map (fn(tyv, h) => Symbol.name(tyv) ^ ": " ^ hty(h) ^ ", ") fs)) ^ ")"
        | hty(TEMPORAL{ty, time}) = "TEMPORAL(" ^ hty(ty) ^ ", " ^ Int.toString(!time) ^ ")"
        | hty(H_DATATYPE(fs, _)) =
          let
            fun stringify(tyv, h_opt) =
              let
                val tyvStr = Symbol.name(tyv)
                val h_optStr = case h_opt of SOME(h) => "SOME(" ^ hty(h) ^ ")" | NONE => "NONE"
              in
                tyvStr ^ ": " ^ h_optStr ^ ", "
              end
          in
            "H_DATATYPE(" ^ (String.concat(map stringify fs)) ^ ")"
          end
        | hty(H_POLY(tyvars, h)) = "H_POLY([" ^ (String.concat(map (fn(tyv) => Symbol.name(tyv) ^ ", ") tyvars)) ^ "], " ^ hty(h) ^ ")"
        | hty(H_UNPOLY(h, args)) = "H_UNPOLY(" ^ hty(h) ^ ", [" ^ (String.concat(map (fn(hi) => hty(hi) ^ ", ") args)) ^ "])"
        | hty(H_META(tyv)) = "H_META(" ^ Symbol.name(tyv) ^ ")"
        | hty(H_TOP) = "H_TOP"
        | hty(H_BOTTOM) = "H_BOTTOM"

      and mty(m) = "MTY: UNIMPLEMENTED FOR NOW"
    in
      case t of
           S_TY(s) => "S_TY(" ^ sty(s) ^ ")"
         | H_TY(h) => "H_TY(" ^ hty(h) ^ ")"
         | M_TY(m) => "M_TY(" ^ mty(m) ^ ")"
         | META(tv) => "META(" ^ Symbol.name(tv) ^ ")"
         | EMPTY => "EMPTY"
         | TOP => "TOP"
         | BOTTOM => "BOTTOM"
    end

end
