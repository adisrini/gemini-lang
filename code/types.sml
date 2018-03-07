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
      fun dolist(f, [a], _, str) = str ^ (f(a))
        | dolist(f, (a::r), sep, str) = dolist(f, r, sep, (str ^ (f(a)) ^ sep))
        | dolist(_, nil, _, str) = str
      and toRecordString(fs) =
        let
          fun isTuple(_, false) = false
            | isTuple([], b) = b
            | isTuple((sym, _)::fs, true) = isTuple(fs, isSome(Int.fromString(Symbol.name(sym))))
        in
          if isTuple(fs, true)
          then dolist((fn(_, ty) => sty(ty)), fs, " * ", "")
          else "{" ^ (dolist((fn(sym, ty) => Symbol.name(sym) ^ ": " ^ sty(ty)), fs, ", ", "")) ^ "}"
        end
      and sty(INT) = "int"
        | sty(REAL) = "real"
        | sty(STRING) = "string"
        | sty(ARROW(s1, s2)) = sty(s1) ^ " -> " ^ sty(s2)
        | sty(LIST(s)) = sty(s) ^ " list"
        | sty(SW_H(h)) = hty(h) ^ " sw"
        | sty(SW_M(m)) = mty(m) ^ " sw"
        | sty(S_RECORD([])) = "unit"
        | sty(S_RECORD(fs)) = toRecordString(fs)
        | sty(REF(s)) = sty(s) ^ " ref"
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
        | sty(S_META(tyv)) = "'sw" ^ Symbol.name(tyv)
        | sty(S_TOP) = "sw_top"
        | sty(S_BOTTOM) = "sw_bottom"
        | sty(S_POLY(tyvars, s)) = "S_POLY([" ^ (String.concat(map (fn(tyv) => Symbol.name(tyv) ^ ", ") tyvars)) ^ "], " ^ sty(s) ^ ")"
        | sty(S_UNPOLY(s, args)) = "S_UNPOLY(" ^ sty(s) ^ ", [" ^ (String.concat(map (fn(si) => sty(si) ^ ", ") args)) ^ "])"

      and hty(BIT) = "bit"
        | hty(ARRAY{ty, size}) = hty(ty) ^ "[" ^ Int.toString(!size) ^ "]"
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
        | hty(H_META(tyv)) = "'hwm" ^ Symbol.name(tyv)
        | hty(H_TOP) = "hw_top"
        | hty(H_BOTTOM) = "h_bottom"

      and mty(m) = "MTY: UNIMPLEMENTED FOR NOW"
    in
      case t of
           S_TY(s) => sty(s)
         | H_TY(h) => hty(h)
         | M_TY(m) => mty(m)
         | META(tv) => Symbol.name(tv)
         | EMPTY => "empty"
         | TOP => "top"
         | BOTTOM => "bottom"
    end

end
