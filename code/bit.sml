structure Bit =
struct

  datatype bit = ZERO | ONE

  fun toString b = case b of
    ZERO => "'b0"
  | ONE => "'b1"

  fun toInt b = case b of
    ZERO => 0
  | ONE => 1

  fun fromString s = case s of
    "'b0" => ZERO
  | "'b1" => ONE
  | _ => raise Match

  fun fromInt s = case s of
    0 => ZERO
  | 1 => ONE
  | _ => raise Match

end
