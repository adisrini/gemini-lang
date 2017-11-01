structure Bit =
struct

  datatype bit = ZERO | ONE

  fun toString b = case b of
    ZERO => "'b:0"
  | ONE => "'b:1"

  fun toInt b = case b of
    ZERO => 0
  | ONE => 1

  fun fromString s = case s of
    "'b:0" => ZERO
  | "'b:1" => ONE
  | _ => raise Match

  fun fromInt s = case s of
    0 => ZERO
  | 1 => ONE
  | _ => raise Match

end
