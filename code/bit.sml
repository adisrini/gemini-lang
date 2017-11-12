structure GeminiBit =
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

  fun notb b = case b of
    ZERO => ONE
  | ONE => ZERO

  fun andb b1 b2 =
    if b1 = ONE andalso b2 = ONE
    then ONE
    else ZERO

  fun orb b1 b2 =
    if b1 = ONE orelse b2 = ONE
    then ONE
    else ZERO

  fun xorb b1 b2 =
    if b1 = b2
    then ZERO
    else ONE

  fun add b1 b2 = (xorb b1 b2, andb b1 b2)

end
