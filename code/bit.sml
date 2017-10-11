structure Bit =
struct

  datatype bit = ZERO | ONE

  fun toString b = case b of
    ZERO => "'b0"
  | ONE => "'b1"

end
