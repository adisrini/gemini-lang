structure BitArray =
struct

  fun toString ba =
    let
      fun list_to_string xs = foldl (fn(x, acc) => acc ^ Bit.toString(x) ^ ", ") "[" xs
      val temp_string = list_to_string ba
    in
      String.substring(temp_string, 0, size(temp_string) - 2) ^ "]"
    end

  (* TODO *)
  fun fromUnsignedInt ui = #[]

  (* TODO *)
  fun fromSignedInt si = #[]

  (* TODO *)
  fun fromReal fp = #[]

end
