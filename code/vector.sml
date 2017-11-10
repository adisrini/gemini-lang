functor Array (A : ARRAY) =
struct
  open A

  fun toString ba =
    let
      fun arr_to_string xs = foldl (fn(x, acc) => acc ^ Bit.toString(x) ^ ", ") "[" xs
      val temp_string = arr_to_string ba
    in
      String.substring(temp_string, 0, size(temp_string) - 2) ^ "]"
    end

end
