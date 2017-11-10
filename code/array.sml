structure GeminiArray =
struct

  fun toString arr f =
    let
      val sep = ", "
      fun arrToString xs = Vector.foldl (fn(x, acc) => acc ^ f(x) ^ sep) "#[" xs
      val tempString = arrToString arr
    in
      String.substring(tempString, 0, size(tempString) - size(sep)) ^ "]"
    end

end
