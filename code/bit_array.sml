structure BitArray =
struct

  type bit_array = Bit.bit vector

  fun toString ba = GeminiArray.toString ba Bit.toString

  fun toList ba = Vector.foldl (fn(x, acc) => x::acc) [] ba

  (* TODO: exception handling *)
  fun zeroExtend ba len =
    let
      fun helper 0 acc = acc
        | helper n acc = helper (n - 1) (Bit.ZERO::acc)
    in
      Vector.fromList(helper (len - Vector.length(ba)) (toList(ba)))
    end

  (* TODO: exception handling *)
  fun fromUnsignedInt num len =
    let
      fun helper 0 acc = acc
        | helper num acc = helper (num div 2) (num mod 2 :: acc)
    in
      zeroExtend (Vector.fromList(map Bit.fromInt (helper num []))) len
    end

  (* TODO: exception handling *)
  fun fromSignedInt num len =
    if num < 0
    then
      let
        val unsigned = fromUnsignedInt (~num) len
        val flip = Vector.map Bit.notb unsigned
        fun add1 vec 0   ci acc = acc
          | add1 vec idx ci acc = let
                                    val (sum, co) = Bit.add ci (Vector.sub(vec, idx))
                                  in
                                    add1 vec (idx - 1) co (sum::acc)
                                  end
      in
        Vector.fromList(add1 flip (Vector.length(flip) - 1) Bit.ONE [])
      end
    else fromUnsignedInt num len

  (* TODO *)
  fun fromReal num mantissa exponent = #[]

end
