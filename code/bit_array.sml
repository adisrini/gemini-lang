functor GeminiBitArray(V: VECTOR) =
struct
  open V

  type bit_array = GeminiBit.bit vector

  fun toString ba = GeminiArray.toString ba GeminiBit.toString

  fun toList ba = Vector.foldr (fn(x, acc) => x::acc) [] ba

  fun zeroExtend ba len pos =
    let
      val () = if(len < Vector.length(ba))
               then ErrorMsg.warning pos "information loss due to cutoff"
               else ()

      fun helper n acc = if n = len
                         then acc
                         else if n >= Vector.length(ba)
                              then (helper (n + 1) (GeminiBit.ZERO::acc))
                              else (helper (n + 1) (Vector.sub(ba, Vector.length(ba) - n - 1)::acc))
    in
      Vector.fromList(helper 0 [])
    end

  fun fromUnsignedInt num len pos =
    let
      fun helper 0 acc = acc
        | helper num acc = helper (num div 2) (num mod 2 :: acc)
    in
      if num < 0
      then (ErrorMsg.error pos "cannot convert signed integer using unsigned semantics"; #[])
      else zeroExtend (Vector.fromList(List.map GeminiBit.fromInt (helper num []))) len pos
    end

  (* TODO: exception handling *)
  fun fromSignedInt num len pos =
    if num < 0
    then
      let
        val unsigned = fromUnsignedInt (~num) len pos
        val flip = Vector.map GeminiBit.notb unsigned
        fun add1 vec ~1   ci acc = acc
          | add1 vec idx ci acc = let
                                    val (sum, co) = GeminiBit.add ci (Vector.sub(vec, idx))
                                  in
                                    add1 vec (idx - 1) co (sum::acc)
                                  end
      in
        Vector.fromList(add1 flip (Vector.length(flip) - 1) GeminiBit.ONE [])
      end
    else fromUnsignedInt num len pos

  (* TODO *)
  fun fromReal num mantissa exponent = #[]

end
