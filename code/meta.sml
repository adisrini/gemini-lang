structure Meta = 
struct

  val metaCount = ref 0

  fun newMeta () =
    let
      val x = !metaCount;
    in
      metaCount := x + 1;
      Symbol.symbol("m" ^ (Int.toString x))
    end

end