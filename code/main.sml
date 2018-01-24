signature MAIN =
sig
  val go : string -> unit
end

structure Main : MAIN =
struct

  fun go filename =
    let
      val ast = Parse.parse filename
    in
      Infer.inferProg ast;
      ()
    end

end
