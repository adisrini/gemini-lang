signature INFER =
sig

  val inferProg: Absyn.exp -> unit

end

structure Infer : INFER =
struct

  fun inferProg exp = ()

end
