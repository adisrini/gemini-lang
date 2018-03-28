structure SWEvaluate : 
sig
  
  type vstore

  val evalProg : Absyn.exp -> unit
  val evalExp  : vstore * Absyn.exp -> SWValue.value
  val evalDec  : vstore * Absyn.dec -> vstore

end = 
struct

  structure V = SWValue
  structure S = Symbol

  type vstore = V.value S.table

  fun evalProg(prog) = 
    let
      val _ = evalExp(V.base_store, prog)
    in
      ()
    end

  and evalExp(vstore, exp) = V.IntVal 0

  and evalDec(vstore, dec) = vstore
(*

eval(FunDef(params, body), vs) =
  fn(value) => 
    let
        valuestore' = valuestore[params |-> value]
    in
        eval(body, vs')
    end


*)

end