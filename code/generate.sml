signature GENERATE = 
sig
  type wire

  val genProg: (string * Value.value * Value.value) -> unit
  val genExp:  Value.value -> (wire * Types.h_ty)
end

structure Generate : GENERATE = 
struct

  structure V = Value
  structure S = Symbol
  structure T = Types

  exception TypeError

  type wire = S.symbol
  type size = int

  val ilist : string list ref = ref []
  type 'a table = 'a IntBinaryMap.map
  val wires : wire list table ref = ref IntBinaryMap.empty

  val count = ref 1

  fun freshWire () =
    let
      val i = !count
      val () = count := i + 1
    in
      S.symbol("r" ^ Int.toString(i))
    end

  fun typeToSize(T.BIT) = 1
    | typeToSize(T.ARRAY{ty, size}) = !size
    | typeToSize(T.H_RECORD vs) = foldl (fn((_, hty), size) => size + typeToSize(hty)) 0 vs
    | typeToSize(_) = raise Match

  fun binOperToString(V.AndOp) = " & "
    | binOperToString(V.OrOp) =  " | "
    | binOperToString(V.XorOp) =   " ^ "
    | binOperToString(V.SLLOp) = " << "
    | binOperToString(V.SRLOp) = " >> "
    | binOperToString(V.SRAOp) = " >>> "

  fun unOperToString(V.NotOp) = "~"
    | unOperToString(V.AndReduceOp) = "&"
    | unOperToString(V.OrReduceOp) = "|"
    | unOperToString(V.XorReduceOp) = "^"

  fun sizeToType(1) = " "
    | sizeToType(n) = " [" ^ (Int.toString(n - 1)) ^ ":0] "

  fun makelist f lst = case lst of 
                              [] => ""
                            | [x] => f x
                            | x::xs => (f x) ^ ", " ^ (makelist f xs)


  fun makeWire(key, value) =
    let
      val value' = case IntBinaryMap.find(!wires, key) of
                        SOME(vs) => value::vs
                      | NONE => [value]
    in
      wires := IntBinaryMap.insert(!wires, key, value')
    end

  fun assign(lhs, rhs) =
    lhs ^ " <= " ^ rhs ^ ";"

  fun getArrayElementType(T.ARRAY{ty, size}) = ty
    | getArrayElementType(_) = raise TypeError

  fun getRecordFieldType(T.H_RECORD fs, field) = #2(valOf(List.find (fn(sym, _) => Symbol.name(sym) = Symbol.name(field)) fs))
    | getRecordFieldType(_) = raise TypeError

  fun getHWType(T.H_TY(h)) = h
    | getHWType(_) = raise TypeError

  fun say s = print(s)

  fun inputsAndOutputs(inputs, output) =
    let
      fun buildInstrings(V.NamedVal(n, ty), acc) = ("input" ^ (sizeToType(typeToSize(getHWType(ty)))) ^ (Symbol.name(n)))::acc
        | buildInstrings(V.HWRecordVal fs, acc) = (foldr (fn((_, v), acc') => buildInstrings(v, acc')) [] fs) @ acc
        | buildInstrings(_) = raise Match (* TODO *)

      val inStrings = buildInstrings(inputs, [])
      val outString = "output reg" ^ (sizeToType(typeToSize(output))) ^ "out"
    in
      makelist (fn(s) => s) (inStrings @ [outString])
    end

  fun genProg(name, args, v) =
    let
      val (outputWire, outputType) = genExp(v)
      val () = ilist := (assign("out", Symbol.name(outputWire)))::(!ilist)
    in
      say("module " ^ name ^ "(" ^ (inputsAndOutputs(args, outputType)) ^ ");\n");
      app (fn(i, ws) => say("\treg" ^ (sizeToType(i)) ^ (makelist Symbol.name ws) ^ ";\n")) (IntBinaryMap.listItemsi(!wires));
      say("\n");
      say("\talways @(*)\n");
      say("\tbegin\n");
      app (fn(s) => say("\t\t" ^ s ^ "\n")) (rev(!ilist));
      say("\tend\n");
      say("endmodule\n")
    end

  and genExp(V.NamedVal(n, ty)) = (n, getHWType(ty))
    | genExp(V.BitVal b) =
      let
        val ret = freshWire()
        val insn = assign(Symbol.name(ret), GeminiBit.toVerilogString(b))
        val () = ilist := insn::(!ilist)
        val () = makeWire(1, ret)
      in
        (ret, T.BIT)
      end
    | genExp(V.ArrayVal vs) =
      let
        val ret = freshWire()
        val arraySize = Vector.length(vs)
        fun foldArrayValue(idx, elem, (acc, ty_opt)) =
          let
            val (elemWire, elemType) = genExp(elem)
            val insn = assign(Symbol.name(ret) ^ "[" ^ (Int.toString(Vector.length(vs) - 1 - idx)) ^ "]", Symbol.name(elemWire))

            val next_ty_opt = case ty_opt of
                                   SOME(_) => ty_opt
                                 | NONE => SOME(elemType)
          in
            (insn::acc, next_ty_opt)
          end
        val (insns, elemTy) = Vector.foldli foldArrayValue ([], NONE) vs
        val () = ilist := insns @ (!ilist)
        val () = makeWire(arraySize, ret)
      in
        (ret, T.ARRAY{ty = valOf(elemTy), size = ref arraySize})
      end
    | genExp(V.ArrayAccVal{arr, index}) =
      let
        val ret = freshWire()
        val (arrWire, arrType) = genExp(arr)
        val elementType = getArrayElementType(arrType)
        val insn = assign(Symbol.name(ret), Symbol.name(arrWire) ^ "[" ^ Int.toString(index) ^ "]")
        val () = ilist := insn::(!ilist)
        val () = makeWire(typeToSize(elementType), ret)
      in
        (ret, elementType)
      end
    | genExp(V.BinOpVal{left, oper, right}) =
      let
        val ret = freshWire()
        val (leftWire,  leftTy)  = genExp(left)
        val (rightWire, rightTy) = genExp(right)
        val insn = assign(Symbol.name(ret), (Symbol.name(leftWire) ^ (binOperToString(oper)) ^ (Symbol.name(rightWire))))
        val unifiedTy = leftTy  (* TODO: unify/typecheck *)
        val () = ilist := insn::(!ilist)
        val () = makeWire(typeToSize(unifiedTy), ret)
      in
        (ret, unifiedTy)
      end
    | genExp(V.UnOpVal{value, oper}) =
      let
        val ret = freshWire()
        val (wire,  valueTy)  = genExp(value)
        val insn = assign(Symbol.name(ret), (unOperToString(oper)) ^ (Symbol.name(wire)))
        val () = ilist := insn::(!ilist)
        val () = makeWire(typeToSize(valueTy), ret)
      in
        (ret, valueTy)
      end
    (*| genExp(V.HWRecordAccVal{record, field}) =
      let
        val ret = freshWire()
        val (recordWire, recordTy) = genExp(record)
        val fieldTy = getRecordFieldType(recordTy, field)
        val insn = assign(Symbol.name(ret), )
        val () = ilist := insn::(!ilist)
        val () = makeWire(typeToSize(fieldTy), ret)
      in
        (ret, fieldTy)
      end*)
    | genExp(V.HWRecordVal vs) =
      let
        val ret = freshWire()
        fun foldField((sym, value), (size, idx)) =
          let
            val (valueWire, valueTy) = genExp(value)
            val valueSize = typeToSize(valueTy)
            val insn = assign(Symbol.name(ret) ^ "[" ^ Int.toString(size) ^ "+:" ^ Int.toString(valueSize) ^ "]", Symbol.name(valueWire))
            val () = ilist := insn::(!ilist)
          in
            (size + valueSize, idx + 1)
          end
        val (totalSize, _) = foldl foldField (0, 0) vs
        val () = makeWire(totalSize, ret)
      in
        (ret, T.ARRAY{ty = T.H_BOTTOM, size = ref totalSize})
      end
    | genExp(_) = raise Match

end