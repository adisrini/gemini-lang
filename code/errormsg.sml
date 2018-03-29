signature ERRORMSG =
sig
    val anyErrors : bool ref
    val fileName : string ref
    val lineNum : int ref
    val linePos : int list ref
    val sourceStream : TextIO.instream ref
    val error : int -> string -> unit
    val warning : int -> string -> unit
    val runtime : int -> string -> unit
    val typeNumArgsError: (int * string * int * int) -> unit
    exception Error
    val impossible : string -> 'a   (* raises Error *)
    val reset : unit -> unit
end

structure ErrorMsg : ERRORMSG =
struct

  val anyErrors = ref false
  val fileName = ref ""
  val lineNum = ref 1
  val linePos = ref [1]
  val sourceStream = ref TextIO.stdIn

  fun reset() = (anyErrors:=false;
		 fileName:="";
		 lineNum:=1;
		 linePos:=[1];
		 sourceStream:=TextIO.stdIn)

  exception Error

  fun display msgtype pos (msg:string) =
    let fun look(a::rest,n) =
    if a<pos then app print [":",
               Int.toString n,
               ".",
               Int.toString (pos-a)]
           else look(rest,n-1)
      | look _ = print "0.0"
       in anyErrors := true;
    print (!fileName);
    look(!linePos,!lineNum);
    print ":[";
    print msgtype;
    print "]:";
    print msg;
    print "\n"
      end

  fun error pos (msg:string) = display "error" pos msg

  fun warning pos (msg:string) = display "warning" pos msg
      
  fun runtime pos (msg:string) = display "runtime" pos msg

  fun typeNumArgsError(pos, name, given, wants) =
    error pos ("type constructor " ^ (case String.size(name) of 0 => "" | _ => ("\"" ^ name ^ "\" ")) ^ "given " ^ Int.toString(given) ^ " arguments, wants " ^ Int.toString(wants))

  fun impossible msg =
      (app print ["Error: Compiler bug: ",msg,"\n"];
       TextIO.flushOut TextIO.stdOut;
       raise Error)

end  (* structure ErrorMsg *)
