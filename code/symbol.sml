signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val look  : 'a table * symbol -> 'a option
  val list  : 'a table -> (symbol * 'a) list
  val print : TextIO.outstream * 'a table * ('a -> string) -> unit
end

structure Symbol :> SYMBOL =
struct

  type symbol = string * int

  structure H = HashTable

  exception Symbol
  val nextsym = ref 0
  val sizeHint = 128
  val hashtable : (string,int) H.hash_table =
		H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)
  val revHashtable : (int,string) H.hash_table =
    H.mkTable(Word.fromInt, op =) (sizeHint,Symbol)

  fun symbol name =
      case H.find hashtable name
       of SOME i => (name,i)
        | NONE => let val i = !nextsym
	           in nextsym := i+1;
		      H.insert hashtable (name,i);
          H.insert revHashtable (i,name);
		      (name,i)
		  end

  fun name(s,n) = s

  structure Table = IntMapTable(type key = symbol
				fun getInt(s,n) = n)

  type 'a table= 'a Table.table
  val empty = Table.empty
  val enter = Table.enter
  val look = Table.look
  fun list x =
    let
      fun mapItems [] = []
        | mapItems ((i, x)::xs) =
          (case H.find revHashtable i of
                SOME(s) => (symbol(s), x)::mapItems(xs)
              | NONE => mapItems(xs))
    in
      mapItems (Table.list(x))
    end

  fun print(outstream, env, str) =
    let
      val items = list(env)
      fun pr(k, v) = TextIO.output(outstream, name(k) ^ ": " ^ (str(v)) ^ "\n")
    in
      app pr items
    end
end
