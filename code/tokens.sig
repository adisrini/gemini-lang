signature Gemini_TOKENS =
sig
type linenum (* = int *)
type token

(******* KEYWORDS *******)
(* declarations *)
val DATATYPE: linenum * linenum -> token
val TYPE:  linenum * linenum -> token
val VAL:  linenum * linenum -> token
val REF: linenum * linenum -> token
val FUN:  linenum * linenum -> token
val MODULE: linenum * linenum -> token
val STRUCTURE: linenum * linenum -> token
val STRUCT: linenum * linenum -> token
val SIGNATURE: linenum * linenum -> token
val SIG: linenum * linenum -> token
val LIST: linenum * linenum -> token
val SW: linenum * linenum -> token

(* constructs *)
val LET:  linenum * linenum -> token
val IN:  linenum * linenum -> token
val END:  linenum * linenum -> token
val IF:  linenum * linenum -> token
val THEN:  linenum * linenum -> token
val ELSE:  linenum * linenum -> token

(* operators *)
val ORELSE: linenum * linenum -> token
val ANDALSO: linenum * linenum -> token
val NOT: linenum * linenum -> token

(* misc *)
val NIL:  linenum * linenum -> token
val WITH: linenum * linenum -> token
val OF: linenum * linenum -> token
val OP: linenum * linenum -> token
val CASE: linenum * linenum -> token
val AND: linenum * linenum -> token

val PIPE_EQUALS: linenum * linenum -> token
val FAT_ARROW: linenum * linenum -> token
val THIN_ARROW: linenum * linenum -> token

(******* OPERATORS *******)
(* bitwise *)
val BIT_OR_REDUCE: linenum * linenum -> token
val BIT_AND_REDUCE: linenum * linenum -> token
val BIT_XOR_REDUCE: linenum * linenum -> token
val BIT_NOT: linenum * linenum -> token
val BIT_OR:  linenum * linenum -> token
val BIT_AND: linenum * linenum -> token
val BIT_XOR: linenum * linenum -> token
val BIT_SLL: linenum * linenum -> token
val BIT_SRL: linenum * linenum -> token
val BIT_SRA: linenum * linenum -> token

(* comparison *)
val GE:  linenum * linenum -> token
val GT:  linenum * linenum -> token
val LE:  linenum * linenum -> token
val LT:  linenum * linenum -> token
val NEQ:  linenum * linenum -> token
val EQ:  linenum * linenum -> token

(* arithmetic *)
val UMINUS: linenum * linenum -> token
val INT_DIVIDE:  linenum * linenum -> token
val INT_TIMES:  linenum * linenum -> token
val INT_MINUS:  linenum * linenum -> token
val INT_PLUS:  linenum * linenum -> token
val INT_MOD: linenum * linenum -> token
val REAL_DIVIDE: linenum * linenum -> token
val REAL_TIMES: linenum * linenum -> token
val REAL_MINUS: linenum * linenum -> token
val REAL_PLUS: linenum * linenum -> token

(******* GROUPING *******)
val RBRACE:  linenum * linenum -> token
val LBRACE:  linenum * linenum -> token
val RBRACK:  linenum * linenum -> token
val LBRACK:  linenum * linenum -> token
val RPAREN:  linenum * linenum -> token
val LPAREN:  linenum * linenum -> token

(******* MISCELLANEOUS *******)
val DOT:  linenum * linenum -> token
val SEMICOLON:  linenum * linenum -> token
val COLON:  linenum * linenum -> token
val COMMA:  linenum * linenum -> token
val POUND: linenum * linenum -> token
val AT: linenum * linenum -> token
val ASSIGN: linenum * linenum -> token
val BANG: linenum * linenum -> token
val CONS: linenum * linenum -> token
val POUND_TIMES: linenum * linenum -> token

(******* LITERALS *******)
val INT: (int) * linenum * linenum -> token
val REAL: (real) * linenum * linenum -> token
val BIT: (GeminiBit.bit) * linenum * linenum -> token
val STRING: (string) * linenum * linenum -> token
val ID: (string) * linenum * linenum -> token
val TID: (string) * linenum * linenum -> token
val EOF:  linenum * linenum -> token

end
