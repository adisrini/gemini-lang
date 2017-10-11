signature GEMINI_TOKENS =
sig
type pos (* int *)
type location (* pos * pos *)
type bit
type token

(******* KEYWORDS *******)
(* declarations *)
val DATATYPE: location -> token
val TYPE:  location -> token
val VAL:  location -> token
val FUN:  location -> token
val MODULE: location -> token
val STRUCTURE: location -> token
val STRUCT: location -> token
val SIGNATURE: location -> token
val SIG: location -> token

(* structures *)
val LET:  location -> token
val IN:  location -> token
val END:  location -> token
val IF:  location -> token
val THEN:  location -> token
val ELSE:  location -> token

(* operators *)
val ORELSE: location -> token
val ANDALSO: location -> token
val NOT: location -> token

(* misc *)
val NIL:  location -> token
val WITH: location -> token
val OF: location -> token
val OP: location -> token

(******* OPERATORS *******)
(* bitwise *)
val BIT_NOT: location -> token
val BIT_OR:  location -> token
val BIT_AND: location -> token
val BIT_XOR: location -> token
val BIT_SLL: location -> token
val BIT_SRL: location -> token
val BIT_SRA: location -> token

(* comparison *)
val GE:  location -> token
val GT:  location -> token
val LE:  location -> token
val LT:  location -> token
val NEQ:  location -> token
val EQ:  location -> token

(* arithmetic *)
val INT_DIVIDE:  location -> token
val INT_TIMES:  location -> token
val INT_MINUS:  location -> token
val INT_PLUS:  location -> token
val INT_MOD: location -> token
val FLOAT_DIVIDE: location -> token
val FLOAT_TIMES: location -> token
val FLOAT_MINUS: location -> token
val FLOAT_PLUS: location -> token

(******* GROUPING *******)
val RBRACE:  location -> token
val LBRACE:  location -> token
val RBRACK:  location -> token
val LBRACK:  location -> token
val RPAREN:  location -> token
val LPAREN:  location -> token

(******* MISCELLANEOUS *******)
val DOT:  location -> token
val SEMICOLON:  location -> token
val COLON:  location -> token
val COMMA:  location -> token
val POUND: location -> token
val AT: location -> token
val TICK: location -> token

(******* LITERALS *******)
val INT: (int) *  location -> token
val FLOAT: (real) * location -> token
val BIT: (bit) * location -> token
val ID: (string) *  location -> token
val EOF:  location -> token

end
