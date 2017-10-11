structure Tokens : GEMINI_TOKENS =
struct

type pos = int
type location = pos * pos
type token = string

(* helper functions *)
fun locationToString (loc: location) = "(" ^ Int.toString(#1 loc) ^ ", " ^ Int.toString(#2 loc) ^ ")"

(******* KEYWORDS *******)
(* declarations *)
fun DATATYPE(loc) = "DATATYPE @" ^ locationToString(loc)
fun TYPE(loc) = "TYPE @" ^ locationToString(loc)
fun VAL(loc) = "VAL @" ^ locationToString(loc)
fun REF(loc) = "REF @" ^ locationToString(loc)
fun FUN(loc) = "FUN @" ^ locationToString(loc)
fun MODULE(loc) = "MODULE @" ^ locationToString(loc)
fun STRUCTURE(loc) = "STRUCTURE @" ^ locationToString(loc)
fun STRUCT(loc) = "STRUCT @" ^ locationToString(loc)
fun SIGNATURE(loc) = "SIGNATURE @" ^ locationToString(loc)
fun SIG(loc) = "SIG @" ^ locationToString(loc)

(* constructs *)
fun LET(loc) = "LET @" ^ locationToString(loc)
fun IN(loc) = "IN @" ^ locationToString(loc)
fun END(loc) = "END @" ^ locationToString(loc)
fun IF(loc) = "IF @" ^ locationToString(loc)
fun THEN(loc) = "THEN @" ^ locationToString(loc)
fun ELSE(loc) = "ELSE @" ^ locationToString(loc)

(* operators *)
fun ORELSE(loc) = "ORELSE @" ^ locationToString(loc)
fun ANDALSO(loc) = "ANDALSO @" ^ locationToString(loc)
fun NOT(loc) = "NOT @" ^ locationToString(loc)

(* misc *)
fun NIL(loc) = "NIL @" ^ locationToString(loc)
fun WITH(loc) = "WITH @" ^ locationToString(loc)
fun OF(loc) = "OF @" ^ locationToString(loc)
fun OP(loc) = "OP @" ^ locationToString(loc)

(******* OPERATORS *******)
(* bitwise *)
fun BIT_NOT(loc) = "BIT_NOT @" ^ locationToString(loc)
fun BIT_OR(loc) = "BIT_OR @" ^ locationToString(loc)
fun BIT_AND(loc) = "BIT_AND @" ^ locationToString(loc)
fun BIT_XOR(loc) = "BIT_XOR @" ^ locationToString(loc)
fun BIT_SLL(loc) = "BIT_SLL @" ^ locationToString(loc)
fun BIT_SRL(loc) = "BIT_SRL @" ^ locationToString(loc)
fun BIT_SRA(loc) = "BIT_SRA @" ^ locationToString(loc)

(* comparison *)
fun GE(loc) = "GE @" ^ locationToString(loc)
fun GT(loc) = "GT @" ^ locationToString(loc)
fun LE(loc) = "LE @" ^ locationToString(loc)
fun LT(loc) = "LT @" ^ locationToString(loc)
fun NEQ(loc) = "NEQ @" ^ locationToString(loc)
fun EQ(loc) = "EQ @" ^ locationToString(loc)

(* arithmetic *)
fun INT_DIVIDE(loc) = "INT_DIVIDE @" ^ locationToString(loc)
fun INT_TIMES(loc) = "INT_TIMES @" ^ locationToString(loc)
fun INT_MINUS(loc) = "INT_MINUS @" ^ locationToString(loc)
fun INT_PLUS(loc) = "INT_PLUS @" ^ locationToString(loc)
fun INT_MOD(loc) = "INT_MOD @" ^ locationToString(loc)
fun REAL_DIVIDE(loc) = "REAL_DIVIDE @" ^ locationToString(loc)
fun REAL_TIMES(loc) = "REAL_TIMES @" ^ locationToString(loc)
fun REAL_MINUS(loc) = "REAL_MINUS @" ^ locationToString(loc)
fun REAL_PLUS(loc) = "REAL_PLUS @" ^ locationToString(loc)

(******* GROUPING *******)
fun RBRACE(loc) = "RBRACE @" ^ locationToString(loc)
fun LBRACE(loc) = "LBRACE @" ^ locationToString(loc)
fun RBRACK(loc) = "RBRACK @" ^ locationToString(loc)
fun LBRACK(loc) = "LBRACK @" ^ locationToString(loc)
fun RPAREN(loc) = "RPAREN @" ^ locationToString(loc)
fun LPAREN(loc) = "LPAREN @" ^ locationToString(loc)

(******* MISCELLANEOUS *******)
fun DOT(loc) = "DOT @" ^ locationToString(loc)
fun SEMICOLON(loc) = "SEMICOLON @" ^ locationToString(loc)
fun COLON(loc) = "COLON @" ^ locationToString(loc)
fun COMMA(loc) = "COMMA @" ^ locationToString(loc)
fun POUND(loc) = "POUND @" ^ locationToString(loc)
fun AT(loc) = "AT @" ^ locationToString(loc)
fun TICK(loc) = "TICK @" ^ locationToString(loc)
fun ASSIGN(loc) = "ASSIGN @" ^ locationToString(loc)

(******* LITERALS *******)
fun INT(value, loc) = "INT(" ^ Int.toString(value) ^ ") @" ^ locationToString(loc)
fun REAL(value, loc) = "REAL(" ^ Real.toString(value) ^ ") @" ^ locationToString(loc)
fun BIT(value, loc) = "BIT(" ^ Int.toString(Bit.toInt(value)) ^ ") @" ^ locationToString(loc)
fun STRING(value, loc) = "STRING(" ^ value ^ ") @" ^ locationToString(loc)
fun ID(id, loc) = "ID(" ^ id ^ ") @" ^ locationToString(loc)
fun EOF(loc) = "EOF @" ^ locationToString(loc)
end
