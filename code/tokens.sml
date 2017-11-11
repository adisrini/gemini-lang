structure Tokens : Gemini_TOKENS =
struct

type linenum = int
type token = string

(* helper functions *)
fun locationToString (a: int, b: int) = "(" ^ Int.toString(a) ^ ", " ^ Int.toString(b) ^ ")"

(******* KEYWORDS *******)
(* declarations *)
fun DATATYPE(a, b) = "DATATYPE @" ^ locationToString(a, b)
fun TYPE(a, b) = "TYPE @" ^ locationToString(a, b)
fun VAL(a, b) = "VAL @" ^ locationToString(a, b)
fun REF(a, b) = "REF @" ^ locationToString(a, b)
fun FUN(a, b) = "FUN @" ^ locationToString(a, b)
fun MODULE(a, b) = "MODULE @" ^ locationToString(a, b)
fun STRUCTURE(a, b) = "STRUCTURE @" ^ locationToString(a, b)
fun STRUCT(a, b) = "STRUCT @" ^ locationToString(a, b)
fun SIGNATURE(a, b) = "SIGNATURE @" ^ locationToString(a, b)
fun SIG(a, b) = "SIG @" ^ locationToString(a, b)
fun LIST(a, b) = "LIST @" ^ locationToString(a, b)
fun SW(a, b) = "SW @" ^ locationToString(a, b)

(* constructs *)
fun LET(a, b) = "LET @" ^ locationToString(a, b)
fun IN(a, b) = "IN @" ^ locationToString(a, b)
fun END(a, b) = "END @" ^ locationToString(a, b)
fun IF(a, b) = "IF @" ^ locationToString(a, b)
fun THEN(a, b) = "THEN @" ^ locationToString(a, b)
fun ELSE(a, b) = "ELSE @" ^ locationToString(a, b)

(* operators *)
fun ORELSE(a, b) = "ORELSE @" ^ locationToString(a, b)
fun ANDALSO(a, b) = "ANDALSO @" ^ locationToString(a, b)
fun NOT(a, b) = "NOT @" ^ locationToString(a, b)

fun PIPE_EQUALS(a, b) = "PIPE_EQUALS @" ^ locationToString(a, b)
fun FAT_ARROW(a, b) = "FAT_ARROW @" ^ locationToString(a, b)
fun THIN_ARROW(a, b) = "THIN_ARROW @" ^ locationToString(a, b)

(* misc *)
fun NIL(a, b) = "NIL @" ^ locationToString(a, b)
fun WITH(a, b) = "WITH @" ^ locationToString(a, b)
fun OF(a, b) = "OF @" ^ locationToString(a, b)
fun OP(a, b) = "OP @" ^ locationToString(a, b)
fun CASE(a, b) = "CASE @" ^ locationToString(a, b)

(******* OPERATORS *******)
(* bitwise *)
fun BIT_NOT(a, b) = "BIT_NOT @" ^ locationToString(a, b)
fun BIT_OR(a, b) = "BIT_OR @" ^ locationToString(a, b)
fun BIT_AND(a, b) = "BIT_AND @" ^ locationToString(a, b)
fun BIT_XOR(a, b) = "BIT_XOR @" ^ locationToString(a, b)
fun BIT_SLL(a, b) = "BIT_SLL @" ^ locationToString(a, b)
fun BIT_SRL(a, b) = "BIT_SRL @" ^ locationToString(a, b)
fun BIT_SRA(a, b) = "BIT_SRA @" ^ locationToString(a, b)

(* comparison *)
fun GE(a, b) = "GE @" ^ locationToString(a, b)
fun GT(a, b) = "GT @" ^ locationToString(a, b)
fun LE(a, b) = "LE @" ^ locationToString(a, b)
fun LT(a, b) = "LT @" ^ locationToString(a, b)
fun NEQ(a, b) = "NEQ @" ^ locationToString(a, b)
fun EQ(a, b) = "EQ @" ^ locationToString(a, b)

(* arithmetic *)
fun INT_DIVIDE(a, b) = "INT_DIVIDE @" ^ locationToString(a, b)
fun INT_TIMES(a, b) = "INT_TIMES @" ^ locationToString(a, b)
fun INT_MINUS(a, b) = "INT_MINUS @" ^ locationToString(a, b)
fun INT_PLUS(a, b) = "INT_PLUS @" ^ locationToString(a, b)
fun INT_MOD(a, b) = "INT_MOD @" ^ locationToString(a, b)
fun REAL_DIVIDE(a, b) = "REAL_DIVIDE @" ^ locationToString(a, b)
fun REAL_TIMES(a, b) = "REAL_TIMES @" ^ locationToString(a, b)
fun REAL_MINUS(a, b) = "REAL_MINUS @" ^ locationToString(a, b)
fun REAL_PLUS(a, b) = "REAL_PLUS @" ^ locationToString(a, b)

(******* GROUPING *******)
fun RBRACE(a, b) = "RBRACE @" ^ locationToString(a, b)
fun LBRACE(a, b) = "LBRACE @" ^ locationToString(a, b)
fun RBRACK(a, b) = "RBRACK @" ^ locationToString(a, b)
fun LBRACK(a, b) = "LBRACK @" ^ locationToString(a, b)
fun RPAREN(a, b) = "RPAREN @" ^ locationToString(a, b)
fun LPAREN(a, b) = "LPAREN @" ^ locationToString(a, b)

(******* MISCELLANEOUS *******)
fun DOT(a, b) = "DOT @" ^ locationToString(a, b)
fun SEMICOLON(a, b) = "SEMICOLON @" ^ locationToString(a, b)
fun COLON(a, b) = "COLON @" ^ locationToString(a, b)
fun COMMA(a, b) = "COMMA @" ^ locationToString(a, b)
fun POUND(a, b) = "POUND @" ^ locationToString(a, b)
fun AT(a, b) = "AT @" ^ locationToString(a, b)
fun TICK(a, b) = "TICK @" ^ locationToString(a, b)
fun ASSIGN(a, b) = "ASSIGN @" ^ locationToString(a, b)
fun BANG(a, b) = "BANG @" ^ locationToString(a, b)
fun BIT_ARRAY(value, a, b) = "BIT_ARRAY @" ^ locationToString(a, b)
fun CONS(a, b) = "CONS @" ^ locationToString(a, b)
fun POUND_TIMES(a, b) = "POUND_TIMES @" ^ locationToString(a, b)

(******* LITERALS *******)
fun INT(value, a, b) = "INT(" ^ Int.toString(value) ^ ") @" ^ locationToString(a, b)
fun REAL(value, a, b) = "REAL(" ^ Real.toString(value) ^ ") @" ^ locationToString(a, b)
fun BIT(value, a, b) = "BIT(" ^ Bit.toString(value) ^ ") @" ^ locationToString(a, b)
fun STRING(value, a, b) = "STRING(" ^ value ^ ") @" ^ locationToString(a, b)
fun ID(id, a, b) = "ID(" ^ id ^ ") @" ^ locationToString(a, b)
fun EOF(a, b) = "EOF @" ^ locationToString(a, b)
end
