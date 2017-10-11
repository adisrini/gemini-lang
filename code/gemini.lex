type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val netCommentBalance     = ref 0
val stringLiteralClosed   = ref true
val buffer                = ref ""
val stringStartPosition   = ref 0

fun asciiCode str = let val num = valOf (Int.fromString str) in
  Char.toString (Char.chr num) end

fun convertControlCharacter char = let val num = (Char.ord (List.nth(String.explode char, 0))) - 64 in
  asciiCode (Int.toString num) end

fun count f x = foldr (fn (a, b) => if f a then (b+1) else b) 0 x

fun escape "\\\"" = "\""
  | escape "\\n"  = "\n"
  | escape "\\t"  = "\t"
  | escape "\\\\" = "\\"
  | escape x      = x

fun eof() = let val pos = hd(!linePos) in
  if(!netCommentBalance <> 0) then ErrorMsg.error pos ("SyntaxError: Unclosed comment.")
  else if (!stringLiteralClosed = false) then ErrorMsg.error pos ("SyntaxError: Unclosed string literal.")
  else ();
  ErrorMsg.lineNum := 1;
  netCommentBalance := 0;
  stringLiteralClosed := true;
  stringStartPosition := 0;
  buffer := "";
  ErrorMsg.reset();
  Tokens.EOF(pos,pos) end


%%
%s STRING COMMENT;
%%

<INITIAL, COMMENT>\n                           => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL, COMMENT>[ \b\r\t]+                   => (continue());

// declarations
<INITIAL>"datatype"  	                         => (Tokens.DATATYPE(yypos, yypos + 8));
<INITIAL>"type"  	                             => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL>"val"  	                             => (Tokens.VAL(yypos, yypos + 3));
<INITIAL>"ref"  	                             => (Tokens.REF(yypos, yypos + 3));
<INITIAL>"fun"  	                             => (Tokens.FUN(yypos, yypos + 3));
<INITIAL>"module"  	                           => (Tokens.MODULE(yypos, yypos + 6));
<INITIAL>"structure"  	                       => (Tokens.STRUCTURE(yypos, yypos + 9));
<INITIAL>"struct"  	                           => (Tokens.STRUCT(yypos, yypos + 6));
<INITIAL>"signature"  	                       => (Tokens.SIGNATURE(yypos, yypos + 9));
<INITIAL>"sig"  	                             => (Tokens.SIG(yypos, yypos + 3));

// constructs
<INITIAL>"let"  	                             => (Tokens.LET(yypos, yypos + 3));
<INITIAL>"in"  	                               => (Tokens.IN(yypos, yypos + 2));
<INITIAL>"end"  	                             => (Tokens.END(yypos, yypos + 3));
<INITIAL>"if"  	                               => (Tokens.IF(yypos, yypos + 2));
<INITIAL>"then"  	                             => (Tokens.THEN(yypos, yypos + 4));
<INITIAL>"else"  	                             => (Tokens.ELSE(yypos, yypos + 4));

// operator keywords
<INITIAL>"orelse"  	                           => (Tokens.ORELSE(yypos, yypos + 6));
<INITIAL>"andalso"  	                         => (Tokens.ANDALSO(yypos, yypos + 7));
<INITIAL>"not"  	                             => (Tokens.NOT(yypos, yypos + 3));

// misc keywords
<INITIAL>"nil"  	                             => (Tokens.NIL(yypos, yypos + 3));
<INITIAL>"with"  	                             => (Tokens.WITH(yypos, yypos + 4));
<INITIAL>"of"  	                               => (Tokens.OF(yypos, yypos + 2));
<INITIAL>"op"  	                               => (Tokens.OP(yypos, yypos + 2));

// bitwise operators

<INITIAL>","	                                 => (Tokens.COMMA(yypos,yypos+1));
<INITIAL>"+"                                   => (Tokens.PLUS(yypos,yypos+1));
<INITIAL>"-"                                   => (Tokens.MINUS(yypos,yypos+1));
<INITIAL>"*"                                   => (Tokens.TIMES(yypos,yypos+1));
<INITIAL>"/"                                   => (Tokens.DIVIDE(yypos,yypos+1));
<INITIAL>"["                                   => (Tokens.LBRACK(yypos,yypos+1));
<INITIAL>"]"                                   => (Tokens.RBRACK(yypos,yypos+1));
<INITIAL>"."                                   => (Tokens.DOT(yypos,yypos+1));
<INITIAL>":="                                  => (Tokens.ASSIGN(yypos,yypos+2));
<INITIAL>":"                                   => (Tokens.COLON(yypos,yypos+1));
<INITIAL>"&"                                   => (Tokens.AND(yypos,yypos+1));
<INITIAL>"|"                                   => (Tokens.OR(yypos,yypos+1));
<INITIAL>"="                                   => (Tokens.EQ(yypos,yypos+1));
<INITIAL>">="                                  => (Tokens.GE(yypos,yypos+2));
<INITIAL>"<="                                  => (Tokens.LE(yypos,yypos+2));
<INITIAL>"<>"                                  => (Tokens.NEQ(yypos,yypos+2));
<INITIAL>">"                                   => (Tokens.GT(yypos,yypos+1));
<INITIAL>"<"                                   => (Tokens.LT(yypos,yypos+1));
<INITIAL>"{"                                   => (Tokens.LBRACE(yypos,yypos+1));
<INITIAL>"}"                                   => (Tokens.RBRACE(yypos,yypos+1));
<INITIAL>";"                                   => (Tokens.SEMICOLON(yypos,yypos+1));
<INITIAL>"("                                   => (Tokens.LPAREN(yypos,yypos+1));
<INITIAL>")"                                   => (Tokens.RPAREN(yypos,yypos+1));

<INITIAL>"/*"                                  => (YYBEGIN COMMENT; netCommentBalance := 1; continue());
<INITIAL>"*/"                                  => (ErrorMsg.error yypos ("closing nonexistent comment!"); continue());
<COMMENT>"/*"                                  => (netCommentBalance := (!netCommentBalance) + 1; continue());
<COMMENT>"*/"                                  => (netCommentBalance := (!netCommentBalance) - 1; if !netCommentBalance = 0 then YYBEGIN INITIAL else (); continue());
<COMMENT>.                                     => (continue());

<INITIAL>[a-zA-Z][a-zA-Z0-9_]*                 => (Tokens.ID(yytext, yypos, yypos + size yytext));
<INITIAL>[0-9]+                                => (Tokens.INT(valOf (Int.fromString yytext), yypos, yypos + size yytext));

<INITIAL>"\""                                  => (YYBEGIN STRING; stringLiteralClosed := false; buffer:= ""; stringStartPosition := yypos; continue());
<STRING>[ -!#-\[\]-~]*                         => (buffer := !buffer ^ yytext; continue());
<STRING>\\n                                    => (buffer := !buffer ^ (escape yytext); continue());
<STRING>\\t                                    => (buffer := !buffer ^ (escape yytext); continue());
<STRING>"\\\""                                 => (buffer := !buffer ^ (escape yytext); continue());
<STRING>"\\\\"                                 => (buffer := !buffer ^ (escape yytext); continue());
<STRING>\\[ \b\r\t\n]+\\                       => (lineNum:= !lineNum + (count (fn c => c = #"\n") (String.explode yytext)); linePos := yypos :: !linePos; continue());
<STRING>\\\^[@-_]                              => (buffer := !buffer ^ escape (convertControlCharacter(String.substring (yytext, 2, 1))); continue());
<STRING>\\(0[0-9][0-9]|1[0-1][0-9]|12[0-7])    => (buffer := !buffer ^ escape (asciiCode(String.substring (yytext, 1, 3))); continue());
<STRING>"\""                                   => (YYBEGIN INITIAL; stringLiteralClosed := true; Tokens.STRING(!buffer, !stringStartPosition, yypos));
<STRING>\n                                     => (YYBEGIN INITIAL; stringLiteralClosed := true; ErrorMsg.error yypos ("illegal new-line within string"); lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<STRING>.                                      => (ErrorMsg.error yypos ("illegal character within string " ^ yytext); continue());

.                                              => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());
