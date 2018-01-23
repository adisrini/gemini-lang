signature PARSE =
sig

  val parse: string -> Absyn.exp

end

structure Parse : PARSE =
struct
  structure GeminiLrVals = GeminiLrValsFun(structure Token = LrParser.Token)
  structure Lex = GeminiLexFun(structure Tokens = GeminiLrVals.Tokens)
  structure GeminiP = Join(structure ParserData = GeminiLrVals.ParserData
			structure Lex = Lex
			structure LrParser = LrParser)
  fun parse filename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.fileName := filename)
      	  val file = TextIO.openIn filename
      	  fun get _ = TextIO.input file
      	  fun parseerror(s,p1,p2) = ErrorMsg.error p1 s
      	  val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
      	  val (absyn, _) = GeminiP.parse(30, lexer, parseerror, ())
       in TextIO.closeIn file;
	   absyn
      end handle LrParser.ParseError => raise ErrorMsg.Error

end
