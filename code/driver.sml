(*structure Lexer =
struct
  fun run filename =
    let
      val file = TextIO.openIn filename
      fun get _ = TextIO.input file
      val lexer = Mlex.makeLexer get
      fun lex_it() =
        let
          val t = lexer()
        in
          print t;
          print "\n";
		      if substring(t, 0, 3) = "EOF"
          then ()
          else lex_it()
	      end
    in
      lex_it();
      TextIO.closeIn file
    end
end*)

structure Parser =
struct
  structure GeminiLrVals = GeminiLrValsFun(structure Token = LrParser.Token)
  structure Lex = GeminiLexFun(structure Tokens = GeminiLrVals.Tokens)
  structure GeminiP = Join(structure ParserData = GeminiLrVals.ParserData
			structure Lex = Lex
			structure LrParser = LrParser)
  fun run filename =
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
