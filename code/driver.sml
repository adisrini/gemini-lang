structure Parse =
struct
  fun parse filename =
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
end
