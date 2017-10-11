{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

(* Numerics *)
let digit = ['0'-'9']
let sign_opt = ['-' '+']?
let frac = '.' digit*
let exp = ['e' 'E'] sign_opt digit+

let int = sign_opt digit+
let float = sign_opt digit* frac exp?

(* Whitespace *)
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

(* Identifier *)
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
