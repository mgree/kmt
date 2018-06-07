
{
  open Parser
  open Printf
  exception Eof

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
      { pos with Lexing.pos_lnum = pos.Lexing.pos_lnum + 1; 
                 Lexing.pos_bol = pos.Lexing.pos_cnum; } ;;

}

let id = ['a'-'z' 'A'-'Z' '_' '0'-'9']+
let symbol = ['~' '`' '!' '@' '#' '$' '%' '^' '&' '|' ':' '?' '>' '<' '[' ']' '=' '-' '.']+

rule token = parse
  | "/*"         { comments 0 lexbuf }
  | "false"      { ZERO }
  | "true"       { ONE }
  | "not"        { NOT }
  | symbol as s  { SYMBOL s }
  | id as s      { VAL s }
  | ","          { COMMA }
  | "+"          { PLUS }
  | ";"          { SEMI }
  | "*"          { STAR }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | [' ' '\t']   { token lexbuf }
  | '\n'         { incr_linenum lexbuf; token lexbuf}
  | _ as c       { printf "[Parse Error] Unrecognized character: %c\n" c; token lexbuf }
  | eof		       { EOF }

and comments level = parse
  | "*/"  { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "/*"  { comments (level+1) lexbuf }
  | '\n'  { incr_linenum lexbuf; comments level lexbuf}
  | _     { comments level lexbuf }
  | eof   { raise End_of_file }