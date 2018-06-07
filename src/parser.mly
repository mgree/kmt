%{
open Syntax
%}

%token <string> VAL
%token <string> SYMBOL
%token ZERO ONE PLUS SEMI NOT STAR 
%token SEMI LPAREN RPAREN COMMA SYMBOL EOF

%start expr
%type <Syntax.expr> expr

%left PLUS
%left SEMI
%right NOT
%nonassoc STAR
%nonassoc SYMBOL

%%

expr:
    | ZERO                     { EZero }
    | ONE                      { EOne }
    | NOT expr                 { ENot $2 }
    | expr PLUS expr           { EPar ($1,$3) }
    | expr SEMI expr           { ESeq ($1,$3) }
    | expr STAR                { EStar $1 }
    | LPAREN expr RPAREN       { $2 }
    | VAL                      { EId $1 }
    | VAL LPAREN exprs RPAREN  { ETheory ($1, $3) }
    | expr SYMBOL expr         { ETheory ($2, [$1; $3]) }
;

exprs:
    | expr                     { [$1] }
    | expr COMMA exprs         { $1 :: $3 }
;