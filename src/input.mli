val read_from_in: in_channel -> Syntax.expr 
(** Read a term from an input stream *)

val read_from_str: string -> Syntax.expr
(** Read a term from a string *)

val read_from_file: string -> Syntax.expr
(** Read a term from a file *)