type t 

val from_range : int * int -> t
val union : t -> t -> t 
val inter : t -> t -> t
val negate : t -> t
val top : t 
val bot : t

val is_true : t -> bool
val is_false : t -> bool

val show : t -> string