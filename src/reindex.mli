(* Provide a 2-way renaming maps.
   Elements of type 'a are mapped to unique positive integer names.
   Useful for converting automata over arbitrary types to be 
   over ints during construction.  *)

module type S = sig 
	type elt 
	type t 
	val create: unit -> t 
	val get_val: t -> int -> elt 
	val get_idx: t -> elt -> int
end

module Make(O: Set.OrderedType): S with type elt = O.t