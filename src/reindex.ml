module type S = sig 
	type elt 
	type t 
	val create: unit -> t 
	val get_val: t -> int -> elt 
	val get_idx: t -> elt -> int
end

module Make(O: Set.OrderedType) = struct 
	
	module M = Map.Make(O)

	type elt = O.t

	type t = {
		mutable count: int;
		mutable key_map: int M.t;
		mutable val_map: elt Ptmap.t
	}

	let create () = {count = -1; key_map = M.empty; val_map = Ptmap.empty}

	let get_val m i = 
		Ptmap.find i m.val_map

	let get_idx m k = 
		try M.find k m.key_map
		with Not_found -> 
		    m.count <- m.count + 1;
		    m.key_map <- M.add k m.count m.key_map;
		    m.val_map <- Ptmap.add m.count k m.val_map;
		    m.count
end