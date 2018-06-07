type range = {lo : int; hi : int}
type t = range list

let empty = {lo=(-1); hi=(-1)}
let full = {lo=0; hi=max_int}

let overlaps (r1 : range) (r2 : range) = 
  (r1.lo >= r2.lo && r1.lo <= r2.hi) || (r1.hi >= r2.lo && r1.hi <= r2.hi) || 
  (r2.lo >= r1.lo && r2.lo <= r1.hi) || (r2.hi >= r1.lo && r2.hi <= r1.hi)

let is_empty (r : range) = r.lo < 0

let unionRange (r1 : range) (r2 : range) = 
  match is_empty r1, is_empty r2 with 
  | true, _ -> r2 
  | _, true -> r1 
  | false, false -> {lo=min r1.lo r2.lo; hi=max r1.hi r2.hi}

let interRange (r1 : range) (r2 : range) = 
  if (is_empty r1) || (is_empty r2) || r1.lo > r2.hi || r2.lo > r1.hi 
    then empty
    else {lo=max r1.lo r2.lo; hi=min r1.hi r2.hi}

let negateRange (r : range) : t = 
  if is_empty r then [full] 
  else 
    match r.lo, r.hi with 
    | 0, x when x = max_int -> [] 
    | 0, x -> [{lo=x+1; hi=max_int}]
    | w, x when x = max_int -> [{lo=0; hi=w-1}]
    | w, x -> [{lo=0; hi=w-1}; {lo=x+1; hi=max_int}]

let fromRange (r : range) = 
   if r = empty then []
   else [ r ]

let trueRanges = [ full ]
let falseRanges = []

let rec unionSingle (r : range) (rs : t) = 
   match rs with
   | [] -> [ r ]
   | hd :: tl -> 
      if r.hi < hd.lo then r :: rs
      else if overlaps r hd then unionSingle (unionRange r hd) tl
      else r :: (unionSingle r tl)

let rec union (rs1 : t) (rs2 : t) = 
    match rs1 with
    | [] -> rs2
    | hd :: tl -> union tl (unionSingle hd rs2)

let rec interSingle (r : range) (rs : t) = 
   match rs with
   | [] -> []
   | hd :: tl -> 
      if overlaps r hd then interRange r hd :: (interSingle r tl)
      else interSingle r tl

let rec inter (rs1 : t) (rs2 : t) = 
    match rs1 with
    | [] -> []
    | hd :: [] -> interSingle hd rs2
    | hd :: tl -> inter tl (interSingle hd rs2)

let negate (rs : t) = 
   if rs = falseRanges then trueRanges
   else List.fold_left (fun acc r -> union acc (negateRange r) ) [] rs

let is_false (rs : t) = rs = []

let is_true (rs : t) = 
  match rs with 
  | [r] -> r = full
  | _ -> false

let top = trueRanges 

let bot = falseRanges

let from_range (x,y) = fromRange {lo=x; hi=y}

let show_range (r : range) =
  if r.lo < 0 then "empty"
  else 
    (if r.hi = max_int then Printf.sprintf "(%d,infinity)" r.lo 
     else Printf.sprintf "(%d,%d)" r.lo r.hi)

let show (rs : t) = 
  Common.show_list show_range rs