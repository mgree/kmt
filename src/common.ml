(*******************************************************************)
(*                                                                 *)
(*         A collection of commonly useful functions               *)
(*                                                                 *)
(*******************************************************************)

module type CollectionType = sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val show : t -> string
end

type ('a, 'b) either = Left of 'a | Right of 'b

let left x = function Left x -> x | Right _ -> failwith "Either [left]"

let right x = function Right x -> x | Left _ -> failwith "Either [right]"

(* Helper functions for dealing with 
  the standard library option type *)

module Option = struct
  (* Creating collection types of pairs *)
  module Make (X : CollectionType) = struct
    type t = X.t option

    let compare a b =
      match (a, b) with
      | None, None -> 0
      | Some x, Some y -> X.compare x y
      | None, Some _ -> -1
      | Some _, None -> 1

    let equal x y = compare x y = 0
    let hash = function None -> 1 | Some x -> 2 + X.hash x
    let show = function
      | None -> "None"
      | Some x -> Printf.sprintf "Some(%s)" (X.show x)
  end

  let unwrap o = match o with None -> failwith "unwrap" | Some v -> v

  let is_none o = match o with None -> true | Some _ -> false

  let is_some o = match o with None -> false | Some _ -> true

  let get o =
    match o with None -> failwith "[Option.get]: None value" | Some v -> v
end

module Either = struct
  (* Creating collection types of pairs *)
  module Make (X : CollectionType) (Y : CollectionType) = struct
    type t = (X.t, Y.t) either

    let compare a b =
      match (a, b) with
      | Left x, Left y -> X.compare x y
      | Right x, Right y -> Y.compare x y
      | Left _, Right _ -> -1
      | Right _, Left _ -> 1

    let equal x y = compare x y = 0
    let hash = function Left x -> 5 + X.hash x | Right y -> 7 + Y.hash y
    let show = function
      | Left x -> "Left(" ^ X.show x ^ ")"
      | Right y -> "Right(" ^ Y.show y ^ ")"
  end
end

(* Pair helper functions *)

module Pair = struct
  (* Creating collection types of pairs *)
  module Make (X : CollectionType) (Y : CollectionType) = struct
    type t = X.t * Y.t
    let compare (a, b) (c, d) =
      let cmp = X.compare a c in
      if cmp <> 0 then cmp else Y.compare b d
    let equal x y = compare x y = 0
    let hash (a, b) = 31 * X.hash a + Y.hash b
    let show (a, b) = Printf.sprintf "(%s,%s)" (X.show a) (Y.show b)
  end

  let map_fst f (a, b) = (f a, b)
  let map_snd f (a, b) = (a, f b)
end

module Memoize (A : CollectionType) = struct
  let cache_size = 2048

  module NP = Hashtbl.Make (A)

  let memoize f =
    let tbl = NP.create (cache_size * 2) in
    let rec aux x =
      try NP.find tbl x with _ ->
        let res = f aux x in
        if NP.length tbl > cache_size then NP.clear tbl ;
        NP.add tbl x res ;
        res
    in
    aux
end

let cross_product x y base f =
  BatSet.PSet.fold
    (fun a' acc1 ->
      BatSet.PSet.fold (fun b' acc2 -> BatSet.PSet.add (f a' b') acc2) y acc1
      )
    x base

let unreachable () = failwith "unreachable"

(* Convenience functions that help for 
   debugging various collection types *)

let debug_enabled = false

let debug f = if debug_enabled then f () else ()

let rec repeat n str =
  match n with x when x <= 0 -> "" | 1 -> str | _ -> str ^ repeat (n - 1) str

let time f x =
  let t = Sys.time () in
  let fx = f x in
  let time = Sys.time () -. t in
  (fx, time)

let add_sep sep acc = if acc = "" then acc else sep ^ acc

let show_set f fold set =
  let elts = fold (fun x acc -> f x ^ add_sep "," acc) set "" in
  "{" ^ elts ^ "}"

let show_list f lst =
  let elts = List.fold_left (fun acc x -> f x ^ add_sep "," acc) "" lst in
  "[" ^ elts ^ "]"

let show_map fkey fval fold map =
  let aux k v acc = fkey k ^ "==>" ^ fval v ^ add_sep "," acc in
  "{" ^ fold aux map "" ^ "}"

(* Set default seed value to make  
   randomized tests deterministic *)

let _ = Random.init 17

let _hash x acc = acc lsr 5 - 1 + x

(* Specialize Maps and Sets for commonly used 
   int and string types. Provides more efficient 
   comparison/hash/equality functions than using 
   polymorphic compare. Since natural numbers are used
   often, we use subtraction for comparison without 
   worrying about overflow. *)

module IntType = struct
  type t = int
  let equal i j = i = j
  let compare (i: int) j = if i < j then -1 else if i > j then 1 else 0
  let hash i = i land max_int
  let show = string_of_int
end

module IntType2 = struct
  type t = int * int
  let equal x y = compare x y = 0
  let compare (a, b) (c, d) =
    let cmp = IntType.compare a c in
    if cmp = 0 then IntType.compare b d else cmp
  let hash (i, j) = i land max_int + j land max_int
  let show (i, j) = "(" ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
end

module NatType = struct
  type t = int
  let compare i j = i - j
  let equal i j = i = j
  let hash i = i land max_int
  let show = string_of_int
end

module NatType2 = struct
  type t = int * int
  let equal x y = compare x y = 0
  let compare (a, b) (c, d) =
    let cmp = a - c in
    if cmp = 0 then b - d else cmp
  let hash (i, j) = (i + j) land max_int
  let show (i, j) = "(" ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
end

module StrType = struct
  type t = string
  let compare = String.compare
  let equal i j = String.compare i j = 0
  let hash s =
    let h = ref 0 in
    for i = 0 to String.length s - 1 do h := !h lsr 5 - 1 + Char.code s.[i]
    done ;
    !h
  let show x = x
end

module NatSet = struct
  module S = Set.Make (NatType)
  include S
  let hash x = S.fold (fun y acc -> _hash y acc) x 0
end

module StrSet = Set.Make (StrType)
module StrMap = Map.Make (StrType)
module NatMap = Map.Make (NatType)
