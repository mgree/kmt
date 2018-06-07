(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(** Association tables over ordered types.

   This module implements applicative association tables, also known as
   finite maps or dictionaries, given a total ordering function
   over the keys.
   All operations over maps are purely applicative (no side-effects).
   The implementation uses balanced binary trees, and therefore searching
   and insertion take time logarithmic in the size of the map.
*)

open Common

module type S =
  sig
    type key
    (** The type of the map keys. *)

    type value

    type t
    (** The type of maps from type [key] to type [value]. *)

    val empty: unit -> t
    (** The empty map. *)

    val is_empty: t -> bool
    (** Test whether a map is empty or not. *)

    val mem: key -> t -> bool
    (** [mem x m] returns [true] if [m] contains a binding for [x],
       and [false] otherwise. *)

    val add: key -> value -> t -> t
    (** [add x y m] returns a map containing the same bindings as
       [m], plus a binding of [x] to [y]. If [x] was already bound
       in [m], its previous binding disappears. *)

    val singleton: key -> value -> t
    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x].
        @since 3.12.0
     *)

    val remove: key -> t -> t
    (** [remove x m] returns a map containing the same bindings as
       [m], except for [x] which is unbound in the returned map. *)

    val disjoint_union: t -> t -> t

    val merge: (key -> value option -> value option -> value option) -> t -> t -> t

    val compare: t -> t -> int
    (** Total ordering between maps.  The first argument is a total ordering
        used to compare data associated with equal keys in the two maps. *)

    val equal: t -> t -> bool
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
       equal, that is, contain equal keys and associate them with
       equal data.  [cmp] is the equality predicate used to compare
       the data associated with the keys. *)

    val show: t -> string
    (** pretty print the map *)

    val hash: t -> int 
    (** compute a hash of the map *)

    val iter: (key -> value -> unit) -> t -> unit
    (** [iter f m] applies [f] to all bindings in map [m].
       [f] receives the key as first argument, and the associated value
       as second argument.  The bindings are passed to [f] in increasing
       order with respect to the ordering over the type of the keys. *)

    val fold: (key -> value -> 'b -> 'b) -> t -> 'b -> 'b
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
       where [k1 ... kN] are the keys of all bindings in [m]
       (in increasing order), and [d1 ... dN] are the associated data. *)

    val for_all: (key -> value -> bool) -> t -> bool
    (** [for_all p m] checks if all the bindings of the map
        satisfy the predicate [p].
        @since 3.12.0
     *)

    val exists: (key -> value -> bool) -> t -> bool
    (** [exists p m] checks if at least one binding of the map
        satisfy the predicate [p].
        @since 3.12.0
     *)

    val filter: (key -> value -> bool) -> t -> t
    (** [filter p m] returns the map with all the bindings in [m]
        that satisfy predicate [p].
        @since 3.12.0
     *)

    val partition: (key -> value -> bool) -> t -> t * t
    (** [partition p m] returns a pair of maps [(m1, m2)], where
        [m1] contains all the bindings of [s] that satisfy the
        predicate [p], and [m2] is the map with all the bindings of
        [s] that do not satisfy [p].
        @since 3.12.0
     *)

    val cardinal: t -> int
    (** Return the number of bindings of a map.
        @since 3.12.0
     *)

    val bindings: t -> (key * value) list
    (** Return the list of all bindings of the given map.
       The returned list is sorted in increasing order with respect
       to the ordering [Ord.compare], where [Ord] is the argument
       given to {!Map.Make}.
        @since 3.12.0
     *)

    val min_binding: t -> (key * value)
    (** Return the smallest binding of the given map
       (with respect to the [Ord.compare] ordering), or raise
       [Not_found] if the map is empty.
        @since 3.12.0
     *)

    val max_binding: t -> (key * value)
    (** Same as {!Map.S.min_binding}, but returns the largest binding
        of the given map.
        @since 3.12.0
     *)

    val choose: t -> (key * value)
    (** Return one binding of the given map, or raise [Not_found] if
       the map is empty. Which binding is chosen is unspecified,
       but equal bindings will be chosen for equal maps.
        @since 3.12.0
     *)

    val split: key -> t -> t * value option * t
    (** [split x m] returns a triple [(l, data, r)], where
          [l] is the map with all the bindings of [m] whose key
        is strictly less than [x];
          [r] is the map with all the bindings of [m] whose key
        is strictly greater than [x];
          [data] is [None] if [m] contains no binding for [x],
          or [Some v] if [m] binds [v] to [x].
        @since 3.12.0 
     *)

    val find: key -> t -> value
    (** [find x m] returns the current binding of [x] in [m],
       or raises [Not_found] if no such binding exists. *)

  end
(** Output signature of the functor {!Map.Make}. *)

module Make (Key : CollectionType) (Value : CollectionType) : S with type key = Key.t and type value = Value.t
(** Functor building an implementation of the map structure
   given a totally ordered type. *)