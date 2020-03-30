(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*s Hash tables for hash consing.

    The technique is described in this paper:
      Sylvain Conchon and Jean-Christophe Filliâtre.
      Type-Safe Modular Hash-Consing.
      In ACM SIGPLAN Workshop on ML, Portland, Oregon, September 2006.
      https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf

    Note: a different, more elaborated hash-consing library
          can be found in Why3 sources at http://why3.lri.fr/

    Hash consed values are of the
    following type [hash_consed]. The field [tag] contains a unique
    integer (for values hash consed with the same table). The field
    [hkey] contains the hash key of the value (without modulo) for
    possible use in other hash tables (and internally when hash
    consing tables are resized). The field [node] contains the value
    itself.

    Hash consing tables are using weak pointers, so that values that are no
    more referenced from anywhere else can be erased by the GC. 

  slightly modified to help with polymorphism: hashcons takes the
  hashing and equality function as parameters, and we removed the
  module based interface

*)

type +'a hash_consed = private {
  hkey : int;
  tag : int;
  node : 'a }

(*s Generic part, using ocaml generic equality and hash function. *)

type 'a t

val create : int -> 'a t
  (** [create n] creates an empty table of initial size [n]. The table
      will grow as needed. *)
  
val clear : 'a t -> unit
  (** Removes all elements from the table. *)
  
val hashcons : ('a -> int) -> ('a -> 'a -> bool) -> 'a t -> 'a -> 'a hash_consed
  (** [hashcons t n] hash-cons the value [n] using table [t] i.e. returns
      any existing value in [t] equal to [n], if any; otherwise, allocates
      a new one hash-consed value of node [n] and returns it.
      As a consequence the returned value is physically equal to
      any equal value already hash-consed using table [t]. *)

val iter : ('a hash_consed -> unit) -> 'a t -> unit
  (** [iter f t] iterates [f] over all elements of [t]. *)

val stats : 'a t -> int * int * int * int * int * int
  (** Return statistics on the table.  The numbers are, in order:
      table length, number of entries, sum of bucket lengths,
      smallest bucket length, median bucket length, biggest bucket length. *)

val int: int -> int hash_consed
  (** `hashed' int *)
