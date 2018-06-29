open Kat
open Common
open Syntax
open Hashcons
open Reindex

(* Internal representation of an automata, 
   parameterized over a KAT implementation. *)
module type AUTOMATA_IMPL = sig
  module K : KAT_IMPL

  module State : CollectionType

  module StateSet : SafeSet.S with type elt = State.t

  module Transition : CollectionType with type t = K.Test.t * K.P.t option

  module Transitions :
    SafeMap.S with type key = Transition.t and type value = StateSet.t

  type t

  val initial : t -> State.t

  val acceptance : t -> State.t -> K.Test.t

  val transition : t -> State.t -> Transitions.t

  val create :
    State.t -> (State.t -> Transitions.t) -> (State.t -> K.Test.t) -> t

  val print : t -> unit
end

(* Implementation of automata that constructs 
   the each automaton lazily by representing 
   everything as functions yet to be evaluated. *)
module Lazy (K : KAT_IMPL) (S : CollectionType) :
  AUTOMATA_IMPL with module K = K and module State = S =
struct
  module K = K
  module State = S
  module StateSet = SafeSet.Make (State)
  module POption = Common.Option.Make (K.P)
  module Transition = Common.Pair.Make (K.Test) (POption)
  module Transitions = SafeMap.Make (Transition) (StateSet)

  type t =
    { initial: State.t
    ; transition: State.t -> Transitions.t
    ; acceptance: State.t -> K.Test.t }

  let initial t = t.initial

  let acceptance t = t.acceptance

  let transition t = t.transition

  let create i t a = {initial= i; transition= t; acceptance= a}

  let explore (auto: t) f g =
    let seen = ref (StateSet.empty ()) in
    let todo = Queue.create () in
    Queue.add (initial auto) todo ;
    while not (Queue.is_empty todo) do
      let state = Queue.pop todo in
      let transitions = transition auto state in
      f (state, acceptance auto state) ;
      Transitions.iter
        (fun (a, p) ls ->
          StateSet.iter
            (fun l ->
              g (state, l, a, p) ;
              if not (StateSet.mem l !seen) then (
                seen := StateSet.add l !seen ;
                Queue.add l todo ) )
            ls )
        transitions
    done


  let print (auto: t) =
    Printf.printf "---------------------------\n" ;
    let print_trans (l, l', a, po) =
      Printf.printf "transition: %s -> %s (%s,%s)\n" (State.show l)
        (State.show l') (K.Test.show a) (POption.show po)
    in
    let print_accept (l, a) =
      Printf.printf "accept:     %s [%s]\n" (State.show l) (K.Test.show a)
    in
    explore auto print_accept print_trans ;
    Printf.printf "---------------------------\n"
end

module type KAT_AUTOMATA = sig
  module K : KAT_IMPL

  type t

  val of_term : K.Term.t -> t

  val equivalent : t -> t -> bool

  val print : t -> unit
end

module Automata (K : KAT_IMPL) : KAT_AUTOMATA with module K = K = struct
  include Lazy (K) (NatType)

  (* Partial derivative tuple *)
  module Derivative = struct
    type t = K.Test.t * int * K.Term.t

    let compare (a, l1, b) (c, l2, d) =
      let cmp = K.Test.compare a c in
      if cmp <> 0 then cmp
      else
        let cmp = l1 - l2 in
        if cmp <> 0 then cmp else K.Term.compare b d


    let equal x y = compare x y = 0

    let hash (a, l, b) = K.Test.hash a + l + K.Term.hash b

    let show (a, l, b) =
      let s1 = K.Test.show a in
      let s2 = string_of_int l in
      let s3 = K.Term.show b in
      Printf.sprintf "(%s,%s,%s)" s1 s2 s3
  end

  module DerivativeSet = SafeSet.Make (Derivative)
  module ActionSet = SafeSet.Make (K.P)
  module NatTermMap = SafeMap.Make (NatType) (K.Term)
  module NatActionMap = SafeMap.Make (NatType) (K.P)
  module TestNatMap = SafeMap.Make (K.Test) (NatType)

  let dotr trips p =
    let f (q, l, k) r = (q, l, K.seq k r) in
    DerivativeSet.fold
      (fun trip acc -> DerivativeSet.add (f trip p) acc)
      trips (DerivativeSet.empty ())


  let dotl p trips =
    let f p (q, l, k) = (K.pseq p q, l, k) in
    DerivativeSet.fold
      (fun trip acc -> DerivativeSet.add (f p trip) acc)
      trips (DerivativeSet.empty ())


  let rec observation_test (test: K.Test.t) =
    match test.node with
    | Theory _ | Zero | One | Placeholder _ | Not _ -> test
    | PPar (a, b) -> K.ppar (observation_test a) (observation_test b)
    | PSeq (a, b) -> K.pseq (observation_test a) (observation_test b)


  let rec observation (term: K.Term.t) =
    match term.node with
    | Action (i, p) -> K.zero ()
    | Pred a -> observation_test a
    | Par (a, b) -> K.ppar (observation a) (observation b)
    | Seq (a, b) -> K.pseq (observation a) (observation b)
    | Star a -> K.one ()


  let rec derivative_test (test: K.Test.t) : DerivativeSet.t =
    match test.node with
    | Not _ -> failwith "Impossible: [(Not _) case in derivative]"
    | Placeholder _ -> failwith "TODO: derivative"
    | Theory _ | Zero | One -> DerivativeSet.empty ()
    | PPar (a, b) ->
        DerivativeSet.union (derivative_test a) (derivative_test b)
    | PSeq (a, b) ->
        let l = dotr (derivative_test a) (K.pred b) in
        let r = dotl (observation (K.pred a)) (derivative_test b) in
        DerivativeSet.union l r


  let rec derivative (term: K.Term.t) : DerivativeSet.t =
    match term.node with
    | Action (i, p) -> DerivativeSet.singleton (K.one (), i, K.pred (K.one ()))
    | Pred a -> DerivativeSet.empty ()
    | Par (a, b) -> DerivativeSet.union (derivative a) (derivative b)
    | Seq (q, r) ->
        DerivativeSet.union
          (dotr (derivative q) r)
          (dotl (observation q) (derivative r))
    | Star q -> dotr (dotl (observation term) (derivative q)) term


  let rec action_map (term: K.Term.t) : NatActionMap.t =
    match term.node with
    | Action (i, p) -> NatActionMap.singleton i p
    | Pred _ -> NatActionMap.empty ()
    | Par (a, b) | Seq (a, b) ->
        NatActionMap.disjoint_union (action_map a) (action_map b)
    | Star a -> action_map a


  let rec replace_test (test: K.Test.t) (map: TestNatMap.t) : K.Test.t =
    match test.node with
    | Placeholder _ -> failwith "replace_test"
    | Zero | One -> test
    | Not a -> K.not (replace_test a map)
    | PPar (a, b) -> K.ppar (replace_test a map) (replace_test b map)
    | PSeq (a, b) -> K.pseq (replace_test a map) (replace_test b map)
    | Theory a -> K.placeholder (TestNatMap.find test map)


  let rec replace_term (term: K.Term.t) (map: TestNatMap.t) : K.Term.t =
    match term.node with
    | Action (i, p) -> term
    | Star a -> K.star (replace_term a map)
    | Par (a, b) -> K.par (replace_term a map) (replace_term b map)
    | Seq (a, b) -> K.seq (replace_term a map) (replace_term b map)
    | Pred a -> K.pred (replace_test a map)


  let rec build_map_test (test: K.Test.t) (i: int ref) : TestNatMap.t =
    match test.node with
    | Placeholder _ -> failwith "build_map_test"
    | Zero | One -> TestNatMap.empty ()
    | Not a -> build_map_test a i
    | Theory a ->
        let ret = TestNatMap.singleton test !i in
        incr i ; ret
    | PPar (a, b) | PSeq (a, b) ->
        TestNatMap.disjoint_union (build_map_test a i) (build_map_test b i)


  let rec build_map (term: K.Term.t) (i: int ref) : TestNatMap.t =
    match term.node with
    | Action (i, p) -> TestNatMap.empty ()
    | Star a -> build_map a i
    | Par (a, b) | Seq (a, b) ->
        TestNatMap.disjoint_union (build_map a i) (build_map b i)
    | Pred a -> build_map_test a i


  let replace_theory_term (term: K.Term.t) : K.Term.t * TestNatMap.t =
    let map = build_map term (ref 0) in
    let new_term = replace_term term map in
    (new_term, map)


  let rec characters (term: K.Term.t) : ActionSet.t =
    match term.node with
    | Action (i, p) -> ActionSet.singleton p
    | Pred a -> ActionSet.empty ()
    | Par (a, b) | Seq (a, b) -> ActionSet.union (characters a) (characters b)
    | Star a -> characters a


  module ASet = SafeSet.Make (K.A)
  module TSet = SafeSet.Make (K.Test)
  module NatSet = SafeSet.Make (NatType)
  module TSetOption = Common.Option.Make (TSet)
  module TestAutomata = Lazy (K) (TSetOption)
  module NatSetAutomata = Lazy (K) (NatSet)

  (* Create a theory test automaton from a test and 
     a collection of characters (actions) that appear
     in the term we are interested in. *)
  module Theory = struct
    let rec is_covered_by (a: K.Test.t) (l: TSet.t) =
      match a.node with
      | One -> true
      | Zero -> false
      | PPar (b, c) -> is_covered_by b l || is_covered_by c l
      | PSeq (b, c) -> is_covered_by b l && is_covered_by c l
      | Not b -> not (is_covered_by b l)
      | Theory _ -> TSet.mem a l
      | Placeholder _ -> failwith "Unreachable: is_covered_by"


    let get_implied_subs (sub: K.Test.t) (subs: TSet.t) : TSet.t =
      TSet.filter (K.implies sub) subs


    module SubtermsSet = SafeSet.Make (TSet)
    module SubtermsMap = SafeMap.Make (K.Test) (TSet)

    let initial_subterms (subs: TSet.t) (map: SubtermsMap.t) : SubtermsSet.t =
      let rec aux subs present_subs implied map =
        if TSet.is_empty subs then
          if TSet.is_empty implied then SubtermsSet.empty ()
          else SubtermsSet.singleton implied
        else
          let sub = TSet.choose subs in
          let subs = TSet.remove sub subs in
          (* check if already implied *)
          if TSet.mem sub implied then
            aux subs (TSet.add sub present_subs) implied map
          else
            let all_subs = SubtermsMap.find sub map in
            let present = TSet.add sub (TSet.diff present_subs all_subs) in
            let x = aux subs present (TSet.union all_subs implied) map in
            let y = aux subs present_subs implied map in
            SubtermsSet.union x y
      in
      aux subs (TSet.empty ()) (TSet.empty ()) map


    let test_automata (test: K.Test.t) (chars: ActionSet.t) : TestAutomata.t =
      let subs = K.subterms test in
      let subs =
        BatSet.PSet.fold (fun s acc -> TSet.add s acc) subs (TSet.empty ())
      in
      debug (fun () -> Printf.printf "All subterms: %s\n" (TSet.show subs)) ;
      (* Accept if the state is labeled with the test *)
      let accept (l: TSetOption.t) =
        match l with
        | None -> K.zero ()
        | Some l -> if TSet.mem test l then K.one () else K.zero ()
      in
      (* Transitions based on push back operations *)
      let trans (l: TSetOption.t) : TestAutomata.Transitions.t =
        (* Look at each character and subterm *)
        let get_transitions_aux (c: K.P.t) (s: K.Test.t) (l: TSet.t) : TSet.t =
          let tests = K.push_back_test c s in
          (* Printf.printf "Pushback(%s,%s) = %s\n" (K.P.show c) (K.Test.show s) (Common.show_set K.Test.show BatSet.PSet.fold tests); *)
          (* if pair (a,p) where a is covered by current state *)
          (* then add this action K.A.t to the map of transitions *)
          BatSet.PSet.fold
            (fun a acc -> if is_covered_by a l then TSet.singleton s else acc)
            tests (TSet.empty ())
        in
        let get_transitions (c: K.P.t) (l: TSet.t) : TestAutomata.StateSet.t =
          let base = TSet.empty () in
          let new_state =
            TSet.fold
              (fun s acc -> TSet.union acc (get_transitions_aux c s l))
              subs base
          in
          TestAutomata.StateSet.singleton (Some new_state)
        in
        (* look at each transition char c *)
        (* look at each subterm to push back *)
        let base = TestAutomata.Transitions.empty () in
        (* Consider the initial state case separately *)
        match l with
        | None ->
            (* Map each subterm to all its implied subterms *)
            let map =
              TSet.fold
                (fun sub acc ->
                  SubtermsMap.add sub (get_implied_subs sub subs) acc )
                subs (SubtermsMap.empty ())
            in
            (* Printf.printf "Subterm map: %s\n" (SubtermsMap.show map); *)
            let initials = initial_subterms subs map in
            (* Printf.printf "Initial states: %s\n" (SubtermsSet.show initials); *)
            SubtermsSet.fold
              (fun subs acc ->
                let sub = TSet.fold K.pseq subs (K.one ()) in
                let next_state = TestAutomata.StateSet.singleton (Some subs) in
                (* Printf.printf "   ADD transition: %s --> %s\n" (K.Test.show sub) (TestAutomata.StateSet.show next_state); *)
                TestAutomata.Transitions.add (sub, None) next_state acc )
              initials
              (TestAutomata.Transitions.empty ())
            (* For each subterm, get all implied subterms and go to that state *)
            (* TSet.fold (fun sub acc -> 
              let implied_subs = get_implied_subs sub subs in
              let next_state = TestAutomata.StateSet.singleton (Some implied_subs) in
              TestAutomata.Transitions.add (sub, None) next_state acc
            ) subs (TestAutomata.Transitions.empty()) *)
        | Some l ->
            (* If not initial state, for each char c, get subterms that pushback here with c *)
            ActionSet.fold
              (fun c acc ->
                TestAutomata.Transitions.add (K.one (), Some c)
                  (get_transitions c l) acc )
              chars base
      in
      TestAutomata.create None trans accept
  end

  (* Module for reindexing an automaton over arbitrary state 
     type to be over simple integers instead. *)
  module Reindex (A : AUTOMATA_IMPL with module K = K) = struct
    module R = Reindex.Make (A.State)

    let reindex (auto: A.t) : t =
      let indexer = R.create () in
      let _ = R.get_idx indexer (A.initial auto) in
      let accept (l: int) = A.acceptance auto (R.get_val indexer l) in
      let trans (l: int) =
        let ts = A.transition auto (R.get_val indexer l) in
        A.Transitions.fold
          (fun k states acc ->
            let f state acc = StateSet.add (R.get_idx indexer state) acc in
            let int_states = A.StateSet.fold f states (StateSet.empty ()) in
            Transitions.add k int_states acc )
          ts (Transitions.empty ())
      in
      create 0 trans accept
  end

  module PairSet = SafeSet.Make (NatType2)
  module PairAutomata = Lazy (K) (NatType2)
  module RT = Reindex (TestAutomata)
  module RP = Reindex (PairAutomata)
  module RN = Reindex (NatSetAutomata)

  (* Intersect a term automaton and a predicate automaton 
     together replacing tests for a particular placeholder test *)
  module Intersection = struct
    let rec replace (x: K.Test.t) (y: K.Test.t) (i: int) : K.Test.t =
      match x.node with
      | One | Zero | Theory _ -> x
      | Placeholder j -> if i = j then y else x
      | Not a -> K.not (replace a y i)
      | PPar (a, b) -> K.ppar (replace a y i) (replace b y i)
      | PSeq (a, b) -> K.pseq (replace a y i) (replace b y i)


    module TSPair = Common.Pair.Make (K.Test) (StateSet)
    module TSPairSet = SafeSet.Make (TSPair)
    module POption = Common.Option.Make (K.P)
    module ActionMap = SafeMap.Make (POption) (TSPairSet)

    let get_action_map (x: Transitions.t) : ActionMap.t =
      Transitions.fold
        (fun (a, po) vs acc ->
          try
            let existing = ActionMap.find po acc in
            ActionMap.add po (TSPairSet.add (a, vs) existing) acc
          with _ -> ActionMap.add po (TSPairSet.singleton (a, vs)) acc )
        x (ActionMap.empty ())


    let intersect (pol: t) (pred: t) (placeholder: int) : PairAutomata.t =
      let cross is js =
        StateSet.fold
          (fun i acc ->
            StateSet.fold
              (fun j acc -> PairAutomata.StateSet.add (i, j) acc)
              js acc )
          is
          (PairAutomata.StateSet.empty ())
      in
      let accept (i, j) =
        let x = acceptance pol i in
        let y = acceptance pred j in
        replace x y placeholder
      in
      let trans (i, j) =
        (* Printf.printf "  State: (%d,%d)\n" i j; *)
        let accept_test = acceptance pred j in
        let x = transition pol i in
        let y = transition pred j in
        (* TODO: special case for the first node *)
        if j = 0 then
          let ret =
            Transitions.fold
              (fun (a, _) is' acc1 ->
                Transitions.fold
                  (fun (b, _) js' acc2 ->
                    let nstates = cross is' js' in
                    let key = (K.pseq a b, None) in
                    try
                      let existing = PairAutomata.Transitions.find key acc2 in
                      PairAutomata.Transitions.add key
                        (PairAutomata.StateSet.union nstates existing)
                        acc2
                    with _ ->
                      let test = K.pseq a b in
                      if test <> K.zero () then
                        PairAutomata.Transitions.add (test, None) nstates acc2
                      else acc2 )
                  y acc1 )
              x
              (PairAutomata.Transitions.empty ())
          in
          ret
        else
          let mapx = get_action_map x in
          let mapy = get_action_map y in
          let ret =
            ActionMap.fold
              (fun po pairs acc ->
                let pairs' = ActionMap.find po mapy in
                let ts = ref (PairAutomata.Transitions.empty ()) in
                TSPairSet.iter
                  (fun (a, l1) ->
                    TSPairSet.iter
                      (fun (b, l2) ->
                        (* Printf.printf "  iter: a=%s, b=%s, l1=%s, l2=%s\n" (K.Test.show a) (K.Test.show b) (StateSet.show l1) (StateSet.show l2); *)
                        let next_states = cross l1 l2 in
                        let new_test = replace a accept_test placeholder in
                        (* Printf.printf "    new_test: %s\n" (K.Test.show new_test); *)
                        if new_test <> K.zero () then
                          (* Printf.printf "    added?: (%s,%s)\n" (K.Test.show new_test) (POption.show po); *)
                          ts
                          := PairAutomata.Transitions.add (new_test, po)
                               next_states !ts )
                      pairs' )
                  pairs ;
                (* PairAutomata.Transitions.iter (fun k v -> (
              Printf.printf "  FINAL IS: (%s,%s)\n" (PairAutomata.Transition.show k) (PairAutomata.StateSet.show v)
            )) !ts; *)
                PairAutomata.Transitions.disjoint_union acc !ts
                (* let next_states = cross vs vs' in
            PairAutomata.Transitions.add (replace a accept_test placeholder, po) next_states acc *)
                )
              mapx
              (PairAutomata.Transitions.empty ())
          in
          ret
      in
      PairAutomata.create (0, 0) trans accept
  end

  (* Determinize a an automaton by making the inital transitions
    disjoint using minterms, and then applying the usual powerset
    construction. *)
  module Determinize = struct
    module StateSetSet = NatSetAutomata.StateSet

    type minterm_tree =
      | Node of K.Test.t * StateSet.t * minterm_tree * minterm_tree
      | Leaf

    let rec show_tree (t: minterm_tree) : string =
      match t with
      | Leaf -> "Leaf"
      | Node (t, ls, left, right) ->
          Printf.sprintf "Node(%s,%s,%s,%s)" (K.Test.show t) (StateSet.show ls)
            (show_tree left) (show_tree right)


    let rec refine (t: minterm_tree) (a: K.Test.t) (l: StateSet.t) =
      match t with
      | Node (b, ls, left, right) ->
          let ls' = StateSet.union l ls in
          let pos = K.pseq a b in
          let neg = K.pseq (K.not a) b in
          let sat_pos = K.satisfiable pos in
          if sat_pos && K.satisfiable neg then
            if left = Leaf then
              Node (b, ls, Node (pos, ls', Leaf, Leaf), Node (neg, ls, Leaf, Leaf))
            else Node (b, ls, refine left a l, refine right a l)
          else if sat_pos then Node (b, ls', refine left a l, right)
          else if K.satisfiable neg then Node (b, ls, left, refine right a l)
          else t
      | Leaf -> Leaf

    let rec leaves (t: minterm_tree) : (K.Test.t * StateSet.t) list =
      match t with
      | Node (b, ls, left, right) ->
          if left = Leaf then [(b, ls)] else leaves left @ leaves right
      | Leaf -> failwith "impossible: leaves"


    let determinize (auto: t) : NatSetAutomata.t =
      let convert states =
        StateSet.fold (fun s acc -> NatSet.add s acc) states (NatSet.empty ())
      in
      let accept (ls: NatSet.t) =
        (* sum of all acceptance conditions *)
        NatSet.fold
          (fun l acc ->
            let a = acceptance auto l in
            K.ppar a acc )
          ls (K.zero ())
      in
      let trans (ls: NatSet.t) =
        if NatSet.equal ls (NatSet.singleton 0) then
          (* ensure predicates are disjoint by constructing minterms *)
          let t = transition auto 0 in
          let true_states = Transitions.find (K.one (), None) t in
          (* Printf.printf "  True states: %s\n" (StateSet.show true_states); *)
          let root = Node (K.one (), true_states, Leaf, Leaf) in
          let tree =
            Transitions.fold (fun (a, _) ls acc -> 
              (* Printf.printf "  Leaves currently:\n";
              List.iter (fun (a,ls) -> Printf.printf "   LEAF: %s, states=%s\n" 
              (K.Test.show a) (StateSet.show ls)) (leaves acc);
              Printf.printf "  mintree add %s\n" (K.Test.show a); *)
              refine acc a ls
            ) t root
          in
          let vs = leaves tree in
          let ret =
            List.fold_left
              (fun acc ((a, ls): K.Test.t * StateSet.t) ->
                (* Printf.printf "Adding transition: %s for %s\n" (K.Test.show a) (StateSet.show ls); *)
                NatSetAutomata.Transitions.add (a, None)
                  (StateSetSet.singleton (convert ls))
                  acc )
              (NatSetAutomata.Transitions.empty ())
              vs
          in
          ret
        else
          (* look for same (test,action) pair and move to set of states *)
          let ret =
            NatSet.fold
              (fun l (acc: NatSetAutomata.Transitions.t) ->
                let t = transition auto l in
                Transitions.fold
                  (fun c state acc ->
                    try
                      let z = NatSetAutomata.Transitions.find c acc in
                      let z = StateSetSet.choose z in
                      let ret =
                        StateSetSet.singleton (NatSet.union (convert state) z)
                      in
                      NatSetAutomata.Transitions.add c ret acc
                    with _ ->
                      NatSetAutomata.Transitions.add c
                        (StateSetSet.singleton (convert state))
                        acc )
                  t acc )
              ls
              (NatSetAutomata.Transitions.empty ())
          in
          ret
      in
      let initial = NatSet.singleton 0 in
      NatSetAutomata.create initial trans accept
  end

  let add_labels (term: K.Term.t) : K.Term.t =
    let curr = ref 2 in
    let rec aux t =
      match t.node with
      | Action (_, p) ->
          let ret = K.action_i !curr p in
          incr curr ; ret
      | Pred _ -> t
      | Par (x, y) ->
          let l = aux x in
          let r = aux y in
          K.par l r
      | Seq (x, y) ->
          let l = aux x in
          let r = aux y in
          K.seq l r
      | Star x -> K.star (aux x)
    in
    aux term


  let of_term (term: K.Term.t) : t =
    let term = add_labels term in
    let term, placeholder_map = replace_theory_term term in
    let add (_, l, k) cmap = NatTermMap.add l k cmap in
    let partials =
      let x = derivative term in
      let y = DerivativeSet.fold add x (NatTermMap.empty ()) in
      add (K.zero (), 1, term) y
    in
    (* let term = remove_labels term in *)
    let chars = characters term in
    let amap = action_map term in
    (* NatTermMap.iter (fun l deriv -> 
      Printf.printf "Partial: %d --> %s\n" l (K.Term.show deriv)
    ) partials; *)
    let accept (l: int) =
      if l = 0 then K.zero () else observation (NatTermMap.find l partials)
    in
    let trans (l: int) =
      if l = 0 then
        Transitions.singleton (K.one (), None) (StateSet.singleton 1)
      else
        let cont = NatTermMap.find l partials in
        let dkl = derivative cont in
        (* Printf.printf "Continuation for %d is %s\n" l (K.Term.show cont);
        Printf.printf "Derivative for %d is %s\n" l (DerivativeSet.show dkl); *)
        let transitions ((d, l, k): DerivativeSet.elt) acc =
          let action = NatActionMap.find l amap in
          (* Printf.printf "  Adding action: (%s,%s)\n" (K.Test.show d) (K.P.show action); *)
          if d = K.zero () then acc
          else
            let key = (d, Some action) in
            try
              let existing = Transitions.find key acc in
              Transitions.add key (StateSet.add l existing) acc
            with _ ->
              Transitions.add (d, Some action) (StateSet.singleton l) acc
        in
        DerivativeSet.fold transitions dkl (Transitions.empty ())
    in
    let auto = create 0 trans accept in
    debug (fun () -> Printf.printf "Action Map: %s\n" (NatActionMap.show amap)) ;
    debug (fun () -> Printf.printf "Replaced: %s\n" (K.Term.show term)) ;
    debug (fun () -> Printf.printf "Map: %s\n" (TestNatMap.show placeholder_map) ) ;
    debug (fun () -> Printf.printf "Characters: %s\n" (ActionSet.show chars)) ;
    debug (fun () -> Printf.printf "Policy Automata:\n") ;
    debug (fun () -> print auto) ;
    let auto =
      TestNatMap.fold
        (fun theory_test placeholder acc ->
          let x = Theory.test_automata theory_test chars in
          debug (fun () ->
              Printf.printf "Automata for: %s\n" (K.Test.show theory_test) ) ;
          debug (fun () -> TestAutomata.print x) ;
          let x = RT.reindex x in
          debug (fun () -> Printf.printf "Reindexed Automaton\n") ;
          debug (fun () -> print x) ;
          let ret = Intersection.intersect acc x placeholder in
          debug (fun () -> Printf.printf "Current intersected Automaton:\n") ;
          debug (fun () -> PairAutomata.print ret) ;
          let ret = RP.reindex ret in
          debug (fun () -> Printf.printf "Intersected reindexed Automaton:\n") ;
          debug (fun () -> print ret) ;
          ret )
        placeholder_map auto
    in
    let auto = Determinize.determinize auto in
    debug (fun () -> Printf.printf "Determinized Automaton: \n") ;
    debug (fun () -> NatSetAutomata.print auto) ;
    let auto = RN.reindex auto in
    auto


  module NatPairSet = SafeSet.Make (NatType2)

  module Equivalence = struct
    type eq_state = Garbage | State of State.t [@@deriving (eq, ord)]

    module EqState = struct
      type t = eq_state

      let compare = compare_eq_state

      let equal = equal_eq_state

      let hash = Hashtbl.hash

      let show = function Garbage -> "Garbage" | State s -> string_of_int s
    end

    module EqStatePair = Pair.Make (EqState) (EqState)
    module EqStateSet = SafeSet.Make (EqStatePair)

    let equivalent (auto1: t) (auto2: t) : bool =
      let r = ref (EqStateSet.empty ()) in
      let todo = Queue.create () in
      (* Find all the similar first states that should be related *)
      let t1 = transition auto1 (initial auto1) in
      let t2 = transition auto2 (initial auto2) in
      let bad = ref false in
      Transitions.iter
        (fun (a, _) l1 ->
          Transitions.iter
            (fun (b, _) l2 ->
              if K.satisfiable (K.pseq a b) then (
                let x = StateSet.choose l1 in
                let y = StateSet.choose l2 in
                (* Ensure same acceptance condition *)
                let a1 = acceptance auto1 x in
                let a2 = acceptance auto2 y in
                if a1 <> a2 then bad := true else () ;
                Queue.push (State x, State y) todo ) )
            t2 )
        t1
      |> ignore ;
      let push_pairs t1 t2 flip exit =
        t1
        |> Transitions.iter (fun (_, po1) l1 ->
               let l1 = StateSet.choose l1 in
               let found = ref false in
               t2
               |> Transitions.iter (fun (_, po2) l2 ->
                      let l2 = StateSet.choose l2 in
                      match (po1, po2) with
                      | Some p1, Some p2 ->
                          if p1 = p2 then (
                            let a1 = acceptance auto1 l1 in
                            let a2 = acceptance auto2 l2 in
                            if a1 <> a2 then (
                              debug (fun () ->
                                  Printf.printf
                                    "Different acceptance: (%d,%d)\n" l1 l2 ) ;
                              exit := true )
                            else found := true ;
                            let value =
                              if flip then (State l2, State l1)
                              else (State l1, State l2)
                            in
                            debug (fun () ->
                                Printf.printf "  Adding state (%s,%s)\n"
                                  (fst value |> EqState.show)
                                  (snd value |> EqState.show) ) ;
                            Queue.push value todo )
                      | _, _ -> failwith "equivalent: unreachable" ) ;
               if not !found then (
                 let value =
                   if flip then (Garbage, State l1) else (State l1, Garbage)
                 in
                 debug (fun () ->
                     Printf.printf "  Adding state (%s,%s)\n"
                       (fst value |> EqState.show)
                       (snd value |> EqState.show) ) ;
                 Queue.push value todo ) )
      in
      if !bad then false
      else (
        debug (fun () ->
            Queue.iter
              (fun (x, y) ->
                Printf.printf "Initial pair: (%s,%s)\n" (EqState.show x)
                  (EqState.show y) )
              todo ) ;
        (* Check if bisimilar. If exit early, then return false *)
        let exit = ref false in
        while not (Queue.is_empty todo) && not !exit do
          let (x, y) as z = Queue.pop todo in
          debug (fun () ->
              Printf.printf "Looking at: (%s,%s)\n" (EqState.show x)
                (EqState.show y) ) ;
          if not (EqStateSet.mem z !r) then
            match (x, y) with
            | Garbage, Garbage -> ()
            | State s1, Garbage ->
                let t1 = transition auto1 s1 in
                let a = acceptance auto1 s1 in
                if a = K.zero () then
                  push_pairs t1 (Transitions.empty ()) false exit
                else (
                  debug (fun () ->
                      Printf.printf "Nonzero acceptance for: (%s,%s)\n"
                        (EqState.show x) (EqState.show y) ) ;
                  exit := true )
            | Garbage, State s2 ->
                let t2 = transition auto2 s2 in
                let a = acceptance auto2 s2 in
                if a = K.zero () then
                  push_pairs t2 (Transitions.empty ()) true exit
                else (
                  debug (fun () ->
                      Printf.printf "Nonzero acceptance for: (%s,%s)\n"
                        (EqState.show x) (EqState.show y) ) ;
                  exit := true )
            | State s1, State s2 ->
                let t1 = transition auto1 s1 in
                let t2 = transition auto2 s2 in
                (* this is very inefficient *)
                push_pairs t1 t2 false exit ;
                r := EqStateSet.add z !r
        done ;
        not !exit )
  end

  include Equivalence
end
