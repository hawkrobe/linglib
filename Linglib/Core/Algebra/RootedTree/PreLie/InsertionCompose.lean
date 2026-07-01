/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Graft
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost

/-!
# Singleton-guest composition of the multi-graft insertion

Inserting one further guest `v` into the outputs of a simultaneous
multi-graft decomposes as: `v` lands at an original host vertex
(extending the simultaneous graft), or inside one of the grafted guest
copies (pre-grafting that guest). This is the single-guest case of the
multi-graft associativity (Oudom-Guin Prop 2.7.v at the basis level)
and the combinatorial content of the Grossman-Larson guest-splitting
identity `GL_product_split_mul_ι`.

## Main results

* `insertion_multiGraft_singleton`: per grafted output, the two-class
  decomposition of single-guest insertion, via `multiGraft_cons_pair`
  (original vertices) and `multiGraft_split_lifted_aux` (guest copies).
* `insertion_bind_singleton`: tree-host form,
  `(insertion T B).bind (insertion · [v]) =
     insertion T (v :: B) + (insertionForest B [v]).bind (insertion T ·)`.
* `insertionForest_bind_singleton`: forest-host form of the same.

All statements are validated computationally on concrete trees,
including the raw (`Tree`-level multiset, not quotient-level) forms of the
last two.
-/

namespace Tree

namespace Pathed

variable {α : Type*}

/-! ### Two-class form of the grafted-vertex decomposition -/

/-- The vertex multiset of a grafted tree: transported originals plus
    lifted guest vertices. Collapses the three classes of
    `vertices_multiGraft_decomp` (`preserveMulti` is `transport` off
    `pairSources`). -/
theorem vertices_multiGraft_transport_lift (T : Tree α)
    (pairs : List (Path × Tree α))
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T) :
    ((vertices (multiGraft T pairs) : List Path) : Multiset Path) =
      ((vertices T : List Path) : Multiset Path).map (transport pairs) +
      (Multiset.ofList (List.finRange pairs.length)).bind
        (fun k => ((vertices pairs[k].snd : List Path) : Multiset Path).map
          (liftMulti pairs k)) := by
  rw [vertices_multiGraft_decomp T pairs h_valid,
      preserved_add_sourceSelf_eq_vertices_map_transport pairs
        ((vertices T : List Path) : Multiset Path)]

/-! ### Single-guest insertion as a vertex sum -/

/-- A single graft is an `insertAt`. -/
private theorem multiGraft_single_pair (W : Tree α) (p : Path) (v : Tree α) :
    multiGraft W [(p, v)] = insertAt p v W := by
  rw [multiGraft_cons_pair, multiGraft_nil, transport_empty_pairs]

/-- Single-guest insertion grafts the guest at each host vertex. -/
theorem insertion_singleton_guest (W v : Tree α) :
    insertion W [v] =
      ((vertices W : List Path) : Multiset Path).map
        (fun p => insertAt p v W) := by
  rw [insertion_def,
      show listChoices (vertices W) ([v] : List (Tree α)).length =
          (vertices W).map (fun p => [p]) from by
        rw [show ([v] : List (Tree α)).length = 1 from rfl, listChoices_succ]
        simp only [listChoices_zero, List.map_cons, List.map_nil]
        induction vertices W with
        | nil => rfl
        | cons p ps ih =>
          rw [List.flatMap_cons, List.map_cons, ← ih]
          rfl,
      List.map_map]
  rw [show ((((vertices W).map
        ((fun choice => multiGraft W (choice.zip [v])) ∘ fun p => [p])) :
        List (Tree α)) : Multiset (Tree α)) =
      ((vertices W : List Path) : Multiset Path).map
        ((fun choice => multiGraft W (choice.zip [v])) ∘ fun p => [p]) from rfl]
  refine Multiset.map_congr rfl fun p _ => ?_
  show multiGraft W [(p, v)] = insertAt p v W
  exact multiGraft_single_pair W p v

/-! ### Per-output decomposition -/

/-- Inserting one guest `v` into a multi-graft output: `v` lands at an
    original vertex (prepend the pair) or inside the `k`-th grafted
    guest (pre-graft that guest). -/
theorem insertion_multiGraft_singleton (T : Tree α)
    (pairs : List (Path × Tree α)) (v : Tree α)
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T) :
    insertion (multiGraft T pairs) [v] =
      ((vertices T : List Path) : Multiset Path).map
        (fun u => multiGraft T ((u, v) :: pairs)) +
      (Multiset.ofList (List.finRange pairs.length)).bind
        (fun k => ((vertices pairs[k].snd : List Path) : Multiset Path).map
          (fun q => multiGraft T
            (pairs.set k.val (pairs[k].fst, insertAt q v pairs[k].snd)))) := by
  rw [insertion_singleton_guest,
      vertices_multiGraft_transport_lift T pairs h_valid,
      Multiset.map_add, Multiset.map_map, Multiset.map_bind]
  congr 1
  · refine Multiset.map_congr rfl fun u _ => ?_
    show insertAt (transport pairs u) v (multiGraft T pairs) =
      multiGraft T ((u, v) :: pairs)
    exact (multiGraft_cons_pair T pairs u v).symm
  · refine Multiset.bind_congr fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun q _ => ?_
    show insertAt (liftMulti pairs k q) v (multiGraft T pairs) =
      multiGraft T (pairs.set k.val (pairs[k].fst, insertAt q v pairs[k].snd))
    exact multiGraft_split_lifted_aux T pairs k q v

/-! ### Singleton-guest associativity -/

/-- Local reproof of `InsertionNodeDecomp.ofList_listChoices_succ`
    (private upstream). A length-`(k+1)` enumeration unfolds to a head
    bind. -/
private theorem ofList_listChoices_succ_local {Y : Type*} (xs : List Y) (k : ℕ) :
    (Multiset.ofList (listChoices xs (k + 1)) : Multiset (List Y)) =
      (Multiset.ofList xs).bind fun v =>
        (Multiset.ofList (listChoices xs k)).map (v :: ·) := by
  rw [listChoices_succ, ← Multiset.coe_bind]
  rfl

/-- For `c.length = B.length`, `c.zip (B.set k w)` equals
    `(c.zip B).set k (c[k], w)`. -/
private theorem zip_set_eq_set_zip {β γ : Type*}
    (c : List β) (B : List γ) (k : ℕ) (w : γ) (hk : k < B.length)
    (hlen : c.length = B.length) :
    c.zip (B.set k w) =
      (c.zip B).set k (c[k]'(by rw [hlen]; exact hk), w) := by
  induction c generalizing B k with
  | nil =>
    simp at hlen
    rw [← hlen] at hk
    exact absurd hk (Nat.not_lt_zero _)
  | cons ch cs ih =>
    cases B with
    | nil => simp at hlen
    | cons bh bs =>
      cases k with
      | zero => simp
      | succ k' =>
        simp only [List.zip_cons_cons, List.set_cons_succ, List.getElem_cons_succ]
        have hk' : k' < bs.length := by
          simp [List.length_cons] at hk; omega
        have hlen' : cs.length = bs.length := by
          simp [List.length_cons] at hlen; omega
        rw [ih bs k' hk' hlen']

/-- Decomposition of `insertionForest B [v]`: insert `v` into each
    position of each tree of `B`. De-privatized 2026-06-12 for
    `GL_T2_reindexing_key` (Q5c) which needs length-preservation of
    single-guest insertion outputs. -/
theorem insertionForest_singleton_guest_set (B : List (Tree α))
    (v : Tree α) :
    insertionForest B [v] =
      (Multiset.ofList (List.finRange B.length)).bind
        (fun k => ((vertices B[k] : List Path) : Multiset Path).map
          (fun q => B.set k.val (insertAt q v B[k]))) := by
  induction B with
  | nil =>
    show insertionForest ([] : List (Tree α)) [v] = _
    rw [insertionForest_empty_host_nonempty_guests]
    show (0 : Multiset _) =
      (Multiset.ofList (List.finRange ([] : List (Tree α)).length)).bind _
    rfl
  | cons b B' ih =>
    rw [insertionForest_cons_assignment]
    -- listChoices [t,f] 1 = [[true],[false]]
    rw [show ([v] : List (Tree α)).length = 1 from rfl]
    rw [show (Multiset.ofList (listChoices [true, false] 1) : Multiset (List Bool)) =
            [true] ::ₘ [false] ::ₘ 0 from rfl,
        Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    -- True branch: insertion b [v], insertionForest B' [], bucket = [B']
    -- Each zip+filterMap reduces by rfl
    show (insertion b [v]).bind
            (fun T' => Multiset.map (fun F' => T' :: F') (insertionForest B' [])) +
          (insertion b []).bind
            (fun T' => Multiset.map (fun F' => T' :: F') (insertionForest B' [v])) = _
    rw [insertionForest_nil_guests B']
    rw [show insertion b ([] : List (Tree α)) = ({b} : Multiset (Tree α)) from by
          rw [insertion_def]
          show (Multiset.ofList [multiGraft b []] : Multiset (Tree α)) = {b}
          rw [multiGraft_nil]; rfl]
    rw [Multiset.singleton_bind]
    rw [show (fun T' => Multiset.map (fun F' => T' :: F') ({B'} : Multiset (List (Tree α)))) =
            (fun T' => ({T' :: B'} : Multiset (List (Tree α)))) from by
          funext T'; rfl]
    rw [Multiset.bind_singleton]
    rw [insertion_singleton_guest]
    rw [ih]
    -- Push the outer maps inside
    rw [Multiset.map_map, Multiset.map_bind]
    -- Now each bind body has Multiset.map (b :: ·) inside; push that through too
    conv_lhs =>
      rhs; rhs; ext k
      rw [Multiset.map_map]
    -- Reassemble with finRange_succ. Use Eq.symm and show form to avoid motive issues.
    symm
    show (Multiset.ofList (List.finRange (b :: B').length)).bind
            (fun k => ((vertices (b :: B')[k.val] : List Path) : Multiset Path).map
              (fun q => (b :: B').set k.val (insertAt q v (b :: B')[k.val]))) = _
    -- Use show to normalize (b :: B').length to B'.length + 1
    show (Multiset.ofList (List.finRange (B'.length + 1))).bind
            (fun k => ((vertices (b :: B')[k.val] : List Path) : Multiset Path).map
              (fun q => (b :: B').set k.val (insertAt q v (b :: B')[k.val]))) = _
    rw [List.finRange_succ]
    show ((0 : Fin (B'.length + 1)) ::ₘ
            ((Multiset.ofList (List.finRange B'.length)).map Fin.succ)).bind _ = _
    rw [Multiset.cons_bind, Multiset.bind_map]
    -- Head simplification
    have head_lhs :
        (((vertices ((b :: B')[(0 : Fin (B'.length + 1)).val])) : List Path) :
            Multiset Path).map (fun q => (b :: B').set (0 : Fin (B'.length + 1)).val
              (insertAt q v ((b :: B')[(0 : Fin (B'.length + 1)).val]))) =
        ((vertices b : List Path) : Multiset Path).map
          (fun q => insertAt q v b :: B') := by
      show ((vertices b : List Path) : Multiset Path).map
            (fun q => (b :: B').set 0 (insertAt q v b)) = _
      refine Multiset.map_congr rfl fun q _ => rfl
    have tail_lhs : (Multiset.ofList (List.finRange B'.length)).bind
            (fun x : Fin B'.length =>
              ((vertices ((b :: B')[(Fin.succ x).val]) : List Path) :
              Multiset Path).map
                (fun q => (b :: B').set (Fin.succ x).val
                  (insertAt q v ((b :: B')[(Fin.succ x).val])))) =
        (Multiset.ofList (List.finRange B'.length)).bind
          (fun k => ((vertices B'[k.val] : List Path) : Multiset Path).map
            (fun q => b :: B'.set k.val (insertAt q v B'[k.val]))) := by
      refine Multiset.bind_congr fun k _ => ?_
      show ((vertices B'[k.val] : List Path) : Multiset Path).map
              (fun q => (b :: B').set (k.val + 1) (insertAt q v B'[k.val])) = _
      refine Multiset.map_congr rfl fun q _ => rfl
    rw [head_lhs, tail_lhs]
    -- LHS = head + bind, RHS = head_composed + bind_composed
    -- Both are pointwise equal; compose maps are defeq
    rfl

/-- Tree-host singleton-guest associativity: grafting `B` then one more
    guest `v` equals grafting `v :: B` simultaneously plus grafting `B`
    with `v` nested into one of its trees. Raw `Tree`-level multiset equality. -/
theorem insertion_bind_singleton (T : Tree α) (B : List (Tree α))
    (v : Tree α) :
    (insertion T B).bind (fun W => insertion W [v]) =
      insertion T (v :: B) +
      (insertionForest B [v]).bind (fun B' => insertion T B') := by
  -- LHS: unfold insertion T B
  rw [insertion_def T B]
  rw [show ((Multiset.ofList ((listChoices (vertices T) B.length).map
              fun choice => multiGraft T (choice.zip B))) :
            Multiset (Tree α)) =
          (Multiset.ofList (listChoices (vertices T) B.length)).map
            (fun choice => multiGraft T (choice.zip B)) from rfl,
      Multiset.bind_map]
  -- Per c: apply C3
  rw [Multiset.bind_congr (g := fun c =>
        ((vertices T : List Path) : Multiset Path).map
          (fun u => multiGraft T ((u, v) :: c.zip B)) +
        (Multiset.ofList (List.finRange (c.zip B).length)).bind
          (fun k => ((vertices (c.zip B)[k].snd : List Path) : Multiset Path).map
            (fun q => multiGraft T
              ((c.zip B).set k.val ((c.zip B)[k].fst,
                insertAt q v (c.zip B)[k].snd)))))
        (fun c hc => insertion_multiGraft_singleton T (c.zip B) v
          (forall_zip_isValidPath_of_listChoices T B c (by rwa [Multiset.mem_coe] at hc)))]
  rw [Multiset.bind_add]
  congr 1
  · -- Original class: bind c, (vertices T).map (u => mG T ((u,v) :: c.zip B))
    --                = insertion T (v :: B)
    rw [insertion_def T (v :: B), show (v :: B).length = B.length + 1 from rfl]
    rw [show ((Multiset.ofList ((listChoices (vertices T) (B.length + 1)).map
              fun choice => multiGraft T (choice.zip (v :: B)))) :
            Multiset (Tree α)) =
          (Multiset.ofList (listChoices (vertices T) (B.length + 1))).map
            (fun choice => multiGraft T (choice.zip (v :: B))) from rfl]
    rw [ofList_listChoices_succ_local (vertices T) B.length, Multiset.map_bind]
    -- RHS = bind u ∈ vertices T, (listChoices ... B.length).map (u::·).map (mG T ∘ (·.zip (v::B)))
    -- Push the second map through: (·.map (u::·)).map(f) = ·.map(f ∘ (u::·))
    rw [show (fun u : Path =>
            Multiset.map (fun choice : List Path => multiGraft T (choice.zip (v :: B)))
              ((Multiset.ofList (listChoices (vertices T) B.length)).map (u :: ·))) =
          (fun u : Path =>
            (Multiset.ofList (listChoices (vertices T) B.length)).map
              fun c => multiGraft T ((u, v) :: c.zip B)) from by
        funext u
        rw [Multiset.map_map]
        rfl]
    -- Swap bind/map ordering: bind u (map c) = bind c (map u)
    -- Use bind_singleton form on both
    rw [show (fun u : Path =>
            (Multiset.ofList (listChoices (vertices T) B.length)).map
              fun c => multiGraft T ((u, v) :: c.zip B)) =
          (fun u : Path =>
            (Multiset.ofList (listChoices (vertices T) B.length)).bind
              fun c => ({multiGraft T ((u, v) :: c.zip B)} : Multiset (Tree α))) from by
        funext u
        rw [Multiset.bind_singleton]]
    -- Bind swap via Multiset.bind_bind
    rw [show ((((vertices T : List Path) : Multiset Path)).bind fun u =>
            (Multiset.ofList (listChoices (vertices T) B.length)).bind
              fun c => ({multiGraft T ((u, v) :: c.zip B)} : Multiset (Tree α))) =
          ((Multiset.ofList (listChoices (vertices T) B.length)).bind fun c =>
            (((vertices T : List Path) : Multiset Path)).bind fun u =>
              ({multiGraft T ((u, v) :: c.zip B)} : Multiset (Tree α))) from by
        rw [Multiset.bind_bind]]
    refine Multiset.bind_congr fun c _ => ?_
    rw [Multiset.bind_singleton]
  · -- Nested class: bind c, (finRange (c.zip B).length).bind k => (vertices (c.zip B)[k].snd).map (q => mG T ((c.zip B).set k (...)))
    -- RHS: (insertionForest B [v]).bind (insertion T)
    rw [insertionForest_singleton_guest_set B v]
    rw [Multiset.bind_assoc]
    -- Per-k: rewrite map-then-bind via bind_map
    conv_rhs =>
      rhs; ext k
      rw [Multiset.bind_map]
    -- Per-k per-q: unfold insertion T (B.set k _) into map form
    have h_insertion_set : ∀ (k : Fin B.length) (q : Path),
        insertion T (B.set k.val (insertAt q v B[k])) =
        (Multiset.ofList (listChoices (vertices T) B.length)).map
          (fun choice => multiGraft T
            (choice.zip (B.set k.val (insertAt q v B[k])))) := by
      intro k q
      rw [insertion_def, List.length_set]
      rfl
    conv_rhs =>
      rhs; ext k; rhs; ext q
      rw [h_insertion_set]
    -- Convert each inner map to bind {·} using Multiset.bind_singleton (in reverse)
    conv_rhs =>
      rhs; ext k; rhs; ext q
      rw [← Multiset.bind_singleton (f := fun choice : List Path =>
            multiGraft T (choice.zip (B.set k.val (insertAt q v B[k]))))]
    -- Swap inner bind q with bind choice via Multiset.bind_bind (innermost first)
    conv_rhs =>
      rhs; ext k
      rw [Multiset.bind_bind]
    -- Now swap outer bind k with bind choice
    conv_rhs =>
      rw [Multiset.bind_bind]
    refine Multiset.bind_congr fun c hc => ?_
    have hc_mem : c ∈ listChoices (vertices T) B.length := by
      rwa [Multiset.mem_coe] at hc
    have hc_len : c.length = B.length :=
      mem_listChoices_length (vertices T) B.length c hc_mem
    have hzip_len : (c.zip B).length = B.length := by
      rw [List.length_zip, hc_len, min_self]
    -- Inside the c-bind: need
    --   bind k ∈ finRange B.length, bind q ∈ vertices B[k], {mG T (c.zip (B.set k (insertAt q v B[k])))}
    -- = bind k ∈ finRange (c.zip B).length, map q ∈ vertices (c.zip B)[k].snd, mG T ((c.zip B).set k ((c.zip B)[k].fst, insertAt q v (c.zip B)[k].snd))
    -- Use hzip_len for finRange equality, zip_set for the set transformation, getElem of zip for projections.
    -- Convert RHS inner map back to bind {·}
    rw [show ((Multiset.ofList (List.finRange (c.zip B).length)).bind
            fun k : Fin (c.zip B).length =>
              ((vertices (c.zip B)[k].snd : List Path) : Multiset Path).map
                (fun q => multiGraft T
                  ((c.zip B).set k.val ((c.zip B)[k].fst,
                    insertAt q v (c.zip B)[k].snd)))) =
          ((Multiset.ofList (List.finRange (c.zip B).length)).bind
            fun k : Fin (c.zip B).length =>
              ((vertices (c.zip B)[k].snd : List Path) : Multiset Path).bind
                (fun q =>
                  ({multiGraft T
                    ((c.zip B).set k.val ((c.zip B)[k].fst,
                      insertAt q v (c.zip B)[k].snd))} : Multiset (Tree α)))) from by
        refine Multiset.bind_congr fun k _ => ?_
        rw [← Multiset.bind_singleton]]
    -- Now LHS: bind k ∈ finRange B.length, bind q ∈ vertices B[k], {mG T (c.zip (B.set k ...))}
    -- RHS: bind k ∈ finRange (c.zip B).length, bind q ∈ vertices (c.zip B)[k].snd, {mG T ((c.zip B).set k ...)}
    -- Bridge finRange (c.zip B).length to finRange B.length via Fin.cast
    -- We show RHS = LHS by congruence at each k after recognizing (c.zip B)[k] = (c[k], B[k]).
    symm
    -- Cast finRange index using hzip_len: finRange (c.zip B).length = (finRange B.length).map (Fin.cast hzip_len.symm)
    rw [show (Multiset.ofList (List.finRange (c.zip B).length) : Multiset (Fin (c.zip B).length)) =
            (Multiset.ofList (List.finRange B.length)).map (Fin.cast hzip_len.symm) from by
        show (Multiset.ofList (List.finRange (c.zip B).length) : Multiset (Fin (c.zip B).length)) =
              Multiset.ofList ((List.finRange B.length).map (Fin.cast hzip_len.symm))
        congr 1
        apply List.ext_getElem
        · rw [List.length_map, List.length_finRange, List.length_finRange, hzip_len]
        · intro n h1 h2
          rw [List.getElem_map, List.getElem_finRange, List.getElem_finRange]
          rfl]
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun k _ => ?_
    -- Per k: (c.zip B)[k] = (c[k], B[k]) elementwise. Use show to normalize
    -- Fin.cast hzip_len.symm k indexing back to k.val.
    have hk_lt_c : k.val < c.length := by rw [hc_len]; exact k.isLt
    have hk_lt_zip : k.val < (c.zip B).length := by rw [hzip_len]; exact k.isLt
    -- The Fin.cast indexing reduces by defeq to k.val indexing
    show ((vertices B[k] : List Path) : Multiset Path).bind
            (fun a => ({multiGraft T (c.zip (B.set k.val (insertAt a v B[k])))} :
              Multiset (Tree α))) =
          (((vertices ((c.zip B)[k.val]'hk_lt_zip).snd : List Path) : Multiset Path)).bind
            fun q => ({multiGraft T ((c.zip B).set k.val
              (((c.zip B)[k.val]'hk_lt_zip).fst, insertAt q v ((c.zip B)[k.val]'hk_lt_zip).snd))} :
                Multiset (Tree α))
    have hzip_get : (c.zip B)[k.val]'hk_lt_zip = (c[k.val]'hk_lt_c, B[k.val]'k.isLt) := by
      rw [List.getElem_zip]
    rw [hzip_get]
    refine Multiset.bind_congr fun q _ => ?_
    have h_set : c.zip (B.set k.val (insertAt q v B[k.val])) =
        (c.zip B).set k.val (c[k.val]'hk_lt_c, insertAt q v B[k.val]) :=
      zip_set_eq_set_zip c B k.val (insertAt q v B[k.val]) k.isLt hc_len
    show ({multiGraft T (c.zip (B.set k.val (insertAt q v B[k.val])))} : Multiset _) =
          ({multiGraft T ((c.zip B).set k.val
            (c[k.val]'hk_lt_c, insertAt q v B[k.val]))} : Multiset _)
    rw [h_set]

/-- Single-guest insertion on a cons-forest splits into the v→head and
    v→tail branches. Specialization of `insertionForest_cons_assignment`
    at guests `[v]`, collapsing the [true]/[false] mask enumeration via
    `insertion_nil_guests` and `insertionForest_nil_guests`. -/
private theorem insertionForest_cons_singleton (T : Tree α)
    (F : List (Tree α)) (v : Tree α) :
    insertionForest (T :: F) [v] =
      (insertion T [v]).map (fun T' => T' :: F) +
      (insertionForest F [v]).map (fun F' => T :: F') := by
  rw [insertionForest_cons_assignment]
  rw [show ([v] : List (Tree α)).length = 1 from rfl]
  rw [show (Multiset.ofList (listChoices [true, false] 1) : Multiset (List Bool)) =
          [true] ::ₘ [false] ::ₘ 0 from rfl,
      Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  -- True branch: zip [v] [true] = [(v, true)], filterMap true→Some, false→None
  -- → T-bucket = [v], F-bucket = [].
  -- False branch: zip [v] [false] = [(v, false)] → T-bucket = [], F-bucket = [v].
  show (insertion T [v]).bind
          (fun T' => (insertionForest F []).map (fun F' => T' :: F')) +
        (insertion T []).bind
          (fun T' => (insertionForest F [v]).map (fun F' => T' :: F')) = _
  rw [insertionForest_nil_guests F, insertion_nil_guests T]
  rw [Multiset.singleton_bind]
  -- True branch: (insertion T [v]).bind (T' => {F}.map (T' :: ·)) = (insertion T [v]).map (· :: F)
  rw [show (fun T' : Tree α =>
            ({F} : Multiset (List (Tree α))).map (fun F' => T' :: F')) =
          (fun T' : Tree α => ({T' :: F} : Multiset (List (Tree α)))) from by
        funext T'; rw [Multiset.map_singleton]]
  rw [show (fun T' : Tree α => ({T' :: F} : Multiset (List (Tree α)))) =
          (fun T' : Tree α => ({(fun T'' => T'' :: F) T'} : Multiset _)) from rfl]
  rw [Multiset.bind_singleton (f := fun T' => T' :: F)]

/-- Bucketing lemma: single-guest insertion `insertionForest B [v]`
    modifies exactly one position of `B`, so after partitioning each
    output `B'` into a t-bucket and f-bucket according to a fixed mask
    `m` (of length `B.length`), the modification appears in exactly one
    of the two buckets. The factored form, summing over a general
    consumer `G`, lets us instantiate `G` to the cons-assignment body
    in `insertionForest_bind_singleton`.

    De-privatized 2026-06-12 for `GL_product_split_mul_ι` (Q5c per-tprod
    induction): the same bucket-split, after descent through the
    `listChoices_bridge_powerset_paired` translation, supplies the
    reindexing for `T2 = F * insertion (op G) (op of'{v})` against the
    powerset-of-B sum produced by `mul_of'_sum_form` + Leibniz on the
    other terms. -/
theorem insertionForest_singleton_bucket_split
    {γ : Type*} (B : List (Tree α)) (m : List Bool) (v : Tree α)
    (G : List (Tree α) → List (Tree α) → Multiset γ)
    (hlen : m.length = B.length) :
    (insertionForest B [v]).bind (fun B' =>
        G ((B'.zip m).filterMap (fun p => if p.snd then some p.fst else none))
          ((B'.zip m).filterMap (fun p => if p.snd then none else some p.fst))) =
      (insertionForest
          ((B.zip m).filterMap (fun p => if p.snd then some p.fst else none))
          [v]).bind (fun W =>
        G W ((B.zip m).filterMap (fun p => if p.snd then none else some p.fst))) +
      (insertionForest
          ((B.zip m).filterMap (fun p => if p.snd then none else some p.fst))
          [v]).bind (fun W' =>
        G ((B.zip m).filterMap (fun p => if p.snd then some p.fst else none)) W') := by
  induction B generalizing m G with
  | nil =>
    -- B = [] → insertionForest [] [v] = 0, both buckets = []; LHS = 0.bind = 0.
    -- RHS: insertionForest ([].filterMap ...) [v] = insertionForest [] [v] = 0 on both sides.
    rw [insertionForest_empty_host_nonempty_guests, Multiset.zero_bind]
    have hm : m = [] := by
      cases m with
      | nil => rfl
      | cons _ _ => simp at hlen
    subst hm
    simp only [List.zip_nil_left, List.filterMap_nil,
               insertionForest_empty_host_nonempty_guests,
               Multiset.zero_bind, add_zero]
  | cons b B' ih =>
    -- m has the form b' :: m' with m'.length = B'.length.
    cases m with
    | nil => simp at hlen
    | cons b' m' =>
      have hm' : m'.length = B'.length := by
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        exact hlen
      -- Stage 0 expansion of insertionForest (b :: B') [v].
      rw [insertionForest_cons_singleton b B' v, Multiset.add_bind]
      -- Reduce zip & filterMap on the cons.
      cases b' with
      | true =>
        -- m head = true: head b goes into t-bucket.
        -- zip (b :: B') (true :: m') = (b, true) :: B'.zip m'
        -- t-bucket = b :: (B'.zip m').filterMap tpick
        -- f-bucket = (B'.zip m').filterMap fpick
        show ((insertion b [v]).map (fun T' => T' :: B')).bind
                (fun B'' =>
                  G ((B''.zip (true :: m')).filterMap
                      (fun p => if p.snd then some p.fst else none))
                    ((B''.zip (true :: m')).filterMap
                      (fun p => if p.snd then none else some p.fst))) +
              ((insertionForest B' [v]).map (fun F' => b :: F')).bind
                (fun B'' =>
                  G ((B''.zip (true :: m')).filterMap
                      (fun p => if p.snd then some p.fst else none))
                    ((B''.zip (true :: m')).filterMap
                      (fun p => if p.snd then none else some p.fst))) = _
        rw [Multiset.bind_map, Multiset.bind_map]
        -- Inside each bind: zip with true at head.
        -- (T' :: B').zip (true :: m') = (T', true) :: B'.zip m'
        -- filterMap tpick = T' :: (B'.zip m').filterMap tpick
        -- filterMap fpick = (B'.zip m').filterMap fpick
        -- (b :: F').zip (true :: m') = (b, true) :: F'.zip m'
        -- filterMap tpick = b :: (F'.zip m').filterMap tpick
        -- filterMap fpick = (F'.zip m').filterMap fpick
        -- For the second part, apply IH at m'.
        have hl1 :
            ((insertion b [v]).bind fun T' =>
              G (T' :: (B'.zip m').filterMap (fun p => if p.snd then some p.fst else none))
                ((B'.zip m').filterMap (fun p => if p.snd then none else some p.fst))) =
            (insertion b [v]).bind fun T' =>
              G ((((T' :: B').zip (true :: m')).filterMap
                  (fun p => if p.snd then some p.fst else none)))
                ((((T' :: B').zip (true :: m')).filterMap
                  (fun p => if p.snd then none else some p.fst))) := by
          refine Multiset.bind_congr fun T' _ => ?_
          show G (T' :: _) _ = G _ _
          rfl
        have hl2 :
            ((insertionForest B' [v]).bind fun F' =>
              G (b :: (F'.zip m').filterMap (fun p => if p.snd then some p.fst else none))
                ((F'.zip m').filterMap (fun p => if p.snd then none else some p.fst))) =
            (insertionForest B' [v]).bind fun F' =>
              G ((((b :: F').zip (true :: m')).filterMap
                  (fun p => if p.snd then some p.fst else none)))
                ((((b :: F').zip (true :: m')).filterMap
                  (fun p => if p.snd then none else some p.fst))) := by
          refine Multiset.bind_congr fun F' _ => ?_
          show G (b :: _) _ = G _ _
          rfl
        rw [← hl1, ← hl2]
        -- Apply IH to the second summand at m' with `G_b := fun W W' => G (b :: W) W'`.
        -- This rewrites it into the t-bucket+f-bucket form (relative to `B'`).
        have hIH := ih (m := m') (G := fun W W' => G (b :: W) W') hm'
        rw [hIH]
        -- RHS: insertionForest (b :: tT) [v] decomposes via Stage 0 into
        --   (insertion b [v]).map (· :: tT) + (insertionForest tT [v]).map (b :: ·)
        -- which after binding with G(·, fT) splits into exactly the first two LHS summands.
        show _ + (_ + _) = _ + _
        -- Show RHS first term equals first + middle of LHS.
        have h_rhs_t :
            ((((b :: B').zip (true :: m')).filterMap
                (fun p => if p.snd then some p.fst else none))) =
            b :: ((B'.zip m').filterMap (fun p => if p.snd then some p.fst else none)) := rfl
        have h_rhs_f :
            ((((b :: B').zip (true :: m')).filterMap
                (fun p => if p.snd then none else some p.fst))) =
            ((B'.zip m').filterMap (fun p => if p.snd then none else some p.fst)) := rfl
        rw [h_rhs_t, h_rhs_f]
        rw [insertionForest_cons_singleton b _ v]
        rw [Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
        rw [add_assoc]
      | false =>
        -- m head = false: head b goes into f-bucket.
        -- zip (b :: B') (false :: m') = (b, false) :: B'.zip m'
        -- t-bucket = (B'.zip m').filterMap tpick
        -- f-bucket = b :: (B'.zip m').filterMap fpick
        show ((insertion b [v]).map (fun T' => T' :: B')).bind
                (fun B'' =>
                  G ((B''.zip (false :: m')).filterMap
                      (fun p => if p.snd then some p.fst else none))
                    ((B''.zip (false :: m')).filterMap
                      (fun p => if p.snd then none else some p.fst))) +
              ((insertionForest B' [v]).map (fun F' => b :: F')).bind
                (fun B'' =>
                  G ((B''.zip (false :: m')).filterMap
                      (fun p => if p.snd then some p.fst else none))
                    ((B''.zip (false :: m')).filterMap
                      (fun p => if p.snd then none else some p.fst))) = _
        rw [Multiset.bind_map, Multiset.bind_map]
        have hl1 :
            ((insertion b [v]).bind fun T' =>
              G ((B'.zip m').filterMap (fun p => if p.snd then some p.fst else none))
                (T' :: (B'.zip m').filterMap (fun p => if p.snd then none else some p.fst))) =
            (insertion b [v]).bind fun T' =>
              G ((((T' :: B').zip (false :: m')).filterMap
                  (fun p => if p.snd then some p.fst else none)))
                ((((T' :: B').zip (false :: m')).filterMap
                  (fun p => if p.snd then none else some p.fst))) := by
          refine Multiset.bind_congr fun T' _ => ?_
          show G _ (T' :: _) = G _ _
          rfl
        have hl2 :
            ((insertionForest B' [v]).bind fun F' =>
              G ((F'.zip m').filterMap (fun p => if p.snd then some p.fst else none))
                (b :: (F'.zip m').filterMap (fun p => if p.snd then none else some p.fst))) =
            (insertionForest B' [v]).bind fun F' =>
              G ((((b :: F').zip (false :: m')).filterMap
                  (fun p => if p.snd then some p.fst else none)))
                ((((b :: F').zip (false :: m')).filterMap
                  (fun p => if p.snd then none else some p.fst))) := by
          refine Multiset.bind_congr fun F' _ => ?_
          show G _ (b :: _) = G _ _
          rfl
        rw [← hl1, ← hl2]
        -- Apply IH at m' with G_b := fun W W' => G W (b :: W').
        have hIH := ih (m := m') (G := fun W W' => G W (b :: W')) hm'
        rw [hIH]
        show _ + (_ + _) = _ + _
        have h_rhs_t :
            ((((b :: B').zip (false :: m')).filterMap
                (fun p => if p.snd then some p.fst else none))) =
            ((B'.zip m').filterMap (fun p => if p.snd then some p.fst else none)) := rfl
        have h_rhs_f :
            ((((b :: B').zip (false :: m')).filterMap
                (fun p => if p.snd then none else some p.fst))) =
            b :: ((B'.zip m').filterMap (fun p => if p.snd then none else some p.fst)) := rfl
        rw [h_rhs_t, h_rhs_f]
        rw [insertionForest_cons_singleton b _ v]
        rw [Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
        -- LHS = A + (X + Y), RHS = X' + (A' + Y')
        -- where A = (insertion b [v]).bind (T' => G tT (T' :: fT))
        --       X = (insertionForest tT [v]).bind (W => G W (b :: fT))
        --       Y = (insertionForest fT [v]).bind (W' => G tT (b :: W'))
        --       X' = (insertionForest tT [v]).bind (W => G W (b :: fT))  [same as X]
        --       A' = (insertion b [v]).bind (T' => G tT (T' :: fT))      [same as A]
        --       Y' = (insertionForest fT [v]).bind (W' => G tT (b :: W'))  [same as Y]
        -- So LHS = A + X + Y, RHS = X + A + Y, equal by add_left_comm.
        rw [← add_assoc, ← add_assoc, add_comm
              ((insertion b [v]).bind _)
              ((insertionForest _ [v]).bind _)]

/-- Forest-host singleton-guest associativity. Raw `Tree`-level multiset
    equality; the nonplanar `insertionMultiset` form follows by the
    standard quotient descent. -/
theorem insertionForest_bind_singleton (A B : List (Tree α))
    (v : Tree α) :
    (insertionForest A B).bind (fun X => insertionForest X [v]) =
      insertionForest A (v :: B) +
      (insertionForest B [v]).bind (fun B' => insertionForest A B') := by
  induction A generalizing B with
  | nil =>
    -- LHS: (insertionForest [] B).bind = either {[]}.bind (when B = []) or 0.bind (when B nonempty)
    -- RHS: insertionForest [] (v::B) = 0 (since v::B is nonempty), plus the second term.
    cases B with
    | nil =>
      -- LHS = {[]}.bind (insertionForest · [v]) = insertionForest [] [v] = 0
      rw [insertionForest_nil_nil, Multiset.singleton_bind,
          insertionForest_empty_host_nonempty_guests]
      -- RHS = insertionForest [] [v] + (insertionForest [] [v]).bind ... = 0 + 0.bind = 0
      rw [Multiset.zero_bind, add_zero]
    | cons b B' =>
      -- LHS = 0.bind = 0
      rw [insertionForest_empty_host_nonempty_guests, Multiset.zero_bind]
      -- RHS: insertionForest [] (v::b::B') + (insertionForest (b::B') [v]).bind (insertionForest [] ·)
      rw [insertionForest_empty_host_nonempty_guests, zero_add]
      -- (insertionForest (b::B') [v]).bind (insertionForest [] ·): each output forest is non-empty
      -- so insertionForest [] of nonempty list = 0; bind sums to 0.
      rw [insertionForest_singleton_guest_set]
      rw [Multiset.bind_assoc]
      -- Goal: bind k, (map q ...).bind (insertionForest [] ·) = 0
      rw [show (fun k : Fin (b :: B').length =>
              (((vertices (b :: B')[k] : List Path) : Multiset Path).map
                (fun q => (b :: B').set k.val (insertAt q v (b :: B')[k]))).bind
              (insertionForest ([] : List (Tree α)))) =
            (fun _ : Fin (b :: B').length => (0 : Multiset (List (Tree α)))) from by
          funext k
          rw [Multiset.bind_map]
          -- Each inner: insertionForest [] (b::B').set k _ — nonempty because set preserves cons-shape
          -- Show: bind q ∈ vertices, 0 = 0 via bind_zero
          have set_cons_form : ∀ (xs : List (Tree α)) (n : ℕ) (w : Tree α),
              ∃ x' xs', ((b :: xs).set n w : List (Tree α)) = x' :: xs' := by
            intro xs n w
            cases n with
            | zero => exact ⟨w, xs, rfl⟩
            | succ n' => exact ⟨b, xs.set n' w, rfl⟩
          have : ∀ q,
              insertionForest ([] : List (Tree α))
                ((b :: B').set k.val (insertAt q v (b :: B')[k])) = 0 := by
            intro q
            obtain ⟨x', xs', hxs⟩ := set_cons_form B' k.val (insertAt q v (b :: B')[k])
            rw [hxs]
            exact insertionForest_empty_host_nonempty_guests x' xs'
          rw [show ((vertices (b :: B')[k] : List Path) : Multiset Path).bind
                (fun q => insertionForest ([] : List (Tree α))
                  ((b :: B').set k.val (insertAt q v (b :: B')[k]))) =
                  ((vertices (b :: B')[k] : List Path) : Multiset Path).bind
                  (fun _ => (0 : Multiset (List (Tree α)))) from by
                refine Multiset.bind_congr fun q _ => ?_
                exact this q]
          rw [Multiset.bind_zero]]
      rw [Multiset.bind_zero]
  | cons T A' ih =>
    -- See `scratch/validate_s5.lean` for the computational validation of this
    -- statement.  Strategy (writing tpick/fpick for the bucket filterMaps):
    --
    --   LHS expansion: expand `insertionForest (T::A') B` via cons_assignment,
    --   push the outer `(· .bind insertionForest · [v])` through the bind chain,
    --   apply Stage 0 (`insertionForest_cons_singleton`) to the inner
    --   `insertionForest (T'::F') [v]`, then distribute via `bind_add`:
    --     LHS = Σ_m [L1(m) + L2(m)]
    --   where (with B_t := (B.zip m).tpick, B_f := (B.zip m).fpick)
    --     L1(m) = (insertion T B_t).bind (T' =>
    --              (insertionForest A' B_f).bind (F' =>
    --                (insertion T' [v]).map (· :: F')))
    --     L2(m) = (insertion T B_t).bind (T' =>
    --              (insertionForest A' B_f).bind (F' =>
    --                (insertionForest F' [v]).map (T' :: ·)))
    --
    --   For L1(m), swap the F'-bind and T''-bind via `bind_bind`, fold via
    --   `bind_assoc`, then apply C4 (`insertion_bind_singleton`) to
    --   `(insertion T B_t).bind (T' => insertion T' [v])`:
    --     L1(m) = L1a(m) + L1b(m)
    --   with
    --     L1a(m) = (insertion T (v :: B_t)).bind (T'' =>
    --                (insertionForest A' B_f).map (T'' :: ·))
    --     L1b(m) = (insertionForest B_t [v]).bind (Bt' =>
    --                (insertion T Bt').bind (T'' =>
    --                  (insertionForest A' B_f).map (T'' :: ·)))
    --
    --   For L2(m), unfold the inner map to a bind-then-singleton, swap the F'-
    --   and singleton-binds via `bind_assoc`, apply the IH to
    --   `(insertionForest A' B_f).bind (F' => insertionForest F' [v])`, then
    --   redistribute via `bind_add` and refold to a map:
    --     L2(m) = L2a(m) + L2b(m)
    --   with
    --     L2a(m) = (insertion T B_t).bind (T' =>
    --                (insertionForest A' (v :: B_f)).map (T' :: ·))
    --     L2b(m) = (insertion T B_t).bind (T' =>
    --                ((insertionForest B_f [v]).bind (insertionForest A')).map (T' :: ·))
    --
    --   RHS expansion. RHS term 1 = `insertionForest (T::A') (v::B)` via cons_assignment
    --   over guests `v::B` (length B.length + 1). Peel the v-decision via
    --   `ofList_listChoices_succ_local`: the b=true branch gives Σ_m L1a, the b=false
    --   branch gives Σ_m L2a. RHS term 2 = (insertionForest B [v]).bind (B' =>
    --   insertionForest (T::A') B'); expand the inner cons_assignment, swap outer
    --   B'-bind with mask-bind, then for each mask apply Stage 6
    --   (`insertionForest_singleton_bucket_split`) with consumer
    --   `G Bt Bf = (insertion T Bt).bind (T' => (insertionForest A' Bf).map (T' :: ·))`.
    --   That gives Σ_m [L1b + L2b].
    --
    --   Stage 7 (assemble): Σ_m [L1a + L1b + L2a + L2b] = (Σ_m L1a + Σ_m L2a)
    --     + (Σ_m L1b + Σ_m L2b) by bind_add + add_assoc/comm.
    --
    -- Canonical sum-of-four form, parameterized by mask. Both LHS and RHS reduce to
    --   Σ_m [L1a + L1b + L2a + L2b]
    -- where (with B_t := (B.zip m).filterMap tp, B_f := (B.zip m).filterMap fp):
    --   L1a m = (insertion T (v :: B_t)).bind (T' => (insertionForest A' B_f).map (T' :: ·))
    --   L1b m = ((insertionForest B_t [v]).bind (insertion T)).bind (T'' => (insertionForest A' B_f).map (T'' :: ·))
    --   L2a m = (insertion T B_t).bind (T' => (insertionForest A' (v :: B_f)).map (T' :: ·))
    --   L2b m = (insertion T B_t).bind (T' => ((insertionForest B_f [v]).bind (insertionForest A')).map (T' :: ·))
    set tp : Tree α × Bool → Option (Tree α) :=
      fun p => if p.snd then some p.fst else none with htp_def
    set fp : Tree α × Bool → Option (Tree α) :=
      fun p => if p.snd then none else some p.fst with hfp_def
    set L1a : List Bool → Multiset (List (Tree α)) := fun m =>
      (insertion T (v :: (B.zip m).filterMap tp)).bind fun T' =>
        (insertionForest A' ((B.zip m).filterMap fp)).map (T' :: ·) with hL1a_def
    set L1b : List Bool → Multiset (List (Tree α)) := fun m =>
      ((insertionForest ((B.zip m).filterMap tp) [v]).bind
        fun Bt' => insertion T Bt').bind fun T'' =>
          (insertionForest A' ((B.zip m).filterMap fp)).map (T'' :: ·) with hL1b_def
    set L2a : List Bool → Multiset (List (Tree α)) := fun m =>
      (insertion T ((B.zip m).filterMap tp)).bind fun T' =>
        (insertionForest A' (v :: (B.zip m).filterMap fp)).map (T' :: ·) with hL2a_def
    set L2b : List Bool → Multiset (List (Tree α)) := fun m =>
      (insertion T ((B.zip m).filterMap tp)).bind fun T' =>
        ((insertionForest ((B.zip m).filterMap fp) [v]).bind
          (fun B'' => insertionForest A' B'')).map (T' :: ·) with hL2b_def
    -- LHS = canon.
    have h_lhs : ((insertionForest (T :: A') B).bind fun X => insertionForest X [v]) =
        (Multiset.ofList (listChoices [true, false] B.length)).bind fun m =>
          L1a m + L1b m + L2a m + L2b m := by
      rw [insertionForest_cons_assignment, Multiset.bind_assoc]
      refine Multiset.bind_congr fun m _ => ?_
      -- per-mask, the LHS body
      --   = (insertion T B_t).bind (T' => (insertionForest A' B_f).map (T' :: ·)).bind (insertionForest · [v])
      -- We show this equals L1a m + L1b m + L2a m + L2b m.
      rw [Multiset.bind_assoc]
      -- inner T'-body becomes (insertionForest A' B_f).map (T' :: ·) .bind (insertionForest · [v])
      --                     = (insertionForest A' B_f).bind (F' => insertionForest (T' :: F') [v])  [bind_map]
      conv_lhs =>
        rhs; ext T'
        rw [Multiset.bind_map]
      -- Apply Stage 0 in the inner F'-body, distribute bind_add and map_add.
      conv_lhs =>
        rhs; ext T'; rhs; ext F'
        rw [insertionForest_cons_singleton T' F' v]
      conv_lhs =>
        rhs; ext T'
        rw [Multiset.bind_add]
      rw [Multiset.bind_add]
      -- LHS = (insertion T B_t).bind (T' => bind F' (insertion T' [v]).map (· :: F'))
      --     + (insertion T B_t).bind (T' => bind F' (insertionForest F' [v]).map (T' :: ·))
      --
      -- First summand reshape: swap F'-bind with the (insertion T' [v]).map via converting
      -- map → singleton-bind and Multiset.bind_bind.
      have h1 :
          ((insertion T ((B.zip m).filterMap tp)).bind fun T' =>
            (insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
              (insertion T' [v]).map (fun T'' => T'' :: F')) =
          L1a m + L1b m := by
        -- Step 1: convert inner .map to bind {·}, swap binds, refold to map.
        conv_lhs =>
          rhs; ext T'; rhs; ext F'
          rw [show (insertion T' [v]).map (fun T'' => T'' :: F') =
                (insertion T' [v]).bind (fun T'' => ({T'' :: F'} : Multiset _)) from by
              rw [Multiset.bind_singleton]]
        conv_lhs =>
          rhs; ext T'
          rw [Multiset.bind_bind]
        conv_lhs =>
          rhs; ext T'; rhs; ext T''
          rw [show ((insertionForest A' ((B.zip m).filterMap fp)).bind
                    fun F' => ({T'' :: F'} : Multiset _)) =
                (insertionForest A' ((B.zip m).filterMap fp)).map (T'' :: ·) from by
              rw [Multiset.bind_singleton]]
        -- Now: (insertion T B_t).bind (T' => (insertion T' [v]).bind (T'' => (insertionForest A' B_f).map (T'' :: ·)))
        --    = ((insertion T B_t).bind (T' => insertion T' [v])).bind (T'' => ...)   [bind_assoc]
        rw [← Multiset.bind_assoc]
        -- Apply C4: (insertion T B_t).bind (T' => insertion T' [v]) = insertion T (v :: B_t) + (insertionForest B_t [v]).bind (insertion T)
        rw [insertion_bind_singleton T ((B.zip m).filterMap tp) v]
        rw [Multiset.add_bind]
        -- = L1a m + L1b m by definitional unfolding of L1a, L1b (rw closes)
      -- Second summand reshape: pull (insertionForest F' [v]) outside via map → bind {·} → bind_assoc → refold.
      have h2 :
          ((insertion T ((B.zip m).filterMap tp)).bind fun T' =>
            (insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
              (insertionForest F' [v]).map (T' :: ·)) =
          L2a m + L2b m := by
        -- Step 1: For each T', the inner .bind F' .map (T' :: ·) = (bind F' (iF F' [v])).map (T' :: ·)
        conv_lhs =>
          rhs; ext T'
          rw [show ((insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
                (insertionForest F' [v]).map (T' :: ·)) =
                ((insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
                  insertionForest F' [v]).map (T' :: ·) from by
              conv_lhs =>
                rhs; ext F'
                rw [show (insertionForest F' [v]).map (fun X => T' :: X) =
                      (insertionForest F' [v]).bind (fun X => ({T' :: X} : Multiset _)) from by
                    rw [Multiset.bind_singleton]]
              rw [← Multiset.bind_assoc]
              rw [show ((insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
                      insertionForest F' [v]).bind (fun X => ({T' :: X} : Multiset _)) =
                    ((insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
                      insertionForest F' [v]).map (T' :: ·) from by
                  rw [Multiset.bind_singleton]]]
        -- Step 2: apply IH to inner double bind.
        rw [show ((insertionForest A' ((B.zip m).filterMap fp)).bind fun F' =>
                  insertionForest F' [v]) =
              insertionForest A' (v :: (B.zip m).filterMap fp) +
              (insertionForest ((B.zip m).filterMap fp) [v]).bind
                fun B' => insertionForest A' B' from ih _]
        -- Step 3: distribute .map over +, then T'-bind over +.
        conv_lhs =>
          rhs; ext T'
          rw [Multiset.map_add]
        rw [Multiset.bind_add]
      rw [h1, h2, ← add_assoc]
    rw [h_lhs]
    -- Now goal: Σ_m [L1a + L1b + L2a + L2b] = insertionForest (T::A') (v::B) + (insertionForest B [v]).bind ...
    -- We rewrite both RHS terms to the canonical form.
    -- RHS term 1: insertionForest (T::A') (v::B) = Σ_m [L1a m + L2a m]
    have h_rhs_term1 : insertionForest (T :: A') (v :: B) =
        (Multiset.ofList (listChoices [true, false] B.length)).bind fun m => L1a m + L2a m := by
      rw [insertionForest_cons_assignment T A' (v :: B)]
      rw [show (v :: B).length = B.length + 1 from rfl,
          ofList_listChoices_succ_local [true, false] B.length]
      rw [Multiset.bind_assoc]
      rw [show (Multiset.ofList [true, false] : Multiset Bool) =
              true ::ₘ false ::ₘ 0 from rfl,
          Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
      rw [Multiset.bind_map, Multiset.bind_map]
      rw [← Multiset.bind_add]
      refine Multiset.bind_congr fun m _ => ?_
      -- per-mask: body(true :: m) + body(false :: m) = L1a m + L2a m
      -- body(b :: m) = (insertion T ((v::B).zip (b::m)).filterMap tp).bind (T' => (insertionForest A' (...filterMap fp)).map (T' :: ·))
      -- For b = true: filterMap tp gives v :: B_t, filterMap fp gives B_f → L1a m.
      -- For b = false: filterMap tp gives B_t, filterMap fp gives v :: B_f → L2a m.
      show _ = L1a m + L2a m
      rfl
    rw [h_rhs_term1]
    -- RHS term 2: (insertionForest B [v]).bind (insertionForest (T :: A')) = Σ_m [L1b m + L2b m]
    have h_rhs_term2 :
        ((insertionForest B [v]).bind fun B' => insertionForest (T :: A') B') =
        (Multiset.ofList (listChoices [true, false] B.length)).bind fun m => L1b m + L2b m := by
      -- Inside the outer bind, expand insertionForest (T :: A') B' via cons_assignment.
      -- All B' in insertionForest B [v] have B'.length = B.length (by insertionForest_singleton_guest_set).
      have hB'_len : ∀ B' ∈ insertionForest B [v], B'.length = B.length := by
        intro B' hB'
        rw [insertionForest_singleton_guest_set] at hB'
        rw [Multiset.mem_bind] at hB'
        obtain ⟨k, _, hk⟩ := hB'
        rw [Multiset.mem_map] at hk
        obtain ⟨_, _, hk'⟩ := hk
        rw [← hk', List.length_set]
      rw [Multiset.bind_congr (g := fun B' =>
            (Multiset.ofList (listChoices [true, false] B.length)).bind fun m =>
              (insertion T ((B'.zip m).filterMap tp)).bind fun T' =>
                (insertionForest A' ((B'.zip m).filterMap fp)).map fun F' => T' :: F')
            (by
              intro B' hB'
              rw [insertionForest_cons_assignment, hB'_len B' hB'])]
      rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun m hm => ?_
      -- For this m, apply Stage 6 (bucketing). Need m.length = B.length.
      have hm_mem : m ∈ listChoices [true, false] B.length := by
        rwa [Multiset.mem_coe] at hm
      have hm_len : m.length = B.length :=
        mem_listChoices_length [true, false] B.length m hm_mem
      have hbucket := insertionForest_singleton_bucket_split B m v
        (fun Bt Bf => (insertion T Bt).bind fun T' =>
          (insertionForest A' Bf).map fun F' => T' :: F') hm_len
      -- hbucket states:
      --   (insertionForest B [v]).bind (B' => (insertion T B'_t).bind (T' => (iF A' B'_f).map (T' :: ·)))
      --   = (insertionForest B_t [v]).bind (W => G W B_f) + (insertionForest B_f [v]).bind (W' => G B_t W')
      -- with G Bt Bf := (insertion T Bt).bind (T' => (iF A' Bf).map (T' :: ·))
      -- The first summand of the RHS is L1b m (need bind_assoc to refold), the second is L2b m.
      rw [hbucket]
      -- L1b m: refold ((insertionForest B_t [v]).bind (insertion T)).bind (T'' => ...) from
      --   (insertionForest B_t [v]).bind (Bt' => (insertion T Bt').bind ...)
      show (insertionForest ((B.zip m).filterMap tp) [v]).bind (fun W =>
              (insertion T W).bind fun T' =>
                (insertionForest A' ((B.zip m).filterMap fp)).map fun F' => T' :: F') +
            (insertionForest ((B.zip m).filterMap fp) [v]).bind (fun W' =>
              (insertion T ((B.zip m).filterMap tp)).bind fun T' =>
                (insertionForest A' W').map fun F' => T' :: F') = L1b m + L2b m
      rw [hL1b_def, hL2b_def]
      simp only
      congr 1
      · -- L1b: ((iF B_t [v]).bind (insertion T)).bind (T'' => (iF A' B_f).map (T'' :: ·))
        --    = (iF B_t [v]).bind (W => (insertion T W).bind (T' => (iF A' B_f).map (T' :: ·)))   [bind_assoc]
        rw [Multiset.bind_assoc]
      · -- L2b: (insertion T B_t).bind (T' => ((iF B_f [v]).bind (iF A')).map (T' :: ·))
        --    = (iF B_f [v]).bind (W' => (insertion T B_t).bind (T' => (iF A' W').map (T' :: ·)))
        -- Push the .map (T' :: ·) inside the bind via Multiset.map_bind, then swap binds.
        conv_rhs =>
          rhs; ext T'
          rw [Multiset.map_bind]
        rw [Multiset.bind_bind]
    rw [h_rhs_term2]
    -- Final: rearrange Σ_m [L1a + L1b + L2a + L2b] = Σ_m [L1a + L2a] + Σ_m [L1b + L2b]
    rw [← Multiset.bind_add]
    refine Multiset.bind_congr fun m _ => ?_
    -- Pure rearrangement in an additive comm monoid (a + b + c + d = a + c + (b + d)).
    abel

end Pathed

end Tree
