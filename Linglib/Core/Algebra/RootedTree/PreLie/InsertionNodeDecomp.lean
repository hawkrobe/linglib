/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost

/-!
# Node-host decomposition of the multi-graft insertion

For a single-tree host `node a cs`, the vertex set splits as
`{root} ⊔ vertices(cs)`, so the simultaneous multi-graft `insertion`
decomposes by which guests land at the root (they are prepended as new
children) versus inside the child forest (a recursive `insertionForest`).
This is the node-level analog of `insertionMultiset_add_host`'s
forest-append bucketing (`InsertionAddHost.lean`).

## Main results

* `listChoices_alphabet_split`: choices over an appended alphabet
  `ys ++ zs` enumerate as a boolean mask plus per-bucket choices,
  recombined by `mergeMask`.
* `insertionForest_eq_multiGraftChildren_choices`: the vertex-choice form
  of `insertionForest` — grafting into a host forest `cs` is the sum over
  `verticesAux 0 cs`-choices of `multiGraftChildren`.
* `insertion_node_split`: the headline `Tree`-level decomposition of
  `insertion (node a cs) gs` by root-vs-subtree guest masks.

All three statements are validated computationally on concrete trees
(multi-vertex hosts, repeated guests, empty edge cases) prior to proof.
-/

namespace Tree

namespace Pathed

open RootedTree

variable {α : Type*}

/-! ### `mergeMask` — interleave two bucket lists along a boolean mask -/

/-- Interleave `us` (used at `true` positions) and `ws` (used at `false`
    positions) along the mask `m`. Off-length inputs truncate. -/
def mergeMask {X : Type*} : List Bool → List X → List X → List X
  | [], _, _ => []
  | true :: m, u :: us, ws => u :: mergeMask m us ws
  | true :: _, [], _ => []
  | false :: m, us, w :: ws => w :: mergeMask m us ws
  | false :: _, _, [] => []

@[simp] theorem mergeMask_nil {X : Type*} (us ws : List X) :
    mergeMask [] us ws = [] := rfl

@[simp] theorem mergeMask_true_cons {X : Type*} (m : List Bool)
    (u : X) (us ws : List X) :
    mergeMask (true :: m) (u :: us) ws = u :: mergeMask m us ws := rfl

@[simp] theorem mergeMask_false_cons {X : Type*} (m : List Bool)
    (us : List X) (w : X) (ws : List X) :
    mergeMask (false :: m) us (w :: ws) = w :: mergeMask m us ws := rfl

/-! ### Alphabet split for `listChoices` -/

/-- A length-`(k+1)` enumeration unfolds to a head bind. -/
private theorem ofList_listChoices_succ {Y : Type*} (xs : List Y) (k : ℕ) :
    (Multiset.ofList (listChoices xs (k + 1)) : Multiset (List Y)) =
      (Multiset.ofList xs).bind fun v =>
        (Multiset.ofList (listChoices xs k)).map (v :: ·) := by
  rw [listChoices_succ, ← Multiset.coe_bind]
  rfl

/-- Choices over an appended alphabet enumerate as: a boolean mask over
    the positions, a choice vector over `ys` for the `true` positions,
    and a choice vector over `zs` for the `false` positions, recombined
    by `mergeMask`. -/
theorem listChoices_alphabet_split {X γ : Type*} (ys zs : List X)
    (n : ℕ) (g : List X → Multiset γ) :
    (Multiset.ofList (listChoices (ys ++ zs) n)).bind g =
      (Multiset.ofList (listChoices [true, false] n)).bind fun m =>
        (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
          (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
            g (mergeMask m u w) := by
  induction n generalizing g with
  | zero =>
    simp only [listChoices_zero]
    rw [show (Multiset.ofList ([[]] : List (List X)) : Multiset (List X)) =
          {[]} from rfl,
        show (Multiset.ofList ([[]] : List (List Bool)) : Multiset (List Bool)) =
          {[]} from rfl,
        Multiset.singleton_bind, Multiset.singleton_bind]
    simp only [List.count_nil, listChoices_zero]
    rw [show (Multiset.ofList ([[]] : List (List X)) : Multiset (List X)) =
          {[]} from rfl,
        Multiset.singleton_bind, Multiset.singleton_bind]
    rfl
  | succ n ih =>
    -- Abbreviate the mask-indexed RHS body.
    set R : List Bool → Multiset γ := fun m =>
      (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
        (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
          g (mergeMask m u w) with hR
    -- Each alphabet half equals a (mask, head)-bind in normal form.
    have ys_half : (Multiset.ofList ys).bind (fun v =>
          ((Multiset.ofList (listChoices (ys ++ zs) n)).map (v :: ·)).bind g) =
        (Multiset.ofList (listChoices [true, false] n)).bind fun m =>
          (Multiset.ofList ys).bind fun v =>
            (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
              (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
                g (v :: mergeMask m u w) := by
      rw [← Multiset.bind_bind]
      refine Multiset.bind_congr fun v _ => ?_
      rw [Multiset.bind_map]
      exact ih (fun ch => g (v :: ch))
    have zs_half : (Multiset.ofList zs).bind (fun v =>
          ((Multiset.ofList (listChoices (ys ++ zs) n)).map (v :: ·)).bind g) =
        (Multiset.ofList (listChoices [true, false] n)).bind fun m =>
          (Multiset.ofList zs).bind fun v =>
            (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
              (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
                g (v :: mergeMask m u w) := by
      rw [← Multiset.bind_bind]
      refine Multiset.bind_congr fun v _ => ?_
      rw [Multiset.bind_map]
      exact ih (fun ch => g (v :: ch))
    -- The true-mask half reduces to the ys normal form.
    have true_half :
        ((Multiset.ofList (listChoices [true, false] n)).map (true :: ·)).bind R =
          (Multiset.ofList (listChoices [true, false] n)).bind fun m =>
            (Multiset.ofList ys).bind fun v =>
              (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
                (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
                  g (v :: mergeMask m u w) := by
      rw [Multiset.bind_map]
      refine Multiset.bind_congr fun m _ => ?_
      rw [hR]
      show (Multiset.ofList (listChoices ys ((true :: m).count true))).bind
            (fun u => (Multiset.ofList
              (listChoices zs ((true :: m).count false))).bind fun w =>
                g (mergeMask (true :: m) u w)) = _
      rw [List.count_cons_self, List.count_cons_of_ne (by decide),
          ofList_listChoices_succ ys, Multiset.bind_assoc]
      refine Multiset.bind_congr fun v _ => ?_
      rw [Multiset.bind_map]
      rfl
    -- The false-mask half reduces to the zs normal form (after commuting
    -- the guest bind past the ys-choice bind).
    have false_half :
        ((Multiset.ofList (listChoices [true, false] n)).map (false :: ·)).bind R =
          (Multiset.ofList (listChoices [true, false] n)).bind fun m =>
            (Multiset.ofList zs).bind fun v =>
              (Multiset.ofList (listChoices ys (m.count true))).bind fun u =>
                (Multiset.ofList (listChoices zs (m.count false))).bind fun w =>
                  g (v :: mergeMask m u w) := by
      rw [Multiset.bind_map]
      refine Multiset.bind_congr fun m _ => ?_
      rw [hR]
      show (Multiset.ofList (listChoices ys ((false :: m).count true))).bind
            (fun u => (Multiset.ofList
              (listChoices zs ((false :: m).count false))).bind fun w =>
                g (mergeMask (false :: m) u w)) = _
      rw [List.count_cons_of_ne (by decide), List.count_cons_self]
      simp only [ofList_listChoices_succ zs, Multiset.bind_assoc,
                 Multiset.bind_map]
      rw [Multiset.bind_bind]
      rfl
    -- Assemble.
    rw [ofList_listChoices_succ (ys ++ zs) n, Multiset.bind_assoc,
        show (Multiset.ofList (ys ++ zs) : Multiset X) =
          Multiset.ofList ys + Multiset.ofList zs from by
            rw [← Multiset.coe_add],
        Multiset.add_bind, ys_half, zs_half,
        ofList_listChoices_succ [true, false] n, Multiset.bind_assoc,
        show (Multiset.ofList [true, false] : Multiset Bool) =
          true ::ₘ {false} from rfl,
        Multiset.cons_bind, Multiset.singleton_bind, true_half, false_half,
        ← Multiset.bind_add]

/-- Choices over a singleton alphabet: the constant vector. -/
theorem listChoices_singleton {X : Type*} (x : X) (n : ℕ) :
    listChoices [x] n = [List.replicate n x] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [listChoices_succ, ih]
    rfl

/-- The `true`-bucket of a mask-zip has length `m.count true`. -/
private theorem length_filterMap_zip_true {X : Type*}
    (gs : List X) (m : List Bool) (hg : gs.length = m.length) :
    ((gs.zip m).filterMap
      fun p => if p.2 then some p.1 else none).length = m.count true := by
  induction m generalizing gs with
  | nil =>
    rw [List.length_eq_zero_iff.mp hg]
    rfl
  | cons b m ih =>
    obtain ⟨g, gs, rfl⟩ : ∃ g gs', gs = g :: gs' := by
      cases gs with
      | nil => simp at hg
      | cons g gs' => exact ⟨g, gs', rfl⟩
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b with
    | true =>
      simp [ih gs (by simpa using hg)]
    | false =>
      simp [ih gs (by simpa using hg)]

/-- The `false`-bucket of a mask-zip has length `m.count false`. -/
private theorem length_filterMap_zip_false {X : Type*}
    (gs : List X) (m : List Bool) (hg : gs.length = m.length) :
    ((gs.zip m).filterMap
      fun p => if p.2 then none else some p.1).length = m.count false := by
  induction m generalizing gs with
  | nil =>
    rw [List.length_eq_zero_iff.mp hg]
    rfl
  | cons b m ih =>
    obtain ⟨g, gs, rfl⟩ : ∃ g gs', gs = g :: gs' := by
      cases gs with
      | nil => simp at hg
      | cons g gs' => exact ⟨g, gs', rfl⟩
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b with
    | true =>
      simp [ih gs (by simpa using hg)]
    | false =>
      simp [ih gs (by simpa using hg)]

/-- `multiGraftChildren` depends on its pair list only through the two
    child filters. -/
private theorem multiGraftChildren_congr {cs : List (Tree α)}
    {pairs₁ pairs₂ : List (Path × Tree α)}
    (h₁ : pairs₁.filterMap headChildFilter = pairs₂.filterMap headChildFilter)
    (h₂ : pairs₁.filterMap tailChildFilter = pairs₂.filterMap tailChildFilter) :
    multiGraftChildren cs pairs₁ = multiGraftChildren cs pairs₂ := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs, h₁, h₂]

/-! ### Index shift for `verticesAux` -/

/-- Increment the head index of a path (identity on the empty path). -/
private def bumpHead : Path → Path
  | [] => []
  | h :: q => (h + 1) :: q

/-- `verticesAux` shifts uniformly at the list level. -/
private theorem verticesAux_succ_list (cs : List (Tree α)) (i : ℕ) :
    verticesAux (i + 1) cs = (verticesAux i cs).map bumpHead := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, verticesAux_cons, List.map_append, List.map_map,
        ih (i + 1)]
    rfl

/-- Paths enumerated by `verticesAux` are nonempty. -/
private theorem ne_nil_of_mem_verticesAux {p : Path} {i : ℕ}
    {cs : List (Tree α)} (hp : p ∈ verticesAux i cs) : p ≠ [] := by
  induction cs generalizing i with
  | nil => simp at hp
  | cons c cs ih =>
    rw [verticesAux_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact List.cons_ne_nil i q
    · exact ih hp

/-! ### `filterMap` plumbing through `mergeMask`-zips

`multiGraft`'s three pair filters (`rootPrependFilter`,
`headChildFilter`, `tailChildFilter`) each kill all pairs from one
bucket of a `mergeMask`-interleaved choice vector; the surviving bucket
zips against its own guests. -/

/-- If `F` kills every `ws`-pair, the filterMap over a merged zip
    reduces to the `us`-bucket zipped with the `true`-position guests. -/
private theorem filterMap_zip_mergeMask_left {X Z : Type*}
    (F : Path × X → Option Z) (m : List Bool) (us ws : List Path)
    (gs : List X) (hu : us.length = m.count true)
    (hw : ws.length = m.count false) (hg : gs.length = m.length)
    (hkill : ∀ p ∈ ws, ∀ g, F (p, g) = none) :
    ((mergeMask m us ws).zip gs).filterMap F =
      (us.zip ((gs.zip m).filterMap
        fun p => if p.2 then some p.1 else none)).filterMap F := by
  induction m generalizing us ws gs with
  | nil =>
    have hus : us = [] := List.length_eq_zero_iff.mp (by simpa using hu)
    have hgs : gs = [] := List.length_eq_zero_iff.mp (by simpa using hg)
    subst hus; subst hgs; rfl
  | cons b m ih =>
    obtain ⟨g, gs, rfl⟩ : ∃ g gs', gs = g :: gs' := by
      cases gs with
      | nil => simp at hg
      | cons g gs' => exact ⟨g, gs', rfl⟩
    cases b with
    | true =>
      obtain ⟨u, us, rfl⟩ : ∃ u us', us = u :: us' := by
        cases us with
        | nil => simp at hu
        | cons u us' => exact ⟨u, us', rfl⟩
      show ((u :: mergeMask m us ws).zip (g :: gs)).filterMap F =
        ((u :: us).zip (g :: (gs.zip m).filterMap
          fun p => if p.2 then some p.1 else none)).filterMap F
      rw [List.zip_cons_cons, List.zip_cons_cons, List.filterMap_cons,
          List.filterMap_cons,
          ih us ws gs (by simpa [List.count_cons] using hu)
            (by simpa [List.count_cons] using hw) (by simpa using hg) hkill]
    | false =>
      obtain ⟨w, ws, rfl⟩ : ∃ w ws', ws = w :: ws' := by
        cases ws with
        | nil => simp at hw
        | cons w ws' => exact ⟨w, ws', rfl⟩
      show ((w :: mergeMask m us ws).zip (g :: gs)).filterMap F =
        (us.zip ((gs.zip m).filterMap
          fun p => if p.2 then some p.1 else none)).filterMap F
      rw [List.zip_cons_cons, List.filterMap_cons,
          hkill w List.mem_cons_self g]
      exact ih us ws gs (by simpa [List.count_cons] using hu)
        (by simpa [List.count_cons] using hw) (by simpa using hg)
        (fun p hp => hkill p (List.mem_cons_of_mem w hp))

/-- If `F` kills every `us`-pair, the filterMap over a merged zip
    reduces to the `ws`-bucket zipped with the `false`-position guests. -/
private theorem filterMap_zip_mergeMask_right {X Z : Type*}
    (F : Path × X → Option Z) (m : List Bool) (us ws : List Path)
    (gs : List X) (hu : us.length = m.count true)
    (hw : ws.length = m.count false) (hg : gs.length = m.length)
    (hkill : ∀ p ∈ us, ∀ g, F (p, g) = none) :
    ((mergeMask m us ws).zip gs).filterMap F =
      (ws.zip ((gs.zip m).filterMap
        fun p => if p.2 then none else some p.1)).filterMap F := by
  induction m generalizing us ws gs with
  | nil =>
    have hws : ws = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    have hgs : gs = [] := List.length_eq_zero_iff.mp (by simpa using hg)
    subst hws; subst hgs; rfl
  | cons b m ih =>
    obtain ⟨g, gs, rfl⟩ : ∃ g gs', gs = g :: gs' := by
      cases gs with
      | nil => simp at hg
      | cons g gs' => exact ⟨g, gs', rfl⟩
    cases b with
    | true =>
      obtain ⟨u, us, rfl⟩ : ∃ u us', us = u :: us' := by
        cases us with
        | nil => simp at hu
        | cons u us' => exact ⟨u, us', rfl⟩
      show ((u :: mergeMask m us ws).zip (g :: gs)).filterMap F =
        (ws.zip ((gs.zip m).filterMap
          fun p => if p.2 then none else some p.1)).filterMap F
      rw [List.zip_cons_cons, List.filterMap_cons,
          hkill u List.mem_cons_self g]
      exact ih us ws gs (by simpa [List.count_cons] using hu)
        (by simpa [List.count_cons] using hw) (by simpa using hg)
        (fun p hp => hkill p (List.mem_cons_of_mem u hp))
    | false =>
      obtain ⟨w, ws, rfl⟩ : ∃ w ws', ws = w :: ws' := by
        cases ws with
        | nil => simp at hw
        | cons w ws' => exact ⟨w, ws', rfl⟩
      show ((w :: mergeMask m us ws).zip (g :: gs)).filterMap F =
        ((w :: ws).zip (g :: (gs.zip m).filterMap
          fun p => if p.2 then none else some p.1)).filterMap F
      rw [List.zip_cons_cons, List.zip_cons_cons, List.filterMap_cons,
          List.filterMap_cons,
          ih us ws gs (by simpa [List.count_cons] using hu)
            (by simpa [List.count_cons] using hw) (by simpa using hg) hkill]

/-! ### Vertex-choice form of `insertionForest` -/

/-- `0`-prefixed paths zipped with guests pass through `headChildFilter`
    intact (with the leading `0` stripped). -/
private theorem filterMap_zip_zeroCons_headChild :
    ∀ (us : List Path) (gs : List (Tree α)),
    ((us.map (List.cons 0)).zip gs).filterMap headChildFilter = us.zip gs := by
  intro us gs
  induction us generalizing gs with
  | nil => rfl
  | cons u us ih =>
    cases gs with
    | nil => rfl
    | cons g gs =>
      show (((0 :: u) :: us.map (List.cons 0)).zip (g :: gs)).filterMap
            headChildFilter = (u :: us).zip (g :: gs)
      rw [List.zip_cons_cons, List.zip_cons_cons, List.filterMap_cons,
          headChildFilter_of_zero_cons, ih gs]

/-- `bumpHead`-shifted nonempty paths zipped with guests pass through
    `tailChildFilter` intact (undoing the bump). -/
private theorem filterMap_zip_bumpHead_tailChild :
    ∀ (ws : List Path) (gs : List (Tree α)),
    (∀ p ∈ ws, p ≠ []) →
    ((ws.map bumpHead).zip gs).filterMap tailChildFilter = ws.zip gs := by
  intro ws gs hne
  induction ws generalizing gs with
  | nil => rfl
  | cons w ws ih =>
    cases gs with
    | nil => rfl
    | cons g gs =>
      have hw : w ≠ [] := hne w List.mem_cons_self
      obtain ⟨h, q, rfl⟩ : ∃ h q, w = h :: q := by
        cases w with
        | nil => exact absurd rfl hw
        | cons h q => exact ⟨h, q, rfl⟩
      show (((bumpHead (h :: q)) :: ws.map bumpHead).zip (g :: gs)).filterMap
            tailChildFilter = (h :: q, g) :: ws.zip gs
      rw [show bumpHead (h :: q) = (h + 1) :: q from rfl]
      rw [List.zip_cons_cons, List.filterMap_cons,
          tailChildFilter_of_succ_cons,
          ih gs (fun p hp => hne p (List.mem_cons_of_mem _ hp))]

/-- Replicate-`[]` zipped with guests passes through `rootPrependFilter`
    intact (the empty paths give `some snd`). -/
private theorem filterMap_zip_replicate_rootPrepend (gs : List (Tree α)) :
    ((List.replicate gs.length ([] : Path)).zip gs).filterMap
        rootPrependFilter = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.filterMap_cons, rootPrependFilter_of_nil]
    exact congrArg (g :: ·) ih

/-- Grafting a guest list into a host forest, in vertex-choice form:
    `insertionForest cs gs` is the sum over assignments of each guest to
    a forest vertex (a `verticesAux 0 cs` path) of the simultaneous
    `multiGraftChildren`. -/
theorem insertionForest_eq_multiGraftChildren_choices
    (cs gs : List (Tree α)) :
    insertionForest cs gs =
      Multiset.ofList ((listChoices (verticesAux 0 cs) gs.length).map
        fun ch => multiGraftChildren cs (ch.zip gs)) := by
  induction cs generalizing gs with
  | nil =>
    -- verticesAux 0 [] = [], so listChoices [] gs.length = []
    -- unless gs.length = 0 in which case it's [[]].
    cases gs with
    | nil =>
      rw [insertionForest_nil_nil]
      show ({[]} : Multiset (List (Tree α))) = _
      rfl
    | cons g gs =>
      rw [insertionForest_empty_host_nonempty_guests]
      show (0 : Multiset (List (Tree α))) = _
      rw [verticesAux_nil, show (g :: gs).length = gs.length + 1 from rfl,
          listChoices_succ]
      simp
  | cons c cs ih =>
    -- LHS = bind over masks m of insertion c (gs_t).bind T' =>
    --         (insertionForest cs (gs_f)).map (T' :: ·)
    rw [insertionForest_cons_assignment]
    -- RHS = via verticesAux_cons, listChoices_alphabet_split, listChoices_map
    -- Move RHS map to bind-singleton form
    rw [show (Multiset.ofList ((listChoices (verticesAux 0 (c :: cs)) gs.length).map
            fun ch => multiGraftChildren (c :: cs) (ch.zip gs)) :
            Multiset (List (Tree α))) =
          (Multiset.ofList (listChoices (verticesAux 0 (c :: cs)) gs.length)).bind
            fun ch => ({multiGraftChildren (c :: cs) (ch.zip gs)} : Multiset _) from by
        rw [← Multiset.map_coe]
        rw [show ((listChoices (verticesAux 0 (c :: cs)) gs.length) :
                Multiset (List Path)) =
              Multiset.ofList (listChoices (verticesAux 0 (c :: cs)) gs.length) from rfl]
        exact (Multiset.bind_singleton _ _).symm]
    -- Now use verticesAux_cons + listChoices_alphabet_split
    rw [verticesAux_cons]
    rw [listChoices_alphabet_split ((vertices c).map (List.cons 0))
          (verticesAux 1 cs) gs.length]
    -- Per-mask congruence
    refine Multiset.bind_congr fun m hm => ?_
    -- Get m.length = gs.length
    have hm' : m ∈ listChoices [true, false] gs.length := by
      rwa [Multiset.mem_coe] at hm
    have hmlen : m.length = gs.length :=
      mem_listChoices_length [true, false] gs.length m hm'
    -- LHS per-m: (insertion c gs_t).bind T' => (insertionForest cs gs_f).map (T' :: ·)
    -- Set abbreviations for the buckets
    set gs_t : List (Tree α) := (gs.zip m).filterMap
      fun p => if p.snd then some p.fst else none with hgst
    set gs_f : List (Tree α) := (gs.zip m).filterMap
      fun p => if p.snd then none else some p.fst with hgsf
    -- Lengths: gs_t.length = m.count true (and similarly for false)
    have hglen : gs.length = m.length := hmlen.symm
    have hgst_len : gs_t.length = m.count true := by
      rw [hgst]; exact length_filterMap_zip_true gs m hglen
    have hgsf_len : gs_f.length = m.count false := by
      rw [hgsf]; exact length_filterMap_zip_false gs m hglen
    -- RHS per-m: bind u': bind w': {multiGraftChildren (c::cs) ((mergeMask m u w).zip gs)}
    -- where u in listChoices ((vertices c).map (0::·)) (m.count true)
    --   and w in listChoices (verticesAux 1 cs) (m.count false)
    -- Convert the u-bind via listChoices_map: 0-prefixed choices over (vertices c)
    rw [listChoices_map (List.cons 0) (vertices c) (m.count true)]
    rw [show (Multiset.ofList ((listChoices (vertices c) (m.count true)).map
              (List.map (List.cons 0))) : Multiset (List Path)) =
            (Multiset.ofList (listChoices (vertices c) (m.count true))).map
              (List.map (List.cons 0)) from rfl]
    rw [Multiset.bind_map]
    -- Convert the w-bind via verticesAux_succ_list + listChoices_map
    have h_vAux1 : verticesAux 1 cs = (verticesAux 0 cs).map bumpHead :=
      verticesAux_succ_list cs 0
    rw [h_vAux1, listChoices_map bumpHead (verticesAux 0 cs) (m.count false)]
    rw [show (Multiset.ofList ((listChoices (verticesAux 0 cs) (m.count false)).map
            (List.map bumpHead)) : Multiset (List Path)) =
          (Multiset.ofList (listChoices (verticesAux 0 cs) (m.count false))).map
            (List.map bumpHead) from rfl]
    conv_rhs =>
      rhs; ext u'
      rw [Multiset.bind_map]
    -- Now per (u', w'): compute multiGraftChildren (c::cs) ((mergeMask m (u'.map (0::·)) (w'.map bumpHead)).zip gs)
    -- The head filter: 0-prefixed → strip; bumpHead → kill. Use filterMap_zip_mergeMask_left.
    -- The tail filter: 0-prefixed → kill; bumpHead → strip. Use filterMap_zip_mergeMask_right.
    -- Need ne_nil for w' entries: paths in verticesAux 0 cs are nonempty.
    -- Now rewrite LHS to match — first compute insertion c gs_t and insertionForest cs gs_f
    rw [insertion_def]
    -- insertion c gs_t = ofList ((listChoices (vertices c) gs_t.length).map ...)
    rw [hgst_len]
    -- Convert this ofList.map to ofList.bind singleton
    rw [show (Multiset.ofList ((listChoices (vertices c) (m.count true)).map
            (fun ch => multiGraft c (ch.zip gs_t))) : Multiset (Tree α)) =
          (Multiset.ofList (listChoices (vertices c) (m.count true))).bind
            (fun u' => ({multiGraft c (u'.zip gs_t)} : Multiset _)) from by
        rw [← Multiset.map_coe]
        rw [show ((listChoices (vertices c) (m.count true)) :
                Multiset (List Path)) =
              Multiset.ofList (listChoices (vertices c) (m.count true)) from rfl]
        exact (Multiset.bind_singleton _ _).symm]
    rw [Multiset.bind_assoc]
    -- Now apply IH to insertionForest cs gs_f
    refine Multiset.bind_congr fun u' hu' => ?_
    rw [ih gs_f]
    rw [hgsf_len]
    rw [show (Multiset.ofList ((listChoices (verticesAux 0 cs) (m.count false)).map
            (fun ch => multiGraftChildren cs (ch.zip gs_f))) :
            Multiset (List (Tree α))) =
          (Multiset.ofList (listChoices (verticesAux 0 cs) (m.count false))).bind
            (fun w' => ({multiGraftChildren cs (w'.zip gs_f)} : Multiset _)) from by
        rw [← Multiset.map_coe]
        rw [show ((listChoices (verticesAux 0 cs) (m.count false)) :
                Multiset (List Path)) =
              Multiset.ofList (listChoices (verticesAux 0 cs) (m.count false)) from rfl]
        exact (Multiset.bind_singleton _ _).symm]
    rw [Multiset.singleton_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun w' hw' => ?_
    rw [Multiset.map_singleton]
    -- Get u' ∈ listChoices (vertices c) (m.count true)
    have hu'len : u'.length = m.count true := by
      have hu'' : u' ∈ listChoices (vertices c) (m.count true) := by
        rwa [Multiset.mem_coe] at hu'
      exact mem_listChoices_length (vertices c) (m.count true) u' hu''
    -- Get w' ∈ listChoices (verticesAux 0 cs) (m.count false)
    have hw'mem : w' ∈ listChoices (verticesAux 0 cs) (m.count false) := by
      rwa [Multiset.mem_coe] at hw'
    have hw'len : w'.length = m.count false :=
      mem_listChoices_length (verticesAux 0 cs) (m.count false) w' hw'mem
    -- ne_nil for entries of w'
    have hw'ne : ∀ p ∈ w', p ≠ [] := fun p hp =>
      ne_nil_of_mem_verticesAux
        (mem_of_mem_listChoices (verticesAux 0 cs) (m.count false) w' hw'mem p hp)
    -- Lengths for bumpHead/0-cons-mapped lists
    have hu'map_len : (u'.map (List.cons 0)).length = m.count true := by
      rw [List.length_map]; exact hu'len
    have hw'map_len : (w'.map bumpHead).length = m.count false := by
      rw [List.length_map]; exact hw'len
    -- ne_nil for w'.map bumpHead entries (all are (h+1) :: q)
    have hw'bump_ne : ∀ p ∈ w'.map bumpHead, ∀ (g : Tree α),
        headChildFilter (p, g) = none := by
      intro p hp g
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have : q ≠ [] := hw'ne q hq
      cases q with
      | nil => exact absurd rfl this
      | cons h r =>
        show headChildFilter (bumpHead (h :: r), g) = none
        rw [show bumpHead (h :: r) = (h + 1) :: r from rfl]
        exact headChildFilter_of_succ_cons h r g
    have hu'zero_ne : ∀ p ∈ u'.map (List.cons 0), ∀ (g : Tree α),
        tailChildFilter (p, g) = none := by
      intro p hp g
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
      exact tailChildFilter_of_zero_cons q g
    -- Compute the head-child filtered zip
    have hhead :
        ((mergeMask m (u'.map (List.cons 0)) (w'.map bumpHead)).zip gs).filterMap
            headChildFilter =
          u'.zip gs_t := by
      rw [filterMap_zip_mergeMask_left headChildFilter m _ _ gs
            hu'map_len hw'map_len hglen hw'bump_ne]
      rw [filterMap_zip_zeroCons_headChild]
    have htail :
        ((mergeMask m (u'.map (List.cons 0)) (w'.map bumpHead)).zip gs).filterMap
            tailChildFilter =
          w'.zip gs_f := by
      rw [filterMap_zip_mergeMask_right tailChildFilter m _ _ gs
            hu'map_len hw'map_len hglen hu'zero_ne]
      rw [filterMap_zip_bumpHead_tailChild w' _ hw'ne]
    -- Now compute multiGraftChildren (c::cs) ((mergeMask ...).zip gs)
    rw [show multiGraftChildren (c :: cs)
          ((mergeMask m (u'.map (List.cons 0)) (w'.map bumpHead)).zip gs) =
        multiGraft c (u'.zip gs_t) :: multiGraftChildren cs (w'.zip gs_f) from by
      rw [multiGraftChildren_cons_cs, hhead, htail]]

/-! ### The node-host decomposition -/

/-- **Node-host decomposition** of the simultaneous multi-graft: guests
    split by a boolean mask into root-guests (prepended as new children,
    in guest order) and subtree-guests (an `insertionForest` into the
    child forest). -/
theorem insertion_node_split (a : α) (cs gs : List (Tree α)) :
    insertion (Tree.node a cs) gs =
      (Multiset.ofList (listChoices [true, false] gs.length)).bind fun m =>
        (insertionForest cs ((gs.zip m).filterMap
            fun p => if p.2 then none else some p.1)).map
          fun cs' => Tree.node a
            (((gs.zip m).filterMap
              fun p => if p.2 then some p.1 else none) ++ cs') := by
  rw [insertion_def, vertices_node]
  -- vertices (node a cs) = [] :: verticesAux 0 cs = [[]] ++ verticesAux 0 cs
  rw [show ([] : Path) :: verticesAux 0 cs = ([[]] : List Path) ++ verticesAux 0 cs
        from rfl]
  -- Convert LHS map to bind-singleton form
  rw [show (Multiset.ofList ((listChoices ([[]] ++ verticesAux 0 cs) gs.length).map
          fun choice => multiGraft (Tree.node a cs) (choice.zip gs)) :
          Multiset (Tree α)) =
        (Multiset.ofList (listChoices ([[]] ++ verticesAux 0 cs) gs.length)).bind
          (fun choice => ({multiGraft (Tree.node a cs) (choice.zip gs)}
            : Multiset _)) from by
      rw [← Multiset.map_coe]
      rw [show ((listChoices ([[]] ++ verticesAux 0 cs) gs.length) :
              Multiset (List Path)) =
            Multiset.ofList (listChoices ([[]] ++ verticesAux 0 cs) gs.length) from rfl]
      exact (Multiset.bind_singleton _ _).symm]
  -- Apply alphabet split with ys = [[]], zs = verticesAux 0 cs
  rw [listChoices_alphabet_split ([[]] : List Path) (verticesAux 0 cs) gs.length]
  -- Per-mask congruence
  refine Multiset.bind_congr fun m hm => ?_
  -- Get m.length = gs.length
  have hm' : m ∈ listChoices [true, false] gs.length := by
    rwa [Multiset.mem_coe] at hm
  have hmlen : m.length = gs.length :=
    mem_listChoices_length [true, false] gs.length m hm'
  have hglen : gs.length = m.length := hmlen.symm
  -- Collapse u-bind via listChoices_singleton
  rw [listChoices_singleton ([] : Path) (m.count true)]
  rw [show (Multiset.ofList ([List.replicate (m.count true) ([] : Path)]) :
            Multiset (List Path)) =
          ({List.replicate (m.count true) ([] : Path)} : Multiset _) from rfl]
  rw [Multiset.singleton_bind]
  -- Set abbreviations for buckets
  set gs_t : List (Tree α) := (gs.zip m).filterMap
    fun p => if p.snd then some p.fst else none with hgst
  set gs_f : List (Tree α) := (gs.zip m).filterMap
    fun p => if p.snd then none else some p.fst with hgsf
  have hgst_len : gs_t.length = m.count true :=
    length_filterMap_zip_true gs m hglen
  have hgsf_len : gs_f.length = m.count false :=
    length_filterMap_zip_false gs m hglen
  -- Length of replicate (m.count true) []
  have hreplen : (List.replicate (m.count true) ([] : Path)).length = m.count true := by
    rw [List.length_replicate]
  -- ne_nil hypotheses for the kill-lemmas
  -- replicate-side ([]-paths): headChildFilter/tailChildFilter kill.
  have hrep_hcf_ne : ∀ p ∈ List.replicate (m.count true) ([] : Path), ∀ (g : Tree α),
      headChildFilter (p, g) = none := by
    intro p hp g
    rw [List.mem_replicate] at hp
    rcases hp with ⟨_, rfl⟩
    exact headChildFilter_of_nil g
  have hrep_tcf_ne : ∀ p ∈ List.replicate (m.count true) ([] : Path), ∀ (g : Tree α),
      tailChildFilter (p, g) = none := by
    intro p hp g
    rw [List.mem_replicate] at hp
    rcases hp with ⟨_, rfl⟩
    exact tailChildFilter_of_nil g
  -- Rewrite the RHS map to bind-singleton form via L3
  rw [insertionForest_eq_multiGraftChildren_choices cs gs_f]
  rw [Multiset.map_coe, hgsf_len, List.map_map]
  -- LHS form: bind w over listChoices (verticesAux 0 cs) (m.count false) of
  --   {multiGraft (node a cs) ((mergeMask m (replicate (m.count true) []) w).zip gs)}
  -- RHS form: ofList ((listChoices ... (m.count false)).map (fun ch => node a (gs_t ++ multiGraftChildren cs (ch.zip gs_f))))
  -- Convert RHS to bind-singleton form
  rw [show (Multiset.ofList ((listChoices (verticesAux 0 cs) (m.count false)).map
            ((fun cs' => Tree.node a (gs_t ++ cs')) ∘
              fun ch => multiGraftChildren cs (ch.zip gs_f))) :
            Multiset (Tree α)) =
          (Multiset.ofList (listChoices (verticesAux 0 cs) (m.count false))).bind
            (fun w => ({Tree.node a
              (gs_t ++ multiGraftChildren cs (w.zip gs_f))} : Multiset _)) from by
      rw [← Multiset.map_coe]
      rw [show ((listChoices (verticesAux 0 cs) (m.count false)) :
              Multiset (List Path)) =
            Multiset.ofList (listChoices (verticesAux 0 cs) (m.count false)) from rfl]
      exact (Multiset.bind_singleton _ _).symm]
  -- Per-w congruence
  refine Multiset.bind_congr fun w hw => ?_
  have hwmem : w ∈ listChoices (verticesAux 0 cs) (m.count false) := by
    rwa [Multiset.mem_coe] at hw
  have hwlen : w.length = m.count false :=
    mem_listChoices_length (verticesAux 0 cs) (m.count false) w hwmem
  have hwne : ∀ p ∈ w, p ≠ [] := fun p hp =>
    ne_nil_of_mem_verticesAux
      (mem_of_mem_listChoices (verticesAux 0 cs) (m.count false) w hwmem p hp)
  -- w-side (nonempty paths): rootPrependFilter kills.
  have hw_rpf_ne : ∀ p ∈ w, ∀ (g : Tree α), rootPrependFilter (p, g) = none := by
    intro p hp g
    have : p ≠ [] := hwne p hp
    cases p with
    | nil => exact absurd rfl this
    | cons h r => exact rootPrependFilter_of_cons h r g
  -- Compute rootPrependFilter on the merged zip → gives gs_t
  have h_rpf :
      ((mergeMask m (List.replicate (m.count true) ([] : Path)) w).zip gs).filterMap
          rootPrependFilter = gs_t := by
    rw [filterMap_zip_mergeMask_left rootPrependFilter m _ _ gs
          hreplen hwlen hglen hw_rpf_ne]
    rw [show (List.replicate (m.count true) ([] : Path)) =
        List.replicate gs_t.length ([] : Path) from by rw [hgst_len]]
    exact filterMap_zip_replicate_rootPrepend gs_t
  -- Compute multiGraftChildren on the merged zip via multiGraftChildren_congr
  have h_mgc :
      multiGraftChildren cs
          ((mergeMask m (List.replicate (m.count true) ([] : Path)) w).zip gs) =
        multiGraftChildren cs (w.zip gs_f) := by
    apply multiGraftChildren_congr
    · -- headChildFilter
      rw [filterMap_zip_mergeMask_right headChildFilter m _ _ gs
            hreplen hwlen hglen hrep_hcf_ne]
    · -- tailChildFilter
      rw [filterMap_zip_mergeMask_right tailChildFilter m _ _ gs
            hreplen hwlen hglen hrep_tcf_ne]
  -- Now combine: multiGraft (node a cs) ((mergeMask ...).zip gs)
  --            = node a (gs_t ++ multiGraftChildren cs (w.zip gs_f))
  rw [multiGraft_node, h_rpf, h_mgc]

end Pathed

end Tree
