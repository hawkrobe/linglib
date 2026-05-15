/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Graft
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Data.Multiset.Bind

set_option autoImplicit false

/-!
# Foissy 2021 Theorem 5.1 multi-tree insertion (path-based)
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{foissy-introduction-hopf-algebras-trees}

The Foissy 2021 Theorem 5.1 multi-tree multi-vertex insertion operator.
Defined as a sum over functions `Ts → V(T)` of `multiGraft`, taken as
a `Multiset` to make the sum-over-choices commutative.

Sibling to `Graft.lean` (path-based multi-graft primitive). Lives under
namespace `RootedTree.Planar.Pathed` for now; the `Pathed`
sub-namespace will be hoisted to `RootedTree.Planar` once the legacy
`Vertex.lean` consumers (`InsertSum.lean`, `Algebra.lean`,
`VertexBijection.lean`) migrate to the path-based representation.

## File scope

- §1: `listChoices` — choice-list enumeration (representation-independent).
- §2: `insertion` — Foissy 2021 Theorem 5.1, single-tree host.
- §3: `insertionForest` — forest host (Foissy 2021 §5.1) + identity/nil lemmas.
- §4: Pair-list `Perm`-invariance (`multiGraft_perm_pair`).
- §5: Guest-list invariance (`insertion_perm_guests`,
  `insertion_planarEquiv_guests`).
- §6: Host invariance substrate — `swapPathAt` path-relabel
  bijection, `vertices_swap_perm`, `multiGraft_swap_planarEquiv`,
  `insertion_planarEquiv_host`.
- §7: Forest invariance variants.

## Status

`[UPSTREAM]` candidate. **Sorry-free**.

- §1–§5: sorry-free.
- §6 (`multiGraft_swap_planarEquiv`, `insertion_planarEquiv_host`):
  sorry-free. Architecture: `PlanarStep.exists_pathBijection` gives, for
  any `PlanarStep t t'`, a path bijection `f` satisfying both
  `((vertices t).map f).Perm (vertices t')` and the `multiGraft`-equivalent
  after pair relabel. Built by induction on the step (swap uses
  `swapPathAt n`; recurse uses `pathLiftRecurse n` of inner bijection).
  `insertion_eq_of_pathBij` is the generic lifter from path bijection to
  `mk`-equality of insertions. Together they yield
  `insertion_planarStep_host` in two lines; the outer `EqvGen` induction
  finishes `insertion_planarEquiv_host`.
- §7 (`insertionForest_planarEquiv_host`): sorry-free. Induction on
  `Forall₂ PlanarEquiv`; cons case lifts via `Multiset.map_bind` +
  `Multiset.bind_map` + `insertion_planarEquiv_host` (head) + IH (tail).
- §7 (`insertionForest_perm_guests`): sorry-free. Outer induction on
  `F`; cons-`F` case routes through `forestPairSum`, a Multiset
  aggregator that splits the guest list into `pre_T` (going to the head
  host) and `pre_F` (going to the tail forest). The bridge
  `forestPairSum_eq_insertionForest` reduces to the canonical
  `insertionForest`; Perm invariance is then established via
  `forestPairSum_pre_perm_mk` (Perm of accumulators, using
  `insertion_perm_guests` for the head + the outer F-IH for the tail) +
  `forestPairSum_swap_mk` (adjacent swap via `Multiset.bind_bind` + the
  pre-perm lemma) + induction on `List.Perm`.
-/

namespace RootedTree

namespace Planar

namespace Pathed

variable {α : Type*}

/-! ## §1: `listChoices` enumeration -/

/-- All length-`n` lists with entries from `xs` (with repetition).
    The "n-fold list power" used in Foissy 2021 Theorem 5.1's
    vertex-choice sum. Representation-independent (no `Vertex`
    dependence): copied from the legacy `Insertion.lean`. -/
def listChoices {β : Type*} : List β → Nat → List (List β)
  | _,  0     => [[]]
  | xs, n + 1 => xs.flatMap fun v => (listChoices xs n).map (v :: ·)

@[simp] theorem listChoices_zero {β : Type*} (xs : List β) :
    listChoices xs 0 = [[]] := rfl

@[simp] theorem listChoices_succ {β : Type*} (xs : List β) (n : Nat) :
    listChoices xs (n + 1) =
      xs.flatMap fun v => (listChoices xs n).map (v :: ·) := rfl

/-! ## §2: `insertion` — Foissy 2021 Theorem 5.1 -/

/-- Foissy 2021 Theorem 5.1 multi-graft on a single-tree host. Sum over
    `(v₁, …, vₙ) ∈ V(T)ⁿ` of `multiGraft T [(v₁, T₁), …, (vₙ, Tₙ)]`. -/
def insertion (T : Planar α) (Ts : List (Planar α)) : Multiset (Planar α) :=
  Multiset.ofList <| (listChoices (vertices T) Ts.length).map
    fun choice => multiGraft T (choice.zip Ts)

theorem insertion_def (T : Planar α) (Ts : List (Planar α)) :
    insertion T Ts =
      Multiset.ofList ((listChoices (vertices T) Ts.length).map
        fun choice => multiGraft T (choice.zip Ts)) := rfl

/-! ## §3: `insertionForest` — forest host -/

/-- Multi-graft into a host forest. Disjoint pattern cases for clean
    auto-generated equation lemmas. -/
def insertionForest : List (Planar α) → List (Planar α) →
    Multiset (List (Planar α))
  | [],     []         => ({[]} : Multiset _)
  | [],     _ :: _     => 0
  | T :: F, []         => ({T :: F} : Multiset _)
  | T :: F, T_g :: Ts  =>
      (Multiset.ofList (listChoices [true, false] (T_g :: Ts).length)).bind
        fun assignment =>
          (insertion T
              (((T_g :: Ts).zip assignment).filterMap fun p =>
                if p.snd then some p.fst else none)).bind
            fun T' =>
              (insertionForest F
                  (((T_g :: Ts).zip assignment).filterMap fun p =>
                    if p.snd then none else some p.fst)).map
                fun F' => T' :: F'
  termination_by F _ => F.length

@[simp] theorem insertionForest_nil_nil :
    insertionForest ([] : List (Planar α)) [] =
      ({[]} : Multiset (List (Planar α))) := by
  unfold insertionForest; rfl

@[simp] theorem insertionForest_empty_host_nonempty_guests
    (T_g : Planar α) (Ts : List (Planar α)) :
    insertionForest ([] : List (Planar α)) (T_g :: Ts) = 0 := by
  unfold insertionForest; rfl

@[simp] theorem insertionForest_cons_host_nil_guests
    (T : Planar α) (F : List (Planar α)) :
    insertionForest (T :: F) ([] : List (Planar α)) =
      ({T :: F} : Multiset (List (Planar α))) := by
  unfold insertionForest; rfl

theorem insertionForest_nil_guests (F : List (Planar α)) :
    insertionForest F [] = ({F} : Multiset (List (Planar α))) := by
  cases F
  · exact insertionForest_nil_nil
  · exact insertionForest_cons_host_nil_guests _ _

theorem insertionForest_cons_cons
    (T : Planar α) (F : List (Planar α))
    (T_g : Planar α) (Ts : List (Planar α)) :
    insertionForest (T :: F) (T_g :: Ts) =
      (Multiset.ofList (listChoices [true, false] (T_g :: Ts).length)).bind
        fun assignment =>
          (insertion T
              (((T_g :: Ts).zip assignment).filterMap fun p =>
                if p.snd then some p.fst else none)).bind
            fun T' =>
              (insertionForest F
                  (((T_g :: Ts).zip assignment).filterMap fun p =>
                    if p.snd then none else some p.fst)).map
                fun F' => T' :: F' :=
  insertionForest.eq_4 T F T_g Ts

/-! ## §4: Pair-list `Perm` invariance for `multiGraft`

`multiGraft T pairs` is `PlanarEquiv`-invariant under permutation of the
pair list: grafts at distinct paths commute, and grafts at the same
path are root-list permutations (lift via `planarEquiv_root_perm`).

Path-based reformulation of the legacy `multiGraft_perm_pair` /
`multiGraftList_perm_pair`. -/

mutual
/-- `PlanarEquiv` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from a `List.Perm` between `pairs` and `pairs'`. Mutual
    recursion on `T` with the children-list aux. -/
theorem multiGraft_perm_pair : ∀ (T : Planar α)
    {pairs pairs' : List (Path × Planar α)},
    pairs.Perm pairs' →
    PlanarEquiv (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    exact (planarEquiv_root_perm
            ((h.filterMap rootPrependFilter).append_right _)).trans
          (planarEquiv_node_componentwise
            (List.rel_append
              (List.forall₂_same.mpr fun _ _ => PlanarEquiv.refl _)
              (multiGraftChildren_perm_pair cs h)))
/-- List-level companion to `multiGraft_perm_pair`: pair-list `Perm`
    lifts to `Forall₂ PlanarEquiv` on the children list output of
    `multiGraftChildren`. -/
theorem multiGraftChildren_perm_pair : ∀ (cs : List (Planar α))
    {pairs pairs' : List (Path × Planar α)},
    pairs.Perm pairs' →
    List.Forall₂ PlanarEquiv
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · exact multiGraft_perm_pair c (h.filterMap _)
    · exact multiGraftChildren_perm_pair cs (h.filterMap _)
end

/-! ### Forall₂-version of `multiGraft_perm_pair`

For `insertion_planarEquiv_guests` we need: when `Ts ~ᶠ Ts'` (Forall₂
PlanarEquiv) and we zip with the same choice, the resulting pair lists
satisfy a Forall₂ relation (same fst, PlanarEquiv snd). Then this lifts
to `multiGraft T pairs ~ multiGraft T pairs'` (`PlanarEquiv`).

Path-based version of the legacy `multiGraft_planarEquiv_pair_Forall₂`. -/

private theorem zip_pair_Forall₂ {β γ : Type*} {R : γ → γ → Prop}
    (choice : List β) :
    ∀ {Ts Ts' : List γ}, List.Forall₂ R Ts Ts' →
      List.Forall₂ (fun p p' : β × γ => p.fst = p'.fst ∧ R p.snd p'.snd)
        (choice.zip Ts) (choice.zip Ts') := by
  induction choice with
  | nil => intro Ts Ts' _; exact List.Forall₂.nil
  | cons c cs ih =>
    intro Ts Ts' h
    cases h with
    | nil => exact List.Forall₂.nil
    | cons hTT' hrest =>
      simp only [List.zip_cons_cons]
      exact List.Forall₂.cons ⟨rfl, hTT'⟩ (ih hrest)

mutual
/-- `PlanarEquiv` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from pair-`Forall₂` (same fst, `PlanarEquiv` snds). -/
private theorem multiGraft_planarEquiv_pair_Forall₂ : ∀ (T : Planar α)
    {pairs pairs' : List (Path × Planar α)},
    List.Forall₂ (fun p p' : Path × Planar α =>
        p.fst = p'.fst ∧ PlanarEquiv p.snd p'.snd) pairs pairs' →
    PlanarEquiv (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    apply planarEquiv_node_componentwise
    apply List.rel_append
    · -- root-prepended children: Forall₂ PlanarEquiv after filterMap
      refine List.rel_filterMap (P := PlanarEquiv) ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil       => exact Option.Rel.some hsnd
      | cons _ _  => exact Option.Rel.none
    · -- children: Forall₂ PlanarEquiv on multiGraftChildren output
      exact multiGraftChildren_planarEquiv_pair_Forall₂ cs h

/-- List-level companion. -/
private theorem multiGraftChildren_planarEquiv_pair_Forall₂ :
    ∀ (cs : List (Planar α))
    {pairs pairs' : List (Path × Planar α)},
    List.Forall₂ (fun p p' : Path × Planar α =>
        p.fst = p'.fst ∧ PlanarEquiv p.snd p'.snd) pairs pairs' →
    List.Forall₂ PlanarEquiv
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · apply multiGraft_planarEquiv_pair_Forall₂
      refine List.rel_filterMap ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil => exact Option.Rel.none
      | cons k _ =>
        cases k with
        | zero   => exact Option.Rel.some ⟨rfl, hsnd⟩
        | succ _ => exact Option.Rel.none
    · apply multiGraftChildren_planarEquiv_pair_Forall₂
      refine List.rel_filterMap ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil => exact Option.Rel.none
      | cons k _ =>
        cases k with
        | zero   => exact Option.Rel.none
        | succ _ => exact Option.Rel.some ⟨rfl, hsnd⟩
end

/-! ## §5: Guest-list invariance for `insertion`

`pairSum t pre Ts` aggregates `mk (multiGraft t (pre ++ c.zip Ts))` over
all choices `c ∈ listChoices (vertices t) |Ts|`. The clean recursive
equation `pairSum t pre (x :: rest) = bind v over vertices of
pairSum t (pre ++ [(v, x)]) rest` lets us prove `Ts`-perm invariance by
`Perm` induction.

Path-based reformulation of the legacy `pairSum` / `insertion_perm_guests`
machinery. The pair type changes from `Vertex t × Planar α` to
`Path × Planar α`. -/

/-- Multi-graft aggregator with an explicit pair pre (path-based). -/
private def pairSum (t : Planar α)
    (pre : List (Path × Planar α))
    (Ts : List (Planar α)) : Multiset (Nonplanar α) :=
  Multiset.ofList ((listChoices (vertices t) Ts.length).map
    fun c => Nonplanar.mk (multiGraft t (pre ++ c.zip Ts)))

private theorem pairSum_nil (t : Planar α)
    (pre : List (Path × Planar α)) :
    pairSum t pre [] =
      ({Nonplanar.mk (multiGraft t pre)} : Multiset (Nonplanar α)) := by
  unfold pairSum
  simp [listChoices_zero]

private theorem pairSum_cons (t : Planar α)
    (pre : List (Path × Planar α))
    (x : Planar α) (rest : List (Planar α)) :
    pairSum t pre (x :: rest) =
      (Multiset.ofList (vertices t)).bind fun v =>
        pairSum t (pre ++ [(v, x)]) rest := by
  unfold pairSum
  rw [List.length_cons, listChoices_succ, List.map_flatMap]
  simp only [List.map_map]
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun v _ => ?_
  apply congrArg Multiset.ofList
  apply List.map_congr_left
  intro c_rest _
  show Nonplanar.mk (multiGraft t (pre ++ (v :: c_rest).zip (x :: rest))) =
       Nonplanar.mk (multiGraft t ((pre ++ [(v, x)]) ++ c_rest.zip rest))
  have h_args : pre ++ (v :: c_rest).zip (x :: rest) =
                (pre ++ [(v, x)]) ++ c_rest.zip rest := by
    rw [List.zip_cons_cons, List.append_assoc]
    rfl
  rw [h_args]

/-- `pairSum` is invariant under `List.Perm` of the pre: pair-list order
    doesn't matter at the nonplanar level. -/
private theorem pairSum_pre_perm (t : Planar α)
    {pre pre' : List (Path × Planar α)}
    (h : pre.Perm pre') (Ts : List (Planar α)) :
    pairSum t pre Ts = pairSum t pre' Ts := by
  unfold pairSum
  congr 1
  apply List.map_congr_left
  intro c _
  apply Nonplanar.mk_eq_mk_iff.mpr
  exact multiGraft_perm_pair t (h.append_right _)

/-- Two unfoldings of `pairSum_cons` packed into a normal form for the
    swap proof. -/
private theorem pairSum_cons_cons (t : Planar α)
    (pre : List (Path × Planar α))
    (x y : Planar α) (rest : List (Planar α)) :
    pairSum t pre (x :: y :: rest) =
      (Multiset.ofList (vertices t)).bind fun v₀ =>
        (Multiset.ofList (vertices t)).bind fun v₁ =>
          pairSum t (pre ++ [(v₀, x), (v₁, y)]) rest := by
  rw [pairSum_cons]
  refine Multiset.bind_congr fun v₀ _ => ?_
  rw [pairSum_cons]
  refine Multiset.bind_congr fun v₁ _ => ?_
  congr 1
  simp [List.append_assoc]

/-- `pairSum` is invariant under swap of the first two guests. -/
private theorem pairSum_swap (t : Planar α)
    (pre : List (Path × Planar α))
    (a b : Planar α) (l : List (Planar α)) :
    pairSum t pre (b :: a :: l) = pairSum t pre (a :: b :: l) := by
  rw [pairSum_cons_cons, pairSum_cons_cons]
  rw [Multiset.bind_bind]
  refine Multiset.bind_congr fun _ _ => Multiset.bind_congr fun _ _ => ?_
  exact pairSum_pre_perm t (List.Perm.append_left pre (List.Perm.swap _ _ _)) l

/-- `pairSum t pre Ts` is invariant under `List.Perm` of `Ts`. -/
private theorem pairSum_perm_guests (t : Planar α)
    (pre : List (Path × Planar α))
    {Ts Ts' : List (Planar α)} (h : Ts.Perm Ts') :
    pairSum t pre Ts = pairSum t pre Ts' := by
  induction h generalizing pre with
  | nil => rfl
  | @cons x rest rest' _ ih =>
    rw [pairSum_cons, pairSum_cons]
    refine Multiset.bind_congr fun v _ => ?_
    exact ih (pre ++ [(v, x)])
  | @swap a b l => exact pairSum_swap t pre a b l
  | trans _ _ ih₁ ih₂ => exact (ih₁ pre).trans (ih₂ pre)

/-- Single-tree `insertion` is `mk`-invariant under `List.Perm` of guests. -/
theorem insertion_perm_guests (t : Planar α)
    {Ts Ts' : List (Planar α)} (h : Ts.Perm Ts') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t Ts').map Nonplanar.mk := by
  have := pairSum_perm_guests t [] h
  unfold pairSum at this
  simpa [insertion_def, Multiset.map_coe, List.map_map] using this

/-- Guest-list `Forall₂ PlanarEquiv` lifts to `insertion mk`-equality. -/
theorem insertion_planarEquiv_guests (t : Planar α)
    {Ts Ts' : List (Planar α)} (h : List.Forall₂ PlanarEquiv Ts Ts') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t Ts').map Nonplanar.mk := by
  have hlen : Ts.length = Ts'.length := h.length_eq
  rw [insertion_def, insertion_def, Multiset.map_coe, Multiset.map_coe,
      List.map_map, List.map_map, hlen]
  congr 1
  apply List.map_congr_left
  intro choice _
  apply Nonplanar.mk_eq_mk_iff.mpr
  -- multiGraft t (choice.zip Ts) ~ multiGraft t (choice.zip Ts')
  -- via List.Forall₂ for the pair (fst eq, snd planarEquiv)
  exact multiGraft_planarEquiv_pair_Forall₂ t (zip_pair_Forall₂ choice h)

/-! ## §5.5: A3.3 substrate — validity discharge and `multiGraft_compose`
        specializations

The A3.3 helpers (`LHS_TRUE_eq_T_buckets`, `LHS_FALSE_eq_FA_buckets` in
`InsertionAssoc.lean`) need to apply `multiGraft_compose` (Graft.lean §11.4)
to collapse nested-graft forms of the shape
```
multiGraft (multiGraft T (choice_o.zip outer_Ts)) (choice_i.zip inner_Ts)
```
into a single `multiGraft T (composePairs ...)`. The validity hypotheses
of `multiGraft_compose` (every pair's `.fst` is a valid path in the host)
are discharged here by lifting `mem ∈ listChoices (vertices T) n` to
`IsValidPath` via the existing `forall_isValidPath`.

These specializations are consumed downstream by the per-class bridge
lemmas (Session 2 onwards) of the A3.3 helpers.

Why this lives here and not in `Graft.lean`: `listChoices` is defined in
`Insertion.lean` §1, but `multiGraft_compose` is defined in `Graft.lean`
§11. The validity bridge crossing between them belongs here. -/

/-- Every element of a `choice ∈ listChoices xs n` is a member of `xs`.
    Lifts membership-in-an-enumerated-choice to membership-in-the-alphabet. -/
theorem mem_of_mem_listChoices {β : Type*}
    (xs : List β) (n : Nat) (choice : List β) (h_choice : choice ∈ listChoices xs n)
    (v : β) (h_v : v ∈ choice) : v ∈ xs := by
  induction n generalizing choice with
  | zero =>
    rw [listChoices_zero, List.mem_singleton] at h_choice
    subst h_choice
    cases h_v
  | succ k ih =>
    rw [listChoices_succ, List.mem_flatMap] at h_choice
    obtain ⟨w, hw_mem, h_choice⟩ := h_choice
    rw [List.mem_map] at h_choice
    obtain ⟨rest, hrest_mem, rfl⟩ := h_choice
    rw [List.mem_cons] at h_v
    rcases h_v with rfl | h_v
    · exact hw_mem
    · exact ih rest hrest_mem h_v

/-- Every path in a `choice.zip Ts` pair list is a valid path in `T`, when
    `choice ∈ listChoices (vertices T) Ts.length`. Discharges the
    `h_outer_valid` hypothesis of `multiGraft_compose` for the canonical
    A3.3 outer pair shape. -/
theorem forall_zip_isValidPath_of_listChoices
    (T : Planar α) (Ts : List (Planar α))
    (choice : List Path)
    (h_choice : choice ∈ listChoices (vertices T) Ts.length)
    (pair : Path × Planar α) (h_pair : pair ∈ choice.zip Ts) :
    IsValidPath pair.fst T := by
  have h_fst_mem : pair.fst ∈ choice := (List.of_mem_zip h_pair).1
  exact forall_isValidPath T (mem_of_mem_listChoices (vertices T) Ts.length
    choice h_choice pair.fst h_fst_mem)

/-- Auto-discharge variant of `multiGraft_compose` for the canonical A3.3
    outer-pair shape `choice_o.zip outer_Ts` with `choice_o ∈ listChoices
    (vertices T) outer_Ts.length`. The inner pair list's validity is
    passed as a hypothesis. -/
theorem multiGraft_compose_at_choice
    (T : Planar α) (outer_Ts : List (Planar α))
    (choice_o : List Path)
    (h_choice_o : choice_o ∈ listChoices (vertices T) outer_Ts.length)
    (inner_pairs : List (Path × Planar α))
    (h_inner_valid : ∀ p ∈ inner_pairs,
        IsValidPath p.fst (multiGraft T (choice_o.zip outer_Ts))) :
    multiGraft (multiGraft T (choice_o.zip outer_Ts)) inner_pairs =
      multiGraft T (composePairs (choice_o.zip outer_Ts) inner_pairs) := by
  apply multiGraft_compose T (choice_o.zip outer_Ts) inner_pairs
  · intro pair h_pair
    exact forall_zip_isValidPath_of_listChoices T outer_Ts choice_o h_choice_o pair h_pair
  · exact h_inner_valid

/-- Doubly auto-discharged variant: both outer and inner choices come from
    `listChoices`-derived enumerations. Specifically for the A3.3 TRUE-side
    shape where `inner = (v_c :: ch).zip (c :: filter_t)` with `v_c ∈
    vertices T'` and `ch ∈ listChoices (vertices T') filter_t.length`. -/
theorem multiGraft_compose_at_choice_inner_zip
    (T : Planar α) (outer_Ts : List (Planar α))
    (choice_o : List Path)
    (h_choice_o : choice_o ∈ listChoices (vertices T) outer_Ts.length)
    (inner_Ts : List (Planar α))
    (choice_i : List Path)
    (h_choice_i : choice_i ∈ listChoices
        (vertices (multiGraft T (choice_o.zip outer_Ts))) inner_Ts.length) :
    multiGraft (multiGraft T (choice_o.zip outer_Ts)) (choice_i.zip inner_Ts) =
      multiGraft T (composePairs (choice_o.zip outer_Ts) (choice_i.zip inner_Ts)) := by
  apply multiGraft_compose_at_choice T outer_Ts choice_o h_choice_o
  intro pair h_pair
  have h_fst_mem : pair.fst ∈ choice_i := (List.of_mem_zip h_pair).1
  exact forall_isValidPath _
    (mem_of_mem_listChoices _ inner_Ts.length choice_i h_choice_i pair.fst h_fst_mem)

/-- Cons-form specialization for the A3.3 TRUE-side pattern: the inner
    pair list has shape `(v_c, c) :: ch.zip filter_t` where `v_c ∈ vertices T'`
    and `ch ∈ listChoices (vertices T') filter_t.length`. The output of
    `multiGraft_compose_at_choice` becomes a single `multiGraft T` with
    `composePairs` building the combined pair list. -/
theorem multiGraft_compose_cons_pair_at_choice
    (T : Planar α) (outer_Ts : List (Planar α))
    (choice_o : List Path)
    (h_choice_o : choice_o ∈ listChoices (vertices T) outer_Ts.length)
    (filter_t : List (Planar α)) (c : Planar α)
    (v_c : Path)
    (h_v_c : v_c ∈ vertices (multiGraft T (choice_o.zip outer_Ts)))
    (ch : List Path)
    (h_ch : ch ∈ listChoices
        (vertices (multiGraft T (choice_o.zip outer_Ts))) filter_t.length) :
    multiGraft (multiGraft T (choice_o.zip outer_Ts))
        ((v_c, c) :: ch.zip filter_t) =
      multiGraft T (composePairs (choice_o.zip outer_Ts)
        ((v_c, c) :: ch.zip filter_t)) := by
  apply multiGraft_compose_at_choice T outer_Ts choice_o h_choice_o
  intro pair h_pair
  rcases List.mem_cons.mp h_pair with rfl | h_pair
  · exact forall_isValidPath _ h_v_c
  · have h_fst_mem : pair.fst ∈ ch := (List.of_mem_zip h_pair).1
    exact forall_isValidPath _
      (mem_of_mem_listChoices _ filter_t.length ch h_ch pair.fst h_fst_mem)

/-- Distribute `vertices_multiGraft_decomp`'s 3-class partition through a
    bind over `Multiset.ofList (vertices (multiGraft T pairs))`. The v_c
    bind in the A3.3 TRUE-side helper has exactly this shape; after this
    rewrite, the bind splits into 3 binds (one per class), each ready for
    per-class absorption (Sessions 2-3 substrate). -/
theorem vc_partition_via_bind
    {γ : Type*}
    (T : Planar α) (pairs : List (Path × Planar α))
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T)
    (f : Path → Multiset γ) :
    (((vertices (multiGraft T pairs) : List Path) : Multiset Path)).bind f =
      ((vertices T : Multiset Path).filterMap (preserveMulti pairs)).bind f +
      (((vertices T : Multiset Path).filter
          (· ∈ pairSources pairs)).map (transport pairs)).bind f +
      ((Multiset.ofList (List.finRange pairs.length)).bind
          (fun k => (vertices pairs[k].snd : Multiset Path).map
            (liftMulti pairs k))).bind f := by
  rw [vertices_multiGraft_decomp T pairs h_valid]
  rw [Multiset.add_bind, Multiset.add_bind]

/-- F-side analog: distribute `vertices_forest_eq_partition`'s per-tree
    3-class partition through a bind over `Multiset.ofList (verticesAux 0
    (forest as constructed))`. Specifically the A3.3 FALSE-side helper
    binds over the F'-side vertex enumeration, which has this shape with
    `cs = F_A` (preserved + sourceSelf) and per-tree lifted into pre_FA_B.

    NOTE: the FALSE side of A3.3 actually binds over `perKFChoice F'` not
    raw vertices of F'; see `perKFChoice_eq_forest_bind` (Session 4
    substrate) for the bridge from `perKFChoice` enumeration to vertex
    enumeration with per-tree (i, v) pairs. This lemma is the raw vertex
    form; pair with the forthcoming bridge to get the `perKFChoice` form. -/
theorem vc_partition_forest_via_bind
    {γ : Type*}
    (cs : List (Planar α))
    (per_tree_pairs : Fin cs.length → List (Path × Planar α))
    (h_valid : ∀ (i : Fin cs.length),
        ∀ pair ∈ per_tree_pairs i, IsValidPath pair.fst cs[i.val])
    (offset : ℕ)
    (f : Path → Multiset γ) :
    (((verticesAux offset
        ((List.finRange cs.length).map fun i =>
          multiGraft cs[i.val] (per_tree_pairs i)) : List Path) :
          Multiset Path)).bind f =
      (Multiset.ofList (List.finRange cs.length)).bind fun i =>
        ((((vertices cs[i.val] : Multiset Path).filterMap
              (preserveMulti (per_tree_pairs i)))
          + (((vertices cs[i.val] : Multiset Path).filter
                (· ∈ pairSources (per_tree_pairs i))).map
              (transport (per_tree_pairs i)))
          + ((Multiset.ofList (List.finRange (per_tree_pairs i).length)).bind
              (fun k => (vertices ((per_tree_pairs i)[k.val].snd) :
                Multiset Path).map (liftMulti (per_tree_pairs i) k)))
        ).map ((offset + i.val) :: ·)).bind f := by
  rw [vertices_forest_eq_partition cs per_tree_pairs h_valid offset]
  rw [Multiset.bind_assoc]

/-- Decompose `insertion T (c :: filter_t)` by extracting the leading vertex
    `v_c` as a bind variable. The first vertex choice routes `c`; the
    remaining `filter_t.length` choices route the rest of the guests. -/
theorem insertion_cons_pair_eq_bind
    (T : Planar α) (c : Planar α) (filter_t : List (Planar α)) :
    insertion T (c :: filter_t) =
      ((vertices T : List Path) : Multiset Path).bind (fun v_c =>
        Multiset.ofList ((listChoices (vertices T) filter_t.length).map (fun ch =>
          multiGraft T ((v_c, c) :: ch.zip filter_t)))) := by
  rw [insertion_def]
  show Multiset.ofList ((listChoices (vertices T) (c :: filter_t).length).map
        (fun choice => multiGraft T (choice.zip (c :: filter_t)))) = _
  rw [show (c :: filter_t).length = filter_t.length + 1 from rfl, listChoices_succ,
      List.map_flatMap]
  rw [show ((vertices T : List Path) : Multiset Path) =
        Multiset.ofList (vertices T) from rfl, ← Multiset.coe_bind]
  refine Multiset.bind_congr fun v_c _ => ?_
  rw [show (List.map (v_c :: ·) (listChoices (vertices T) filter_t.length)).map
            (fun choice => multiGraft T (choice.zip (c :: filter_t))) =
          (listChoices (vertices T) filter_t.length).map (fun ch =>
            multiGraft T ((v_c, c) :: ch.zip filter_t)) from by
    rw [List.map_map]
    rfl]

/-- Combined form for `insertion (multiGraft T pairs) (c :: filter_t)` binding
    into a function `K`: the v_c bind splits into preserved + sourceSelf + lifted
    via `vc_partition_via_bind`, with each class producing a sub-bind over
    `ch ∈ listChoices (vertices (multiGraft T pairs)) filter_t.length`. -/
theorem insertion_cons_pair_at_multiGraft_bind
    {γ : Type*}
    (T : Planar α) (pairs : List (Path × Planar α))
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T)
    (c : Planar α) (filter_t : List (Planar α))
    (K : Planar α → Multiset γ) :
    (insertion (multiGraft T pairs) (c :: filter_t)).bind K =
    -- preserved + sourceSelf class (v_c originates from T via transport pairs)
    (((vertices T : List Path) : Multiset Path).map (transport pairs)).bind (fun v_c =>
      (Multiset.ofList ((listChoices (vertices (multiGraft T pairs)) filter_t.length).map
          (fun ch =>
            multiGraft (multiGraft T pairs) ((v_c, c) :: ch.zip filter_t)))).bind K)
    +
    -- lifted class (v_c originates from pairs[k].snd via liftMulti pairs k)
    ((Multiset.ofList (List.finRange pairs.length)).bind
        (fun k => (vertices pairs[k].snd : Multiset Path).map
          (liftMulti pairs k))).bind (fun v_c =>
      (Multiset.ofList ((listChoices (vertices (multiGraft T pairs)) filter_t.length).map
          (fun ch =>
            multiGraft (multiGraft T pairs) ((v_c, c) :: ch.zip filter_t)))).bind K) := by
  rw [insertion_cons_pair_eq_bind]
  rw [Multiset.bind_assoc]
  rw [vc_partition_via_bind T pairs h_valid]
  rw [← preserved_add_sourceSelf_eq_vertices_map_transport pairs
        ((vertices T : List Path) : Multiset Path)]
  rw [Multiset.add_bind]

/-! ## §6: Host invariance via path-swap bijection

`insertion T Ts` is `mk`-invariant under `PlanarEquiv` of the host: the
original blocker for the path-based refactor.

Strategy:
1. `swapPathAt n` — swap the first index `n ↔ n+1` in a path.
2. `vertices_swap_perm` — applying `swapPathAt pre.length` to vertices of
   `node a (pre ++ l :: r :: post)` is a `List.Perm` of vertices of
   `node a (pre ++ r :: l :: post)`. Reduces to a `List.Perm` of two
   appendable middle blocks, via `verticesAux_append` + a
   `List.perm_append_comm`.
3. `multiGraft_swap_planarEquiv` — the multiGraft results differ only by
   the swap of l/r in the root children list; lift via
   `PlanarStep.swapAtRoot`.
4. Combine via listChoices Perm-respect → `insertion_swap_invariant`.
5. Lift via `PlanarStep` (recurse case) and `PlanarEquiv = EqvGen
   PlanarStep`. -/

/-- Swap the first index `n ↔ n+1` of a path. Acts as identity on paths
    starting outside `{n, n+1}` and on the root path `[]`. -/
def swapPathAt (n : ℕ) : Path → Path
  | []        => []
  | i :: rest =>
      if i = n then (n + 1) :: rest
      else if i = n + 1 then n :: rest
      else i :: rest

@[simp] theorem swapPathAt_nil (n : ℕ) : swapPathAt n [] = [] := rfl

theorem swapPathAt_cons_eq (n : ℕ) (rest : Path) :
    swapPathAt n (n :: rest) = (n + 1) :: rest := by
  simp [swapPathAt]

theorem swapPathAt_cons_eq_succ (n : ℕ) (rest : Path) :
    swapPathAt n ((n + 1) :: rest) = n :: rest := by
  simp [swapPathAt, Nat.succ_ne_self]

theorem swapPathAt_cons_of_ne (n i : ℕ) (rest : Path)
    (h1 : i ≠ n) (h2 : i ≠ n + 1) :
    swapPathAt n (i :: rest) = i :: rest := by
  simp [swapPathAt, h1, h2]

@[simp] theorem swapPathAt_involution (n : ℕ) (p : Path) :
    swapPathAt n (swapPathAt n p) = p := by
  cases p with
  | nil => rfl
  | cons i rest =>
    by_cases h1 : i = n
    · subst h1
      rw [swapPathAt_cons_eq, swapPathAt_cons_eq_succ]
    · by_cases h2 : i = n + 1
      · subst h2
        rw [swapPathAt_cons_eq_succ, swapPathAt_cons_eq]
      · rw [swapPathAt_cons_of_ne n i rest h1 h2,
            swapPathAt_cons_of_ne n i rest h1 h2]

/-- For paths produced by `verticesAux start cs` with all indices
    bounded below `n`, `swapPathAt n` acts as the identity. -/
private theorem map_swapPathAt_verticesAux_below
    (n start : ℕ) (cs : List (Planar α)) (h : start + cs.length ≤ n) :
    (verticesAux start cs).map (swapPathAt n) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have hlt : start < n := by simp [List.length_cons] at h; omega
    have hcs : start + 1 + cs.length ≤ n := by
      simp [List.length_cons] at h; omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show swapPathAt n (start :: q) = start :: q
      exact swapPathAt_cons_of_ne n start q (Nat.ne_of_lt hlt) (by omega)
    · exact ih (start + 1) hcs

/-- For paths produced by `verticesAux start cs` with all indices
    bounded above `n + 1`, `swapPathAt n` acts as the identity. -/
private theorem map_swapPathAt_verticesAux_above
    (n start : ℕ) (cs : List (Planar α)) (h : n + 1 < start) :
    (verticesAux start cs).map (swapPathAt n) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have h' : n + 1 < start + 1 := by omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show swapPathAt n (start :: q) = start :: q
      exact swapPathAt_cons_of_ne n start q (by omega) (by omega)
    · exact ih (start + 1) h'

/-- Vertices of `node a (pre ++ l :: r :: post)` mapped through
    `swapPathAt pre.length` is a `List.Perm` of vertices of
    `node a (pre ++ r :: l :: post)`. -/
theorem vertices_swap_perm (a : α) (pre : List (Planar α))
    (l r : Planar α) (post : List (Planar α)) :
    ((vertices (Planar.node a (pre ++ l :: r :: post))).map
        (swapPathAt pre.length)).Perm
      (vertices (Planar.node a (pre ++ r :: l :: post))) := by
  set n := pre.length with hn
  rw [vertices_node, vertices_node]
  -- Expand verticesAux via _append, plus verticesAux_cons twice
  rw [verticesAux_append, verticesAux_append, Nat.zero_add,
      verticesAux_cons, verticesAux_cons, verticesAux_cons, verticesAux_cons,
      List.map_cons]
  rw [swapPathAt_nil]
  refine List.Perm.cons _ ?_
  -- Distribute List.map over ++
  rw [List.map_append, List.map_append, List.map_append]
  -- pre's slice: identity
  rw [map_swapPathAt_verticesAux_below n 0 pre (by simp [hn])]
  -- post's slice: identity
  rw [map_swapPathAt_verticesAux_above n (n + 2) post (by omega)]
  -- l's slice: n → n+1
  have hl : (List.map (fun x => n :: x) (vertices l)).map (swapPathAt n) =
            List.map (fun x => (n + 1) :: x) (vertices l) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    exact swapPathAt_cons_eq n q
  -- r's slice: n+1 → n
  have hr : (List.map (fun x => (n + 1) :: x) (vertices r)).map (swapPathAt n) =
            List.map (fun x => n :: x) (vertices r) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    exact swapPathAt_cons_eq_succ n q
  rw [hl, hr]
  -- Goal: pre' ++ (l@n+1) ++ ((r@n) ++ post') ~ pre' ++ ((r@n) ++ ((l@n+1) ++ post'))
  -- Common prefix `pre'` peels off; then swap two middle blocks.
  refine List.Perm.append_left _ ?_
  rw [← List.append_assoc, ← List.append_assoc]
  refine List.Perm.append_right _ ?_
  exact List.perm_append_comm

/-! ### §6.2 substrate: pair-relabel + planarEquiv prefix-cons-lift -/

/-- The path-relabel function for swapAtRoot. -/
private def pathRelabelSwap (n : ℕ) : Path × Planar α → Path × Planar α :=
  Prod.map (swapPathAt n) id

@[simp] private theorem pathRelabelSwap_fst (n : ℕ) (p : Path × Planar α) :
    (pathRelabelSwap n p).fst = swapPathAt n p.fst := rfl

@[simp] private theorem pathRelabelSwap_snd (n : ℕ) (p : Path × Planar α) :
    (pathRelabelSwap n p).snd = p.snd := rfl

/-- Path bijection induced by `PlanarStep.recurse`: lift an inner path
    bijection `f` (applicable to vertices of the changed subtree at child
    position `n`) to the whole tree. Identity on paths not going through
    child `n`. -/
private def pathLiftRecurse (n : ℕ) (f : Path → Path) : Path → Path
  | []        => []
  | i :: rest => if i = n then n :: f rest else i :: rest

@[simp] private theorem pathLiftRecurse_nil (n : ℕ) (f : Path → Path) :
    pathLiftRecurse n f [] = [] := rfl

private theorem pathLiftRecurse_cons_eq (n : ℕ) (f : Path → Path) (rest : Path) :
    pathLiftRecurse n f (n :: rest) = n :: f rest := by
  simp [pathLiftRecurse]

private theorem pathLiftRecurse_cons_of_ne (n i : ℕ) (f : Path → Path) (rest : Path)
    (h : i ≠ n) :
    pathLiftRecurse n f (i :: rest) = i :: rest := by
  simp [pathLiftRecurse, h]

/-- `pathLiftRecurse n f` acts as identity on paths produced by
    `verticesAux start cs` when those paths' first indices are all below `n`. -/
private theorem map_pathLiftRecurse_verticesAux_below
    (n start : ℕ) (f : Path → Path) (cs : List (Planar α))
    (h : start + cs.length ≤ n) :
    (verticesAux start cs).map (pathLiftRecurse n f) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have hlt : start < n := by simp [List.length_cons] at h; omega
    have hcs : start + 1 + cs.length ≤ n := by simp [List.length_cons] at h; omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show pathLiftRecurse n f (start :: q) = start :: q
      exact pathLiftRecurse_cons_of_ne n start f q (Nat.ne_of_lt hlt)
    · exact ih (start + 1) hcs

/-- `pathLiftRecurse n f` acts as identity on paths produced by
    `verticesAux start cs` when those paths' first indices are all above `n`. -/
private theorem map_pathLiftRecurse_verticesAux_above
    (n start : ℕ) (f : Path → Path) (cs : List (Planar α))
    (h : n < start) :
    (verticesAux start cs).map (pathLiftRecurse n f) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have h' : n < start + 1 := by omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show pathLiftRecurse n f (start :: q) = start :: q
      exact pathLiftRecurse_cons_of_ne n start f q (by omega : start ≠ n)
    · exact ih (start + 1) h'

/-- Vertices Perm under `PlanarStep.recurse`: given a path bijection on
    the changed subtree, lift to a Perm on the bigger tree's vertices. -/
private theorem vertices_recurse_perm (a : α) (pre : List (Planar α))
    (old new : Planar α) (post : List (Planar α)) (f : Path → Path)
    (hf : ((vertices old).map f).Perm (vertices new)) :
    ((vertices (Planar.node a (pre ++ old :: post))).map
        (pathLiftRecurse pre.length f)).Perm
      (vertices (Planar.node a (pre ++ new :: post))) := by
  set n := pre.length with hn_eq
  rw [vertices_node, vertices_node,
      verticesAux_append, verticesAux_append, Nat.zero_add,
      verticesAux_cons, verticesAux_cons, List.map_cons, pathLiftRecurse_nil]
  refine List.Perm.cons _ ?_
  rw [List.map_append, List.map_append]
  rw [map_pathLiftRecurse_verticesAux_below n 0 f pre (by simp [hn_eq])]
  rw [map_pathLiftRecurse_verticesAux_above n (n + 1) f post (by omega)]
  -- Goal: pre' ++ ((vertices old).map (n :: ·)).map (pathLiftRecurse n f) ++ post' ~Perm~
  --       pre' ++ (vertices new).map (n :: ·) ++ post'
  refine List.Perm.append_left _ (List.Perm.append_right _ ?_)
  -- Goal: ((vertices old).map (n :: ·)).map (pathLiftRecurse n f) ~Perm~ (vertices new).map (n :: ·)
  rw [List.map_map]
  -- Goal: List.map (pathLiftRecurse n f ∘ fun x => n :: x) (vertices old) ~Perm~ ...
  have h_map_eq : List.map (pathLiftRecurse n f ∘ fun x => n :: x) (vertices old) =
                  ((vertices old).map f).map (fun x => n :: x) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    show pathLiftRecurse n f (n :: q) = n :: f q
    exact pathLiftRecurse_cons_eq n f q
  rw [h_map_eq]
  exact hf.map _

/-- Helper: `PlanarEquiv` of two trees with a common children prefix.
    Lifts `(node a cs) ~ (node a ds)` to `(node a (pre ++ cs)) ~ (node a (pre ++ ds))`
    by iterated `planarEquiv_cons_lift`. -/
private theorem planarEquiv_append_left_node {a : α} (pre : List (Planar α))
    {cs ds : List (Planar α)}
    (h : PlanarEquiv (.node a cs) (.node a ds)) :
    PlanarEquiv (.node a (pre ++ cs)) (.node a (pre ++ ds)) := by
  induction pre with
  | nil => exact h
  | cons p pre' ih => exact planarEquiv_cons_lift p ih

/-- `multiGraft` is `PlanarEquiv`-invariant under a `PlanarStep.recurse`:
    if the inner subtree change `old → new` admits a path-bijection `f`
    that turns `multiGraft old` into `multiGraft new ∘ relabel-via-f`, then
    the same holds for the host with prefix `pre` and suffix `post`, using
    `pathLiftRecurse pre.length f`. -/
private theorem multiGraft_recurse_planarEquiv (a : α)
    {old new : Planar α} (f : Path → Path)
    (hf : ∀ sub_pairs, PlanarEquiv (multiGraft old sub_pairs)
                                    (multiGraft new (sub_pairs.map (Prod.map f id)))) :
    ∀ (pre : List (Planar α)) (post : List (Planar α))
      (pairs : List (Path × Planar α)),
    PlanarEquiv
      (multiGraft (Planar.node a (pre ++ old :: post)) pairs)
      (multiGraft (Planar.node a (pre ++ new :: post))
                  (pairs.map (Prod.map (pathLiftRecurse pre.length f) id))) := by
  intro pre post pairs
  induction pre generalizing pairs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs old post, multiGraftChildren_cons_cs new post]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, rootPrependFilter, pathLiftRecurse]
        · simp [hp, rootPrependFilter, pathLiftRecurse_cons_of_ne 0 i f rest h1]
    have h_cP : (pairs.filterMap headChildFilter).map (Prod.map f id) =
                (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                  headChildFilter := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, headChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, headChildFilter,
                pathLiftRecurse_cons_of_ne 0 i f rest h1]
          cases i with
          | zero => exact absurd rfl h1
          | succ k => rfl
    have h_csP : pairs.filterMap tailChildFilter =
                 (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                   tailChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, tailChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, tailChildFilter, pathLiftRecurse_cons_of_ne 0 i f rest h1]
    -- Use hf on the head child; identity on root prepends and post; lift via recurse.
    have h_old := hf (pairs.filterMap headChildFilter)
    rw [h_cP] at h_old
    rw [← h_RP, ← h_csP]
    -- Goal: node a (RP ++ multiGraft old cP :: mGC post csP) ~PE~
    --        node a (RP ++ multiGraft new cP' :: mGC post csP) where
    --        cP' = (pairs.map ...).filterMap headChildFilter = cP.map (Prod.map f id)
    exact planarEquiv_append_left_node _
      (planarEquiv_recurse_lift [] _ h_old)
  | cons c pre' ih =>
    rw [show (c :: pre') ++ old :: post = c :: (pre' ++ old :: post) from rfl,
        show (c :: pre') ++ new :: post = c :: (pre' ++ new :: post) from rfl,
        show (c :: pre').length = pre'.length + 1 from rfl]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs c (pre' ++ old :: post),
        multiGraftChildren_cons_cs c (pre' ++ new :: post)]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, rootPrependFilter, pathLiftRecurse_cons_eq]
        · simp [hp, rootPrependFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
    have h_cP : pairs.filterMap headChildFilter =
                (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                  headChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, headChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, headChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
    have h_csP : (pairs.filterMap tailChildFilter).map
                   (Prod.map (pathLiftRecurse pre'.length f) id) =
                 (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                   tailChildFilter := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathLiftRecurse_cons_eq,
                pathLiftRecurse_cons_eq pre'.length f rest]
        · simp [hp, tailChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
          cases i with
          | zero => simp [tailChildFilter]
          | succ j =>
            have hjne : j ≠ pre'.length := by intro heq; apply h1; omega
            simp [tailChildFilter, pathLiftRecurse_cons_of_ne pre'.length j f rest hjne]
    -- Apply IH on pre' with input csP (= pairs.filterMap tailChildFilter).
    -- IH gives PE on multiGrafts; unfold via multiGraft_node and discard empty rootPrepends
    -- (tailChildFilter only produces non-empty fsts).
    have h_ih := ih (pairs.filterMap tailChildFilter)
    rw [h_csP] at h_ih
    rw [multiGraft_node, multiGraft_node] at h_ih
    have h_RP_lhs : (pairs.filterMap tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j => simp [hp, tailChildFilter, rootPrependFilter]
    have h_RP_rhs : ((pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                       tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap, List.filterMap_map]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathLiftRecurse_cons_eq, rootPrependFilter]
        · simp [hp, tailChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
          cases i with
          | zero => simp [tailChildFilter]
          | succ j => simp [tailChildFilter, rootPrependFilter]
    rw [h_RP_lhs, List.nil_append] at h_ih
    rw [h_RP_rhs, List.nil_append] at h_ih
    rw [← h_RP, ← h_cP]
    -- Goal: node a (RP ++ multiGraft c cP :: mGC (pre' ++ old :: post) csP) ~PE~
    --        node a (RP ++ multiGraft c cP :: mGC (pre' ++ new :: post) csP_relabeled)
    exact planarEquiv_append_left_node _ (planarEquiv_cons_lift _ h_ih)

/-- `multiGraft` is `PlanarEquiv`-invariant under swap of two adjacent
    root children, with pairs relabeled via `swapPathAt`. The proof
    decomposes both sides into matching children lists (up to a single
    swap), then applies `PlanarStep.swapAtRoot`.

    Sub-lemmas for the filter equalities are proved inline as `have`
    statements to ensure the inline-match expressions unify with the
    matcher generated by `multiGraft_node`. -/
theorem multiGraft_swap_planarEquiv
    (a : α) (pre : List (Planar α)) (l r : Planar α)
    (post : List (Planar α)) (pairs : List (Path × Planar α)) :
    PlanarEquiv
      (multiGraft (Planar.node a (pre ++ l :: r :: post)) pairs)
      (multiGraft (Planar.node a (pre ++ r :: l :: post))
                  (pairs.map (pathRelabelSwap pre.length))) := by
  -- The cleanest path: induct on pre, peeling off one child at a time.
  -- Base case (pre = []) does the actual swap; inductive case lifts via
  -- planarEquiv_cons_lift.
  induction pre generalizing pairs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [multiGraft_node, multiGraft_node]
    -- Build sub-perms and combine via planarEquiv_root_perm.
    have h_RP_perm : (pairs.filterMap fun pair => match pair.fst with
                                                    | []     => some pair.snd
                                                    | _ :: _ => none).Perm
                      ((pairs.map (pathRelabelSwap 0)).filterMap
                          fun pair => match pair.fst with
                                       | []     => some pair.snd
                                       | _ :: _ => none) := by
      rw [List.filterMap_map]
      apply List.Perm.of_eq
      refine List.filterMap_congr fun pair _ => ?_
      simp only [Function.comp, pathRelabelSwap_fst, pathRelabelSwap_snd]
      cases hp : pair.fst with
      | nil => rw [swapPathAt_nil]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; rw [swapPathAt_cons_eq]
        · by_cases h2 : i = 1
          · subst h2; rw [swapPathAt_cons_eq_succ]
          · rw [swapPathAt_cons_of_ne 0 i rest h1 h2]
    have h_mGC_perm : (multiGraftChildren (l :: r :: post) pairs).Perm
                      (multiGraftChildren (r :: l :: post)
                          (pairs.map (pathRelabelSwap 0))) := by
      -- Decompose both via cons_cs (now using top-level filter helpers).
      rw [multiGraftChildren_cons_cs l (r :: post),
          multiGraftChildren_cons_cs r (l :: post),
          multiGraftChildren_cons_cs r post,
          multiGraftChildren_cons_cs l post]
      -- Three filter equalities, each via List.filterMap_map +
      -- List.filterMap_filterMap + List.filterMap_congr + case analysis.
      have h_l : pairs.filterMap headChildFilter =
                 ((pairs.map (pathRelabelSwap 0)).filterMap tailChildFilter).filterMap
                    headChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, headChildFilter, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, headChildFilter, tailChildFilter,
                            pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, headChildFilter, tailChildFilter,
                              pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, headChildFilter, tailChildFilter,
                                  pathRelabelSwap, swapPathAt]
      have h_r : (pairs.filterMap tailChildFilter).filterMap headChildFilter =
                 (pairs.map (pathRelabelSwap 0)).filterMap headChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, headChildFilter, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, headChildFilter, tailChildFilter,
                            pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, headChildFilter, tailChildFilter,
                              pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, headChildFilter, tailChildFilter,
                                  pathRelabelSwap, swapPathAt]
      have h_post : (pairs.filterMap tailChildFilter).filterMap tailChildFilter =
                    ((pairs.map (pathRelabelSwap 0)).filterMap tailChildFilter).filterMap
                       tailChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
      rw [h_l, h_r, h_post]
      exact List.Perm.swap _ _ _
    exact planarEquiv_root_perm (List.Perm.append h_RP_perm h_mGC_perm)
  | cons c pre' ih =>
    -- pre = c :: pre'. n = pre'.length + 1.
    -- Strategy: peel off `c` via multiGraftChildren_cons_cs, identify the
    -- rootPrepends and head-child filter (invariant under relabel-at-(n+1)
    -- since the relabel only swaps indices n+1, n+2), then apply IH on
    -- pre' with input = pairs.filterMap tailChildFilter.
    rw [show (c :: pre') ++ l :: r :: post = c :: (pre' ++ l :: r :: post) from rfl,
        show (c :: pre') ++ r :: l :: post = c :: (pre' ++ r :: l :: post) from rfl,
        show (c :: pre').length = pre'.length + 1 from rfl]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs c (pre' ++ l :: r :: post),
        multiGraftChildren_cons_cs c (pre' ++ r :: l :: post)]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2; simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
          · simp [hp, rootPrependFilter, pathRelabelSwap,
                  swapPathAt_cons_of_ne (pre'.length + 1) i rest h1 h2]
    have h_X_l : pairs.filterMap headChildFilter =
                 (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                   headChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2; simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
          · simp [hp, headChildFilter, pathRelabelSwap,
                  swapPathAt_cons_of_ne (pre'.length + 1) i rest h1 h2]
    have h_X_pre : (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                       tailChildFilter =
                   (pairs.filterMap tailChildFilter).map
                       (pathRelabelSwap pre'.length) := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2
            simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
          · cases i with
            | zero =>
              simp [hp, tailChildFilter, pathRelabelSwap,
                    swapPathAt_cons_of_ne (pre'.length + 1) 0 rest h1 h2]
            | succ j =>
              have hjne : j ≠ pre'.length := by intro heq; apply h1; omega
              have hjne2 : j ≠ pre'.length + 1 := by intro heq; apply h2; omega
              simp [hp, tailChildFilter, pathRelabelSwap,
                    swapPathAt_cons_of_ne (pre'.length + 1) (j + 1) rest h1 h2,
                    swapPathAt_cons_of_ne pre'.length j rest hjne hjne2]
    -- Use IH on pre' with input = pairs.filterMap tailChildFilter.
    have h_ih := ih (pairs.filterMap tailChildFilter)
    -- IH: PlanarEquiv (multiGraft (node a (pre' ++ l :: r :: post)) X_pre)
    --                 (multiGraft (node a (pre' ++ r :: l :: post)) (X_pre.map ...))
    -- Unfold both sides of IH to expose mGC.
    rw [multiGraft_node, multiGraft_node] at h_ih
    -- The rootPrepends in h_ih's LHS: (pairs.filterMap tailChildFilter).filterMap rootPrependFilter.
    -- tailChildFilter never outputs empty fst, so this is [].
    have h_empty_RP_lhs :
        (pairs.filterMap tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j => simp [hp, tailChildFilter, rootPrependFilter]
    have h_empty_RP_rhs :
        ((pairs.filterMap tailChildFilter).map (pathRelabelSwap pre'.length)).filterMap
          rootPrependFilter = [] := by
      rw [List.filterMap_map, List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j =>
          by_cases hj1 : j = pre'.length
          · subst hj1
            simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                  swapPathAt_cons_eq]
          · by_cases hj2 : j = pre'.length + 1
            · subst hj2
              simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                    swapPathAt_cons_eq_succ]
            · simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                    swapPathAt_cons_of_ne pre'.length j rest hj1 hj2]
    rw [h_empty_RP_lhs, List.nil_append] at h_ih
    rw [h_empty_RP_rhs, List.nil_append] at h_ih
    -- Now h_ih has form: PlanarEquiv (node a (mGC ... X_pre)) (node a (mGC ... X_pre_relabeled))
    -- Use h_X_pre to rewrite X_pre_relabeled inside.
    rw [← h_X_pre] at h_ih
    -- Lift IH through cons (multiGraft c X_l ::) and append_left (RP ++).
    have h_after_cons : PlanarEquiv
        (Planar.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ l :: r :: post)
                           (pairs.filterMap tailChildFilter)))
        (Planar.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ r :: l :: post)
                           ((pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                             tailChildFilter))) :=
      planarEquiv_cons_lift _ h_ih
    have h_after_append := planarEquiv_append_left_node
                            (pairs.filterMap rootPrependFilter) h_after_cons
    -- Goal's RHS uses relabeled forms; rewrite back to unrelabeled to match
    -- h_after_append.
    rw [← h_RP, ← h_X_l]
    exact h_after_append

/-! ### §6.3 substrate for `insertion_planarEquiv_host`

The `swapAtRoot` case of `insertion_planarStep_host` needs to lift a Perm
of vertices into a Perm of choice lists (via `listChoices`), then combine
with `multiGraft_swap_planarEquiv` to get equal `mk`-mapped insertion
outputs. Helpers below build this bridge. -/

/-- `listChoices` is compatible with `List.map`: applying `f` element-wise
    to choices in `xs.map f` gives the same as mapping `List.map f` over
    `listChoices xs n`. -/
theorem listChoices_map {β γ : Type*} (f : β → γ) (xs : List β) (n : Nat) :
    listChoices (xs.map f) n = (listChoices xs n).map (List.map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [listChoices_succ, listChoices_succ]
    -- (xs.map f).flatMap (fun v => listChoices (xs.map f) n .map (v :: ·)) =
    -- (xs.flatMap (fun v => listChoices xs n .map (v :: ·))).map (List.map f)
    rw [List.flatMap_map]
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro b _
    rw [ih]
    rw [List.map_map, List.map_map]
    rfl

/-- `listChoices` respects `List.Perm` of the source: a Perm of `xs` and
    `ys` lifts to a Perm of `listChoices xs n` and `listChoices ys n`. -/
theorem listChoices_perm {β : Type*} {xs ys : List β}
    (h : xs.Perm ys) (n : Nat) :
    (listChoices xs n).Perm (listChoices ys n) := by
  induction n with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    rw [listChoices_succ, listChoices_succ]
    refine h.flatMap (fun b _ => ?_)
    exact ih.map _

/-- Generic lifting: a path bijection `f` that turns vertices of `t` into a
    `Perm` of vertices of `t'` and turns `multiGraft t pairs` into a
    `PlanarEquiv` of `multiGraft t' (pairs.map (Prod.map f id))` lifts to
    `mk`-equality of `insertion t Ts` and `insertion t' Ts`. -/
private theorem insertion_eq_of_pathBij {t t' : Planar α}
    (f : Path → Path)
    (hf_perm : ((vertices t).map f).Perm (vertices t'))
    (hf_graft : ∀ pairs, PlanarEquiv (multiGraft t pairs)
                                      (multiGraft t' (pairs.map (Prod.map f id))))
    (Ts : List (Planar α)) :
    (insertion t Ts).map Nonplanar.mk = (insertion t' Ts).map Nonplanar.mk := by
  rw [insertion_def, insertion_def, Multiset.map_coe, Multiset.map_coe,
      List.map_map, List.map_map]
  refine Quot.sound ?_
  have hlc_eq : listChoices ((vertices t).map f) Ts.length =
                (listChoices (vertices t) Ts.length).map (List.map f) :=
    listChoices_map _ _ _
  have hlc_perm := listChoices_perm hf_perm Ts.length
  rw [hlc_eq] at hlc_perm
  -- LHS values agree with t'-multiGraft after relabel; RHS values are just t'-multiGraft.
  have step1 :
      ((listChoices (vertices t) Ts.length).map
          (fun choice => Nonplanar.mk (multiGraft t (choice.zip Ts)))).Perm
      ((listChoices (vertices t) Ts.length).map
          (fun choice => Nonplanar.mk (multiGraft t' ((choice.map f).zip Ts)))) := by
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro choice _
    apply Nonplanar.mk_eq_mk_iff.mpr
    have h_mge := hf_graft (choice.zip Ts)
    have h_zip : (choice.zip Ts).map (Prod.map f id) = (choice.map f).zip Ts := by
      simp [List.zip_map_left]
    rw [h_zip] at h_mge
    exact h_mge
  have step2 :
      ((listChoices (vertices t) Ts.length).map
          (fun choice => Nonplanar.mk (multiGraft t' ((choice.map f).zip Ts)))).Perm
      ((listChoices (vertices t') Ts.length).map
          (fun choice => Nonplanar.mk (multiGraft t' (choice.zip Ts)))) := by
    have := hlc_perm.map (fun choice => Nonplanar.mk (multiGraft t' (choice.zip Ts)))
    rw [List.map_map] at this
    exact this
  exact step1.trans step2

/-- Every `PlanarStep` admits a path bijection that respects both vertex
    enumeration (up to `Perm`) and `multiGraft` (up to `PlanarEquiv` after
    `Prod.map f id` relabel). For `swapAtRoot` the bijection is
    `swapPathAt pre.length`; for `recurse` it is `pathLiftRecurse pre.length`
    of the inner bijection. -/
private theorem exists_pathBijection_planarStep :
    ∀ {t t' : Planar α}, PlanarStep t t' →
    ∃ f : Path → Path,
      ((vertices t).map f).Perm (vertices t') ∧
      ∀ pairs, PlanarEquiv (multiGraft t pairs)
                            (multiGraft t' (pairs.map (Prod.map f id))) := by
  intro t t' h
  induction h with
  | @swapAtRoot a l r pre post =>
    exact ⟨swapPathAt pre.length, vertices_swap_perm a pre l r post,
           fun pairs => multiGraft_swap_planarEquiv a pre l r post pairs⟩
  | @recurse a pre old new post h_inner ih =>
    obtain ⟨f', hf_perm', hf_graft'⟩ := ih
    exact ⟨pathLiftRecurse pre.length f',
           vertices_recurse_perm a pre old new post f' hf_perm',
           fun pairs => multiGraft_recurse_planarEquiv a f' hf_graft' pre post pairs⟩

/-- `insertion T Ts` is `mk`-invariant under a single `PlanarStep` of the
    host. Direct application of `exists_pathBijection_planarStep` +
    `insertion_eq_of_pathBij`. -/
private theorem insertion_planarStep_host (Ts : List (Planar α))
    {t t' : Planar α} (h : PlanarStep t t') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t' Ts).map Nonplanar.mk := by
  obtain ⟨f, hf_perm, hf_graft⟩ := exists_pathBijection_planarStep h
  exact insertion_eq_of_pathBij f hf_perm hf_graft Ts

/-- `insertion T Ts` is `mk`-invariant under `PlanarEquiv` of the host. -/
theorem insertion_planarEquiv_host (Ts : List (Planar α))
    {t t' : Planar α} (h : PlanarEquiv t t') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t' Ts).map Nonplanar.mk := by
  induction h with
  | rel _ _ hstep => exact insertion_planarStep_host Ts hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- `List.Forall₂ PlanarEquiv` lifts to `List` equality after mapping by
    `Nonplanar.mk` — used for the `Ts = []` base case of forest host
    invariance. -/
private theorem map_mk_eq_of_forall2_planarEquiv {F F' : List (Planar α)}
    (h : List.Forall₂ PlanarEquiv F F') :
    F.map Nonplanar.mk = F'.map Nonplanar.mk := by
  induction h with
  | nil => rfl
  | cons hd_pe _ ih => simp [Nonplanar.mk_eq_mk_iff.mpr hd_pe, ih]

/-- Forest host invariance: `Forall₂ PlanarEquiv F F'` lifts to
    `mk`-equality of `insertionForest F Ts` and `insertionForest F' Ts`. -/
theorem insertionForest_planarEquiv_host
    (Ts : List (Planar α)) {F F' : List (Planar α)}
    (h : List.Forall₂ PlanarEquiv F F') :
    (insertionForest F Ts).map (List.map Nonplanar.mk) =
      (insertionForest F' Ts).map (List.map Nonplanar.mk) := by
  induction h generalizing Ts with
  | nil =>
    cases Ts with
    | nil => rfl
    | cons _ _ => rfl
  | @cons T T' F_tail F'_tail hd_pe tail_pe ih =>
    cases Ts with
    | nil =>
      simp [insertionForest_cons_host_nil_guests, Multiset.map_singleton,
            List.map_cons, Nonplanar.mk_eq_mk_iff.mpr hd_pe,
            map_mk_eq_of_forall2_planarEquiv tail_pe]
    | cons T_g Ts_inner =>
      rw [insertionForest_cons_cons, insertionForest_cons_cons]
      rw [Multiset.map_bind, Multiset.map_bind]
      refine Multiset.bind_congr fun assign _ => ?_
      rw [Multiset.map_bind, Multiset.map_bind]
      simp only [Multiset.map_map, Function.comp, List.map_cons]
      let f_T : Nonplanar α → Multiset (List (Nonplanar α)) :=
        fun mk_T_ins =>
          (insertionForest F_tail (((T_g :: Ts_inner).zip assign).filterMap fun p =>
              if p.snd then none else some p.fst)).map
            (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
      let f_T' : Nonplanar α → Multiset (List (Nonplanar α)) :=
        fun mk_T_ins =>
          (insertionForest F'_tail (((T_g :: Ts_inner).zip assign).filterMap fun p =>
              if p.snd then none else some p.fst)).map
            (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
      change (insertion T _).bind (fun T_ins => f_T (Nonplanar.mk T_ins)) =
             (insertion T' _).bind (fun T_ins => f_T' (Nonplanar.mk T_ins))
      rw [← Multiset.bind_map, ← Multiset.bind_map]
      rw [insertion_planarEquiv_host _ hd_pe]
      refine Multiset.bind_congr fun mk_T_ins _ => ?_
      show (insertionForest F_tail _).map (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk) =
           (insertionForest F'_tail _).map (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
      rw [show (fun F_ins : List (Planar α) => mk_T_ins :: F_ins.map Nonplanar.mk) =
              ((fun L : List (Nonplanar α) => mk_T_ins :: L) ∘ List.map Nonplanar.mk) from rfl]
      rw [← Multiset.map_map, ← Multiset.map_map]
      rw [ih]

/-! ### §7.1 substrate for `insertionForest_perm_guests`

Forest-side analogue of `pairSum`: a Multiset aggregator that splits the
guest list into a `pre_T` bucket (going to the head host `T`) and a
`pre_F` bucket (going to the tail forest), then aggregates over all
remaining assignments. Used to make `Ts`-Perm-invariance provable by
induction on the Perm structure (the swap case becomes a clean
`Multiset.bind_bind` after lifting to the mk-mapped level). -/

/-- Aggregator: at the leaf (no remaining guests), produce the inner
    forest insertion using `pre_T` for `T` and `pre_F` for the tail.
    At a cons, bind over `[true, false]` and extend either bucket. -/
private def forestPairSum (F : List (Planar α)) :
    List (Planar α) → List (Planar α) → List (Planar α) →
      Multiset (List (Planar α))
  | pre_T, pre_F, []       =>
      match F with
      | []          =>
          match pre_T, pre_F with
          | [], [] => ({[]} : Multiset _)
          | _, _ => 0
      | T :: F_tail =>
          (insertion T pre_T).bind fun T' =>
            (insertionForest F_tail pre_F).map fun F' => T' :: F'
  | pre_T, pre_F, x :: rest =>
      (Multiset.ofList [true, false]).bind fun b =>
        if b then forestPairSum F (pre_T ++ [x]) pre_F rest
        else forestPairSum F pre_T (pre_F ++ [x]) rest

/-- Equation lemma: `forestPairSum F pre_T pre_F []` for `F = T :: F_tail`. -/
private theorem forestPairSum_cons_F_nil_remaining
    (T : Planar α) (F_tail pre_T pre_F : List (Planar α)) :
    forestPairSum (T :: F_tail) pre_T pre_F [] =
      (insertion T pre_T).bind fun T' =>
        (insertionForest F_tail pre_F).map fun F' => T' :: F' := by
  unfold forestPairSum; rfl

/-- Equation lemma: `forestPairSum F pre_T pre_F (x :: rest)`. -/
private theorem forestPairSum_cons_remaining
    (F pre_T pre_F : List (Planar α)) (x : Planar α) (rest : List (Planar α)) :
    forestPairSum F pre_T pre_F (x :: rest) =
      (Multiset.ofList [true, false]).bind fun b =>
        if b then forestPairSum F (pre_T ++ [x]) pre_F rest
        else forestPairSum F pre_T (pre_F ++ [x]) rest := rfl

/-- Assignment-rewrite: `forestPairSum` over remaining guests `Ts`
    equals the sum over all `[true, false]`-assignments to `Ts` of
    `forestPairSum` on the empty remaining list with the accumulators
    augmented by the partition of `Ts.zip α`. This rephrases the
    recursive accumulator-build as a single bind over `listChoices`. -/
private theorem forestPairSum_assignment_rewrite (F : List (Planar α)) :
    ∀ (pre_T pre_F : List (Planar α)) (Ts : List (Planar α)),
    forestPairSum F pre_T pre_F Ts =
      (Multiset.ofList (listChoices [true, false] Ts.length)).bind fun α =>
        forestPairSum F
          (pre_T ++ (Ts.zip α).filterMap (fun p => if p.snd then some p.fst else none))
          (pre_F ++ (Ts.zip α).filterMap (fun p => if p.snd then none else some p.fst))
          [] := by
  intro pre_T pre_F Ts
  induction Ts generalizing pre_T pre_F with
  | nil =>
    simp [listChoices_zero, List.filterMap_nil, List.append_nil]
  | cons x rest ih =>
    rw [forestPairSum_cons_remaining]
    -- Decompose RHS: listChoices_succ + coe-bind
    conv_rhs =>
      rw [show (x :: rest).length = rest.length + 1 from rfl, listChoices_succ]
      rw [show (Multiset.ofList ([true, false].flatMap fun v =>
                  (listChoices [true, false] rest.length).map (v :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList [true, false]).bind fun v =>
                Multiset.ofList ((listChoices [true, false] rest.length).map (v :: ·))
              from by rw [← Multiset.coe_bind]]
      rw [Multiset.bind_assoc]
    -- Both sides have outer bind on ofList [t,f]; congrue per branch
    refine Multiset.bind_congr fun b _ => ?_
    cases b with
    | true =>
      rw [if_pos rfl]
      rw [show (Multiset.ofList ((listChoices [true, false] rest.length).map (true :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList (listChoices [true, false] rest.length)).map (true :: ·)
              from rfl]
      rw [Multiset.bind_map]
      rw [ih (pre_T ++ [x]) pre_F]
      refine Multiset.bind_congr fun α _ => ?_
      rw [List.append_assoc, List.singleton_append]
      rfl
    | false =>
      rw [if_neg (by decide : (false : Bool) ≠ true)]
      rw [show (Multiset.ofList ((listChoices [true, false] rest.length).map (false :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList (listChoices [true, false] rest.length)).map (false :: ·)
              from rfl]
      rw [Multiset.bind_map]
      rw [ih pre_T (pre_F ++ [x])]
      refine Multiset.bind_congr fun α _ => ?_
      rw [List.append_assoc, List.singleton_append]
      rfl

/-- `forestPairSum [] [] [] [] = {[]}`. -/
private theorem forestPairSum_nil_F_nil_pre_nil_Ts :
    forestPairSum ([] : List (Planar α)) [] [] [] =
      ({[]} : Multiset (List (Planar α))) := by
  unfold forestPairSum; rfl

/-- `forestPairSum []` with a non-empty `pre_T` is `0`. -/
private theorem forestPairSum_nil_F_zero_of_pre_T_cons
    (a : Planar α) (pre_T pre_F : List (Planar α)) :
    forestPairSum ([] : List (Planar α)) (a :: pre_T) pre_F [] = 0 := by
  unfold forestPairSum; rfl

/-- `forestPairSum []` with empty `pre_T` but non-empty `pre_F` is `0`. -/
private theorem forestPairSum_nil_F_zero_of_pre_F_cons
    (a : Planar α) (pre_F : List (Planar α)) :
    forestPairSum ([] : List (Planar α)) [] (a :: pre_F) [] = 0 := by
  unfold forestPairSum; rfl

/-- For the empty host `F = []`, if either accumulator is non-empty,
    `forestPairSum [] pre_T pre_F Ts = 0` regardless of `Ts`. -/
private theorem forestPairSum_nil_F_eq_zero
    (pre_T pre_F : List (Planar α)) (Ts : List (Planar α))
    (h : pre_T ≠ [] ∨ pre_F ≠ []) :
    forestPairSum ([] : List (Planar α)) pre_T pre_F Ts = 0 := by
  induction Ts generalizing pre_T pre_F with
  | nil =>
    rcases h with h | h
    · rcases pre_T with _ | ⟨a, pre_T_rest⟩
      · exact absurd rfl h
      · exact forestPairSum_nil_F_zero_of_pre_T_cons a pre_T_rest pre_F
    · rcases pre_F with _ | ⟨a, pre_F_rest⟩
      · exact absurd rfl h
      · rcases pre_T with _ | ⟨b, pre_T_rest⟩
        · exact forestPairSum_nil_F_zero_of_pre_F_cons a pre_F_rest
        · exact forestPairSum_nil_F_zero_of_pre_T_cons b pre_T_rest (a :: pre_F_rest)
  | cons x rest ih =>
    rw [forestPairSum_cons_remaining]
    refine (Multiset.bind_congr (g := fun _ => (0 : Multiset _)) ?_).trans
      (Multiset.bind_zero _)
    intro b _
    cases b
    · rw [if_neg (by decide : (false : Bool) ≠ true)]
      refine ih pre_T (pre_F ++ [x]) ?_
      right
      intro h_eq
      cases pre_F <;> simp at h_eq
    · rw [if_pos rfl]
      refine ih (pre_T ++ [x]) pre_F ?_
      left
      intro h_eq
      cases pre_T <;> simp at h_eq

/-- Bridge: `forestPairSum F [] [] Ts = insertionForest F Ts`. -/
private theorem forestPairSum_eq_insertionForest (F : List (Planar α))
    (Ts : List (Planar α)) :
    forestPairSum F [] [] Ts = insertionForest F Ts := by
  cases F with
  | nil =>
    cases Ts with
    | nil =>
      rw [forestPairSum_nil_F_nil_pre_nil_Ts, insertionForest_nil_nil]
    | cons T_g Ts_inner =>
      rw [insertionForest_empty_host_nonempty_guests, forestPairSum_cons_remaining]
      refine (Multiset.bind_congr (g := fun _ => (0 : Multiset _)) ?_).trans
        (Multiset.bind_zero _)
      intro b _
      cases b
      · rw [if_neg (by decide : (false : Bool) ≠ true)]
        exact forestPairSum_nil_F_eq_zero [] [T_g] Ts_inner (Or.inr (by simp))
      · rw [if_pos rfl]
        exact forestPairSum_nil_F_eq_zero [T_g] [] Ts_inner (Or.inl (by simp))
  | cons T F_tail =>
    cases Ts with
    | nil =>
      rw [forestPairSum_cons_F_nil_remaining, insertionForest_cons_host_nil_guests,
          insertionForest_nil_guests]
      have h_ins_T : insertion T [] = ({T} : Multiset (Planar α)) := by
        rw [insertion_def]
        simp [listChoices_zero, multiGraft_nil]
      rw [h_ins_T, Multiset.singleton_bind, Multiset.map_singleton]
    | cons T_g Ts_inner =>
      rw [forestPairSum_assignment_rewrite, insertionForest_cons_cons]
      refine Multiset.bind_congr fun α _ => ?_
      simp only [List.nil_append]
      rw [forestPairSum_cons_F_nil_remaining]

/-- Pair-list Perm invariance of the accumulators, in the `T :: F_tail` case.
    Takes `ih_F` (forest-Perm invariance on `F_tail`) as an explicit
    argument to cut circularity with the outer induction on `F`. -/
private theorem forestPairSum_pre_perm_mk
    (T : Planar α) (F_tail : List (Planar α))
    (ih_F : ∀ {Ts Ts' : List (Planar α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    {pre_T pre_T' pre_F pre_F' : List (Planar α)}
    (hT : pre_T.Perm pre_T') (hF : pre_F.Perm pre_F')
    (Ts : List (Planar α)) :
    (forestPairSum (T :: F_tail) pre_T pre_F Ts).map (List.map Nonplanar.mk) =
    (forestPairSum (T :: F_tail) pre_T' pre_F' Ts).map (List.map Nonplanar.mk) := by
  induction Ts generalizing pre_T pre_T' pre_F pre_F' with
  | nil =>
    rw [forestPairSum_cons_F_nil_remaining, forestPairSum_cons_F_nil_remaining,
        Multiset.map_bind, Multiset.map_bind]
    -- LHS = (insertion T pre_T).bind fun T' =>
    --         ((insertionForest F_tail pre_F).map (fun F' => T' :: F')).map (List.map mk)
    -- = (insertion T pre_T).bind fun T' =>
    --     (insertionForest F_tail pre_F).map (fun F' => mk T' :: F'.map mk)
    -- Refactor: factor mk T' out, then use insertion_perm_guests + ih_F
    rw [show (fun T' : Planar α =>
              ((insertionForest F_tail pre_F).map fun F' => T' :: F').map (List.map Nonplanar.mk)) =
            (fun T' : Planar α =>
              ((insertionForest F_tail pre_F).map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L))
            from by
          funext T'
          rw [Multiset.map_map, Multiset.map_map]
          rfl]
    rw [show (fun T' : Planar α =>
              ((insertionForest F_tail pre_F').map fun F' => T' :: F').map (List.map Nonplanar.mk)) =
            (fun T' : Planar α =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L))
            from by
          funext T'
          rw [Multiset.map_map, Multiset.map_map]
          rfl]
    -- Apply ih_F: (insertionForest F_tail pre_F).map (List.map mk) = (insertionForest F_tail pre_F').map (List.map mk)
    rw [ih_F hF]
    -- Now both inner forests are on pre_F'. Pull T' through mk via Multiset.bind_map.
    -- (insertion T pre_T).bind (fun T' => ((insertionForest F_tail pre_F').map (List.map mk)).map (fun L => mk T' :: L))
    -- = ((insertion T pre_T).map mk).bind (fun mk_T' => ((insertionForest F_tail pre_F').map (List.map mk)).map (fun L => mk_T' :: L))
    -- via Multiset.bind_map reversed
    rw [show (insertion T pre_T).bind (fun T' : Planar α =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L)) =
            ((insertion T pre_T).map Nonplanar.mk).bind (fun mk_T' =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => mk_T' :: L))
            from by rw [Multiset.bind_map]]
    rw [show (insertion T pre_T').bind (fun T' : Planar α =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L)) =
            ((insertion T pre_T').map Nonplanar.mk).bind (fun mk_T' =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => mk_T' :: L))
            from by rw [Multiset.bind_map]]
    -- Apply insertion_perm_guests on (insertion T pre_T).map mk = (insertion T pre_T').map mk
    rw [insertion_perm_guests T hT]
  | cons x rest ih =>
    rw [forestPairSum_cons_remaining, forestPairSum_cons_remaining,
        Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun b _ => ?_
    cases b
    · rw [if_neg (by decide : (false : Bool) ≠ true), if_neg (by decide : (false : Bool) ≠ true)]
      exact ih hT (hF.append_right [x])
    · rw [if_pos rfl, if_pos rfl]
      exact ih (hT.append_right [x]) hF

/-- Two-step unfolding: `forestPairSum F pre_T pre_F (x :: y :: rest)`
    as a nested bind over `[true, false] × [true, false]`. -/
private theorem forestPairSum_cons_cons_unfold (F : List (Planar α))
    (pre_T pre_F : List (Planar α)) (x y : Planar α) (rest : List (Planar α)) :
    forestPairSum F pre_T pre_F (x :: y :: rest) =
      (Multiset.ofList [true, false]).bind fun b_x =>
        (Multiset.ofList [true, false]).bind fun b_y =>
          if b_x then
            (if b_y then forestPairSum F ((pre_T ++ [x]) ++ [y]) pre_F rest
                   else forestPairSum F (pre_T ++ [x]) (pre_F ++ [y]) rest)
          else
            (if b_y then forestPairSum F (pre_T ++ [y]) (pre_F ++ [x]) rest
                   else forestPairSum F pre_T ((pre_F ++ [x]) ++ [y]) rest) := by
  rw [forestPairSum_cons_remaining]
  refine Multiset.bind_congr fun b_x _ => ?_
  cases b_x
  · change forestPairSum F pre_T (pre_F ++ [x]) (y :: rest) =
        (Multiset.ofList [true, false]).bind fun b_y =>
          if b_y then forestPairSum F (pre_T ++ [y]) (pre_F ++ [x]) rest
                 else forestPairSum F pre_T ((pre_F ++ [x]) ++ [y]) rest
    rw [forestPairSum_cons_remaining]
  · change forestPairSum F (pre_T ++ [x]) pre_F (y :: rest) =
        (Multiset.ofList [true, false]).bind fun b_y =>
          if b_y then forestPairSum F ((pre_T ++ [x]) ++ [y]) pre_F rest
                 else forestPairSum F (pre_T ++ [x]) (pre_F ++ [y]) rest
    rw [forestPairSum_cons_remaining]

/-- Adjacent swap of remaining guests preserves `forestPairSum` (mk-mapped). -/
private theorem forestPairSum_swap_mk
    (T : Planar α) (F_tail : List (Planar α))
    (ih_F : ∀ {Ts Ts' : List (Planar α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    (pre_T pre_F : List (Planar α)) (a b : Planar α) (rest : List (Planar α)) :
    (forestPairSum (T :: F_tail) pre_T pre_F (a :: b :: rest)).map (List.map Nonplanar.mk) =
    (forestPairSum (T :: F_tail) pre_T pre_F (b :: a :: rest)).map (List.map Nonplanar.mk) := by
  rw [forestPairSum_cons_cons_unfold, forestPairSum_cons_cons_unfold]
  -- Push .map mk through both nested binds on both sides
  rw [Multiset.map_bind]
  conv_lhs =>
    rhs; ext _; rw [Multiset.map_bind]
  rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext _; rw [Multiset.map_bind]
  -- Now LHS = (ofList [t,f]).bind fun b_a => (ofList [t,f]).bind fun b_b => (... .map mk)
  --     RHS = (ofList [t,f]).bind fun b_b => (ofList [t,f]).bind fun b_a => (... .map mk)
  -- Commute LHS binds via bind_bind
  rw [Multiset.bind_bind]
  -- Now both sides have outer bind on "b first guest of original RHS = second of original LHS"
  refine Multiset.bind_congr fun b₁ _ => ?_
  refine Multiset.bind_congr fun b₂ _ => ?_
  -- Case-split on (b₁, b₂)
  cases b₁
  · cases b₂
    · -- F, F: pre_F PERM
      change (forestPairSum (T :: F_tail) pre_T ((pre_F ++ [a]) ++ [b]) rest).map
                (List.map Nonplanar.mk) =
              (forestPairSum (T :: F_tail) pre_T ((pre_F ++ [b]) ++ [a]) rest).map
                (List.map Nonplanar.mk)
      exact forestPairSum_pre_perm_mk T F_tail ih_F
        (List.Perm.refl pre_T)
        (by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left pre_F (List.Perm.swap b a []))
        rest
    · -- F, T: equal
      rfl
  · cases b₂
    · -- T, F: equal
      rfl
    · -- T, T: pre_T PERM
      change (forestPairSum (T :: F_tail) ((pre_T ++ [a]) ++ [b]) pre_F rest).map
                (List.map Nonplanar.mk) =
              (forestPairSum (T :: F_tail) ((pre_T ++ [b]) ++ [a]) pre_F rest).map
                (List.map Nonplanar.mk)
      exact forestPairSum_pre_perm_mk T F_tail ih_F
        (by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left pre_T (List.Perm.swap b a []))
        (List.Perm.refl pre_F)
        rest

/-- `List.Perm` of remaining guests preserves `forestPairSum` (mk-mapped). -/
private theorem forestPairSum_perm_remaining_mk
    (T : Planar α) (F_tail : List (Planar α))
    (ih_F : ∀ {Ts Ts' : List (Planar α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    (pre_T pre_F : List (Planar α))
    {Ts Ts' : List (Planar α)} (h : Ts.Perm Ts') :
    (forestPairSum (T :: F_tail) pre_T pre_F Ts).map (List.map Nonplanar.mk) =
    (forestPairSum (T :: F_tail) pre_T pre_F Ts').map (List.map Nonplanar.mk) := by
  induction h generalizing pre_T pre_F with
  | nil => rfl
  | @cons x rest rest' _ ih =>
    rw [forestPairSum_cons_remaining, forestPairSum_cons_remaining,
        Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun b _ => ?_
    cases b
    · rw [if_neg (by decide : (false : Bool) ≠ true),
          if_neg (by decide : (false : Bool) ≠ true)]
      exact ih pre_T (pre_F ++ [x])
    · rw [if_pos rfl, if_pos rfl]
      exact ih (pre_T ++ [x]) pre_F
  | @swap a b l => exact forestPairSum_swap_mk T F_tail ih_F pre_T pre_F b a l
  | @trans Ts₁ Ts₂ Ts₃ _ _ ih₁ ih₂ => exact (ih₁ pre_T pre_F).trans (ih₂ pre_T pre_F)

/-- Forest guest invariance: `List.Perm` of guests lifts to
    `mk`-equality of `insertionForest`. -/
theorem insertionForest_perm_guests
    (F : List (Planar α)) {Ts Ts' : List (Planar α)} (h : Ts.Perm Ts') :
    (insertionForest F Ts).map (List.map Nonplanar.mk) =
      (insertionForest F Ts').map (List.map Nonplanar.mk) := by
  induction F generalizing Ts Ts' with
  | nil =>
    cases hTs : Ts with
    | nil =>
      have hTs' : Ts' = [] := by
        have hlen := h.length_eq
        rw [hTs] at hlen
        exact List.length_eq_zero_iff.mp hlen.symm
      rw [hTs']
    | cons _ _ =>
      cases hTs' : Ts' with
      | nil =>
        exfalso
        have hlen := h.length_eq
        rw [hTs, hTs'] at hlen
        simp at hlen
      | cons _ _ =>
        simp [insertionForest_empty_host_nonempty_guests]
  | cons T F_tail ih_F =>
    rw [show insertionForest (T :: F_tail) Ts = forestPairSum (T :: F_tail) [] [] Ts from
          (forestPairSum_eq_insertionForest _ _).symm]
    rw [show insertionForest (T :: F_tail) Ts' = forestPairSum (T :: F_tail) [] [] Ts' from
          (forestPairSum_eq_insertionForest _ _).symm]
    exact forestPairSum_perm_remaining_mk T F_tail ih_F [] [] h

/-! ### §8: Singleton-host insertion = single-tree insertion lifted to singleton lists

`insertionForest [T] gs = (insertion T gs).map (fun T' => [T'])` — when the
host has exactly one tree, the multi-graft is just the single-tree multi-graft
with each output wrapped in a singleton list. Used downstream to handle
`hostTripleSum T [T'] F` patterns at the singleton-F_A level. -/

/-- `insertion T []` is the singleton `{T}` — multi-graft of no guests is
    the identity. Public version of the InsertionAddHost.lean private helper. -/
theorem insertion_nil_guests (T : Planar α) :
    insertion T ([] : List (Planar α)) = ({T} : Multiset (Planar α)) := by
  rw [insertion_def]
  simp only [List.length_nil, listChoices_zero, List.zip_nil_right,
             multiGraft_nil, List.map_cons, List.map_nil,
             Multiset.coe_singleton]

/-- `forestPairSum [T] pre (a :: pre_F_rest) gs = 0`. With a non-empty `pre_F`
    accumulator, the inner `insertionForest [] (a :: pre_F_rest ++ ...)` is 0,
    and the recursion preserves the non-empty invariant. -/
private theorem forestPairSum_singleton_host_pre_F_nonempty (T : Planar α) (a : Planar α) :
    ∀ (pre pre_F_rest gs : List (Planar α)),
    forestPairSum [T] pre (a :: pre_F_rest) gs = 0 := by
  intro pre pre_F_rest gs
  induction gs generalizing pre pre_F_rest with
  | nil =>
    rw [forestPairSum_cons_F_nil_remaining]
    rw [insertionForest_empty_host_nonempty_guests]
    -- Goal: (insertion T pre).bind (fun T' => (0 : Multiset _).map (fun F' => T' :: F')) = 0
    rw [show (fun T' : Planar α =>
              ((0 : Multiset (List (Planar α))).map (fun F' => T' :: F'))) =
            (fun (_ : Planar α) => (0 : Multiset (List (Planar α)))) from by
          funext T'
          rw [Multiset.map_zero]]
    exact Multiset.bind_zero _
  | cons g rest ih =>
    rw [forestPairSum_cons_remaining]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [ih (pre ++ [g]) pre_F_rest]
    rw [show (a :: pre_F_rest) ++ [g] = a :: (pre_F_rest ++ [g]) from rfl]
    rw [ih pre (pre_F_rest ++ [g])]
    rfl

/-- `forestPairSum [T] pre [] gs = (insertion T (pre ++ gs)).map (fun T' => [T'])`.
    The single-host `[T]` only allows one bucket assignment (all guests to T);
    the empty `pre_F` accumulator stays empty. Helper for `insertionForest_singleton`.
-/
private theorem forestPairSum_singleton_host_no_pre_F (T : Planar α) :
    ∀ (pre gs : List (Planar α)),
    forestPairSum [T] pre [] gs = (insertion T (pre ++ gs)).map (fun T' => [T']) := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    rw [forestPairSum_cons_F_nil_remaining, insertionForest_nil_nil, List.append_nil]
    -- Goal: (insertion T pre).bind (fun T' => ({[]}).map (fun F' => T' :: F')) =
    --       (insertion T pre).map (fun T' => [T'])
    rw [show (fun T' : Planar α =>
              ({([] : List (Planar α))} : Multiset (List (Planar α))).map (fun F' => T' :: F')) =
            (fun T' : Planar α => ({[T']} : Multiset (List (Planar α)))) from by
          funext T'
          rw [Multiset.map_singleton]]
    exact Multiset.bind_singleton (s := insertion T pre) (fun T' => [T'])
  | cons g rest ih =>
    rw [forestPairSum_cons_remaining]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [ih (pre ++ [g])]
    rw [show ([] : List (Planar α)) ++ [g] = [g] from rfl]
    rw [forestPairSum_singleton_host_pre_F_nonempty T g pre [] rest]
    rw [add_zero]
    -- (pre ++ [g]) ++ rest = pre ++ (g :: rest)
    rw [List.append_assoc]
    rfl

/-- **Singleton-host insertion**: when the host has exactly one tree,
    `insertionForest` reduces to single-tree `insertion` followed by singleton
    lift. This lets us match `hostTripleSum T [T_other] F` patterns by
    converting `(insertionForest [T_other] pre).bind` to `(insertion T_other pre).bind`
    (via `Multiset.bind_map`). -/
theorem insertionForest_singleton (T : Planar α) (gs : List (Planar α)) :
    insertionForest [T] gs = (insertion T gs).map (fun T' => [T']) := by
  rw [show insertionForest [T] gs = forestPairSum [T] [] [] gs from
        (forestPairSum_eq_insertionForest _ _).symm]
  rw [forestPairSum_singleton_host_no_pre_F T [] gs, List.nil_append]

end Pathed

end Planar

end RootedTree
