/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Graft
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.Data.Multiset.Bind

set_option autoImplicit false

/-!
# Foissy 2021 Theorem 5.1 multi-tree insertion (path-based)
[foissy-typed-decorated-rooted-trees-2018]
[foissy-introduction-hopf-algebras-trees]

The Foissy 2021 Theorem 5.1 multi-tree multi-vertex insertion operator.
Defined as a sum over functions `Ts → V(T)` of `multiGraft`, taken as
a `Multiset` to make the sum-over-choices commutative.

Sibling to `Graft.lean` (path-based multi-graft primitive). Lives under
namespace `RoseTree.Pathed`.

## File scope

- §1: `listChoices` — choice-list enumeration (representation-independent).
- §2: `insertion` — Foissy 2021 Theorem 5.1, single-tree host.
- §3: `insertionForest` — forest host + identity/nil lemmas.
- §4: Pair-list `Perm`-invariance for `multiGraft`.
- §5: Guest-list invariance for `insertion` (`insertion_perm_guests`).
- §5.5: Validity discharge for `listChoices`-derived pair lists.
- §6: Host invariance via the `swapPathAt` path-relabel bijection.
- §7: Forest invariance (`insertionForest_perm_host`,
  `insertionForest_perm_guests`).
- §8: Singleton-host insertion.

## Status

`[UPSTREAM]` candidate. **Sorry-free**.
-/

namespace RoseTree

namespace Pathed

open RootedTree

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
def insertion (T : RoseTree α) (Ts : List (RoseTree α)) : Multiset (RoseTree α) :=
  Multiset.ofList <| (listChoices (vertices T) Ts.length).map
    fun choice => multiGraft T (choice.zip Ts)

theorem insertion_def (T : RoseTree α) (Ts : List (RoseTree α)) :
    insertion T Ts =
      Multiset.ofList ((listChoices (vertices T) Ts.length).map
        fun choice => multiGraft T (choice.zip Ts)) := rfl

/-! ## §3: `insertionForest` — forest host -/

/-- Multi-graft into a host forest. Disjoint pattern cases for clean
    auto-generated equation lemmas. -/
def insertionForest : List (RoseTree α) → List (RoseTree α) →
    Multiset (List (RoseTree α))
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
    insertionForest ([] : List (RoseTree α)) [] =
      ({[]} : Multiset (List (RoseTree α))) := by
  unfold insertionForest; rfl

@[simp] theorem insertionForest_empty_host_nonempty_guests
    (T_g : RoseTree α) (Ts : List (RoseTree α)) :
    insertionForest ([] : List (RoseTree α)) (T_g :: Ts) = 0 := by
  unfold insertionForest; rfl

@[simp] theorem insertionForest_cons_host_nil_guests
    (T : RoseTree α) (F : List (RoseTree α)) :
    insertionForest (T :: F) ([] : List (RoseTree α)) =
      ({T :: F} : Multiset (List (RoseTree α))) := by
  unfold insertionForest; rfl

theorem insertionForest_nil_guests (F : List (RoseTree α)) :
    insertionForest F [] = ({F} : Multiset (List (RoseTree α))) := by
  cases F
  · exact insertionForest_nil_nil
  · exact insertionForest_cons_host_nil_guests _ _

theorem insertionForest_cons_cons
    (T : RoseTree α) (F : List (RoseTree α))
    (T_g : RoseTree α) (Ts : List (RoseTree α)) :
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

`multiGraft T pairs` is `Perm`-invariant under permutation of the
pair list: grafts at distinct paths commute, and grafts at the same
path are root-list permutations (lift via `Perm.node_of_perm`).

Path-based reformulation of the legacy `multiGraft_perm_pair` /
`multiGraftList_perm_pair`. -/

mutual
/-- `Perm` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from a `List.Perm` between `pairs` and `pairs'`. Mutual
    recursion on `T` with the children-list aux. -/
private theorem multiGraft_perm_pair : ∀ (T : RoseTree α)
    {pairs pairs' : List (Path × RoseTree α)},
    pairs.Perm pairs' →
    Perm (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    exact (Perm.node_of_perm
            ((h.filterMap rootPrependFilter).append_right _)).trans
          (Perm.node_of_forall₂
            (List.rel_append
              (List.forall₂_same.mpr fun _ _ => Perm.refl _)
              (multiGraftChildren_perm_pair cs h)))
/-- List-level companion to `multiGraft_perm_pair`: pair-list `Perm`
    lifts to `Forall₂ Perm` on the children list output of
    `multiGraftChildren`. -/
private theorem multiGraftChildren_perm_pair : ∀ (cs : List (RoseTree α))
    {pairs pairs' : List (Path × RoseTree α)},
    pairs.Perm pairs' →
    List.Forall₂ Perm
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · exact multiGraft_perm_pair c (h.filterMap _)
    · exact multiGraftChildren_perm_pair cs (h.filterMap _)
end

/-! ### Forall₂-version of `multiGraft_perm_pair`

For `insertion_perm_guests` we need: when `Ts ~ᶠ Ts'` (Forall₂
Perm) and we zip with the same choice, the resulting pair lists
satisfy a Forall₂ relation (same fst, Perm snd). Then this lifts
to `multiGraft T pairs ~ multiGraft T pairs'` (`Perm`).

Path-based version of the legacy `multiGraft_perm_pair_Forall₂`. -/

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
/-- `Perm` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from pair-`Forall₂` (same fst, `Perm` snds). -/
private theorem multiGraft_perm_pair_Forall₂ : ∀ (T : RoseTree α)
    {pairs pairs' : List (Path × RoseTree α)},
    List.Forall₂ (fun p p' : Path × RoseTree α =>
        p.fst = p'.fst ∧ Perm p.snd p'.snd) pairs pairs' →
    Perm (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    apply Perm.node_of_forall₂
    apply List.rel_append
    · -- root-prepended children: Forall₂ Perm after filterMap
      refine List.rel_filterMap (P := Perm) ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil       => exact Option.Rel.some hsnd
      | cons _ _  => exact Option.Rel.none
    · -- children: Forall₂ Perm on multiGraftChildren output
      exact multiGraftChildren_perm_pair_Forall₂ cs h

/-- List-level companion. -/
private theorem multiGraftChildren_perm_pair_Forall₂ :
    ∀ (cs : List (RoseTree α))
    {pairs pairs' : List (Path × RoseTree α)},
    List.Forall₂ (fun p p' : Path × RoseTree α =>
        p.fst = p'.fst ∧ Perm p.snd p'.snd) pairs pairs' →
    List.Forall₂ Perm
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · apply multiGraft_perm_pair_Forall₂
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
    · apply multiGraftChildren_perm_pair_Forall₂
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
machinery. The pair type changes from `Vertex t × RoseTree α` to
`Path × RoseTree α`. -/

/-- Multi-graft aggregator with an explicit pair pre (path-based). -/
private def pairSum (t : RoseTree α)
    (pre : List (Path × RoseTree α))
    (Ts : List (RoseTree α)) : Multiset (Nonplanar α) :=
  Multiset.ofList ((listChoices (vertices t) Ts.length).map
    fun c => Nonplanar.mk (multiGraft t (pre ++ c.zip Ts)))

private theorem pairSum_cons (t : RoseTree α)
    (pre : List (Path × RoseTree α))
    (x : RoseTree α) (rest : List (RoseTree α)) :
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
private theorem pairSum_pre_perm (t : RoseTree α)
    {pre pre' : List (Path × RoseTree α)}
    (h : pre.Perm pre') (Ts : List (RoseTree α)) :
    pairSum t pre Ts = pairSum t pre' Ts := by
  unfold pairSum
  congr 1
  apply List.map_congr_left
  intro c _
  apply Nonplanar.mk_eq_mk_iff.mpr
  exact multiGraft_perm_pair t (h.append_right _)

/-- Two unfoldings of `pairSum_cons` packed into a normal form for the
    swap proof. -/
private theorem pairSum_cons_cons (t : RoseTree α)
    (pre : List (Path × RoseTree α))
    (x y : RoseTree α) (rest : List (RoseTree α)) :
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
private theorem pairSum_swap (t : RoseTree α)
    (pre : List (Path × RoseTree α))
    (a b : RoseTree α) (l : List (RoseTree α)) :
    pairSum t pre (b :: a :: l) = pairSum t pre (a :: b :: l) := by
  rw [pairSum_cons_cons, pairSum_cons_cons]
  rw [Multiset.bind_bind]
  refine Multiset.bind_congr fun _ _ => Multiset.bind_congr fun _ _ => ?_
  exact pairSum_pre_perm t (List.Perm.append_left pre (List.Perm.swap _ _ _)) l

/-- `pairSum t pre Ts` is invariant under `List.Perm` of `Ts`. -/
private theorem pairSum_perm_guests (t : RoseTree α)
    (pre : List (Path × RoseTree α))
    {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
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
private theorem insertion_perm_guests (t : RoseTree α)
    {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t Ts').map Nonplanar.mk := by
  have := pairSum_perm_guests t [] h
  unfold pairSum at this
  simpa [insertion_def, Multiset.map_coe, List.map_map, Function.comp_def] using this

/-- Guest-list `Forall₂ Perm` lifts to `insertion mk`-equality. -/
theorem insertion_forall₂_perm_guests (t : RoseTree α)
    {Ts Ts' : List (RoseTree α)} (h : List.Forall₂ Perm Ts Ts') :
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
  -- via List.Forall₂ for the pair (fst eq, snd perm)
  exact multiGraft_perm_pair_Forall₂ t (zip_pair_Forall₂ choice h)

/-! ## §5.5: Validity discharge for `listChoices`-derived pair lists

Every element of a `listChoices`-enumerated choice is a member of the
alphabet (`mem_of_mem_listChoices`), so a pair list of the canonical
shape `choice.zip Ts` automatically satisfies the validity hypothesis
that graft operations require (`forall_zip_isValidPath_of_listChoices`).
These utilities are consumed by `InsertionNodeDecomp` and
`InsertionCompose`. -/

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
    `choice ∈ listChoices (vertices T) Ts.length`. Discharges the validity
    hypothesis of the graft operations for `listChoices`-derived pair lists. -/
theorem forall_zip_isValidPath_of_listChoices
    (T : RoseTree α) (Ts : List (RoseTree α))
    (choice : List Path)
    (h_choice : choice ∈ listChoices (vertices T) Ts.length)
    (pair : Path × RoseTree α) (h_pair : pair ∈ choice.zip Ts) :
    IsValidPath pair.fst T := by
  have h_fst_mem : pair.fst ∈ choice := (List.of_mem_zip h_pair).1
  exact forall_isValidPath T (mem_of_mem_listChoices (vertices T) Ts.length
    choice h_choice pair.fst h_fst_mem)

/-! ## §6: Host invariance via path-swap bijection

`insertion T Ts` is `mk`-invariant under `Perm` of the host: the
original blocker for the path-based refactor.

Strategy:
1. `swapPathAt n` — swap the first index `n ↔ n+1` in a path.
2. `vertices_swap_perm` — applying `swapPathAt pre.length` to vertices of
   `node a (pre ++ l :: r :: post)` is a `List.Perm` of vertices of
   `node a (pre ++ r :: l :: post)`. Reduces to a `List.Perm` of two
   appendable middle blocks, via `verticesAux_append` + a
   `List.perm_append_comm`.
3. `multiGraft_swap_perm` — the multiGraft results differ only by
   the swap of l/r in the root children list.
4. `vertices_recurse_perm` / `multiGraft_recurse_perm` — the child-recursion
   building block, lifting an inner bijection via `pathLiftRecurse`.
5. `hasPathBij_of_perm` (with its `PermList` companion) assembles these
   building blocks over the mutual `Perm`/`PermList` structure;
   `insertion_eq_of_pathBij` turns the bijection into `mk`-equality. -/

/-- Swap the first index `n ↔ n+1` of a path. Acts as identity on paths
    starting outside `{n, n+1}` and on the root path `[]`. -/
private def swapPathAt (n : ℕ) : Path → Path
  | []        => []
  | i :: rest =>
      if i = n then (n + 1) :: rest
      else if i = n + 1 then n :: rest
      else i :: rest

@[simp] private theorem swapPathAt_nil (n : ℕ) : swapPathAt n [] = [] := rfl

private theorem swapPathAt_cons_eq (n : ℕ) (rest : Path) :
    swapPathAt n (n :: rest) = (n + 1) :: rest := by
  simp [swapPathAt]

private theorem swapPathAt_cons_eq_succ (n : ℕ) (rest : Path) :
    swapPathAt n ((n + 1) :: rest) = n :: rest := by
  simp [swapPathAt]

private theorem swapPathAt_cons_of_ne (n i : ℕ) (rest : Path)
    (h1 : i ≠ n) (h2 : i ≠ n + 1) :
    swapPathAt n (i :: rest) = i :: rest := by
  simp [swapPathAt, h1, h2]

/-- For paths produced by `verticesAux start cs` with all indices
    bounded below `n`, `swapPathAt n` acts as the identity. -/
private theorem map_swapPathAt_verticesAux_below
    (n start : ℕ) (cs : List (RoseTree α)) (h : start + cs.length ≤ n) :
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
    (n start : ℕ) (cs : List (RoseTree α)) (h : n + 1 < start) :
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
private theorem vertices_swap_perm (a : α) (pre : List (RoseTree α))
    (l r : RoseTree α) (post : List (RoseTree α)) :
    ((vertices (RoseTree.node a (pre ++ l :: r :: post))).map
        (swapPathAt pre.length)).Perm
      (vertices (RoseTree.node a (pre ++ r :: l :: post))) := by
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

/-! ### §6.2 substrate: pair-relabel + perm prefix-cons-lift -/

/-- The path-relabel function for swapAtRoot. -/
private def pathRelabelSwap (n : ℕ) : Path × RoseTree α → Path × RoseTree α :=
  Prod.map (swapPathAt n) id

@[simp] private theorem pathRelabelSwap_fst (n : ℕ) (p : Path × RoseTree α) :
    (pathRelabelSwap n p).fst = swapPathAt n p.fst := rfl

@[simp] private theorem pathRelabelSwap_snd (n : ℕ) (p : Path × RoseTree α) :
    (pathRelabelSwap n p).snd = p.snd := rfl

/-- Path bijection for a single-child recursion: lift an inner path
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
    (n start : ℕ) (f : Path → Path) (cs : List (RoseTree α))
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
    (n start : ℕ) (f : Path → Path) (cs : List (RoseTree α))
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

/-- Vertices Perm under a single-child recursion: given a path bijection on
    the changed subtree, lift to a Perm on the bigger tree's vertices. -/
private theorem vertices_recurse_perm (a : α) (pre : List (RoseTree α))
    (old new : RoseTree α) (post : List (RoseTree α)) (f : Path → Path)
    (hf : ((vertices old).map f).Perm (vertices new)) :
    ((vertices (RoseTree.node a (pre ++ old :: post))).map
        (pathLiftRecurse pre.length f)).Perm
      (vertices (RoseTree.node a (pre ++ new :: post))) := by
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

/-- Helper: `Perm` of two trees with a common children prefix.
    Lifts `(node a cs) ~ (node a ds)` to `(node a (pre ++ cs)) ~ (node a (pre ++ ds))`
    by iterated `Perm.cons_child`. -/
private theorem perm_append_left_node {a : α} (pre : List (RoseTree α))
    {cs ds : List (RoseTree α)}
    (h : Perm (.node a cs) (.node a ds)) :
    Perm (.node a (pre ++ cs)) (.node a (pre ++ ds)) := by
  induction pre with
  | nil => exact h
  | cons p pre' ih => exact Perm.cons_child p ih

/-- `multiGraft` is `Perm`-invariant under a single-child recursion:
    if the inner subtree change `old → new` admits a path-bijection `f`
    that turns `multiGraft old` into `multiGraft new ∘ relabel-via-f`, then
    the same holds for the host with prefix `pre` and suffix `post`, using
    `pathLiftRecurse pre.length f`. -/
private theorem multiGraft_recurse_perm (a : α)
    {old new : RoseTree α} (f : Path → Path)
    (hf : ∀ sub_pairs, Perm (multiGraft old sub_pairs)
                                    (multiGraft new (sub_pairs.map (Prod.map f id)))) :
    ∀ (pre : List (RoseTree α)) (post : List (RoseTree α))
      (pairs : List (Path × RoseTree α)),
    Perm
      (multiGraft (RoseTree.node a (pre ++ old :: post)) pairs)
      (multiGraft (RoseTree.node a (pre ++ new :: post))
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
    exact perm_append_left_node _
      (Perm.congr_child [] _ h_old)
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
          | zero => simp
          | succ j =>
            have hjne : j ≠ pre'.length := by intro heq; apply h1; omega
            simp [pathLiftRecurse_cons_of_ne pre'.length j f rest hjne]
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
          | zero => simp
          | succ j => simp [rootPrependFilter]
    rw [h_RP_lhs, List.nil_append] at h_ih
    rw [h_RP_rhs, List.nil_append] at h_ih
    rw [← h_RP, ← h_cP]
    -- Goal: node a (RP ++ multiGraft c cP :: mGC (pre' ++ old :: post) csP) ~PE~
    --        node a (RP ++ multiGraft c cP :: mGC (pre' ++ new :: post) csP_relabeled)
    exact perm_append_left_node _ (Perm.cons_child _ h_ih)

/-- `multiGraft` is `Perm`-invariant under swap of two adjacent
    root children, with pairs relabeled via `swapPathAt`. The proof
    decomposes both sides into matching children lists (up to a single
    swap of the two adjacent root children).

    Sub-lemmas for the filter equalities are proved inline as `have`
    statements to ensure the inline-match expressions unify with the
    matcher generated by `multiGraft_node`. -/
private theorem multiGraft_swap_perm
    (a : α) (pre : List (RoseTree α)) (l r : RoseTree α)
    (post : List (RoseTree α)) (pairs : List (Path × RoseTree α)) :
    Perm
      (multiGraft (RoseTree.node a (pre ++ l :: r :: post)) pairs)
      (multiGraft (RoseTree.node a (pre ++ r :: l :: post))
                  (pairs.map (pathRelabelSwap pre.length))) := by
  -- The cleanest path: induct on pre, peeling off one child at a time.
  -- Base case (pre = []) does the actual swap; inductive case lifts via
  -- Perm.cons_child.
  induction pre generalizing pairs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [multiGraft_node, multiGraft_node]
    -- Build sub-perms and combine via Perm.node_of_perm.
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
    exact Perm.node_of_perm (List.Perm.append h_RP_perm h_mGC_perm)
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
    -- IH: Perm (multiGraft (node a (pre' ++ l :: r :: post)) X_pre)
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
    -- Now h_ih has form: Perm (node a (mGC ... X_pre)) (node a (mGC ... X_pre_relabeled))
    -- Use h_X_pre to rewrite X_pre_relabeled inside.
    rw [← h_X_pre] at h_ih
    -- Lift IH through cons (multiGraft c X_l ::) and append_left (RP ++).
    have h_after_cons : Perm
        (RoseTree.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ l :: r :: post)
                           (pairs.filterMap tailChildFilter)))
        (RoseTree.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ r :: l :: post)
                           ((pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                             tailChildFilter))) :=
      Perm.cons_child _ h_ih
    have h_after_append := perm_append_left_node
                            (pairs.filterMap rootPrependFilter) h_after_cons
    -- Goal's RHS uses relabeled forms; rewrite back to unrelabeled to match
    -- h_after_append.
    rw [← h_RP, ← h_X_l]
    exact h_after_append

/-! ### §6.3 substrate for `insertion_perm_host`

The `swapAtRoot` case of `insertion_permStep_host` needs to lift a Perm
of vertices into a Perm of choice lists (via `listChoices`), then combine
with `multiGraft_swap_perm` to get equal `mk`-mapped insertion
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
private theorem listChoices_perm {β : Type*} {xs ys : List β}
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
    `Perm` of `multiGraft t' (pairs.map (Prod.map f id))` lifts to
    `mk`-equality of `insertion t Ts` and `insertion t' Ts`. -/
private theorem insertion_eq_of_pathBij {t t' : RoseTree α}
    (f : Path → Path)
    (hf_perm : ((vertices t).map f).Perm (vertices t'))
    (hf_graft : ∀ pairs, Perm (multiGraft t pairs)
                                      (multiGraft t' (pairs.map (Prod.map f id))))
    (Ts : List (RoseTree α)) :
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

/-- A path bijection `f` relating the vertex enumeration and `multiGraft`
    behaviour of `t` and `t'`, the data `insertion_eq_of_pathBij` turns into
    `mk`-equality. Reflexive and transitive, and produced by every `Perm`
    of hosts (`hasPathBij_of_perm`). -/
private def HasPathBij (t t' : RoseTree α) : Prop :=
  ∃ f : Path → Path,
    ((vertices t).map f).Perm (vertices t') ∧
    ∀ pairs, Perm (multiGraft t pairs)
                  (multiGraft t' (pairs.map (Prod.map f id)))

private theorem HasPathBij.refl (t : RoseTree α) : HasPathBij t t :=
  ⟨id, by simp, fun pairs => by simpa using Perm.refl _⟩

private theorem HasPathBij.trans {t t' t'' : RoseTree α}
    (h₁ : HasPathBij t t') (h₂ : HasPathBij t' t'') : HasPathBij t t'' := by
  obtain ⟨f, hvf, hgf⟩ := h₁
  obtain ⟨g, hvg, hgg⟩ := h₂
  refine ⟨g ∘ f, ?_, fun pairs => ?_⟩
  · rw [← List.map_map]
    exact (hvf.map g).trans hvg
  · refine (hgf pairs).trans ?_
    have h := hgg (pairs.map (Prod.map f id))
    rw [List.map_map,
        show (Prod.map g id ∘ Prod.map f id) = Prod.map (g ∘ f) id from
          funext fun _ => rfl] at h
    exact h

mutual
/-- Every `Perm` of hosts admits a path bijection. For a `swap` of two root
    children the bijection is `swapPathAt`; for a `cons` (a `Perm` on one
    child) it is `pathLiftRecurse` of the child's bijection; both thread a
    child-prefix context via the mutually-recursive `PermList` companion. -/
private theorem hasPathBij_of_perm :
    ∀ {t t' : RoseTree α}, Perm t t' → HasPathBij t t'
  | _, _, .node h => hasPathBij_of_permList h _ []
  | _, _, .trans h₁ h₂ => (hasPathBij_of_perm h₁).trans (hasPathBij_of_perm h₂)

/-- Companion of `hasPathBij_of_perm`: a `PermList` of children, in any
    prefix context, gives a path bijection on the enclosing node. -/
private theorem hasPathBij_of_permList :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      ∀ (a : α) (pre : List (RoseTree α)),
        HasPathBij (.node a (pre ++ cs)) (.node a (pre ++ ds))
  | _, _, .nil, _, _ => .refl _
  | _, _, @PermList.cons _ c d cs ds hcd hs, a, pre => by
    obtain ⟨f, hvf, hgf⟩ := hasPathBij_of_perm hcd
    have head : HasPathBij (.node a (pre ++ c :: cs)) (.node a (pre ++ d :: cs)) :=
      ⟨pathLiftRecurse pre.length f,
       vertices_recurse_perm a pre c d cs f hvf,
       fun pairs => multiGraft_recurse_perm a f hgf pre cs pairs⟩
    have tail := hasPathBij_of_permList hs a (pre ++ [d])
    simp only [List.append_assoc, List.singleton_append] at tail
    exact head.trans tail
  | _, _, .swap c d cs, a, pre =>
    ⟨swapPathAt pre.length, vertices_swap_perm a pre d c cs,
     fun pairs => multiGraft_swap_perm a pre d c cs pairs⟩
  | _, _, .trans h₁ h₂, a, pre =>
    (hasPathBij_of_permList h₁ a pre).trans (hasPathBij_of_permList h₂ a pre)
end

/-- `insertion T Ts` is `mk`-invariant under `Perm` of the host. -/
private theorem insertion_perm_host (Ts : List (RoseTree α))
    {t t' : RoseTree α} (h : Perm t t') :
    (insertion t Ts).map Nonplanar.mk =
      (insertion t' Ts).map Nonplanar.mk := by
  obtain ⟨f, hf_perm, hf_graft⟩ := hasPathBij_of_perm h
  exact insertion_eq_of_pathBij f hf_perm hf_graft Ts

/-- `List.Forall₂ Perm` lifts to `List` equality after mapping by
    `Nonplanar.mk` — used for the `Ts = []` base case of forest host
    invariance. -/
private theorem map_mk_eq_of_forall2_perm {F F' : List (RoseTree α)}
    (h : List.Forall₂ Perm F F') :
    F.map Nonplanar.mk = F'.map Nonplanar.mk := by
  induction h with
  | nil => rfl
  | cons hd_pe _ ih => simp [Nonplanar.mk_eq_mk_iff.mpr hd_pe, ih]

/-- Forest host invariance: `Forall₂ Perm F F'` lifts to
    `mk`-equality of `insertionForest F Ts` and `insertionForest F' Ts`. -/
theorem insertionForest_perm_host
    (Ts : List (RoseTree α)) {F F' : List (RoseTree α)}
    (h : List.Forall₂ Perm F F') :
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
            map_mk_eq_of_forall2_perm tail_pe]
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
      rw [insertion_perm_host _ hd_pe]
      refine Multiset.bind_congr fun mk_T_ins _ => ?_
      show (insertionForest F_tail _).map (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk) =
           (insertionForest F'_tail _).map (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
      rw [show (fun F_ins : List (RoseTree α) => mk_T_ins :: F_ins.map Nonplanar.mk) =
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
private def forestPairSum (F : List (RoseTree α)) :
    List (RoseTree α) → List (RoseTree α) → List (RoseTree α) →
      Multiset (List (RoseTree α))
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
    (T : RoseTree α) (F_tail pre_T pre_F : List (RoseTree α)) :
    forestPairSum (T :: F_tail) pre_T pre_F [] =
      (insertion T pre_T).bind fun T' =>
        (insertionForest F_tail pre_F).map fun F' => T' :: F' := by
  unfold forestPairSum; rfl

/-- Equation lemma: `forestPairSum F pre_T pre_F (x :: rest)`. -/
private theorem forestPairSum_cons_remaining
    (F pre_T pre_F : List (RoseTree α)) (x : RoseTree α) (rest : List (RoseTree α)) :
    forestPairSum F pre_T pre_F (x :: rest) =
      (Multiset.ofList [true, false]).bind fun b =>
        if b then forestPairSum F (pre_T ++ [x]) pre_F rest
        else forestPairSum F pre_T (pre_F ++ [x]) rest := rfl

/-- Assignment-rewrite: `forestPairSum` over remaining guests `Ts`
    equals the sum over all `[true, false]`-assignments to `Ts` of
    `forestPairSum` on the empty remaining list with the accumulators
    augmented by the partition of `Ts.zip α`. This rephrases the
    recursive accumulator-build as a single bind over `listChoices`. -/
private theorem forestPairSum_assignment_rewrite (F : List (RoseTree α)) :
    ∀ (pre_T pre_F : List (RoseTree α)) (Ts : List (RoseTree α)),
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
    forestPairSum ([] : List (RoseTree α)) [] [] [] =
      ({[]} : Multiset (List (RoseTree α))) := by
  unfold forestPairSum; rfl

/-- `forestPairSum []` with a non-empty `pre_T` is `0`. -/
private theorem forestPairSum_nil_F_zero_of_pre_T_cons
    (a : RoseTree α) (pre_T pre_F : List (RoseTree α)) :
    forestPairSum ([] : List (RoseTree α)) (a :: pre_T) pre_F [] = 0 := by
  unfold forestPairSum; rfl

/-- `forestPairSum []` with empty `pre_T` but non-empty `pre_F` is `0`. -/
private theorem forestPairSum_nil_F_zero_of_pre_F_cons
    (a : RoseTree α) (pre_F : List (RoseTree α)) :
    forestPairSum ([] : List (RoseTree α)) [] (a :: pre_F) [] = 0 := by
  unfold forestPairSum; rfl

/-- For the empty host `F = []`, if either accumulator is non-empty,
    `forestPairSum [] pre_T pre_F Ts = 0` regardless of `Ts`. -/
private theorem forestPairSum_nil_F_eq_zero
    (pre_T pre_F : List (RoseTree α)) (Ts : List (RoseTree α))
    (h : pre_T ≠ [] ∨ pre_F ≠ []) :
    forestPairSum ([] : List (RoseTree α)) pre_T pre_F Ts = 0 := by
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
private theorem forestPairSum_eq_insertionForest (F : List (RoseTree α))
    (Ts : List (RoseTree α)) :
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
      have h_ins_T : insertion T [] = ({T} : Multiset (RoseTree α)) := by
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
    (T : RoseTree α) (F_tail : List (RoseTree α))
    (ih_F : ∀ {Ts Ts' : List (RoseTree α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    {pre_T pre_T' pre_F pre_F' : List (RoseTree α)}
    (hT : pre_T.Perm pre_T') (hF : pre_F.Perm pre_F')
    (Ts : List (RoseTree α)) :
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
    rw [show (fun T' : RoseTree α =>
              ((insertionForest F_tail pre_F).map fun F' => T' :: F').map (List.map Nonplanar.mk)) =
            (fun T' : RoseTree α =>
              ((insertionForest F_tail pre_F).map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L))
            from by
          funext T'
          rw [Multiset.map_map, Multiset.map_map]
          rfl]
    rw [show (fun T' : RoseTree α =>
              ((insertionForest F_tail pre_F').map fun F' => T' :: F').map (List.map Nonplanar.mk)) =
            (fun T' : RoseTree α =>
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
    rw [show (insertion T pre_T).bind (fun T' : RoseTree α =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => Nonplanar.mk T' :: L)) =
            ((insertion T pre_T).map Nonplanar.mk).bind (fun mk_T' =>
              ((insertionForest F_tail pre_F').map (List.map Nonplanar.mk)).map
                (fun L => mk_T' :: L))
            from by rw [Multiset.bind_map]]
    rw [show (insertion T pre_T').bind (fun T' : RoseTree α =>
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
private theorem forestPairSum_cons_cons_unfold (F : List (RoseTree α))
    (pre_T pre_F : List (RoseTree α)) (x y : RoseTree α) (rest : List (RoseTree α)) :
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
    (T : RoseTree α) (F_tail : List (RoseTree α))
    (ih_F : ∀ {Ts Ts' : List (RoseTree α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    (pre_T pre_F : List (RoseTree α)) (a b : RoseTree α) (rest : List (RoseTree α)) :
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
    (T : RoseTree α) (F_tail : List (RoseTree α))
    (ih_F : ∀ {Ts Ts' : List (RoseTree α)} (_ : Ts.Perm Ts'),
            (insertionForest F_tail Ts).map (List.map Nonplanar.mk) =
            (insertionForest F_tail Ts').map (List.map Nonplanar.mk))
    (pre_T pre_F : List (RoseTree α))
    {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
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
    (F : List (RoseTree α)) {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
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
    the identity. -/
theorem insertion_nil_guests (T : RoseTree α) :
    insertion T ([] : List (RoseTree α)) = ({T} : Multiset (RoseTree α)) := by
  rw [insertion_def]
  simp only [List.length_nil, listChoices_zero, List.zip_nil_right,
             multiGraft_nil, List.map_cons, List.map_nil,
             Multiset.coe_singleton]

/-- `forestPairSum [T] pre (a :: pre_F_rest) gs = 0`. With a non-empty `pre_F`
    accumulator, the inner `insertionForest [] (a :: pre_F_rest ++ ...)` is 0,
    and the recursion preserves the non-empty invariant. -/
private theorem forestPairSum_singleton_host_pre_F_nonempty (T : RoseTree α) (a : RoseTree α) :
    ∀ (pre pre_F_rest gs : List (RoseTree α)),
    forestPairSum [T] pre (a :: pre_F_rest) gs = 0 := by
  intro pre pre_F_rest gs
  induction gs generalizing pre pre_F_rest with
  | nil =>
    rw [forestPairSum_cons_F_nil_remaining]
    rw [insertionForest_empty_host_nonempty_guests]
    -- Goal: (insertion T pre).bind (fun T' => (0 : Multiset _).map (fun F' => T' :: F')) = 0
    rw [show (fun T' : RoseTree α =>
              ((0 : Multiset (List (RoseTree α))).map (fun F' => T' :: F'))) =
            (fun (_ : RoseTree α) => (0 : Multiset (List (RoseTree α)))) from by
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
private theorem forestPairSum_singleton_host_no_pre_F (T : RoseTree α) :
    ∀ (pre gs : List (RoseTree α)),
    forestPairSum [T] pre [] gs = (insertion T (pre ++ gs)).map (fun T' => [T']) := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    rw [forestPairSum_cons_F_nil_remaining, insertionForest_nil_nil, List.append_nil]
    -- Goal: (insertion T pre).bind (fun T' => ({[]}).map (fun F' => T' :: F')) =
    --       (insertion T pre).map (fun T' => [T'])
    rw [show (fun T' : RoseTree α =>
              ({([] : List (RoseTree α))} : Multiset (List (RoseTree α))).map (fun F' => T' :: F')) =
            (fun T' : RoseTree α => ({[T']} : Multiset (List (RoseTree α)))) from by
          funext T'
          rw [Multiset.map_singleton]]
    exact Multiset.bind_singleton (s := insertion T pre) (fun T' => [T'])
  | cons g rest ih =>
    rw [forestPairSum_cons_remaining]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [ih (pre ++ [g])]
    rw [show ([] : List (RoseTree α)) ++ [g] = [g] from rfl]
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
theorem insertionForest_singleton (T : RoseTree α) (gs : List (RoseTree α)) :
    insertionForest [T] gs = (insertion T gs).map (fun T' => [T']) := by
  rw [show insertionForest [T] gs = forestPairSum [T] [] [] gs from
        (forestPairSum_eq_insertionForest _ _).symm]
  rw [forestPairSum_singleton_host_no_pre_F T [] gs, List.nil_append]

end Pathed

end RoseTree
