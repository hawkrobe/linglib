import Linglib.Core.IntensionalLogic.Premise
import Mathlib.Data.Fintype.Basic

/-!
# Kratzer (1977) — Premise semantics worked example

@cite{kratzer-1977} @cite{kratzer-2012}

A concrete formalization of the New Zealand judgments scenario from §1.3
of @cite{kratzer-1977} (= Chapter 1 of @cite{kratzer-2012}), exercising
the API of `Core.IntensionalLogic.Premise`.

## The scenario

@cite{kratzer-1977} imagines a country whose entire common law consists
of three judgments:

1. *Murder is a crime.* — call this proposition `p`.
2. *Deer are personally responsible for damage they inflict on young
   trees.* — call this proposition `q`.
3. *Deer are not personally responsible for damage they inflict on young
   trees.* — proposition `¬q`.

The premise set `A = [p, q, ¬q]` is **inconsistent** (its intersection
is empty: no world makes `q` and `¬q` both true). Yet our intuitions
about modal claims relativized to *what the New Zealand judgments
provide* are crisp:

- (7) "Murder must be a crime." — TRUE
- (8) "It must be that murder is not a crime." — FALSE
- (9) "It is possible that deer are responsible." — TRUE
- (10) "It is possible that deer are not responsible." — TRUE
- (14) "It is possible that murder is not a crime." — FALSE

Kratzer's original Defs 5–6 (necessity = consequence, possibility =
compatibility) collapse on inconsistent `A`: by *ex falso quodlibet*,
**everything** follows from `A`, so `must p` and `must ¬p` are both
true, and **nothing** is compatible with `A`, so `can q` and `can ¬q`
are both false. Defs 7–8 — quantifying over the consistent subsets of
`A` and asking for an extension that supports the conclusion — recover
the intuitive predictions.

## What this study is

A Phenomenon-layer **integration test** for `Core.IntensionalLogic.Premise`:
it picks the worked example Kratzer uses to motivate the revision from
Defs 5–6 to Defs 7–8 and verifies, by structural proofs over the four-world
frame, that the formalization gets each prediction right and that the
unrevised definitions fail in exactly the way Kratzer says they do.
-/

namespace Phenomena.Modality.Studies.Kratzer1977

open Core.IntensionalLogic.Premise

/-! ## §1. The model

A four-world frame, indexed by `Fin 4`, that distinguishes the two
contingent dimensions of the scenario: whether murder is a crime
(`p`) and whether deer are responsible (`q`). All four combinations
are represented so that every singleton premise — `p`, `q`, `¬q`, `¬p`
— is individually consistent.

| world | p (murder is a crime) | q (deer responsible) |
|-------|-----------------------|----------------------|
| `w₀`  | true                  | true                 |
| `w₁`  | true                  | false                |
| `w₂`  | false                 | true                 |
| `w₃`  | false                 | false                |
-/

/-- "Murder is a crime." True at `w₀` and `w₁`. -/
def p : Fin 4 → Prop
  | 0 => True
  | 1 => True
  | 2 => False
  | 3 => False

/-- "Deer are personally responsible for damage they inflict on young trees."
    True at `w₀` and `w₂`. -/
def q : Fin 4 → Prop
  | 0 => True
  | 1 => False
  | 2 => True
  | 3 => False

/-- "Deer are not personally responsible…" — the negation of `q`. -/
def negQ : Fin 4 → Prop := fun w => ¬ q w

/-- "Murder is not a crime." The negation of `p`. -/
def negP : Fin 4 → Prop := fun w => ¬ p w

/-- The premise set `A` of @cite{kratzer-1977} §1.3 — *what the New Zealand
    judgments provide*: the three rulings, taken together. -/
def A : List (Fin 4 → Prop) := [p, q, negQ]

/-- The constant modal restriction: at every world, the premise set is `A`.
    The scenario abstracts away from world-to-world variation in the
    judgments. -/
def f : Fin 4 → List (Fin 4 → Prop) := fun _ => A

/-! ## Membership lemmas: each judgment is in `A`. -/

lemma p_mem_A : p ∈ A := List.mem_cons_self
lemma q_mem_A : q ∈ A := List.mem_cons_of_mem _ List.mem_cons_self
lemma negQ_mem_A : negQ ∈ A :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-! ## §2. `A` is inconsistent

The premise set contains both `q` and its negation, so its
intersection is empty. -/

theorem A_inconsistent : ¬ isConsistent A := by
  rintro ⟨w, hw⟩
  exact (hw negQ negQ_mem_A) (hw q q_mem_A)

/-! ## §3. Unrevised Defs 5–6 give paradoxical predictions

These two theorems are the formal counterpart of Kratzer's diagnosis
of the original definitions: they trivialize over an inconsistent `A`. -/

/-- Under the original Def 5 (`mustInView`), the inconsistent `A`
    entails *every* proposition — including `¬p`. This is the paradox
    of *ex falso quodlibet* that motivates the revision to Def 7. -/
theorem must_negP_under_def5 : mustInView f negP 0 := by
  intro w hw
  -- propIntersection A is empty, so the goal is vacuously derivable.
  exact absurd (hw q q_mem_A) (hw negQ negQ_mem_A)

/-- Under the original Def 6 (`canInView`), nothing is compatible with
    the inconsistent `A` — including `q`, which intuitively *is*
    possible in view of the judgments. -/
theorem can_q_under_def6 : ¬ canInView f q 0 := by
  rintro ⟨w, hw⟩
  -- hw : ∀ r ∈ q :: A, r w
  have hq : q w := hw q List.mem_cons_self
  have hnq : ¬ q w := hw negQ (List.mem_cons_of_mem _ negQ_mem_A)
  exact hnq hq

/-! ## §4. Revised Defs 7–8 give the intuitive predictions

Each theorem corresponds to a sentence number from @cite{kratzer-1977}
§1.3, with the predicted truth value Kratzer argues for.

The proofs proceed by enumerating the consistent sublists of `A` and,
for each one, exhibiting an extension that witnesses (or refutes) the
target consequence. -/

/-! ### Membership helpers for the four worlds -/

@[simp] lemma p_zero : p 0 := trivial
@[simp] lemma p_one : p 1 := trivial
@[simp] lemma not_p_two : ¬ p 2 := id
@[simp] lemma not_p_three : ¬ p 3 := id

@[simp] lemma q_zero : q 0 := trivial
@[simp] lemma not_q_one : ¬ q 1 := id
@[simp] lemma q_two : q 2 := trivial
@[simp] lemma not_q_three : ¬ q 3 := id

@[simp] lemma negQ_one : negQ 1 := not_q_one
@[simp] lemma negQ_three : negQ 3 := not_q_three

/-! ### Consistency of relevant sublists of `A` -/

lemma cons_singleton_p : isConsistent ([p] : List (Fin 4 → Prop)) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact p_zero

lemma cons_singleton_q : isConsistent ([q] : List (Fin 4 → Prop)) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact q_zero

lemma cons_singleton_negQ : isConsistent ([negQ] : List (Fin 4 → Prop)) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact negQ_one

lemma cons_pair_pq : isConsistent ([p, q] : List (Fin 4 → Prop)) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact p_zero
  · rcases List.mem_singleton.mp hr with rfl; exact q_zero

lemma cons_pair_pnegQ : isConsistent ([p, negQ] : List (Fin 4 → Prop)) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact p_one
  · rcases List.mem_singleton.mp hr with rfl; exact negQ_one

/-! ### Sublist enumeration

Every sublist of `A = [p, q, negQ]` has every element drawn from `{p, q, negQ}`. -/

lemma mem_of_sublist_A {B : List (Fin 4 → Prop)}
    (hB : B ∈ A.sublists) {x : Fin 4 → Prop} (hx : x ∈ B) :
    x = p ∨ x = q ∨ x = negQ := by
  have hSub : B.Sublist A := List.mem_sublists.mp hB
  have hxA : x ∈ A := hSub.subset hx
  rcases List.mem_cons.mp hxA with rfl | hxA
  · exact Or.inl rfl
  rcases List.mem_cons.mp hxA with rfl | hxA
  · exact Or.inr (Or.inl rfl)
  · rcases List.mem_singleton.mp hxA with rfl
    exact Or.inr (Or.inr rfl)

/-- A consistent sublist of `A` cannot contain both `q` and `negQ`. -/
lemma not_q_and_negQ {B : List (Fin 4 → Prop)} (hCons : isConsistent B)
    (hq : q ∈ B) (hnq : negQ ∈ B) : False := by
  obtain ⟨w, hw⟩ := hCons
  exact (hw negQ hnq) (hw q hq)

/-! ### Sublist relations against `A = [p, q, negQ]` -/

/-- `[p, q]` is a sublist of `[p, q, negQ]` (drop `negQ`). -/
lemma pq_sublist_A : ([p, q] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]
  -- Build [p, q].Sublist [p, q, negQ]: keep p, keep q, drop negQ.
  exact ((List.nil_sublist [negQ]).cons₂ q).cons₂ p

/-- `[p, negQ]` is a sublist of `[p, q, negQ]` (drop `q`). -/
lemma pnegQ_sublist_A : ([p, negQ] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]
  -- Build [p, negQ].Sublist [p, q, negQ]: keep p, drop q, keep negQ.
  exact ((List.Sublist.refl ([negQ] : List (Fin 4 → Prop))).cons q).cons₂ p

/-- `[p]` is a sublist of `[p, q, negQ]`. -/
lemma p_sublist_A : ([p] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]
  -- Build [p].Sublist [p, q, negQ]: keep p, drop q, drop negQ.
  exact ((List.nil_sublist [negQ]).cons q).cons₂ p

/-- `[q]` is a sublist of `[p, q, negQ]`. -/
lemma q_sublist_A : ([q] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]
  -- Build [q].Sublist [p, q, negQ]: drop p, keep q, drop negQ.
  exact (((List.nil_sublist [negQ]).cons₂ q).cons p)

/-- `[negQ]` is a sublist of `[p, q, negQ]`. -/
lemma negQ_sublist_A : ([negQ] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]
  -- Build [negQ].Sublist [p, q, negQ]: drop p, drop q, keep negQ.
  exact ((List.Sublist.refl ([negQ] : List (Fin 4 → Prop))).cons q).cons p

/-- The empty list is a sublist of `A`. -/
lemma nil_sublist_A : ([] : List (Fin 4 → Prop)) ∈ A.sublists := by
  rw [List.mem_sublists]; exact List.nil_sublist _

/-! ### Witness selection for the revised must/can theorems -/

/-- For any consistent sublist `B` of `A`, exhibit a consistent sublist
    `C` of `A` with `B ⊆ C` and `p ∈ C`. We use `[p, q]` if `B` does not
    contain `negQ`, and `[p, negQ]` otherwise. -/
lemma exists_extension_with_p {B : List (Fin 4 → Prop)}
    (hBSub : B ∈ A.sublists) (hBCons : isConsistent B) :
    ∃ C ∈ A.sublists, isConsistent C ∧ B ⊆ C ∧ p ∈ C := by
  by_cases hNegQ : negQ ∈ B
  · refine ⟨[p, negQ], pnegQ_sublist_A, cons_pair_pnegQ, ?_, ?_⟩
    · intro x hxB
      rcases mem_of_sublist_A hBSub hxB with rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd (not_q_and_negQ hBCons hxB hNegQ) id
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
  · refine ⟨[p, q], pq_sublist_A, cons_pair_pq, ?_, ?_⟩
    · intro x hxB
      rcases mem_of_sublist_A hBSub hxB with rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd hxB hNegQ
    · exact List.mem_cons_self

/-- Any list containing `p` entails `p`: ⋂ C ⊆ propExtension p. -/
lemma followsFrom_p_of_mem {C : List (Fin 4 → Prop)} (hp : p ∈ C) :
    followsFrom p C := fun _ hi => hi p hp

/-- (7) "Murder must be a crime" — TRUE under Def 7. The extension
    `[p, q]` (or `[p, ¬q]`) of any consistent subset of `A` entails `p`. -/
theorem sentence_7_must_p : mustInView' f p 0 := by
  intro B hB
  obtain ⟨hBSub, hBCons⟩ := hB
  obtain ⟨C, hCSub, hCCons, hBC, hpC⟩ := exists_extension_with_p hBSub hBCons
  exact ⟨C, ⟨hCSub, hCCons⟩, hBC, followsFrom_p_of_mem hpC⟩

/-- (8) "It must be that murder is not a crime" — FALSE under Def 7.
    Apply Def 7 at `B = [p]`; any consistent extension `C ⊇ [p]` of `A`
    contains `p`, but `negP` cannot follow from `C` because `C` admits
    a witness world (`0` if `q ∈ C`, else `1`) where `p` holds, hence
    `negP` fails. -/
theorem sentence_8_not_must_negP : ¬ mustInView' f negP 0 := by
  intro h
  have hp : [p] ∈ consistentSublists (f 0) := ⟨p_sublist_A, cons_singleton_p⟩
  obtain ⟨C, ⟨hCSub, hCCons⟩, hpC, hFollows⟩ := h _ hp
  have hpInC : p ∈ C := hpC List.mem_cons_self
  by_cases hqInC : q ∈ C
  · -- world 0: at 0, p holds and q holds; negQ ∉ C since C consistent.
    have hnegQNotInC : negQ ∉ C := fun h2 => not_q_and_negQ hCCons hqInC h2
    have h0_in : (0 : Fin 4) ∈ propIntersection C := by
      intro r hr
      rcases mem_of_sublist_A hCSub hr with rfl | rfl | rfl
      · exact p_zero
      · exact q_zero
      · exact absurd hr hnegQNotInC
    exact (hFollows h0_in) p_zero
  · -- world 1: at 1, p holds and ¬q holds (so negQ would hold), but q ∉ C.
    have h1_in : (1 : Fin 4) ∈ propIntersection C := by
      intro r hr
      rcases mem_of_sublist_A hCSub hr with rfl | rfl | rfl
      · exact p_one
      · exact absurd hr hqInC
      · exact negQ_one
    exact (hFollows h1_in) p_one

/-- (9) "It is possible that deer are responsible" — TRUE under Def 8.
    Witness: take `B = [q]`; every consistent extension already contains `q`,
    so adding `q` preserves consistency. -/
theorem sentence_9_can_q : canInView' f q 0 := by
  refine ⟨[q], ⟨q_sublist_A, cons_singleton_q⟩, ?_⟩
  intro C hC hBC
  obtain ⟨hCSub, hCCons⟩ := hC
  have hqC : q ∈ C := hBC List.mem_cons_self
  obtain ⟨w, hw⟩ := hCCons
  refine ⟨w, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hrC
  · exact hw q hqC
  · exact hw r hrC

/-- (10) "It is possible that deer are not responsible" — TRUE under Def 8.
    Symmetric to (9), with witness `B = [¬q]`. -/
theorem sentence_10_can_negQ : canInView' f negQ 0 := by
  refine ⟨[negQ], ⟨negQ_sublist_A, cons_singleton_negQ⟩, ?_⟩
  intro C hC hBC
  obtain ⟨hCSub, hCCons⟩ := hC
  have hnegQC : negQ ∈ C := hBC List.mem_cons_self
  obtain ⟨w, hw⟩ := hCCons
  refine ⟨w, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hrC
  · exact hw negQ hnegQC
  · exact hw r hrC

/-- (14) "It is possible that murder is not a crime" — FALSE under Def 8.
    Every consistent subset of `A` extends to one containing `p`, and
    adding `¬p` to such a set is never consistent. -/
theorem sentence_14_not_can_negP : ¬ canInView' f negP 0 := by
  rintro ⟨B, hB, hAll⟩
  obtain ⟨hBSub, hBCons⟩ := hB
  obtain ⟨C, hCSub, hCCons, hBC, hpC⟩ := exists_extension_with_p hBSub hBCons
  have hCompat := hAll C ⟨hCSub, hCCons⟩ hBC
  obtain ⟨w, hw⟩ := hCompat
  have hnegP : negP w := hw negP List.mem_cons_self
  have hp : p w := hw p (List.mem_cons_of_mem _ hpC)
  exact hnegP hp

/-! ## §5. The contrast in one place

Two theorems pinning the bug-vs-fix asymmetry: the revised definitions
agree with intuition exactly where the original definitions trivialize. -/

/-- Def 5 wrongly accepts `must ¬p`; Def 7 correctly rejects it. -/
theorem def5_vs_def7_negP :
    mustInView f negP 0 ∧ ¬ mustInView' f negP 0 :=
  ⟨must_negP_under_def5, sentence_8_not_must_negP⟩

/-- Def 6 wrongly rejects `can q`; Def 8 correctly accepts it. -/
theorem def6_vs_def8_q :
    ¬ canInView f q 0 ∧ canInView' f q 0 :=
  ⟨can_q_under_def6, sentence_9_can_q⟩

end Phenomena.Modality.Studies.Kratzer1977
