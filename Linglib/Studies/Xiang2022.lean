import Mathlib.Tactic.FinCases
import Linglib.Semantics.Questions.Closure
import Linglib.Semantics.Exhaustification.Excluder
import Linglib.Data.Examples.Xiang2022

/-!
# Xiang (2022): Relativized Exhaustivity: Mention-Some and Uniqueness

This file formalizes [xiang-2022]'s Relativized Exhaustivity, the presupposition that replaces
[dayal-1996]'s exhaustivity presupposition in modalized questions. A question is a topical
property `P : α → Set W` from short answers to propositions, answered by [fox-2013]'s
max-informative true short answers, those not asymmetrically entailed by another true answer
(`MaxI`, mathlib's `MinimalFor`), so that a *can*-question may have several complete answers.
Dayal's presupposition that a strongest true answer exists (`DEP`) rules these out;
Relativized Exhaustivity (`RelExh`) requires it instead of the non-modalized question at every
accessible world verifying a true answer.

The main results are the paper's generalization for existential modals, that the mention-some
readings of *Wh-A can P?* satisfy Relativized Exhaustivity exactly when *Wh-A P?* satisfies
Dayal's presupposition at every accessible world where some member of *A* satisfies *P*
(`relExh_poss_iff`), and the scenarios separating the two presuppositions. Local
exhaustification of the nucleus makes the non-modalized question uniquely answered wherever it
has a true answer, so the exhaustified mention-some reading of a *can*-question always
satisfies Relativized Exhaustivity while Dayal's presupposition fails (`relExh_poss_localExh`,
`chair_scenario`). A *have to*-question with a narrow-scope disjunctive answer separates them
the other way: Dayal's presupposition holds while Relativized Exhaustivity fails wherever an
accessible world violates uniqueness, the local-uniqueness inference of
[hirsch-schwarz-2020] (`assign_scenario`).

## Implementation notes

The paper states Relativized Exhaustivity by quantifying over modal bases that send the
evaluation world to a singleton subset of the original base; `RelExh` states the intended
condition directly, for the modalized question `O ∘ P` built from the non-modalized property by
an operator `O` over the accessibility relation. Local exhaustification is
`Exhaustification.exh` over the alternatives of the wh-trace. Modal flavour and the
anti-exhaustification analysis of disjunctive mention-all answers are not modelled.

## References

* [xiang-2022]
* [dayal-1996]
* [fox-2013]
* [hirsch-schwarz-2020]
-/

namespace Xiang2022

open Question ModalLogic Exhaustification Set

variable {W α : Type*}

/-! ### Answerhood over topical properties -/

/-- The short answers true at a world. -/
def trueShort (P : α → Set W) (w : W) : Set α := {a | w ∈ P a}

@[simp] theorem mem_trueShort {P : α → Set W} {w : W} {a : α} :
    a ∈ trueShort P w ↔ w ∈ P a := Iff.rfl

/-- Dayal's exhaustivity presupposition for a topical property: its answer space has a
strongest true member. -/
def DEP (P : α → Set W) (w : W) : Prop := IsExhaustivelyResolvable (range P) w

/-- The presupposition over short answers: a true short answer whose proposition entails
every true one. -/
theorem dep_iff (P : α → Set W) (w : W) :
    DEP P w ↔ ∃ a, w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b :=
  isExhaustivelyResolvable_range_iff P w

/-- A max-informative true short answer: true, and minimal under entailment among the true
short answers. -/
abbrev MaxI (P : α → Set W) (w : W) (a : α) : Prop := MinimalFor (· ∈ trueShort P w) P a

/-- The paper's form: true, and not asymmetrically entailed by another true answer. -/
theorem maxI_iff {P : α → Set W} {w : W} {a : α} :
    MaxI P w a ↔ w ∈ P a ∧ ∀ b, w ∈ P b → ¬ P b ⊂ P a := by
  simp only [MaxI, MinimalFor, mem_trueShort, not_lt_iff_le_imp_ge]

/-- The short-answer operator: the max-informative true short answers. -/
def ansS (P : α → Set W) (w : W) : Set α := {a | MaxI P w a}

/-- The propositional operator: the image of the short-answer operator. -/
def ansP (P : α → Set W) (w : W) : Set (Set W) := P '' ansS P w

/-- The propositional operator returns the minimal true members of the answer space. -/
theorem mem_ansP_iff {P : α → Set W} {w : W} {p : Set W} :
    p ∈ ansP P w ↔ Minimal (· ∈ trueAnswers (range P) w) p := by
  constructor
  · rintro ⟨a, ⟨ha, hmin⟩, rfl⟩
    refine ⟨⟨⟨a, rfl⟩, ha⟩, ?_⟩
    rintro _ ⟨⟨b, rfl⟩, hb⟩ hle
    exact hmin hb hle
  · rintro ⟨⟨⟨a, rfl⟩, ha⟩, hmin⟩
    exact ⟨a, ⟨ha, λ b hb hle => hmin (y := P b) ⟨⟨b, rfl⟩, hb⟩ hle⟩, rfl⟩

/-- Under Dayal's presupposition the operator returns the strongest true answer alone. -/
theorem ansP_eq_singleton {P : α → Set W} {w : W} {p : Set W}
    (h : IsStrongestTrueAnswer (range P) w p) : ansP P w = {p} := by
  ext q
  rw [mem_ansP_iff, h.minimal_iff, mem_singleton_iff]

/-! ### Modalized questions -/

/-- Relativized Exhaustivity for the question `O ∘ P` built from the non-modalized `P` by the
operator `O` over the accessibility `R`: at every accessible world verifying one of the
modalized question's true short answers, `P` satisfies Dayal's presupposition. -/
def RelExh (O : Set W → Set W) (R : W → W → Prop) (P : α → Set W) (w : W) : Prop :=
  ∀ v, R w v → (∃ a, w ∈ O (P a) ∧ v ∈ P a) → DEP P v

/-- The generalization for existential modals: the mention-some readings satisfy Relativized
Exhaustivity exactly when the non-modalized question satisfies Dayal's presupposition at every
accessible world where some short answer is true. -/
theorem relExh_poss_iff (R : W → W → Prop) (P : α → Set W) (w : W) :
    RelExh (poss R) R P w ↔ ∀ v, R w v → (trueShort P v).Nonempty → DEP P v :=
  forall₂_congr λ v hv => imp_congr_left
    ⟨λ ⟨a, _, ha⟩ => ⟨a, ha⟩, λ ⟨a, ha⟩ => ⟨a, ⟨v, hv, ha⟩, ha⟩⟩

/-- For a non-modalized question, over the identity relation on which both modals are the
identity, Relativized Exhaustivity is Dayal's presupposition wherever the question has a true
answer. -/
theorem relExh_id_iff (P : α → Set W) (w : W) :
    RelExh id Eq P w ↔ ((trueShort P w).Nonempty → DEP P w) := by
  simp [RelExh, Set.Nonempty]

/-! ### Local exhaustification -/

/-- The nucleus exhaustified against the alternatives of the wh-trace: each short answer, and
no other. -/
def localExh (P : α → Set W) : α → Set W := exh (range P) ∘ P

/-- Two true exhaustified short answers have the same proposition. -/
theorem eq_of_mem_localExh {P : α → Set W} {w : W} {a b : α} (ha : w ∈ localExh P a)
    (hb : w ∈ localExh P b) : P a = P b :=
  (ha.2 _ ⟨b, rfl⟩ hb.1).antisymm (hb.2 _ ⟨a, rfl⟩ ha.1)

/-- The exhaustified question satisfies Dayal's presupposition wherever it has a true answer. -/
theorem dep_localExh {P : α → Set W} {w : W} (h : (trueShort (localExh P) w).Nonempty) :
    DEP (localExh P) w :=
  let ⟨a, ha⟩ := h
  (dep_iff _ _).2 ⟨a, ha, λ b hb => by
    simp only [localExh, Function.comp_apply, eq_of_mem_localExh ha hb, subset_rfl]⟩

/-- The exhaustified mention-some reading of a *can*-question satisfies Relativized
Exhaustivity over any accessibility relation: the uniqueness it presupposes is existential. -/
theorem relExh_poss_localExh (R : W → W → Prop) (P : α → Set W) (w : W) :
    RelExh (poss R) R (localExh P) w :=
  (relExh_poss_iff R _ w).2 λ _ _ h => dep_localExh h

/-! ### The committee scenario -/

/-- The worlds of the committee scenario: the evaluation world `0` and the accessible worlds
`1` and `2`. -/
abbrev CW := Fin 3

/-- *x chairs the committee*: Andy (`0`) chairs in world 1, Billy (`1`) in world 2. -/
def chair : Fin 2 → Set CW
  | 0 => {1}
  | 1 => {2}

/-- The modal base: the evaluation world accesses both alternatives, each of which accesses
only itself. -/
def chairR : CW → CW → Prop
  | 0, v => v ≠ 0
  | w, v => w = v

/-- Under the base, *x can chair* holds at the evaluation world and at `x`'s own world. -/
theorem poss_localExh_chair (a : Fin 2) : poss chairR (localExh chair a) = {0, a.succ} := by
  ext w; fin_cases a <;> fin_cases w <;> simp [localExh, exh, chair, chairR]

/-- The exhaustified mention-some reading of *Who can chair the committee?* has both short
answers max-informative, satisfies Relativized Exhaustivity, and violates Dayal's
presupposition. -/
theorem chair_scenario :
    ansS (poss chairR ∘ localExh chair) 0 = univ ∧
      RelExh (poss chairR) chairR (localExh chair) 0 ∧
        ¬ DEP (poss chairR ∘ localExh chair) 0 := by
  refine ⟨eq_univ_of_forall λ a => ⟨by simp [poss_localExh_chair], λ b _ hle => ?_⟩,
    relExh_poss_localExh _ _ _, ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [poss_localExh_chair, subset_def] at hle ⊢
  · rw [dep_iff]
    rintro ⟨a, -, h⟩
    fin_cases a
    · simpa [poss_localExh_chair, subset_def] using h 1
    · simpa [poss_localExh_chair, subset_def] using h 0

/-! ### The chapter scenario -/

/-- The worlds of the chapter scenario: the evaluation worlds `0` and `4`, and the accessible
worlds `1`, `2`, `3`. -/
abbrev AW := Fin 5

/-- *We assign chapter c*: chapter 1 is assigned in worlds 1 and 3, chapter 2 in worlds 2
and 3. -/
def assigned : Fin 2 → Set AW
  | 0 => {1, 3}
  | 1 => {2, 3}

/-- The narrow-scope higher-order answers: either chapter, or their disjunction. -/
def assign : Fin 3 → Set AW
  | 0 => assigned 0
  | 1 => assigned 1
  | 2 => assigned 0 ∪ assigned 1

/-- The higher-order answer space is the disjunctive closure of the first-order one. -/
theorem range_assign : range assign = disjClosure assigned := by
  ext q
  simp only [mem_range, disjClosure, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨{0}, by simp, by simp [disj, assign]⟩
    · exact ⟨{1}, by simp, by simp [disj, assign]⟩
    · exact ⟨{0, 1}, by simp, by simp [disj, assign]⟩
  · rintro ⟨S, hS, rfl⟩
    fin_cases S
    · exact absurd hS (by simp)
    · exact ⟨0, by simp [disj, assign]⟩
    · exact ⟨1, by simp [disj, assign]⟩
    · exact ⟨2, by simp [disj, assign]⟩

/-- The modal base: world `0` accesses the uniqueness-violating world `3`, world `4` does
not. -/
def assignR : AW → AW → Prop
  | 0, v => v ∈ ({1, 2, 3} : Set AW)
  | 4, v => v ∈ ({1, 2} : Set AW)
  | w, v => w = v

/-- The first-order question satisfies Dayal's presupposition exactly at the worlds assigning
one chapter. -/
theorem dep_assigned_iff (v : AW) : DEP assigned v ↔ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp [dep_iff, assigned, Fin.exists_fin_two, Fin.forall_fin_two, subset_def]

/-- So does the higher-order question: at world 3 the disjunction is entailed by both
disjuncts, so no true answer is strongest. -/
theorem dep_assign_iff (v : AW) : DEP assign v ↔ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp [dep_iff, assign, assigned, Fin.exists_fin_succ, Fin.forall_fin_succ,
    subset_def]

/-- Dayal's presupposition holds of the modalized question at world 0, where the disjunction
is its only true answer, while Relativized Exhaustivity fails there and holds at world 4:
the local-uniqueness inference of *Which chapter do we have to assign?*. -/
theorem assign_scenario :
    DEP (nec assignR ∘ assign) 0 ∧ ¬ RelExh (nec assignR) assignR assign 0 ∧
      RelExh (nec assignR) assignR assign 4 := by
  have h0 : nec assignR (assign 0) = {1, 3} := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  have h1 : nec assignR (assign 1) = {2, 3} := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  have h2 : nec assignR (assign 2) = univ := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  refine ⟨(dep_iff _ _).2 ⟨2, by simp [h2], λ b hb => by
    fin_cases b <;> simp [h0, h1, h2] at hb ⊢⟩, λ h => ?_, λ v hv _ => ?_⟩
  · simpa [dep_assign_iff] using
      h 3 (by simp [assignR]) ⟨2, by simp [h2], by simp [assign, assigned]⟩
  · exact (dep_assign_iff v).2 (by simpa [assignR] using hv)

/-- The first-order mention-some reading of *Which chapter can we assign?* over the same base:
Relativized Exhaustivity fails at world 0, whose accessible world 3 assigns both chapters,
and holds at world 4, the universal local-uniqueness inference. -/
theorem assign_can_scenario :
    ¬ RelExh (poss assignR) assignR assigned 0 ∧ RelExh (poss assignR) assignR assigned 4 := by
  simp only [relExh_poss_iff, dep_assigned_iff]
  exact ⟨λ h => by simpa using h 3 (by simp [assignR]) ⟨0, by simp [assigned]⟩,
    λ v hv _ => by simpa [assignR] using hv⟩

end Xiang2022
