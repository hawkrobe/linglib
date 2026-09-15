import Mathlib.Tactic.FinCases
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Data.Examples.Xiang2022

/-!
# Xiang (2022): Relativized Exhaustivity: Mention-Some and Uniqueness

This file formalizes [xiang-2022]'s replacement for [dayal-1996]'s exhaustivity presupposition.
A question is a topical property, a function from short answers to propositions, and the
answerhood operator of [fox-2018] returns its max-informative true answers, those not
asymmetrically entailed by another true answer (`MaxI`). This lets a *can*-question have
several complete answers, the mention-some reading, but conflicts with Dayal's presupposition
that a question has an exhaustive true answer (`DEP`), which explains why a singular
*which*-question presupposes a unique true answer. Relativized Exhaustivity resolves the
dilemma: a modalized question is defined only if its non-modalized counterpart satisfies
Dayal's presupposition in every accessible world that verifies one of its true answers
(`RelExh`). For an existential modal this is the paper's generalization: the mention-some
readings of *Wh-A can P?* satisfy Relativized Exhaustivity exactly when *Wh-A P?* satisfies
Dayal's presupposition in every accessible world where some member of *A* satisfies *P*
(`relExh_diamond_iff`); for a non-modalized question the two presuppositions coincide
(`relExh_id_iff`). Local exhaustification of the nucleus makes the non-modalized question
uniquely answered wherever it has a true answer, so the exhaustified mention-some reading
always satisfies Relativized Exhaustivity while Dayal's presupposition fails on the modalized
question (`relExh_diamond_exh`, `chair_scenario`). A universal modal with a narrow-scope
disjunctive answer separates the two conditions the other way: Dayal's presupposition holds
of the modalized question while Relativized Exhaustivity fails in a world with an accessible
world violating uniqueness, the local-uniqueness inference (`assign_scenario`).

## Implementation notes

The paper states Relativized Exhaustivity through modal bases that map the evaluation world
to a singleton subset of the original modal base; a proposition built from a modal over
such a base is trivial, so the condition is taken in the paper's own gloss, as Dayal's
presupposition for the non-modalized topical property at each verifying accessible world.
The modalized question is built from the non-modalized property by a modal operator over
the base, and the verification clause is stated for that operator. Modal flavour and the
anti-exhaustification analysis of disjunctive mention-all answers are not modelled.

## References

* [xiang-2022]
* [dayal-1996]
* [fox-2018]
* [hirsch-schwarz-2020]
-/

namespace Xiang2022

open Question

variable {W α : Type*}

/-! ### Answerhood over topical properties -/

/-- The short answers true at a world. -/
def trueShort (P : α → Set W) (w : W) : Set α := {a | w ∈ P a}

/-- Dayal's exhaustivity presupposition for a topical property: its answer space has a
strongest true member. -/
def DEP (P : α → Set W) (w : W) : Prop := IsExhaustivelyResolvable (Set.range P) w

/-- The presupposition over short answers: a true short answer whose proposition entails
every true one. -/
theorem dep_iff (P : α → Set W) (w : W) :
    DEP P w ↔ ∃ a, w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b := by
  constructor
  · rintro ⟨p, ⟨⟨a, rfl⟩, hw⟩, hmin⟩
    exact ⟨a, hw, λ b hb => hmin ⟨⟨b, rfl⟩, hb⟩⟩
  · rintro ⟨a, hw, hmin⟩
    exact ⟨P a, ⟨⟨a, rfl⟩, hw⟩, by rintro q ⟨⟨b, rfl⟩, hb⟩; exact hmin b hb⟩

/-- A max-informative true answer: true, and not asymmetrically entailed by another true
answer. -/
def MaxI (P : α → Set W) (w : W) (a : α) : Prop :=
  w ∈ P a ∧ ∀ b, w ∈ P b → ¬ P b ⊂ P a

/-- The short-answer operator: the max-informative true short answers. -/
def ansS (P : α → Set W) (w : W) : Set α := {a | MaxI P w a}

/-- The propositional operator: the image of the short-answer operator. -/
def ansP (P : α → Set W) (w : W) : Set (Set W) := P '' ansS P w

/-- A strongest true answer is max-informative, so under Dayal's presupposition the operator
returns the exhaustive answer among others. -/
theorem maxI_of_isLeast {P : α → Set W} {w : W} {a : α} (hw : w ∈ P a)
    (h : ∀ b, w ∈ P b → P a ⊆ P b) : MaxI P w a :=
  ⟨hw, λ b hb hlt => hlt.2 (h b hb)⟩

/-! ### Modalized questions -/

/-- The question under an existential modal over the base `M`. -/
def diamond (M : W → Set W) (P : α → Set W) : α → Set W :=
  λ a => {w | ∃ w' ∈ M w, w' ∈ P a}

/-- The question under a universal modal over the base `M`. -/
def box (M : W → Set W) (P : α → Set W) : α → Set W :=
  λ a => {w | ∀ w' ∈ M w, w' ∈ P a}

/-- Relativized Exhaustivity for the question `Op M P` built from the non-modalized `P`: in
every accessible world verifying one of the modalized question's true short answers, `P`
satisfies Dayal's presupposition. -/
def RelExh (Op : (W → Set W) → (α → Set W) → α → Set W) (M : W → Set W)
    (P : α → Set W) (w : W) : Prop :=
  ∀ w' ∈ M w, (∃ a, w ∈ Op M P a ∧ w' ∈ P a) → DEP P w'

/-- The generalization for existential modals: the mention-some readings satisfy Relativized
Exhaustivity exactly when the non-modalized question satisfies Dayal's presupposition in every
accessible world where some short answer is true. -/
theorem relExh_diamond_iff (M : W → Set W) (P : α → Set W) (w : W) :
    RelExh diamond M P w ↔ ∀ w' ∈ M w, (trueShort P w').Nonempty → DEP P w' := by
  refine forall₂_congr λ w' hw' => imp_congr_left ⟨?_, ?_⟩
  · rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, ⟨w', hw', ha⟩, ha⟩

/-- The identity modal base, on which both modals return the question itself. -/
def idBase : W → Set W := λ w => {w}

theorem diamond_idBase (P : α → Set W) : diamond idBase P = P := by
  ext a w; simp [diamond, idBase]

theorem box_idBase (P : α → Set W) : box idBase P = P := by
  ext a w; simp [box, idBase]

/-- For a non-modalized question, Relativized Exhaustivity is Dayal's presupposition wherever
the question has a true answer. -/
theorem relExh_id_iff (P : α → Set W) (w : W) :
    RelExh diamond idBase P w ↔ ((trueShort P w).Nonempty → DEP P w) := by
  rw [relExh_diamond_iff]; simp [idBase]

/-! ### Local exhaustification -/

/-- The nucleus exhaustified against the variable alternatives: `a` and no other short
answer. -/
def exh [DecidableEq α] (φ : α → Set W) : α → Set W :=
  λ a => {w | w ∈ φ a ∧ ∀ b, b ≠ a → w ∉ φ b}

/-- An exhaustified question has at most one true short answer. -/
theorem exh_unique [DecidableEq α] {φ : α → Set W} {w : W} {a b : α} (ha : w ∈ exh φ a)
    (hb : w ∈ exh φ b) : a = b :=
  by_contra λ h => ha.2 b (Ne.symm h) hb.1

/-- Hence it satisfies Dayal's presupposition wherever it has a true answer. -/
theorem dep_exh [DecidableEq α] {φ : α → Set W} {w : W} (h : (trueShort (exh φ) w).Nonempty) :
    DEP (exh φ) w := by
  obtain ⟨a, ha⟩ := h
  exact (dep_iff _ _).2 ⟨a, ha, λ b hb => by rw [exh_unique ha hb]⟩

/-- The exhaustified mention-some reading of a *can*-question satisfies Relativized
Exhaustivity on any modal base: the uniqueness it presupposes is existential. -/
theorem relExh_diamond_exh [DecidableEq α] (M : W → Set W) (φ : α → Set W) (w : W) :
    RelExh diamond M (exh φ) w :=
  (relExh_diamond_iff M (exh φ) w).2 λ _ _ h => dep_exh h

/-! ### The committee scenario -/

/-- The worlds of the committee scenario: the evaluation world and two accessible ones. -/
abbrev CW := Fin 3

/-- Andy chairs alone in world 1, Billy alone in world 2. -/
def chair : Bool → Set CW
  | true => {1}
  | false => {2}

/-- The modal base: the evaluation world sees both alternatives. -/
def chairBase : CW → Set CW
  | 0 => {1, 2}
  | w => {w}

/-- The exhaustified mention-some reading of *Who can chair the committee?* has two
max-informative true answers, satisfies Relativized Exhaustivity, and violates Dayal's
presupposition. -/
theorem chair_scenario :
    MaxI (diamond chairBase (exh chair)) 0 true ∧ MaxI (diamond chairBase (exh chair)) 0 false ∧
      RelExh diamond chairBase (exh chair) 0 ∧ ¬ DEP (diamond chairBase (exh chair)) 0 := by
  have h1 : diamond chairBase (exh chair) true = {0, 1} := by
    ext w; fin_cases w <;> simp [diamond, chairBase, exh, chair]
  have h2 : diamond chairBase (exh chair) false = {0, 2} := by
    ext w; fin_cases w <;> simp [diamond, chairBase, exh, chair]
  refine ⟨⟨by simp [h1], ?_⟩, ⟨by simp [h2], ?_⟩, relExh_diamond_exh _ _ _, ?_⟩
  · intro b _ hlt
    cases b <;> simp [h1, h2, Set.ssubset_def, Set.subset_def] at hlt
  · intro b _ hlt
    cases b <;> simp [h1, h2, Set.ssubset_def, Set.subset_def] at hlt
  · rw [dep_iff]
    rintro ⟨a, -, h⟩
    cases a
    · have := h true (by simp [h1]); simp [h1, h2, Set.subset_def] at this
    · have := h false (by simp [h2]); simp [h1, h2, Set.subset_def] at this

/-! ### The chapter scenario -/

/-- The worlds of the chapter scenario: two evaluation worlds and three accessible ones. -/
abbrev AW := Fin 5

/-- The narrow-scope higher-order answers: chapter 1, chapter 2, or either. World 1 assigns
chapter 1, world 2 chapter 2, and world 3 both. -/
def assign : Fin 3 → Set AW
  | 0 => {1, 3}
  | 1 => {2, 3}
  | 2 => {1, 2, 3}

/-- The modal base: world 0 sees the uniqueness-violating world 3, world 4 does not. -/
def assignBase : AW → Set AW
  | 0 => {1, 2, 3}
  | 4 => {1, 2}
  | w => {w}

/-- Dayal's presupposition holds of the modalized question at world 0, where the disjunction
is its only true answer, while Relativized Exhaustivity fails there and holds at world 4:
the local-uniqueness inference of *Which chapter do we have to assign?*. -/
theorem assign_scenario :
    DEP (box assignBase assign) 0 ∧ ¬ RelExh box assignBase assign 0 ∧
      RelExh box assignBase assign 4 := by
  have h0 : box assignBase assign 0 = {1, 3} := by
    ext w; fin_cases w <;> simp [box, assignBase, assign]
  have h1 : box assignBase assign 1 = {2, 3} := by
    ext w; fin_cases w <;> simp [box, assignBase, assign]
  have h2 : box assignBase assign 2 = {0, 1, 2, 3, 4} := by
    ext w; fin_cases w <;> simp [box, assignBase, assign]
  refine ⟨(dep_iff _ _).2 ⟨2, by simp [h2], ?_⟩, ?_, ?_⟩
  · intro b hb
    fin_cases b <;> simp [h0, h1, h2] at hb ⊢
  · intro h
    have := h 3 (by simp [assignBase]) ⟨2, by simp [h2], by simp [assign]⟩
    rw [dep_iff] at this
    obtain ⟨a, ha, hmin⟩ := this
    fin_cases a
    · have := hmin 1 (by simp [assign]); simp [assign, Set.subset_def] at this
    · have := hmin 0 (by simp [assign]); simp [assign, Set.subset_def] at this
    · have := hmin 0 (by simp [assign]); simp [assign, Set.subset_def] at this
  · intro w' hw' _
    simp only [assignBase, Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    rcases hw' with rfl | rfl
    · exact (dep_iff _ _).2 ⟨0, by simp [assign], λ b hb => by
        fin_cases b <;> simp [assign, Set.subset_def] at hb ⊢⟩
    · exact (dep_iff _ _).2 ⟨1, by simp [assign], λ b hb => by
        fin_cases b <;> simp [assign, Set.subset_def] at hb ⊢⟩

end Xiang2022
