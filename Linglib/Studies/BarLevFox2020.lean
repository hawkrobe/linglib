import Linglib.Semantics.Exhaustification.Disjunctive
import Linglib.Semantics.Conditionals.Counterfactual
import Linglib.Semantics.Presupposition.Defs
import Linglib.Logic.Modal.Basic
import Linglib.Data.Examples.BarLevFox2020
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

/-!
# Bar-Lev and Fox 2020: Free choice, simplification, and Innocent Inclusion

Exhaustification with Innocent Inclusion returns the cell of the partition induced by the
alternatives whenever that cell is consistent. Free-choice disjunction `◇(a ∨ b)`, whose
alternatives are `◇a`, `◇b` and `◇(a ∧ b)`, strengthens to `◇a ∧ ◇b ∧ ¬◇(a ∧ b)`; plain `a ∨ b`,
whose conjunctive alternative is the conjunction of the other two, only denies it. `only`
presupposes the includable alternatives, so free choice under `only` projects. Free choice
under a universal quantifier, its negative counterpart, the existential-over-universal case
and *most* with a disjunctive restrictor are one computation over eight alternatives.
Simplification of disjunctive antecedents is the same strengthening over a variably strict
conditional: it fails when the consequent is one of the disjuncts, and an *or both*
antecedent, exhaustified by Hurford's constraint, turns the conjunctive simplification from
excluded into included.

## Main results

* `freeChoice`, `simpleDisjunction`: the modal and the plain disjunction.
* `only_presup`: free choice under `only` is presupposed.
* `universalFreeChoice`, `negativeUniversalFreeChoice`, `freeChoiceOverUniversal`,
  `simplificationMost`: instances of `Exhaustification.exhIEII_quantified`.
* `sda`, `sda_consequent_disjunct`, `orBoth`: simplification, its failure, and the switches.

## References

* [bar-lev-fox-2020]
* [fox-2007]
* [alxatib-2014]
* [chemla-2009]
* [nouwen-2017]
* [mckay-vaninwagen-1977]
* [nute-1980]
* [ciardelli-zhang-champollion-2018]
* [chierchia-fox-spector-2012]
-/

namespace BarLevFox2020

open Exhaustification ModalLogic Presupposition

variable {W : Type*}

/-! ### Free choice and simple disjunction -/

section FreeChoice

variable (R : W → W → Prop) (a b : Set W)

/-- Permission: possibility over the accessibility relation `R`, as a proposition. -/
abbrev poss (p : Set W) : Set W := ◇[R] p

/-- Obligation: necessity over the accessibility relation `R`, as a proposition. -/
abbrev nec (s : Set W) : Set W := □[R] s

/-- The alternatives of `◇(a ∨ b)`: the disjunction replaced by its disjuncts and their
conjunction. -/
def fcAlts : Set (Set W) := {poss R (a ∪ b), poss R a, poss R b, poss R (a ∩ b)}

variable {R a b}

theorem poss_mono {p q : Set W} (h : p ⊆ q) : poss R p ⊆ poss R q :=
  λ _ ⟨v, hv, h'⟩ => ⟨v, hv, h h'⟩

theorem poss_union : poss R (a ∪ b) = poss R a ∪ poss R b :=
  Set.ext λ _ => ⟨λ ⟨v, hv, h⟩ => h.elim (λ h => Or.inl ⟨v, hv, h⟩) (λ h => Or.inr ⟨v, hv, h⟩),
    λ h => h.elim (λ ⟨v, hv, h⟩ => ⟨v, hv, Or.inl h⟩) (λ ⟨v, hv, h⟩ => ⟨v, hv, Or.inr h⟩)⟩

theorem poss_inter_subset : poss R (a ∩ b) ⊆ poss R a ∩ poss R b :=
  λ _ ⟨v, hv, h⟩ => ⟨⟨v, hv, h.1⟩, ⟨v, hv, h.2⟩⟩

theorem poss_compl {s : Set W} : poss R sᶜ = (nec R s)ᶜ :=
  Set.ext λ _ => ⟨λ ⟨v, hv, h⟩ hb => h (hb v hv),
    λ h => let ⟨v, hv⟩ := not_forall.1 h
      ⟨v, (Classical.not_imp.1 hv).1, (Classical.not_imp.1 hv).2⟩⟩

variable (h₁ : ∃ w ∈ poss R a, w ∉ poss R b) (h₂ : ∃ w ∈ poss R b, w ∉ poss R a)
  (h : ∃ w ∈ poss R a ∩ poss R b, w ∉ poss R (a ∩ b))
include h₁ h₂ h

/-- Free choice: given a world permitting only `a`, one permitting only `b`, and one
permitting each but not both, `◇(a ∨ b)` strengthens to `◇a ∧ ◇b ∧ ¬◇(a ∧ b)`. -/
theorem freeChoice :
    exhIEII (fcAlts R a b) (poss R (a ∪ b)) = (poss R a ∩ poss R b) \ poss R (a ∩ b) := by
  rw [fcAlts, exhIEII_pair poss_union.le
    (h₁.imp λ _ h => ⟨⟨poss_mono Set.subset_union_left h.1, h.1⟩,
      λ h' => h.2 (h'.elim id (λ h' => (poss_inter_subset h').2))⟩)
    (h₂.imp λ _ h => ⟨⟨poss_mono Set.subset_union_right h.1, h.1⟩,
      λ h' => h.2 (h'.elim id (λ h' => (poss_inter_subset h').1))⟩)
    (h.imp λ _ h => ⟨⟨⟨poss_mono Set.subset_union_left h.1.1, h.1.1⟩, h.1.2⟩, h.2⟩),
    Set.inter_assoc, Set.inter_eq_right.2 λ _ h => poss_mono Set.subset_union_left h.1]

/-- The includable alternatives of `◇(a ∨ b)` are the prejacent and the disjunct
alternatives. -/
theorem II_fcAlts : II (fcAlts R a b) (poss R (a ∪ b)) = {poss R (a ∪ b), poss R a, poss R b} :=
  II_pair poss_union.le
    (h₁.imp λ _ h => ⟨⟨poss_mono Set.subset_union_left h.1, h.1⟩,
      λ h' => h.2 (h'.elim id (λ h' => (poss_inter_subset h').2))⟩)
    (h₂.imp λ _ h => ⟨⟨poss_mono Set.subset_union_right h.1, h.1⟩,
      λ h' => h.2 (h'.elim id (λ h' => (poss_inter_subset h').1))⟩)
    (h.imp λ _ h => ⟨⟨⟨poss_mono Set.subset_union_left h.1.1, h.1.1⟩, h.1.2⟩, h.2⟩)

omit h₁ h₂ h in
/-- Without the modal the conjunctive alternative is the conjunction of the disjunct
alternatives: exhaustification denies it and includes neither disjunct. -/
theorem simpleDisjunction (h₁ : ∃ w ∈ a, w ∉ b) (h₂ : ∃ w ∈ b, w ∉ a) :
    exhIEII {a ∪ b, a, b, a ∩ b} (a ∪ b) = (a ∪ b) \ (a ∩ b) :=
  exhIEII_pair_inter le_rfl (h₁.imp λ _ h => ⟨⟨Or.inl h.1, h.1⟩, h.2⟩)
    (h₂.imp λ _ h => ⟨⟨Or.inr h.1, h.1⟩, h.2⟩)

omit h₁ h₂ h in
/-- The cell of simple disjunction is contradictory, so cell identification does not apply. -/
theorem simpleDisjunction_cell (h₁ : ∃ w ∈ a, w ∉ b) (h₂ : ∃ w ∈ b, w ∉ a) :
    cell {a ∪ b, a, b, a ∩ b} (a ∪ b) = ∅ :=
  cell_pair_inter le_rfl (h₁.imp λ _ h => ⟨⟨Or.inl h.1, h.1⟩, h.2⟩)
    (h₂.imp λ _ h => ⟨⟨Or.inr h.1, h.1⟩, h.2⟩)

end FreeChoice

/-! ### `only` -/

/-- `only` presupposes the innocently includable alternatives and asserts the prejacent with
the innocently excludable ones denied. -/
def only (ALT : Set (Set W)) (φ : Set W) : PartialProp W where
  presup w := ∀ r ∈ II ALT φ, r w
  assertion w := φ w ∧ ∀ q, IsInnocentlyExcludable ALT φ q → ¬ q w

/-- Free choice under `only` is presupposed: `only ◇(a ∨ b)` presupposes `◇a` and `◇b`. -/
theorem only_presup {R : W → W → Prop} {a b : Set W} (h₁ : ∃ w ∈ poss R a, w ∉ poss R b)
    (h₂ : ∃ w ∈ poss R b, w ∉ poss R a) (h : ∃ w ∈ poss R a ∩ poss R b, w ∉ poss R (a ∩ b))
    (w : W) : (only (fcAlts R a b) (poss R (a ∪ b))).presup w ↔ w ∈ poss R a ∩ poss R b := by
  simp only [only, II_fcAlts h₁ h₂ h, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  exact ⟨λ h => ⟨h.2.1, h.2.2⟩, λ h => ⟨poss_mono Set.subset_union_left h.1, h.1, h.2⟩⟩

/-! ### Simplification of disjunctive antecedents -/

section Simplification

open Semantics.Conditionals Semantics.Conditionals.Counterfactual

variable [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W) (p q r : W → Prop)
  [DecidablePred p] [DecidablePred q] [DecidablePred r]

/-- The variably strict conditional as a proposition. -/
abbrev conditional (A B : W → Prop) [DecidablePred A] [DecidablePred B] : Set W :=
  {w | universalCounterfactual sim A B w}

/-- The alternatives of `(p ∨ q) → r`: the antecedent's disjunction replaced by its disjuncts
and their conjunction. -/
def sdaAlts : Set (Set W) :=
  {conditional sim (λ v => p v ∨ q v) r, conditional sim p r, conditional sim q r,
    conditional sim (λ v => p v ∧ q v) r}

variable {sim p q r}

/-- Simplification of disjunctive antecedents: over a total similarity ordering, given a world
where only the first simplification holds, one where only the second does, and one where both
hold but the conjunctive one fails, `(p ∨ q) → r` strengthens to
`(p → r) ∧ (q → r) ∧ ¬((p ∧ q) → r)`. -/
theorem sda (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h₁ : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r,
      w ∉ conditional sim q r ∪ conditional sim (λ v => p v ∧ q v) r)
    (h₂ : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r,
      w ∉ conditional sim p r ∪ conditional sim (λ v => p v ∧ q v) r)
    (h : ∃ w ∈ conditional sim p r ∩ conditional sim q r,
      w ∉ conditional sim (λ v => p v ∧ q v) r) :
    exhIEII (sdaAlts sim p q r) (conditional sim (λ v => p v ∨ q v) r) =
      (conditional sim p r ∩ conditional sim q r) \ conditional sim (λ v => p v ∧ q v) r := by
  have hsub : conditional sim p r ∩ conditional sim q r ⊆ conditional sim (λ v => p v ∨ q v) r :=
    λ _ h => universalCounterfactual_or_of sim h.1 h.2
  have hcov : conditional sim (λ v => p v ∨ q v) r ⊆ conditional sim p r ∪ conditional sim q r :=
    λ _ h => universalCounterfactual_or sim htot h
  rw [sdaAlts, exhIEII_pair hcov
    (h₁.imp λ w h => ⟨⟨h.1, (hcov h.1).resolve_right λ h' => h.2 (Or.inl h')⟩, h.2⟩)
    (h₂.imp λ w h => ⟨⟨h.1, (hcov h.1).resolve_left λ h' => h.2 (Or.inl h')⟩, h.2⟩)
    (h.imp λ w h => ⟨⟨⟨hsub h.1, h.1.1⟩, h.1.2⟩, h.2⟩), Set.inter_assoc, Set.inter_eq_right.2 hsub]

/-- Simplification fails when the consequent is one of the disjuncts (71): the other
simplification is the only contingent alternative, so it is excluded. -/
theorem sda_consequent_disjunct
    (h : ∃ w ∈ conditional sim (λ v => p v ∨ q v) p, w ∉ conditional sim q p) :
    exhIEII (sdaAlts sim p q p) (conditional sim (λ v => p v ∨ q v) p) =
      conditional sim (λ v => p v ∨ q v) p \ conditional sim q p := by
  refine exhIEII_eq_diff_of_forall_subset (by simp [sdaAlts]) (λ x hx hne => ?_) h
  simp only [sdaAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_rfl
  · exact λ _ _ => universalCounterfactual_of_imp sim λ _ h => h
  · exact absurd rfl hne
  · exact λ _ _ => universalCounterfactual_of_imp sim λ _ h => h.1

variable (sim p q r) in
/-- The alternatives of `(Exh(p ∨ q) ∨ (p ∧ q)) → r`, the *or both* antecedent parsed with an
embedded exhaustifier by Hurford's constraint (80): the antecedent's three cells. -/
def orBothAlts : Set (Set W) :=
  {conditional sim (λ v => p v ∨ q v) r, conditional sim (λ v => p v ∧ ¬ q v) r,
    conditional sim (λ v => q v ∧ ¬ p v) r, conditional sim (λ v => p v ∧ q v) r}

/-- With the antecedent's cells as alternatives nothing is excludable and, given a world
verifying each cell's conditional alone and one verifying all three, everything is included:
`(p ∨ q) → r` asserts the conjunctive conditional it denied under `sdaAlts` (82). -/
theorem orBoth (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h₁ : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r ∩ conditional sim (λ v => p v ∧ ¬ q v) r,
      w ∉ conditional sim (λ v => q v ∧ ¬ p v) r ∪ conditional sim (λ v => p v ∧ q v) r)
    (h₂ : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r ∩ conditional sim (λ v => q v ∧ ¬ p v) r,
      w ∉ conditional sim (λ v => p v ∧ ¬ q v) r ∪ conditional sim (λ v => p v ∧ q v) r)
    (h₃ : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r ∩ conditional sim (λ v => p v ∧ q v) r,
      w ∉ conditional sim (λ v => p v ∧ ¬ q v) r ∪ conditional sim (λ v => q v ∧ ¬ p v) r)
    (h : ∃ w ∈ conditional sim (λ v => p v ∨ q v) r, w ∈ conditional sim (λ v => p v ∧ ¬ q v) r ∧
      w ∈ conditional sim (λ v => q v ∧ ¬ p v) r ∧ w ∈ conditional sim (λ v => p v ∧ q v) r) :
    exhIEII (orBothAlts sim p q r) (conditional sim (λ v => p v ∨ q v) r) =
      conditional sim (λ v => p v ∨ q v) r ∩ conditional sim (λ v => p v ∧ ¬ q v) r ∩
        conditional sim (λ v => q v ∧ ¬ p v) r ∩ conditional sim (λ v => p v ∧ q v) r := by
  have hcov : conditional sim (λ v => p v ∨ q v) r ⊆
      ⋃ i, ![conditional sim (λ v => p v ∧ ¬ q v) r, conditional sim (λ v => q v ∧ ¬ p v) r,
        conditional sim (λ v => p v ∧ q v) r] i := by
    intro w hw
    have hw' := (universalCounterfactual_congr sim (B := λ v => (p v ∧ ¬ q v) ∨
      ((q v ∧ ¬ p v) ∨ (p v ∧ q v))) (λ v => by tauto)).1 hw
    rcases universalCounterfactual_or sim htot hw' with h | h
    · exact Set.mem_iUnion.2 ⟨0, h⟩
    rcases universalCounterfactual_or sim htot h with h | h
    · exact Set.mem_iUnion.2 ⟨1, h⟩
    · exact Set.mem_iUnion.2 ⟨2, h⟩
  have hA : orBothAlts sim p q r = insert (conditional sim (λ v => p v ∨ q v) r)
      (Set.range ![conditional sim (λ v => p v ∧ ¬ q v) r, conditional sim (λ v => q v ∧ ¬ p v) r,
        conditional sim (λ v => p v ∧ q v) r]) := by
    simp only [orBothAlts, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.union_empty]
  rw [hA, exhIEII_insert_range hcov ?_ ?_]
  · ext w
    simp [Set.mem_iInter, Fin.forall_fin_succ, and_assoc]
  · intro i
    fin_cases i
    · exact h₁.imp λ w h => ⟨h.1, λ j hj hw => by
        fin_cases j
        · exact hj rfl
        · exact h.2 (Or.inl hw)
        · exact h.2 (Or.inr hw)⟩
    · exact h₂.imp λ w h => ⟨h.1, λ j hj hw => by
        fin_cases j
        · exact h.2 (Or.inl hw)
        · exact hj rfl
        · exact h.2 (Or.inr hw)⟩
    · exact h₃.imp λ w h => ⟨h.1, λ j hj hw => by
        fin_cases j
        · exact h.2 (Or.inl hw)
        · exact h.2 (Or.inr hw)
        · exact hj rfl⟩
  · exact h.imp λ w h => ⟨h.1, λ i => by fin_cases i <;> simp [h.2.1, h.2.2.1, h.2.2.2]⟩

end Simplification

/-! ### The switches -/

/-- A world of [ciardelli-zhang-champollion-2018]'s scenario: whether each switch is up, and
the wiring of the light. -/
structure Switch where
  up₁ : Bool
  up₂ : Bool
  light : Bool → Bool → Bool
  deriving DecidableEq, Fintype

namespace Switch

open Semantics.Conditionals

/-- Worlds with a different wiring are farther than any with the same; among the latter,
distance is the number of switches in another position. -/
def rank (w₀ w : Switch) : ℕ :=
  (if w.light = w₀.light then 0 else 4) + (if w.up₁ = w₀.up₁ then 0 else 1) +
    (if w.up₂ = w₀.up₂ then 0 else 1)

/-- The similarity ordering by `rank`. -/
def sim : SimilarityOrdering Switch := .ofRank rank

theorem sim_total (w₀ w₁ w₂ : Switch) : sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁ :=
  le_total _ _

/-- Switch A is down. -/
def down₁ (w : Switch) : Prop := w.up₁ = false

/-- Switch B is down. -/
def down₂ (w : Switch) : Prop := w.up₂ = false

/-- The light is off. -/
def off (w : Switch) : Prop := w.light w.up₁ w.up₂ = false

instance : DecidablePred down₁ := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred down₂ := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred off := λ _ => inferInstanceAs (Decidable (_ = _))

/-- Both switches up, and the light on exactly when the switches agree. -/
def actual : Switch := ⟨true, true, λ x y => x == y⟩

open Semantics.Conditionals.Counterfactual

/-- *If switch A or switch B were down, the light would be off* (76) is true in the scenario:
its strengthening asserts both simplifications and denies the conjunctive one. -/
theorem sda_actual :
    actual ∈ exhIEII (sdaAlts sim down₁ down₂ off)
      (conditional sim (λ v => down₁ v ∨ down₂ v) off) := by
  rw [sda sim_total ⟨⟨false, true, λ x y => !x && !y⟩, by decide⟩
    ⟨⟨true, false, λ x y => !x && !y⟩, by decide⟩ ⟨actual, by decide⟩]
  decide

/-- *If switch A or switch B or both were down, the light would be off* (78) is false in the
scenario: its strengthening asserts the conjunctive conditional. -/
theorem orBoth_actual :
    actual ∉ exhIEII (orBothAlts sim down₁ down₂ off)
      (conditional sim (λ v => down₁ v ∨ down₂ v) off) := by
  rw [orBoth sim_total ⟨⟨false, true, λ x y => x || !y⟩, by decide⟩
    ⟨⟨true, false, λ x y => y || !x⟩, by decide⟩ ⟨⟨false, false, λ x y => x || y⟩, by decide⟩
    ⟨⟨true, true, λ x y => x && y⟩, by decide⟩]
  decide

end Switch

/-! ### Free choice under quantifiers -/

section Quantified

variable {D : Type*} [Nonempty D] (P Q B : D → Set W)

/-- The alternatives of `∀x(Px ∨ Qx)` (41): the disjunction replaced by its disjuncts and by
their conjunctive counterpart `B`, and the universal by the existential. -/
def universalAlts : Set (Set W) :=
  {⋂ x, P x ∪ Q x, ⋂ x, P x, ⋂ x, Q x, ⋂ x, B x, ⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, B x}

variable {P Q B}

/-- Universal free choice (44): given a world where every individual has `P` and none `Q`, one
the other way round, one where each has exactly one and both occur, and one where every
individual has `P` and `Q` but none `B`, `∀x(Px ∨ Qx)` strengthens to
`∀x Px ∧ ∀x Qx ∧ ¬∃x Bx`. With `Px = ◇px` and `Bx = ◇(px ∧ qx)` this is (36). -/
theorem universalFreeChoice (hB : ∀ x, B x ⊆ P x ∩ Q x)
    (h₁ : ∃ w, (∀ x, w ∈ P x) ∧ ∀ x, w ∉ Q x) (h₂ : ∃ w, (∀ x, w ∈ Q x) ∧ ∀ x, w ∉ P x)
    (h₃ : ∃ w, (∀ x, w ∈ P x ↔ w ∉ Q x) ∧ (∃ x, w ∈ P x) ∧ ∃ x, w ∈ Q x)
    (h : ∃ w, (∀ x, w ∈ P x) ∧ (∀ x, w ∈ Q x) ∧ ∀ x, w ∉ B x) :
    exhIEII (universalAlts P Q B) (⋂ x, P x ∪ Q x) = ((⋂ x, P x) ∩ ⋂ x, Q x) \ ⋃ x, B x := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  rw [universalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_union,
      not_or, not_exists]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨-, hP⟩, hQ⟩, -⟩, -⟩, -⟩, -, hB'⟩
      exact ⟨⟨hP, hQ⟩, hB'⟩
    · rintro ⟨⟨hP, hQ⟩, hB'⟩
      exact ⟨⟨⟨⟨⟨⟨λ x => Or.inl (hP x), hP⟩, hQ⟩, ⟨x₀, Or.inl (hP x₀)⟩⟩, ⟨x₀, hP x₀⟩⟩,
        ⟨x₀, hQ x₀⟩⟩, λ hx => hB' x₀ (hx x₀), hB'⟩
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union] at hw ⊢
    by_cases hq : ∀ x, w ∉ Q x
    · exact Or.inl ⟨λ x => (hw x).resolve_right (hq x), ⟨x₀, hw x₀⟩,
        ⟨x₀, (hw x₀).resolve_right (hq x₀)⟩⟩
    push Not at hq
    obtain ⟨y, hy⟩ := hq
    by_cases hp : ∀ x, w ∉ P x
    · exact Or.inr (Or.inl ⟨λ x => (hw x).resolve_left (hp x), ⟨x₀, hw x₀⟩, ⟨y, hy⟩⟩)
    push Not at hp
    obtain ⟨z, hz⟩ := hp
    exact Or.inr (Or.inr ⟨⟨x₀, hw x₀⟩, ⟨z, hz⟩, ⟨y, hy⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨λ x => Or.inl (hP x), hP, ⟨x₀, Or.inl (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, λ h => hQ x₀ (hB x₀ h).2⟩, hQ, λ x h => hQ x (hB x h).2⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨λ x => Or.inr (hQ x), hQ, ⟨x₀, Or.inr (hQ x₀)⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hP x₀⟩,
      ⟨x₀, λ h => hP x₀ (hB x₀ h).1⟩, hP, λ x h => hP x (hB x h).1⟩
  · obtain ⟨w, hPQ, ⟨y, hy⟩, ⟨z, hz⟩⟩ := h₃
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    refine ⟨λ x => by by_cases h : w ∈ P x; exacts [Or.inl h, Or.inr (not_not.1 (mt (hPQ x).2 h))],
      ⟨y, Or.inl hy⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨z, (hPQ z).not.2 (not_not.2 hz)⟩, ⟨y, (hPQ y).1 hy⟩,
      ⟨y, λ h => (hPQ y).1 hy (hB y h).2⟩, λ x h => (hPQ x).1 (hB x h).1 (hB x h).2⟩
  · obtain ⟨w, hP, hQ, hB'⟩ := h
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨λ x => Or.inl (hP x), hP, hQ, ⟨x₀, Or.inl (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, hB' x₀⟩, hB'⟩

section Negative

variable (R : W → W → Prop) (p q : D → Set W)

/-- The alternatives of `¬∃x □(px ∧ qx)`, *no student is required to solve both* (46): the
conjunction replaced by its conjuncts and their disjunction, *no* by *not every*. -/
def negativeUniversalAlts : Set (Set W) :=
  {(⋃ x, nec R (p x ∩ q x))ᶜ, (⋃ x, nec R (p x))ᶜ, (⋃ x, nec R (q x))ᶜ,
    (⋃ x, nec R (p x ∪ q x))ᶜ, (⋂ x, nec R (p x ∩ q x))ᶜ, (⋂ x, nec R (p x))ᶜ,
    (⋂ x, nec R (q x))ᶜ, (⋂ x, nec R (p x ∪ q x))ᶜ}

variable {R p q}

theorem mem_nec_inter {s t : Set W} {w : W} : w ∈ nec R (s ∩ t) ↔ w ∈ nec R s ∧ w ∈ nec R t :=
  ⟨λ h => ⟨λ v hv => (h v hv).1, λ v hv => (h v hv).2⟩, λ h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩

theorem nec_mono {s t : Set W} (h : s ⊆ t) : nec R s ⊆ nec R t := λ _ h' v hv => h (h' v hv)

/-- Negative universal free choice (47): the alternatives of `¬∃x □(px ∧ qx)` stand in the
entailment pattern of universal free choice, so with the corresponding worlds it strengthens
to `¬∃x □px ∧ ¬∃x □qx ∧ ∀x □(px ∨ qx)`. -/
theorem negativeUniversalFreeChoice
    (h₁ : ∃ w, (∀ x, w ∉ nec R (p x)) ∧ ∀ x, w ∈ nec R (q x))
    (h₂ : ∃ w, (∀ x, w ∉ nec R (q x)) ∧ ∀ x, w ∈ nec R (p x))
    (h₃ : ∃ w, (∀ x, w ∈ nec R (p x ∪ q x)) ∧ (∀ x, w ∉ nec R (p x ∩ q x)) ∧
      (∃ x, w ∈ nec R (p x)) ∧ (∃ x, w ∈ nec R (q x)) ∧ (∃ x, w ∉ nec R (p x)) ∧
      ∃ x, w ∉ nec R (q x))
    (h : ∃ w, (∀ x, w ∉ nec R (p x)) ∧ (∀ x, w ∉ nec R (q x)) ∧ ∀ x, w ∈ nec R (p x ∪ q x)) :
    exhIEII (negativeUniversalAlts R p q) (⋃ x, nec R (p x ∩ q x))ᶜ =
      ((⋃ x, nec R (p x))ᶜ ∩ (⋃ x, nec R (q x))ᶜ) ∩ ⋂ x, nec R (p x ∪ q x) := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  have hpq : ∀ {w : W} {x : D}, w ∉ nec R (p x) → w ∉ nec R (p x ∩ q x) :=
    λ h h' => h (mem_nec_inter.1 h').1
  have hqp : ∀ {w : W} {x : D}, w ∉ nec R (q x) → w ∉ nec R (p x ∩ q x) :=
    λ h h' => h (mem_nec_inter.1 h').2
  rw [negativeUniversalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
      Set.mem_iInter, Set.mem_iUnion, not_or, not_exists, not_forall, not_not]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨-, hP⟩, hQ⟩, -⟩, -⟩, -⟩, -, hPQ⟩
      exact ⟨⟨hP, hQ⟩, hPQ⟩
    · rintro ⟨⟨hP, hQ⟩, hPQ⟩
      exact ⟨⟨⟨⟨⟨⟨λ x => hpq (hP x), hP⟩, hQ⟩, ⟨x₀, hpq (hP x₀)⟩⟩, ⟨x₀, hP x₀⟩⟩, ⟨x₀, hQ x₀⟩⟩,
        ⟨x₀, hPQ x₀⟩, hPQ⟩
  · intro w hw
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall] at hw ⊢
    by_cases hp : ∀ x, w ∉ nec R (p x)
    · exact Or.inl ⟨hp, ⟨x₀, hw x₀⟩, ⟨x₀, hp x₀⟩⟩
    push Not at hp
    obtain ⟨y, hy⟩ := hp
    by_cases hq : ∀ x, w ∉ nec R (q x)
    · exact Or.inr (Or.inl ⟨hq, ⟨x₀, hw x₀⟩, ⟨x₀, hq x₀⟩⟩)
    push Not at hq
    obtain ⟨z, hz⟩ := hq
    exact Or.inr (Or.inr ⟨⟨x₀, hw x₀⟩, ⟨z, λ h => hw z (mem_nec_inter.2 ⟨h, hz⟩)⟩,
      ⟨y, λ h => hw y (mem_nec_inter.2 ⟨hy, h⟩)⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨λ x => hpq (hP x), hP, ⟨x₀, hpq (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, nec_mono Set.subset_union_right (hQ x₀)⟩, hQ,
      λ x => nec_mono Set.subset_union_right (hQ x)⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨λ x => hqp (hQ x), hQ, ⟨x₀, hqp (hQ x₀)⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hP x₀⟩,
      ⟨x₀, nec_mono Set.subset_union_left (hP x₀)⟩, hP,
      λ x => nec_mono Set.subset_union_left (hP x)⟩
  · obtain ⟨w, hPQ, hB, ⟨y, hy⟩, ⟨z, hz⟩, ⟨y', hy'⟩, ⟨z', hz'⟩⟩ := h₃
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨hB, ⟨x₀, hB x₀⟩, ⟨y', hy'⟩, ⟨z', hz'⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨x₀, hPQ x₀⟩, hPQ⟩
  · obtain ⟨w, hP, hQ, hPQ⟩ := h
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨λ x => hpq (hP x), hP, hQ, ⟨x₀, hpq (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hPQ x₀⟩,
      hPQ⟩

end Negative

section OverUniversal

variable (R : W → W → Prop) (p q : D → Set W)

/-- The alternatives of `◇∀x(px ∨ qx)` (55). -/
def overUniversalAlts : Set (Set W) :=
  {poss R (⋂ x, p x ∪ q x), poss R (⋂ x, p x), poss R (⋂ x, q x), poss R (⋂ x, p x ∩ q x),
    poss R (⋃ x, p x ∪ q x), poss R (⋃ x, p x), poss R (⋃ x, q x), poss R (⋃ x, p x ∩ q x)}

variable {R p q}

/-- Free choice with the existential modal over the universal (57), [nouwen-2017]'s case:
given the corresponding worlds, `◇∀x(px ∨ qx)` strengthens to `◇∀x px ∧ ◇∀x qx ∧ ¬◇∃x(px ∧ qx)`,
although `◇∀` does not distribute over disjunction. -/
theorem freeChoiceOverUniversal
    (h₁ : ∃ w ∈ poss R (⋂ x, p x), w ∉ poss R (⋃ x, q x))
    (h₂ : ∃ w ∈ poss R (⋂ x, q x), w ∉ poss R (⋃ x, p x))
    (h₃ : ∃ w ∈ poss R (⋂ x, p x ∪ q x) ∩ poss R (⋃ x, p x) ∩ poss R (⋃ x, q x),
      w ∉ poss R (⋂ x, p x) ∪ poss R (⋂ x, q x) ∪ poss R (⋃ x, p x ∩ q x))
    (h : ∃ w ∈ poss R (⋂ x, p x) ∩ poss R (⋂ x, q x), w ∉ poss R (⋃ x, p x ∩ q x)) :
    exhIEII (overUniversalAlts R p q) (poss R (⋂ x, p x ∪ q x)) =
      (poss R (⋂ x, p x) ∩ poss R (⋂ x, q x)) \ poss R (⋃ x, p x ∩ q x) := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  have hφ : poss R (⋂ x, p x) ⊆ poss R (⋂ x, p x ∪ q x) :=
    poss_mono (Set.iInter_mono λ x => Set.subset_union_left)
  have hφ' : poss R (⋂ x, q x) ⊆ poss R (⋂ x, p x ∪ q x) :=
    poss_mono (Set.iInter_mono λ x => Set.subset_union_right)
  have he : poss R (⋂ x, p x) ⊆ poss R (⋃ x, p x ∪ q x) :=
    poss_mono λ w h => Set.mem_iUnion.2 ⟨x₀, Or.inl (Set.mem_iInter.1 h x₀)⟩
  have he₁ : poss R (⋂ x, p x) ⊆ poss R (⋃ x, p x) :=
    poss_mono λ w h => Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have he₂ : poss R (⋂ x, q x) ⊆ poss R (⋃ x, q x) :=
    poss_mono λ w h => Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have hsb : poss R (⋂ x, p x ∩ q x) ⊆ poss R (⋃ x, p x ∩ q x) :=
    poss_mono λ w h => Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have hbp : poss R (⋃ x, p x ∩ q x) ⊆ poss R (⋃ x, p x) :=
    poss_mono (Set.iUnion_mono λ x => Set.inter_subset_left)
  have hbq : poss R (⋃ x, p x ∩ q x) ⊆ poss R (⋃ x, q x) :=
    poss_mono (Set.iUnion_mono λ x => Set.inter_subset_right)
  rw [overUniversalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, not_or]
    exact ⟨λ h => ⟨⟨h.1.1.1.1.1.2, h.1.1.1.1.2⟩, h.2.2⟩,
      λ h => ⟨⟨⟨⟨⟨⟨hφ h.1.1, h.1.1⟩, h.1.2⟩, he h.1.1⟩, he₁ h.1.1⟩, he₂ h.1.2⟩,
        λ h' => h.2 (hsb h'), h.2⟩⟩
  · rintro w ⟨v, hv, hvpq⟩
    have hvpq' := λ x => Set.mem_iInter.1 hvpq x
    by_cases hq : ∀ x, v ∉ q x
    · exact Or.inl ⟨⟨v, hv, Set.mem_iInter.2 λ x => (hvpq' x).resolve_right (hq x)⟩,
        ⟨v, hv, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩⟩,
        ⟨v, hv, Set.mem_iUnion.2 ⟨x₀, (hvpq' x₀).resolve_right (hq x₀)⟩⟩⟩
    push Not at hq
    obtain ⟨y, hy⟩ := hq
    by_cases hp : ∀ x, v ∉ p x
    · exact Or.inr (Or.inl ⟨⟨v, hv, Set.mem_iInter.2 λ x => (hvpq' x).resolve_left (hp x)⟩,
        ⟨v, hv, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩⟩, ⟨v, hv, Set.mem_iUnion.2 ⟨y, hy⟩⟩⟩)
    push Not at hp
    obtain ⟨z, hz⟩ := hp
    exact Or.inr (Or.inr ⟨⟨v, hv, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩⟩,
      ⟨v, hv, Set.mem_iUnion.2 ⟨z, hz⟩⟩, ⟨v, hv, Set.mem_iUnion.2 ⟨y, hy⟩⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    exact ⟨w, hφ hP, hP, he hP, he₁ hP, λ h => hQ (he₂ h), λ h => hQ (hbq (hsb h)), hQ,
      λ h => hQ (hbq h)⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    exact ⟨w, hφ' hQ, hQ, poss_mono (Set.iUnion_mono λ x => Set.subset_union_right) (he₂ hQ),
      he₂ hQ, λ h => hP (he₁ h), λ h => hP (hbp (hsb h)), hP, λ h => hP (hbp h)⟩
  · obtain ⟨w, ⟨⟨hPQ, hP⟩, hQ⟩, hn⟩ := h₃
    simp only [Set.mem_union, not_or] at hn
    exact ⟨w, hPQ, poss_mono (Set.iUnion_mono λ x => Set.subset_union_left) hP, hP, hQ, hn.1.1,
      hn.1.2, λ h => hn.2 (hsb h), hn.2⟩
  · obtain ⟨w, ⟨hP, hQ⟩, hB⟩ := h
    exact ⟨w, hφ hP, hP, hQ, he hP, he₁ hP, he₂ hQ, λ h => hB (hsb h), hB⟩

end OverUniversal

end Quantified

/-! ### Simplification with *most* -/

section Most

variable {D : Type*} [DecidableEq D]

/-- `most(P)(S)`: more than half of `P` lies in `S` (86). -/
def Most (P S : Finset D) : Prop := P.card < 2 * (P ∩ S).card

/-- `some(P)(S)`: `P` and `S` overlap. -/
def Overlaps (P S : Finset D) : Prop := (P ∩ S).Nonempty

variable {P Q S : Finset D}

theorem Most.overlaps (h : Most P S) : Overlaps P S :=
  Finset.card_pos.1 (by unfold Most at h; omega)

theorem Overlaps.of_inter_left (h : Overlaps (P ∩ Q) S) : Overlaps P S :=
  h.mono (Finset.inter_subset_inter_right Finset.inter_subset_left)

theorem Overlaps.of_inter_right (h : Overlaps (P ∩ Q) S) : Overlaps Q S :=
  h.mono (Finset.inter_subset_inter_right Finset.inter_subset_right)

theorem overlaps_union_iff : Overlaps (P ∪ Q) S ↔ Overlaps P S ∨ Overlaps Q S := by
  simp only [Overlaps, Finset.union_inter_distrib_right, Finset.union_nonempty]

/-- *Most* is not monotone in its restrictor, but a restrictor that adds nothing to the scope
can be dropped. -/
theorem Most.of_union (h : Most (P ∪ Q) S) (hQ : ¬ Overlaps Q S) : Most P S := by
  have h₁ : (P ∪ Q) ∩ S = P ∩ S := by
    rw [Finset.union_inter_distrib_right, Finset.not_nonempty_iff_eq_empty.1 hQ,
      Finset.union_empty]
  have h₂ := Finset.card_le_card (Finset.subset_union_left (s₁ := P) (s₂ := Q))
  unfold Most at h ⊢
  rw [h₁] at h
  omega

theorem Most.of_union_right (h : Most (P ∪ Q) S) (hP : ¬ Overlaps P S) : Most Q S :=
  (Finset.union_comm P Q ▸ h).of_union hP

variable (P Q S : W → Finset D)

/-- The alternatives of `most(P ∪ Q)(S)` (87): the disjunctive restrictor replaced by its
disjuncts and their intersection, and *most* by *some*. -/
def mostAlts : Set (Set W) :=
  {{w | Most (P w ∪ Q w) (S w)}, {w | Most (P w) (S w)}, {w | Most (Q w) (S w)},
    {w | Most (P w ∩ Q w) (S w)}, {w | Overlaps (P w ∪ Q w) (S w)}, {w | Overlaps (P w) (S w)},
    {w | Overlaps (Q w) (S w)}, {w | Overlaps (P w ∩ Q w) (S w)}}

variable {P Q S}

/-- Simplification with *most* (89): given a world where most of `P ∪ Q` and most of `P` are in
`S` but nothing of `Q` is, one the other way round, one where most of `P ∪ Q` but of neither
`P` nor `Q` is, and one where most of each is but nothing of `P ∩ Q`, `most(P ∪ Q)(S)`
strengthens to `most(P)(S) ∧ most(Q)(S) ∧ ¬some(P ∩ Q)(S)`. -/
theorem simplificationMost
    (h₁ : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (P w) (S w) ∧ ¬ Overlaps (Q w) (S w))
    (h₂ : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (Q w) (S w) ∧ ¬ Overlaps (P w) (S w))
    (h₃ : ∃ w, Most (P w ∪ Q w) (S w) ∧ ¬ Most (P w) (S w) ∧ ¬ Most (Q w) (S w) ∧
      Overlaps (P w) (S w) ∧ Overlaps (Q w) (S w) ∧ ¬ Overlaps (P w ∩ Q w) (S w))
    (h : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (P w) (S w) ∧ Most (Q w) (S w) ∧
      ¬ Overlaps (P w ∩ Q w) (S w)) :
    exhIEII (mostAlts P Q S) {w | Most (P w ∪ Q w) (S w)} =
      ({w | Most (P w ∪ Q w) (S w)} ∩ {w | Most (P w) (S w)} ∩ {w | Most (Q w) (S w)}) \
        {w | Overlaps (P w ∩ Q w) (S w)} := by
  rw [mostAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
    exact ⟨λ h => ⟨⟨⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩, h.1.1.1.1.2⟩, h.2.2⟩,
      λ h => ⟨⟨⟨⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.1.1.1.overlaps⟩, h.1.1.2.overlaps⟩,
        h.1.2.overlaps⟩, λ h' => h.2 h'.overlaps, h.2⟩⟩
  · intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rcases overlaps_union_iff.1 hw.overlaps with hP | hQ
    · by_cases hQ : Overlaps (Q w) (S w)
      · exact Or.inr (Or.inr ⟨hw.overlaps, hP, hQ⟩)
      · exact Or.inl ⟨hw.of_union hQ, hw.overlaps, hP⟩
    · by_cases hP : Overlaps (P w) (S w)
      · exact Or.inr (Or.inr ⟨hw.overlaps, hP, hQ⟩)
      · exact Or.inr (Or.inl ⟨hw.of_union_right hP, hw.overlaps, hQ⟩)
  · obtain ⟨w, hPQ, hP, hQ⟩ := h₁
    exact ⟨w, hPQ, hP, hPQ.overlaps, hP.overlaps, λ h => hQ h.overlaps,
      λ h => hQ h.overlaps.of_inter_right, hQ, λ h => hQ h.of_inter_right⟩
  · obtain ⟨w, hPQ, hQ, hP⟩ := h₂
    exact ⟨w, hPQ, hQ, hPQ.overlaps, hQ.overlaps, λ h => hP h.overlaps,
      λ h => hP h.overlaps.of_inter_left, hP, λ h => hP h.of_inter_left⟩
  · obtain ⟨w, hPQ, hP, hQ, hP', hQ', hB⟩ := h₃
    exact ⟨w, hPQ, hPQ.overlaps, hP', hQ', hP, hQ, λ h => hB h.overlaps, hB⟩
  · obtain ⟨w, hPQ, hP, hQ, hB⟩ := h
    exact ⟨w, hPQ, hP, hQ, hPQ.overlaps, hP.overlaps, hQ.overlaps, λ h => hB h.overlaps, hB⟩

end Most

end BarLevFox2020
