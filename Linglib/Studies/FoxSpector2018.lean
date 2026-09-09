import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Data.Examples.FoxSpector2018

/-!
# Fox and Spector (2018): Economy and Embedded Exhaustification

This file formalizes [fox-spector-2018]'s economy condition on the exhaustivity operator: an
occurrence of `exh` is licensed only if it is not incrementally weakening, that is, unless for
every continuation of the sentence at that point eliminating it leaves the meaning unchanged or
stronger (`Licensed`). The condition derives Singh's asymmetry between the two orders of a
Hurford disjunction (`singh_canonical`, `singh_reverse`), its disappearance for distant
entailing disjuncts (`licensed_orRight_iff`), and the ban on Hurford disjunctions under one
downward-entailing operator but not two (`not_licensed_of_forall_antitone`,
`licensed_iff_of_forall_monotone`). The comparison-class refinement of the condition,
`GloballyWeakeningCC`, is what forces narrow focus under a downward-entailing operator: with
more innocently excludable alternatives the two-layered exhaustification is weaker
(`op_exh_mono`), and the exclusive construal of a disjunction under negation becomes
conjunctive (`exh_neg_exh`, `exh_neg_exh_or`) though not under a negative quantifier
(`exh_no_exh`).

## Implementation notes

Sentences are propositions `Set W`; a continuation is a map on the meaning of the constituent,
and the continuations available at a point are a set of such maps, so "incrementally" is
quantification over that set. Downward-entailing operators are antitone maps and the paper's
exhaustivity operator is Fox's innocent exclusion `Exhaustification.exhIE`. Focus and the
Minimize Focus principle of §8 are not represented; the rows record the distribution of Hurford
disjunctions by the paper's own classification of each sentence.

## References

* [fox-spector-2018]
* [chierchia-fox-spector-2012]
* [hurford-1974]
* [singh-2008]
* [gajewski-sharvit-2012]
* [schlenker-2008]
* [chierchia-2004]
-/

namespace FoxSpector2018

open Exhaustification Set Data.Examples

variable {W : Type*}

/-- A continuation: what the rest of the sentence does with the constituent's meaning. -/
abbrev Continuation (W : Type*) := Set W → Set W

/-! ### The economy condition -/

section Economy

variable (S : Continuation W) (conts : Set (Continuation W)) (C : Set (Set W)) (A : Set W)

/-- Globally vacuous: eliminating `exh` does not change the truth conditions. -/
def GloballyVacuous : Prop := S (exhIE C A) = S A

/-- Globally weakening: eliminating `exh` does not alter or strengthens the truth conditions. -/
def GloballyWeakening : Prop := S A ⊆ S (exhIE C A)

/-- Incrementally vacuous: vacuous for every continuation available at the point. -/
def IncrementallyVacuous : Prop := ∀ S ∈ conts, GloballyVacuous S C A

/-- Incrementally weakening: weakening for every continuation available at the point. -/
def IncrementallyWeakening : Prop := ∀ S ∈ conts, GloballyWeakening S C A

/-- The economy condition: an occurrence of `exh` is licensed unless it is incrementally
weakening. -/
def Licensed : Prop := ¬ IncrementallyWeakening conts C A

variable {S conts C A}

theorem GloballyVacuous.globallyWeakening (h : GloballyVacuous S C A) :
    GloballyWeakening S C A := h.symm.subset

/-- The first version of the condition, on vacuity, follows from the second. -/
theorem not_licensed_of_incrementallyVacuous (h : IncrementallyVacuous conts C A) :
    ¬ Licensed conts C A := λ hl => hl λ S hS => (h S hS).globallyWeakening

/-- Vacuous exhaustification is never licensed. -/
theorem not_licensed_of_eq (h : exhIE C A = A) : ¬ Licensed conts C A :=
  λ hl => hl λ S _ => (congrArg S h).symm.subset

/-- Under a downward-entailing continuation, `exh` is always weakening. -/
theorem globallyWeakening_of_antitone (hS : Antitone S) : GloballyWeakening S C A :=
  hS (exhIE_subset C A)

/-- Under an upward-entailing continuation, `exh` is weakening only when it is vacuous. -/
theorem globallyWeakening_iff_of_monotone (hS : Monotone S) :
    GloballyWeakening S C A ↔ GloballyVacuous S C A :=
  ⟨λ h => subset_antisymm (hS (exhIE_subset C A)) h, GloballyVacuous.globallyWeakening⟩

/-- Under a downward-entailing operator, `exh` is never licensed. -/
theorem not_licensed_of_forall_antitone (h : ∀ S ∈ conts, Antitone S) : ¬ Licensed conts C A :=
  λ hl => hl λ S hS => globallyWeakening_of_antitone (h S hS)

/-- Under upward-entailing continuations, as below two downward-entailing operators, `exh` is
licensed exactly when it is not vacuous for one of them. -/
theorem licensed_iff_of_forall_monotone (h : ∀ S ∈ conts, Monotone S) :
    Licensed conts C A ↔ ∃ S ∈ conts, S (exhIE C A) ≠ S A := by
  simp only [Licensed, IncrementallyWeakening, not_forall, exists_prop]
  exact exists_congr λ S => and_congr_right λ hS =>
    (globallyWeakening_iff_of_monotone (h S hS)).not

end Economy

/-! ### Hurford disjunctions -/

section Hurford

variable {C : Set (Set W)} {p q A X : Set W}

/-- Hurford's Constraint is violated when one disjunct entails the other. -/
def HurfordViolation (p q : Set W) : Prop := p ⊆ q ∨ q ⊆ p

/-- The continuations of a first disjunct: any second disjunct may follow. -/
def orLeft : Set (Continuation W) := range λ Y : Set W => λ A => A ∪ Y

/-- The continuation of a final disjunct after `X`: nothing follows. -/
def orRight (X : Set W) : Set (Continuation W) := {λ A => X ∪ A}

/-- On a first disjunct, `exh` is licensed whenever it excludes something: the empty second
disjunct is a continuation on which it is not vacuous. -/
theorem licensed_orLeft (h : exhIE C A ≠ A) : Licensed orLeft C A := λ hw =>
  h (subset_antisymm (exhIE_subset C A) (by simpa [GloballyWeakening] using hw _ ⟨∅, rfl⟩))

/-- On a final disjunct, `exh` is licensed exactly when it strengthens the whole disjunction. -/
theorem licensed_orRight_iff : Licensed (orRight X) C A ↔ ¬ X ∪ A ⊆ X ∪ exhIE C A := by
  simp only [Licensed, IncrementallyWeakening, orRight, mem_singleton_iff, forall_eq,
    GloballyWeakening]

/-- Singh's asymmetry, canonical order: exhaustifying the weak disjunct of *p or q, or both* is
licensed. -/
theorem singh_canonical (h : (p ∩ q).Nonempty) (h' : ((p ∪ q) \ (p ∩ q)).Nonempty) :
    Licensed orLeft {p ∪ q, p ∩ q} (p ∪ q) := by
  refine licensed_orLeft ?_
  rw [exhIE_pair_sdiff (p ∪ q) h']
  obtain ⟨w, hw⟩ := h
  intro he
  have hw' : w ∈ p ∪ q := Or.inl hw.1
  rw [← he] at hw'
  exact hw'.2 hw

/-- Singh's asymmetry, reverse order: exhaustifying the final weak disjunct of *both, or p or q*
is vacuous, hence not licensed. -/
theorem singh_reverse (h' : ((p ∪ q) \ (p ∩ q)).Nonempty) :
    ¬ Licensed (orRight (p ∩ q)) {p ∪ q, p ∩ q} (p ∪ q) := by
  rw [licensed_orRight_iff, exhIE_pair_sdiff (p ∪ q) h', not_not]
  rintro w (hw | hw)
  · exact Or.inl hw
  · by_cases hpq : w ∈ p ∩ q
    · exact Or.inl hpq
    · exact Or.inr ⟨hw, hpq⟩

/-- Distant entailing disjuncts in reverse order: `exh` on the final weak disjunct is licensed
when the exhaustified disjunction is strictly stronger than the bare one. -/
theorem licensed_orRight_of_ssubset (h : q ∪ exhIE C p ⊂ q ∪ p) : Licensed (orRight q) C p :=
  licensed_orRight_iff.2 (ssubset_def ▸ h).2

/-- Exhaustifying the first disjunct restores Hurford's Constraint once the exhaustified
disjunct and the second are logically independent. -/
theorem not_hurfordViolation_of_independent (h₁ : ¬ exhIE C p ⊆ q) (h₂ : ¬ q ⊆ exhIE C p) :
    ¬ HurfordViolation (exhIE C p) q := λ h => h.elim h₁ h₂

/-- A Hurford disjunction under negation: every continuation negates a disjunction or a
conjunction containing the exhaustified disjunct, so `exh` is incrementally weakening. -/
theorem not_licensed_neg :
    ¬ Licensed (range (λ r : Set W => λ A => (A ∪ r)ᶜ) ∪ range λ r : Set W => λ A => (A ∩ r)ᶜ)
      C A := by
  refine not_licensed_of_forall_antitone ?_
  rintro _ (⟨r, rfl⟩ | ⟨r, rfl⟩)
  · exact λ _ _ h => compl_subset_compl.2 (union_subset_union_left r h)
  · exact λ _ _ h => compl_subset_compl.2 (inter_subset_inter_left r h)

end Hurford

/-! ### The comparison class -/

section ComparisonClass

variable {S : Continuation W} {C C' : Set (Set W)} {A : Set W}

/-- The innocently excludable alternatives. -/
def excludable (C : Set (Set W)) (A : Set W) : Set (Set W) := {q | IsInnocentlyExcludable C A q}

theorem mem_excludable {q : Set W} : q ∈ excludable C A ↔ IsInnocentlyExcludable C A q := Iff.rfl

/-- Globally weakening relative to the comparison class: some set of alternatives with strictly
fewer innocently excludable members gives a result at least as strong. -/
def GloballyWeakeningCC (S : Continuation W) (C : Set (Set W)) (A : Set W) : Prop :=
  ∃ C', excludable C' A ⊂ excludable C A ∧ S (exhIE C' A) ⊆ S (exhIE C A)

/-- The comparison-class condition subsumes the earlier one: the empty set of alternatives is a
comparison. -/
theorem GloballyWeakening.globallyWeakeningCC (h : GloballyWeakening S C A)
    (hne : (excludable C A).Nonempty) : GloballyWeakeningCC S C A := by
  refine ⟨∅, ?_, by rwa [exhIE_empty]⟩
  refine ssubset_of_subset_of_ne (λ _ hq => (mem_excludable.1 hq).1.elim) ?_
  obtain ⟨q, hq⟩ := hne
  exact λ h => (mem_excludable.1 (h ▸ hq : q ∈ excludable ∅ A)).1.elim

/-- Under a downward-entailing operator, exhaustifying against the un-exhaustified sentence
denies it. -/
theorem exhIE_op (hne : (S (exhIE C A) \ S A).Nonempty) :
    exhIE {S (exhIE C A), S A} (S (exhIE C A)) = S (exhIE C A) \ S A :=
  exhIE_pair_sdiff _ hne

/-- The theorem of §10: with more innocently excludable alternatives, the two-layered
exhaustification under a downward-entailing operator is weaker, so economy forces the smaller
alternative set, narrow focus. -/
theorem op_exh_mono (hOP : Antitone S) (hC : C.Finite) (hC' : C'.Finite)
    (hsub : excludable C' A ⊆ excludable C A) (hne : (S (exhIE C A) \ S A).Nonempty)
    (hne' : (S (exhIE C' A) \ S A).Nonempty) :
    exhIE {S (exhIE C' A), S A} (S (exhIE C' A)) ⊆ exhIE {S (exhIE C A), S A} (S (exhIE C A)) := by
  rw [exhIE_op hne, exhIE_op hne']
  exact Set.sdiff_subset_sdiff_left (hOP (exhIE_subset_exhIE C A hC hC' λ q hq => hsub hq))

end ComparisonClass

/-! ### Exhaustification under negation -/

section NegExh

variable {C : Set (Set W)} {A p q : Set W}

/-- Under negation, the exhaustified sentence exhaustified against the bare one yields what the
inner exhaustification excluded: the embedded implicature turns into its conjunctive dual. -/
theorem exh_neg_exh (hne : (A \ exhIE C A).Nonempty) :
    exhIE {(exhIE C A)ᶜ, Aᶜ} (exhIE C A)ᶜ = A \ exhIE C A := by
  rw [exhIE_pair_sdiff (exhIE C A)ᶜ (d := Aᶜ) (by rwa [compl_sdiff_compl]), compl_sdiff_compl]

/-- An exclusive construal of a disjunction under negation is conjunctive. -/
theorem exh_neg_exh_or (h : (p ∩ q).Nonempty) (h' : ((p ∪ q) \ (p ∩ q)).Nonempty) :
    exhIE {(exhIE {p ∪ q, p ∩ q} (p ∪ q))ᶜ, (p ∪ q)ᶜ} (exhIE {p ∪ q, p ∩ q} (p ∪ q))ᶜ = p ∩ q := by
  rw [exh_neg_exh, exhIE_pair_sdiff (p ∪ q) h', sdiff_sdiff_right_self]
  · exact inter_eq_right.2 (Set.inter_subset_left.trans Set.subset_union_left)
  · rw [exhIE_pair_sdiff (p ∪ q) h', sdiff_sdiff_right_self]
    obtain ⟨w, hw⟩ := h
    exact ⟨w, Or.inl hw.1, hw⟩

/-- Under a negative quantifier the construal is not conjunctive: no individual has the weak
property without the strong one, and some individual has the strong one. -/
theorem exh_no_exh {ι : Type*} {P Q : ι → Set W} (hQ : ∀ x, Q x ⊆ P x)
    (hne : ((⋃ x, P x \ Q x)ᶜ ∩ ⋃ x, Q x).Nonempty) :
    exhIE {(⋃ x, P x \ Q x)ᶜ, (⋃ x, P x)ᶜ} (⋃ x, P x \ Q x)ᶜ =
      (⋃ x, P x \ Q x)ᶜ ∩ ⋃ x, Q x := by
  have hne' : ((⋃ x, P x \ Q x)ᶜ \ (⋃ x, P x)ᶜ).Nonempty := by
    obtain ⟨w, hw, hwQ⟩ := hne
    exact ⟨w, hw, λ h => h (iUnion_mono (λ x => hQ x) hwQ)⟩
  rw [exhIE_pair_sdiff _ hne']
  ext w
  simp only [mem_sdiff, mem_compl_iff, mem_iUnion, not_exists, not_forall, not_not, mem_inter_iff]
  refine and_congr_right λ hw => ⟨?_, λ ⟨x, hx⟩ => ⟨x, hQ x hx⟩⟩
  rintro ⟨x, hx⟩
  by_contra hno
  exact hw x ⟨hx, λ hq => hno ⟨x, hq⟩⟩

end NegExh

/-! ### The data -/

/-- A disjunction of the data: whether its disjuncts stand in entailment, whether a scalar
alternative lets exhaustification break it, the order of the disjuncts, whether they are
distant entailing disjuncts, and how many downward-entailing operators scope over it. -/
structure Row where
  hurford : Bool
  rescuable : Bool
  canonical : Bool
  distant : Bool
  de : ℕ
  judgment : Features.Judgment
  deriving DecidableEq

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let h ← ex.parse? "hurford" yesNoTable
  let r ← ex.parse? "rescuable" yesNoTable
  let o ← ex.parse? "order" [("canonical", true), ("reverse", false)]
  let d ← ex.parse? "distant" yesNoTable
  let n ← ex.nat? "de"
  pure ⟨h, r, o, d, n, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Economy accounts for the distribution: a Hurford disjunction is acceptable when a scalar
alternative lets `exh` break the entailment on a disjunct where it is licensed, the first one or
a distant one, and no single downward-entailing operator makes it weakening. -/
theorem rows_predicted : ∀ r ∈ rows, (r.judgment = .acceptable ↔
    r.hurford = false ∨ (r.rescuable = true ∧ (r.canonical = true ∨ r.distant = true) ∧ r.de ≠ 1)) := by
  decide

end FoxSpector2018
