module

public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Degree.Quantifier

/-!
# Strawson entailment

This file defines Strawson downward entailingness and the presuppositional operators that
motivate it. An operator into partial propositions is Strawson downward entailing when a smaller
argument gives a conclusion Strawson-entailed by the premise: the downward inference is checked
only where the conclusion's presupposition holds ([von-fintel-1999]). The operators are focus
*only*, the adversative attitudes, superlatives, temporal *since*, and conditional antecedents,
each of which licenses negative polarity items without being downward entailing in the
classical sense.

## Main definitions

* `IsStrawsonDE`, `IsStrawsonAntiAdditive`: Strawson downward entailingness and Strawson
  anti-additivity ([gajewski-2011]) of an operator into `PartialProp`.
* `only`, `regret`, `glad`, `superlative`, `since`, `would`: the operators.

## Main results

* `IsStrawsonDE.of_antitone`: an operator whose assertion is antitone is Strawson downward
  entailing, whatever its presupposition.
* `not_antitone_truthSet`: an operator whose presupposition fails at a smaller argument is not
  classically downward entailing.
* `IsStrawsonAntiAdditive.of_antiAdditive`: a monotone presupposition over an anti-additive
  assertion is Strawson anti-additive.
* `only_isStrawsonDE`, `regret_isStrawsonDE`, `superlative_isStrawsonDE`, `since_isStrawsonDE`,
  `would_isStrawsonDE`, and the `_not_antitone` counterexamples.

## Implementation notes

Every operator here has a presupposition monotone in its argument and an assertion antitone in
it; Strawson downward entailingness is the antitone assertion alone, and the failure of
classical downward entailingness is the presupposition failing at the empty argument. The
attitude operators take their belief set and best worlds as world-indexed sets so that
`Modality.Kratzer.bestWorlds` can be supplied at the use site, and `only` and `superlative`
take an intensional property `ι → Set W`, an extensional predicate being its world-constant
case.

## References

* [von-fintel-1999]
* [strawson-1952]
* [horn-1996]
* [heim-1992]
* [kratzer-1986]
* [gajewski-2011]
-/

@[expose] public section

namespace NaturalLogic

open Presupposition

variable {α ι W D : Type*}

/-! ### Strawson downward entailingness -/

section StrawsonDE

variable [Preorder α] {f : α → PartialProp W}

/-- An operator into partial propositions is Strawson downward entailing when `p ≤ q` makes
`f q` Strawson-entail `f p`: the downward inference is checked only where the conclusion is
defined ([von-fintel-1999]'s Definition 14). -/
def IsStrawsonDE (f : α → PartialProp W) : Prop :=
  ∀ ⦃p q⦄, p ≤ q → (f q).strawsonEntails (f p)

theorem isStrawsonDE_iff :
    IsStrawsonDE f ↔ ∀ ⦃p q⦄, p ≤ q → ∀ w, (f p).presup w → (f q).holds w → (f p).holds w :=
  ⟨λ h _ _ hpq w hp hq => ⟨hp, h hpq w hq.1 hp hq.2⟩,
    λ h _ _ hpq w hq hp hq' => (h hpq w hp ⟨hq, hq'⟩).2⟩

/-- An antitone assertion is Strawson downward entailing, whatever the presupposition. -/
theorem IsStrawsonDE.of_antitone (h : Antitone λ p => (f p).assertion) : IsStrawsonDE f :=
  λ _ _ hpq w _ _ hq => h hpq w hq

/-- Classical downward entailingness of the total meaning implies the Strawson form. -/
theorem IsStrawsonDE.of_antitone_truthSet (h : Antitone λ p => (f p).truthSet) :
    IsStrawsonDE f :=
  λ _ _ hpq _ hq _ hq' => (h hpq ⟨hq, hq'⟩).2

theorem IsStrawsonDE.comp_monotone {β : Type*} [Preorder β] {g : β → α} (hf : IsStrawsonDE f)
    (hg : Monotone g) : IsStrawsonDE (f ∘ g) :=
  λ _ _ hpq => hf (hg hpq)

/-- Presupposition failure at a smaller argument defeats classical downward entailingness. -/
theorem not_antitone_truthSet {p q : α} {w : W} (hpq : p ≤ q) (hq : (f q).holds w)
    (hp : ¬ (f p).presup w) : ¬ Antitone λ p => (f p).truthSet :=
  λ h => hp (h hpq hq).1

end StrawsonDE

/-! ### Strawson anti-additivity -/

section StrawsonAA

variable [SemilatticeSup α] {f : α → PartialProp W}

/-- Anti-additivity of the total meaning, checked where both arguments' presuppositions hold
([gajewski-2011]'s Strawson anti-additivity). -/
def IsStrawsonAntiAdditive (f : α → PartialProp W) : Prop :=
  ∀ p q w, (f p).presup w → (f q).presup w →
    ((f (p ⊔ q)).holds w ↔ (f p).holds w ∧ (f q).holds w)

/-- A monotone presupposition over an anti-additive assertion is Strawson anti-additive. -/
theorem IsStrawsonAntiAdditive.of_antiAdditive (hp : Monotone λ p => (f p).presup)
    (ha : IsAntiAdditive λ p => (f p).assertion) : IsStrawsonAntiAdditive f := by
  intro p q w hpw hqw
  have h : (f (p ⊔ q)).assertion w ↔ (f p).assertion w ∧ (f q).assertion w :=
    iff_of_eq (congrFun (ha p q) w)
  exact ⟨λ hs => ⟨⟨hpw, (h.1 hs.2).1⟩, hqw, (h.1 hs.2).2⟩,
    λ hs => ⟨hp le_sup_left w hpw, h.2 ⟨hs.1.2, hs.2.2⟩⟩⟩

/-- Strawson anti-additivity implies Strawson downward entailingness once the presupposition is
monotone. -/
theorem IsStrawsonAntiAdditive.isStrawsonDE (hAA : IsStrawsonAntiAdditive f)
    (hp : Monotone λ p => (f p).presup) : IsStrawsonDE f :=
  λ p q hpq w hq hp' hq' =>
    ((hAA p q w hp' (hp hpq w hp')).1 (by rw [sup_eq_right.mpr hpq]; exact ⟨hq, hq'⟩)).1.2

end StrawsonAA

/-! ### *Only* -/

section Only

variable (x : ι) (P : ι → Set W)

/-- *Only x is P* presupposes that `x` is `P` and asserts that nothing else is
([von-fintel-1999]'s (15)); [horn-1996]'s presupposition that something is `P` derives this one
from the assertion. -/
def only : PartialProp W where
  presup w := w ∈ P x
  assertion w := ∀ y, y ≠ x → w ∉ P y

theorem only_isStrawsonDE : IsStrawsonDE (only (W := W) x) :=
  .of_antitone λ _ _ h _ hQ y hy hP => hQ y hy (h y hP)

theorem only_isStrawsonAA : IsStrawsonAntiAdditive (only (W := W) x) :=
  .of_antiAdditive (λ _ _ h _ hw => h x hw) λ _ _ => funext λ _ => propext <| by
    simp only [only, Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Set.mem_union,
      not_or, imp_and, forall_and]

/-- *Only John ate vegetables* does not classically entail *only John ate kale*: the
conclusion's presupposition may fail ([von-fintel-1999]'s (11)). -/
theorem only_not_antitone : ¬ Antitone λ P : Bool → Set Unit => (only true P).truthSet :=
  not_antitone_truthSet (p := ⊥) (q := λ y => {_u | y = true}) (w := ()) bot_le
    ⟨rfl, λ _ hy h => hy h⟩ id

end Only

/-! ### Adversative and congruent attitudes -/

section Attitudes

variable (dox best : W → Set W)

/-- *Sorry*, *regret*, *amazed*, *surprised* ([von-fintel-1999]'s (53)): the subject believes
`p` and the best relevant worlds are not `p`-worlds; the attitudes differ only in the ordering
behind `best`. Factivity is doxastic ([heim-1992]). -/
def regret (p : Set W) : PartialProp W where
  presup w := dox w ⊆ p
  assertion w := Disjoint (best w) p

theorem regret_isStrawsonDE : IsStrawsonDE (regret dox best) :=
  .of_antitone λ _ _ h _ hq => hq.mono_right h

theorem regret_isStrawsonAA : IsStrawsonAntiAdditive (regret dox best) :=
  .of_antiAdditive (λ _ _ h _ hw => hw.trans h)
    λ _ _ => funext λ _ => propext Set.disjoint_union_right

/-- *Sorry that Robin bought a car* does not classically entail *sorry that Robin bought a Honda
Civic*: the conclusion's factive presupposition may fail ([von-fintel-1999]'s (30)). -/
theorem regret_not_antitone :
    ¬ Antitone λ p : Set Bool => (regret (λ w => {w}) (λ _ => {false}) p).truthSet :=
  not_antitone_truthSet (p := ∅) (q := {true}) (w := true) (Set.empty_subset _)
    ⟨Set.Subset.rfl, Set.disjoint_singleton.2 Bool.false_ne_true⟩ λ h => h rfl

/-- *Glad* ([von-fintel-1999]'s (50)): the subject believes `p` and the best relevant worlds
are `p`-worlds, which makes *glad* belief conjoined with *want*. -/
def glad (p : Set W) : PartialProp W where
  presup w := dox w ⊆ p
  assertion w := best w ⊆ p

/-- *Glad* is upward entailing in its complement, so it licenses no negative polarity item. -/
theorem glad_monotone : Monotone λ p => (glad dox best p).truthSet :=
  λ _ _ h _ hw => ⟨hw.1.trans h, hw.2.trans h⟩

end Attitudes

/-! ### Superlatives -/

section Superlative

variable [Preorder D] (μ : ι → D) (Q : ι → Set W) (a : ι)

/-- *a is the μ-est Q* ([von-fintel-1999]'s (79)): presupposes that `a` is a `Q` and asserts that
every other `Q` has a smaller degree; at a world this is [heim-1999]'s absolute superlative
(`superlative_holds_iff`). -/
def superlative : PartialProp W where
  presup w := w ∈ Q a
  assertion w := ∀ x, w ∈ Q x → x ≠ a → μ x < μ a

theorem superlative_isStrawsonDE : IsStrawsonDE (superlative (W := W) μ · a) :=
  .of_antitone λ _ _ h _ hQ x hx => hQ x (h x hx)

theorem superlative_isStrawsonAA : IsStrawsonAntiAdditive (superlative (W := W) μ · a) :=
  .of_antiAdditive (λ _ _ h _ hw => h a hw) λ _ _ => funext λ _ => propext <| by
    simp only [superlative, Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union,
      Set.mem_union, or_imp, forall_and]

theorem superlative_holds_iff {D : Type*} [LinearOrder D] (μ : ι → D) (w : W) :
    (superlative μ Q a).holds w ↔ Degree.absoluteSuperlative μ {x | w ∈ Q x} a :=
  Iff.rfl

end Superlative

/-! ### Temporal *since* -/

section Since

variable (past window : W → Set W)

/-- *It has been five years since p* ([von-fintel-1999]'s (20)–(22)): presupposes a `p`-time
five years ago and asserts none since. -/
def since (p : Set W) : PartialProp W where
  presup w := (past w ∩ p).Nonempty
  assertion w := Disjoint (window w) p

theorem since_isStrawsonDE : IsStrawsonDE (since past window) :=
  .of_antitone λ _ _ h _ hq => hq.mono_right h

/-- *Since I saw a bird of prey* does not classically entail *since I saw an eagle*
([von-fintel-1999]'s (20)). -/
theorem since_not_antitone :
    ¬ Antitone λ p : Set Unit => (since (λ _ => Set.univ) (λ _ => ∅) p).truthSet :=
  not_antitone_truthSet (p := ∅) (q := Set.univ) (w := ()) (Set.empty_subset _)
    ⟨⟨(), trivial, trivial⟩, Set.empty_disjoint _⟩ λ h => h.ne_empty (Set.inter_empty _)

end Since

/-! ### Conditional antecedents -/

section Would

variable (domain : W → Set W)

/-- *If p, would q* over a modal base with an idle ordering source ([von-fintel-1999]'s (72),
[kratzer-1986]): presupposes that the base admits `p` and asserts the strict conditional. -/
def would (p q : Set W) : PartialProp W where
  presup w := (domain w ∩ p).Nonempty
  assertion w := w ∈ Conditional.strictImp domain p q

theorem would_isStrawsonDE (q : Set W) : IsStrawsonDE (would domain · q) :=
  .of_antitone λ _ _ h _ hw => Conditional.strictImp_anti_left (access := domain) (q := q) h hw

theorem would_isStrawsonAA (q : Set W) : IsStrawsonAntiAdditive (would domain · q) :=
  .of_antiAdditive (λ _ _ h _ hw => hw.mono (Set.inter_subset_inter_right _ h))
    λ _ _ => funext λ _ => propext <| by
      simp only [would, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Conditional.mem_strictImp,
        Set.inter_union_distrib_left, Set.union_subset_iff]

/-- With its presupposition in, *would* is not classically downward entailing in its antecedent:
an impossible antecedent fails it. -/
theorem would_not_antitone :
    ¬ Antitone λ p : Set Unit => (would (λ _ => Set.univ) p Set.univ).truthSet :=
  not_antitone_truthSet (p := ∅) (q := Set.univ) (w := ()) (Set.empty_subset _)
    ⟨⟨(), trivial, trivial⟩, Set.subset_univ _⟩ λ h => h.ne_empty (Set.inter_empty _)

end Would

/-- Strawson downward entailingness is strictly weaker than the classical notion. -/
theorem strawsonDE_strictly_weaker_than_antitone :
    ∃ f : (Bool → Set Unit) → PartialProp Unit,
      IsStrawsonDE f ∧ ¬ Antitone λ P => (f P).truthSet :=
  ⟨only true, only_isStrawsonDE true, only_not_antitone⟩

end NaturalLogic
