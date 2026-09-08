import Linglib.Logic.Natural.Soundness
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Exhaustification.Antiexhaustive
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Data.Examples.Chierchia2013

/-!
# Chierchia (2013): Logic in Grammar

This file formalizes the opening chapter of [chierchia-2013], where the preferred reading of
*or* and the distribution of *any* and *ever* are shown to track one logical property of a
position. *Or* is exclusive in an upward-entailing position and inclusive in a
downward-entailing one, because Maximize Strength adds the not-both implicature only where it
strengthens, and an implicature strengthens under a monotone embedding and weakens under an
antitone one. *Any* and *ever* are grammatical in the downward-entailing positions and out
elsewhere, because their subdomain alternatives are obligatorily active and must be
exhaustified: under an antitone context every subdomain alternative is entailed and
exhaustification is vacuous, while at the existential itself no witness is entailed and
exhaustification is a contradiction. *Any* alone extends to the free-choice positions, a
possibility modal or an imperative, the divide between it and *ever* and between Italian
*qualsiasi* and *alcuno*. The positions are the paper's easy and hard columns, the hard column
being the licensing contexts whose signatures fix their polarity, and the readings and
judgments are rows: the theorems derive each reading from Maximize Strength and each judgment
from the licensing keystone applied to the Fragment entries.

## References

* [chierchia-2013]
* [ladusaw-1979]
-/

namespace Chierchia2013

open NaturalLogic Polarity Exhaustification Data.Examples

/-! ### Maximize Strength -/

section MaximizeStrength

variable {W : Type*} (p q : Set W)

/-- The readings of *or*. -/
inductive DisjunctionReading where
  | inclusive
  | exclusive
  deriving DecidableEq, Repr

/-- The proposition a reading assigns to *p or q*: the disjunction, or the disjunction with the
not-both implicature added. -/
def DisjunctionReading.denotation : DisjunctionReading → Set W
  | .inclusive => p ∪ q
  | .exclusive => (p ∪ q) \ (p ∩ q)

def DisjunctionReading.key : DisjunctionReading → String
  | .inclusive => "inclusive"
  | .exclusive => "exclusive"

/-- The implicature strengthens. -/
theorem exclusive_subset_inclusive :
    DisjunctionReading.exclusive.denotation p q ⊆ DisjunctionReading.inclusive.denotation p q :=
  Set.sdiff_subset

/-- Maximize Strength: a reading is preferred in a position when the position's embedding of it
is at least as strong as its embedding of the other reading. -/
def IsStrongest (C : Set W → Set W) (r : DisjunctionReading) : Prop :=
  ∀ r' : DisjunctionReading, C (r.denotation p q) ⊆ C (r'.denotation p q)

/-- Under a monotone embedding the implicature still strengthens, so the exclusive reading is
preferred. -/
theorem isStrongest_exclusive {C : Set W → Set W} (hC : Monotone C) :
    IsStrongest p q C .exclusive
  | .inclusive => hC (exclusive_subset_inclusive p q)
  | .exclusive => subset_rfl

/-- Under an antitone embedding the implicature weakens, so the inclusive reading is preferred. -/
theorem isStrongest_inclusive {C : Set W → Set W} (hC : Antitone C) :
    IsStrongest p q C .inclusive
  | .inclusive => subset_rfl
  | .exclusive => hC (exclusive_subset_inclusive p q)

/-- The reading Maximize Strength selects from the polarity of a position; a non-monotone
position selects neither. -/
def maximizeStrength : ContextPolarity → Option DisjunctionReading
  | .upward => some .exclusive
  | .downward => some .inclusive
  | .nonMonotonic => none

/-- The selection is sound: for an embedding with a signature of the position's polarity, the
selected reading is the strongest. -/
theorem isStrongest_maximizeStrength {φ : Signature} {C : Set W → Set W} (hφ : φ.SoundFor C) :
    ∀ r ∈ maximizeStrength φ.toContextPolarity, IsStrongest p q C r := by
  intro r hr
  cases hpol : φ.toContextPolarity <;> rw [hpol] at hr <;>
    simp only [maximizeStrength, Option.mem_def, Option.some.injEq, reduceCtorEq] at hr
  · exact hr ▸ isStrongest_exclusive p q (hφ.monotone hpol)
  · exact hr ▸ isStrongest_inclusive p q (hφ.antitone hpol)

end MaximizeStrength

/-! ### Exhaustifying obligatory subdomain alternatives -/

section Exhaustification

variable {W E : Type*} (D : List E) (P : E → Set W)

/-- The exhaustification operator, the covert counterpart of *only*: the prejacent, with every
alternative it does not entail negated. -/
def exh (C : Set (Set W)) (p : Set W) : Set W := {w | w ∈ p ∧ ∀ q ∈ C, ¬ p ⊆ q → w ∉ q}

theorem exh_subset (C : Set (Set W)) (p : Set W) : exh C p ⊆ p := λ _ h => h.1

/-- Exhaustification cannot exhaustify away entailments: it is vacuous when the prejacent
entails every alternative. -/
theorem exh_eq_self {C : Set (Set W)} {p : Set W} (h : ∀ q ∈ C, p ⊆ q) : exh C p = p :=
  (exh_subset C p).antisymm λ _ hw => ⟨hw, λ q hq hnq => absurd (h q hq) hnq⟩

/-- A subdomain existential entails the existential over the whole domain. -/
theorem existsIn_subset {D' : List E} (h : ∀ x ∈ D', x ∈ D) : existsIn D' P ⊆ existsIn D P := by
  rintro w ⟨x, hx, hPx⟩
  exact ⟨x, h x hx, hPx⟩

/-- Under an antitone context the existential entails each of its subdomain alternatives, so
*any* in a downward-entailing position is exhaustified vacuously: a plain existential. -/
theorem exh_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    exh (C '' dMinAlts D P) (C (existsIn D P)) = C (existsIn D P) :=
  exh_eq_self (by rintro _ ⟨_, ⟨D', hD', rfl⟩, rfl⟩; exact hC (existsIn_subset D P hD'))

/-- At the existential itself, where no witness is entailed, exhaustifying the obligatory
alternatives negates every singleton alternative and is a contradiction: the source of the
deviance of *any* in a positive episodic sentence. -/
theorem exh_dMinAlts_eq_empty (h : ∀ a ∈ D, ¬ existsIn D P ⊆ P a) :
    exh (dMinAlts D P) (existsIn D P) = ∅ := by
  refine Set.eq_empty_of_forall_notMem λ w ⟨⟨a, ha, hPa⟩, hall⟩ => ?_
  refine hall (existsIn [a] P) ⟨[a], by simpa using ha, rfl⟩ (λ hsub => h a ha λ v hv => ?_)
    ⟨a, List.mem_singleton_self a, hPa⟩
  obtain ⟨x, hx, hPx⟩ := hsub hv
  obtain rfl := List.mem_singleton.1 hx
  exact hPx

end Exhaustification

/-! ### The positions -/

/-- The positions of the paper's two columns: the easy column, where *or* is exclusive and *any*
is out, and the hard column, the downward-entailing licensing contexts of [ladusaw-1979], where
*or* is inclusive and *any* is in. -/
inductive Position where
  /-- A positive sentence. -/
  | matrix
  /-- The consequent of a conditional. -/
  | conditionalConsequent
  /-- The second argument of *every*. -/
  | everyScope
  /-- The scope of a positive quantifier such as *somebody*. -/
  | positiveQuantifierScope
  /-- A licensing context: the antecedent of a conditional, the first argument of *every*,
  negation, *nobody*, *doubt*, a possibility modal, an imperative. -/
  | licensing (c : LicensingContext)
  deriving DecidableEq, Repr

/-- The polarity of a position: the easy column is upward entailing, and a licensing context has
the polarity of its signature. -/
def Position.polarity : Position → ContextPolarity
  | .licensing c => c.properties.strawsonSignature.toContextPolarity
  | _ => .upward

/-- A position licenses an item when it is a licensing context that licenses it. -/
def Position.Licenses : Position → Item → Prop
  | .licensing c, e => c.licenses e
  | _, _ => False

instance : (pos : Position) → (e : Item) → Decidable (pos.Licenses e)
  | .licensing c, e => inferInstanceAs (Decidable (c.licenses e))
  | .matrix, _ | .conditionalConsequent, _ | .everyScope, _ | .positiveQuantifierScope, _ =>
    inferInstanceAs (Decidable False)

/-- Every downward-entailing position licenses *ever*: the hard column of the readings of *or*
is the column where the pure negative-polarity item is grammatical. -/
theorem licenses_ever_of_downward :
    ∀ pos : Position, pos.polarity = .downward → pos.Licenses English.PolarityItems.ever := by
  intro pos
  (cases pos <;> try (rename_i c; cases c)) <;> decide

/-- *Any* parts ways with *ever* in exactly the free-choice contexts, those licensing by the
generic-indefinite mechanism: a possibility modal, an imperative, a generic. -/
theorem licenses_any_not_ever_iff (c : LicensingContext) :
    c.licenses English.PolarityItems.any ∧ ¬ c.licenses English.PolarityItems.ever ↔
      c.properties.mechanism = .byGenericIndefinite := by
  cases c <;> decide

/-! ### The rows -/

private def Position.ofKey : String → Option Position
  | "matrix" => some .matrix
  | "conditionalConsequent" => some .conditionalConsequent
  | "everyScope" => some .everyScope
  | "positiveQuantifierScope" => some .positiveQuantifierScope
  | "conditionalAntecedent" => some (.licensing .conditionalAntecedent)
  | "universalRestrictor" => some (.licensing .universalRestrictor)
  | "negation" => some (.licensing .negation)
  | "nobody" => some (.licensing .nobody)
  | "doubtVerb" => some (.licensing .doubtVerb)
  | "modalPossibility" => some (.licensing .modalPossibility)
  | "imperative" => some (.licensing .imperative)
  | _ => none

private def item : String → Option Item
  | "any" => some English.PolarityItems.any
  | "ever" => some English.PolarityItems.ever
  | "alcuno" => some Italian.PolarityItems.alcuno
  | "qualsiasi" => some Italian.PolarityItems.qualsiasi
  | _ => none

/-- In every unforced row the reading of *or* is the one Maximize Strength selects from the
polarity of its position. -/
theorem or_rows :
    ∀ e ∈ Examples.all, e.feature? "item" = some "or" → e.feature? "forced" = none →
      ∀ pos ∈ (e.feature? "position").bind Position.ofKey,
        e.feature? "reading" = (maximizeStrength pos.polarity).map DisjunctionReading.key := by
  decide

/-- The exclusive reading is available under *nobody*, but only forced by the context. -/
theorem exclusive_under_nobody_forced :
    ∃ e ∈ Examples.all, e.feature? "forced" = some "true" ∧
      e.feature? "position" = some "nobody" ∧ e.feature? "reading" = some "exclusive" := by
  decide

/-- Every judgment on *any*, *ever*, *alcuno* and *qualsiasi* is the keystone's: acceptable
exactly in a licensing context that licenses the Fragment entry. -/
theorem polarity_rows :
    ∀ e ∈ Examples.all, ∀ i ∈ (e.feature? "item").bind item,
      ∀ pos ∈ (e.feature? "position").bind Position.ofKey,
        (e.judgment = .acceptable ↔ pos.Licenses i) := by
  decide

end Chierchia2013
