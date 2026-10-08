module

public import Linglib.Logic.Natural.Soundness
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Fragments.Romance.Italian.PolarityItems
public import Linglib.Data.Examples.Chierchia2013

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
from the licensing relation applied to the Fragment entries.

## References

* [chierchia-2013]
* [ladusaw-1979]
-/

@[expose] public section

namespace Chierchia2013

open NaturalLogic PolarityItem Exhaustification

/-! ### Maximize Strength -/

section MaximizeStrength

variable {W : Type*} (p q : Set W)

/-- *Or* has an inclusive and an exclusive reading. -/
inductive DisjunctionReading where
  | inclusive
  | exclusive
  deriving DecidableEq, Repr

/-- A reading assigns to *p or q* the disjunction, or the disjunction with the not-both
implicature added. -/
def DisjunctionReading.denotation : DisjunctionReading → Set W
  | .inclusive => p ∪ q
  | .exclusive => (p ∪ q) \ (p ∩ q)

/-- The name of a reading in the example rows. -/
def DisjunctionReading.key : DisjunctionReading → String
  | .inclusive => "inclusive"
  | .exclusive => "exclusive"

/-- The not-both implicature strengthens the disjunction. -/
theorem exclusive_subset_inclusive :
    DisjunctionReading.exclusive.denotation p q ⊆ DisjunctionReading.inclusive.denotation p q :=
  Set.sdiff_subset

/-- By Maximize Strength a reading is preferred in a position when the position's embedding of
it is at least as strong as its embedding of the other reading. -/
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
def maximizeStrength : SignType → Option DisjunctionReading
  | .pos => some .exclusive
  | .neg => some .inclusive
  | .zero => none

/-- The selection is sound: for an embedding with a signature of the position's polarity, the
selected reading is the strongest. -/
theorem isStrongest_maximizeStrength {φ : Signature} {C : Set W → Set W} (hφ : φ.SoundFor C) :
    ∀ r ∈ maximizeStrength φ.sign, IsStrongest p q C r := by
  intro r hr
  cases hpol : φ.sign <;> rw [hpol] at hr <;>
    simp only [maximizeStrength, Option.mem_def, Option.some.injEq, reduceCtorEq] at hr
  · exact hr ▸ isStrongest_inclusive p q (hφ.antitone hpol)
  · exact hr ▸ isStrongest_exclusive p q (hφ.monotone hpol)

end MaximizeStrength

/-! ### Exhaustifying obligatory subdomain alternatives -/

section Exhaustification

variable {W E : Type*} (D : Finset E) (P : E → Set W)

/-- Under an antitone context the existential entails each of its subdomain alternatives, so
*any* in a downward-entailing position is exhaustified vacuously: a plain existential. -/
theorem exh_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    exh (C '' subDisjs D P) (C (disj D P)) = C (disj D P) :=
  exh_eq_self (by rintro _ ⟨_, ⟨S, hS, -, rfl⟩, rfl⟩; exact hC (subDisj_mono hS))

/-- At the existential itself, where no witness is entailed, exhaustifying the obligatory
alternatives negates every singleton alternative and is a contradiction: the source of the
deviance of *any* in a positive episodic sentence. -/
theorem exh_subDisjs_eq_empty (h : ∀ a ∈ D, ¬ disj D P ⊆ P a) :
    exh (subDisjs D P) (disj D P) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun w ⟨hw, hall⟩ ↦ ?_
  obtain ⟨a, ha, hPa⟩ := mem_subDisj.1 hw
  exact h a ha (by simpa using hall _ ⟨{a}, by simpa, by simp, rfl⟩ (by simpa))

end Exhaustification

/-! ### The positions -/

/-- The positions fall into the paper's two columns, the easy column, where *or* is exclusive and
*any* is out, and the hard column, the downward-entailing licensing contexts of [ladusaw-1979],
where *or* is inclusive and *any* is in. -/
inductive Position where
  /-- A positive sentence. -/
  | matrix
  /-- The consequent of a conditional. -/
  | conditionalConsequent
  /-- The second argument of *every*. -/
  | everyScope
  /-- The scope of a positive quantifier such as *somebody*. -/
  | positiveQuantifierScope
  /-- A licensing context, such as the antecedent of a conditional, the first argument of
  *every*, negation, *nobody*, *doubt*, a possibility modal or an imperative. -/
  | licensing (c : LicensingContext)

open Classical in
/-- A position in the easy column is upward entailing, and a licensing context is downward
entailing when its licenser carries weak strength. -/
noncomputable def Position.polarity : Position → SignType
  | .licensing c => if c.licenser.Carries .weak then -1 else 1
  | _ => 1

theorem polarity_licensing_of_carries {c : LicensingContext} (h : c.licenser.Carries .weak) :
    (Position.licensing c).polarity = -1 := by
  simp [Position.polarity, h]

theorem polarity_licensing_of_not_carries {c : LicensingContext} (h : ¬ c.licenser.Carries .weak) :
    (Position.licensing c).polarity = 1 := by
  simp [Position.polarity, h]

/-- A position licenses an item when it is a licensing context that licenses it. -/
def Position.Licenses : Position → PolarityItem → Prop
  | .licensing c, e => c.Licenses e
  | _, _ => False

@[simp] theorem Position.licenses_licensing {c : LicensingContext} {e : PolarityItem} :
    (Position.licensing c).Licenses e ↔ c.Licenses e := Iff.rfl

/-- Every downward-entailing position licenses *ever*: the hard column of the readings of *or*
is the column where the pure negative-polarity item is grammatical. -/
theorem licenses_ever_of_downward :
    ∀ pos : Position, pos.polarity = -1 → pos.Licenses English.PolarityItems.ever := by
  rintro (_ | _ | _ | _ | c) h <;> try exact absurd h (by decide)
  by_cases hc : c.licenser.Carries .weak
  · exact .inl ⟨.weak, rfl, hc⟩
  · exact absurd ((polarity_licensing_of_not_carries hc).symm.trans h) (by decide)

/-- *Any* parts ways with *ever* exactly where the context licenses free choice: a possibility
modal, an imperative, a generic. -/
theorem licenses_any_not_ever_iff (c : LicensingContext) :
    c.Licenses English.PolarityItems.any ∧ ¬ c.Licenses English.PolarityItems.ever ↔
      c.licenser.LicensesFreeChoice := by
  have hfc : c.licenser.LicensesFreeChoice →
      ¬ c.licenser.Carries .weak ∧ ¬ c.licenser.LicensesByRelevance := by
    generalize c.licenser = L
    cases L <;> simp [Licenser.LicensesFreeChoice, Licenser.Carries, Licenser.IsStrawsonDE,
      Licenser.LicensesByRelevance]
  have ha : c.Licenses English.PolarityItems.any ↔ c.licenser.Carries .weak ∨
      c.licenser.LicensesFreeChoice ∨ c.licenser.LicensesByRelevance := by
    simp [LicensingContext.Licenses, English.PolarityItems.any, PolarityItem.IsFCI]
  have he : c.Licenses English.PolarityItems.ever ↔ c.licenser.Carries .weak ∨
      c.licenser.LicensesByRelevance := by
    simp [LicensingContext.Licenses, English.PolarityItems.ever, PolarityItem.IsFCI]
  rw [ha, he]
  refine ⟨fun ⟨h, hn⟩ ↦ h.elim (fun h' ↦ absurd (.inl h') hn) fun h' ↦
    h'.resolve_right fun h'' ↦ hn (.inr h''), fun h ↦ ⟨.inr (.inl h), ?_⟩⟩
  rintro (h' | h')
  exacts [(hfc h).1 h', (hfc h).2 h']

/-- The licensers of the downward-entailing positions carry weak strength, those of the modal
positions do not. -/
theorem carries_weak_conditionalAntecedent :
    LicensingContext.conditionalAntecedent.licenser.Carries .weak :=
  LicensingContext.isStrawsonDE_conditionalAntecedent

theorem carries_weak_universalRestrictor :
    LicensingContext.universalRestrictor.licenser.Carries .weak :=
  Licenser.carries_of_holds ((LicensingContext.holds_universalRestrictor_iff (s := .weak)).2
    (by decide))

theorem carries_weak_negation : LicensingContext.negation.licenser.Carries .weak :=
  Licenser.carries_of_holds (LicensingContext.holds_negation .weak)

theorem carries_weak_nobody : LicensingContext.nobody.licenser.Carries .weak :=
  Licenser.carries_of_holds ((LicensingContext.holds_nobody_iff (s := .weak)).2 (by decide))

theorem carries_weak_doubtVerb : LicensingContext.doubtVerb.licenser.Carries .weak :=
  Licenser.carries_of_holds (LicensingContext.holds_doubtVerb_iff.2 le_rfl)

theorem not_carries_weak_modalPossibility :
    ¬ LicensingContext.modalPossibility.licenser.Carries .weak := id

theorem not_carries_weak_imperative : ¬ LicensingContext.imperative.licenser.Carries .weak := id

/-! ### The rows -/

/-- The position a row names. -/
def Position.ofKey : String → Option Position
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

/-- The Fragment entry a row names. -/
def item : String → Option PolarityItem
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
  simp +decide [Examples.all, Position.ofKey, Datum.feature?, List.lookup,
    Position.polarity, maximizeStrength, carries_weak_conditionalAntecedent,
    carries_weak_universalRestrictor, carries_weak_negation, carries_weak_nobody,
    carries_weak_doubtVerb, not_carries_weak_modalPossibility, not_carries_weak_imperative,
    Examples.ex1a, Examples.ex1b, Examples.ex5a, Examples.ex5b, Examples.ex12a,
    Examples.ex12b, Examples.ex12c, Examples.ex12d, Examples.ex13, Examples.ex19a,
    Examples.ex15ia, Examples.ex15ib, Examples.ex15iia, Examples.ex15iib, Examples.ex15iiia,
    Examples.ex15iiib, Examples.ex16ia, Examples.ex16ib, Examples.ex16iia, Examples.ex16iib,
    Examples.ex16iiia, Examples.ex16iiib, Examples.ex21a, Examples.ex21b, Examples.ex21c,
    Examples.ex21d, Examples.ex70ai, Examples.ex70aii, Examples.ex70ci, Examples.ex70cii,
    Examples.ex70di, Examples.ex70dii, Examples.ex70ei, Examples.ex70eii]

/-- The exclusive reading is available under *nobody*, but only forced by the context. -/
theorem exclusive_under_nobody_forced :
    ∃ e ∈ Examples.all, e.feature? "forced" = some "true" ∧
      e.feature? "position" = some "nobody" ∧ e.feature? "reading" = some "exclusive" := by
  decide

/-- Every judgment on *any*, *ever*, *alcuno* and *qualsiasi* is the licensing theory's: acceptable
exactly in a licensing context that licenses the Fragment entry. -/
theorem polarity_rows :
    ∀ e ∈ Examples.all, ∀ i ∈ (e.feature? "item").bind item,
      ∀ pos ∈ (e.feature? "position").bind Position.ofKey,
        (e.judgment = .acceptable ↔ pos.Licenses i) := by
  simp +decide [Examples.all, Position.ofKey, item, Datum.feature?,
    List.lookup, Position.Licenses, English.PolarityItems.any, English.PolarityItems.ever,
    Italian.PolarityItems.alcuno, Italian.PolarityItems.qualsiasi,
    Examples.ex1a, Examples.ex1b, Examples.ex5a, Examples.ex5b, Examples.ex12a,
    Examples.ex12b, Examples.ex12c, Examples.ex12d, Examples.ex13, Examples.ex19a,
    Examples.ex15ia, Examples.ex15ib, Examples.ex15iia, Examples.ex15iib, Examples.ex15iiia,
    Examples.ex15iiib, Examples.ex16ia, Examples.ex16ib, Examples.ex16iia, Examples.ex16iib,
    Examples.ex16iiia, Examples.ex16iiib, Examples.ex21a, Examples.ex21b, Examples.ex21c,
    Examples.ex21d, Examples.ex70ai, Examples.ex70aii, Examples.ex70ci, Examples.ex70cii,
    Examples.ex70di, Examples.ex70dii, Examples.ex70ei, Examples.ex70eii]

end Chierchia2013
