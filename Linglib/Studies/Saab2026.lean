import Linglib.Fragments.Spanish.Binominals
import Linglib.Syntax.Number.Basic
import Linglib.Data.Examples.Saab2026
import Mathlib.Tactic.DeriveFintype

/-!
# Saab (2026): NP-Ellipsis Patterns in Spanish Binominals

This file formalizes the paper's argument that pseudo-partitive and quantificational
binominals (*un grupo*, *un montón de estudiantes*) and qualitative binominals (*una mierda de
departamento*) have different underlying syntax. In the former the genitive coda is the nP
complement of Num, a primeval genitive in the sense of [pesetsky-2013], so an [E]-feature on
Num licenses NP-ellipsis of the coda under the usual identity condition of [merchant-2001],
and Num controls verbal agreement; in the latter the coda is the specifier of an equative
phrase relating it to an indexical empty noun, so no licensor can elide it and its gap is
resolved by context rather than by an antecedent. A structure is the nominal that is the
complement of Num together with the nominal in the specifier above it (`Structure`).
NP-ellipsis of a nominal is licensed exactly when it is that complement and has internal
structure (`Structure.Elidable`), and the verb agrees with the number of that complement. The
same principle covers the paper's structural ambiguity of quantity nouns: under the
descriptive reading the noun heads the projection, so it can be elided and the verb is
singular, and under the quantificational reading the coda heads it, so the coda can be elided
and the verb is plural (`elidable_first_iff_singular`). The rows are the paper's examples,
with the type of each first noun read from the Spanish fragment, and their ellipsis,
agreement and gap facts follow from the structure assigned to them (`ellipsis_matches`).

## Implementation notes

Identity between an antecedent and an ellipsis site is taken modulo case and number, as the
paper argues: case is assigned at PF or overwritten by D after identity is computed, and
number sits on the licensing head outside the ellipsis domain. The paper's three kinds of
nominal gap are distinguished by the recovery they need, a linguistic antecedent for
ellipsis, a contextual assignment for the indexical empty noun and none for a silent noun,
which is what the sub-extraction, argument-structure and context diagnostics of the rows
track. Pesetsky's derivation of genitive marking and the equations at the entity and
proposition types are not formalized.

## References

* [saab-2026]
* [pesetsky-2013]
* [merchant-2001]
* [hankamer-sag-1976]
-/

namespace Saab2026

open Quantification.Binominal Spanish.Binominals Data.Examples

/-! ### Structures -/

/-- The nominals of a binominal: the first noun, the genitive coda, and the indexical empty
noun of the equative structure. -/
inductive Nominal where
  | first
  | coda
  | index
  deriving DecidableEq, Repr, Fintype

/-- A structure: the nominal that is the complement of Num, the head of the extended
projection, and the nominal in the specifier above it. -/
structure Structure where
  head : Nominal
  spec : Option Nominal
  deriving DecidableEq, Repr, Fintype

/-- The primeval-genitive structure of pseudo-partitive and quantificational binominals: the
coda is the nP complement of Num and the quantity phrase sits in the specifier. -/
def quantificational : Structure := ⟨.coda, some .first⟩

/-- The descriptive reading of a quantity noun: the noun heads the projection and the coda is
its complement. -/
def descriptive : Structure := ⟨.first, none⟩

/-- The equative structure of qualitative binominals: the complement of Num is the indexical
empty noun, which the equative head relates to the coda in its specifier. -/
def equative : Structure := ⟨.index, some .coda⟩

/-- A nominal can be elided when it is the complement of Num, whose [E]-feature licenses the
ellipsis of its complement, and has internal structure: the indexical empty noun is an atomic
index, so eliding it is vacuous. -/
def Structure.Elidable (s : Structure) (x : Nominal) : Prop := s.head = x ∧ x ≠ .index

instance (s : Structure) (x : Nominal) : Decidable (s.Elidable x) := by
  unfold Structure.Elidable; infer_instance

/-- The number of a nominal, given the coda's: the first noun is singular, and the indexical
empty noun takes the coda's number through the equation. -/
def Nominal.number (c : Number) : Nominal → Number
  | .first => .singular
  | .coda | .index => c

/-- The verb agrees with the Num head, whose number is that of its complement. -/
def Structure.agreement (s : Structure) (c : Number) : Number := s.head.number c

/-- The gap left by a missing nominal: a true ellipsis or an indexical empty noun. -/
inductive Gap where
  | ellipsis
  | index
  deriving DecidableEq, Repr

/-- The gap of a binominal whose coda is missing: an indexical empty noun when the structure
has one, an ellipsis otherwise. -/
def Structure.gap (s : Structure) : Gap := if s.head = .index then .index else .ellipsis

/-- A gap with internal structure hosts arguments and allows sub-extraction. -/
def Gap.Structured : Gap → Prop
  | .ellipsis => True
  | .index => False

/-- A gap resolved by a contextual assignment rather than a linguistic antecedent. -/
def Gap.ContextResolved : Gap → Prop
  | .ellipsis => False
  | .index => True

instance : DecidablePred Gap.Structured := λ g => by
  cases g <;> unfold Gap.Structured <;> infer_instance

instance : DecidablePred Gap.ContextResolved := λ g => by
  cases g <;> unfold Gap.ContextResolved <;> infer_instance

/-- Nothing in the equative structure can be elided: the coda has no licensor and the index is
atomic. -/
theorem equative_not_elidable (x : Nominal) : ¬ equative.Elidable x := by
  cases x <;> decide

/-- The quantificational structure elides its coda and not the quantity noun; the descriptive
structure the reverse. -/
theorem quantificational_descriptive_elidable :
    quantificational.Elidable .coda ∧ ¬ quantificational.Elidable .first ∧
      descriptive.Elidable .first ∧ ¬ descriptive.Elidable .coda := by
  decide

/-! ### Readings -/

/-- The two readings of a quantity noun. -/
inductive Reading where
  | quantificational
  | descriptive
  deriving DecidableEq, Repr, Fintype

/-- The structure of a binominal of a given type under a reading. -/
def structureOf : BinominalType → Reading → Structure
  | .qualitative, _ => equative
  | _, .quantificational => quantificational
  | _, .descriptive => descriptive

/-- With a plural coda, a quantity noun can be elided exactly when the verb agrees in the
singular: both follow from the noun heading the projection. -/
theorem elidable_first_iff_singular (b : BinominalType) (r : Reading) (hb : b ≠ .qualitative) :
    (structureOf b r).Elidable .first ↔ (structureOf b r).agreement .plural = .singular := by
  cases b <;> cases r <;> simp_all [structureOf, Structure.Elidable, Structure.agreement,
    Nominal.number, quantificational, descriptive]

/-! ### The paper's examples -/

/-- A row's binominal type, from the fragment entry of its first noun. -/
def binominalType? (x : LinguisticExample) : Option BinominalType :=
  (x.feature? "noun").bind λ f => (lookup f).map (·.binominalType)

private def readings : List (String × Reading) :=
  [("quantificational", .quantificational), ("descriptive", .descriptive)]

/-- The structure the paper assigns to a row: from its first noun's type and, for a quantity
noun, its reading, quantificational unless recorded otherwise. -/
def structure? (x : LinguisticExample) : Option Structure :=
  (binominalType? x).map λ b =>
    structureOf b ((x.parse? "reading" readings).getD .quantificational)

private def nominals : List (String × Nominal) := [("first", .first), ("coda", .coda)]

private def numbers : List (String × Number) := [("singular", .singular), ("plural", .plural)]

/-- Whether the ellipsis reading of a row is acceptable: the reading's judgment when one is
recorded, else the row's. -/
def EllipsisAcceptable (x : LinguisticExample) : Prop :=
  (x.readings.lookup "ellipsis").getD x.judgment = .acceptable

instance (x : LinguisticExample) : Decidable (EllipsisAcceptable x) := by
  unfold EllipsisAcceptable; infer_instance

/-- The rows that elide a nominal: the ellipsis reading is acceptable exactly when the row's
structure licenses eliding that nominal. -/
theorem ellipsis_matches :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s → ∀ e, x.parse? "elided" nominals = some e →
      (EllipsisAcceptable x ↔ s.Elidable e) := by
  decide +kernel

/-- The rows that record verbal agreement agree with the Num head of the row's structure. -/
theorem agreement_matches :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s → (x.feature? "agreement").isSome →
      x.parse? "agreement" numbers = (x.parse? "codaNumber" numbers).map s.agreement := by
  decide +kernel

/-- The diagnostics of the rows: sub-extraction and argument structure succeed exactly in a
structured gap, and contextual resolution exactly in an indexical one. -/
theorem diagnostics_match :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s →
      (x.feature? "diagnostic" = some "subextraction" ∨
          x.feature? "diagnostic" = some "argumentStructure" →
        (x.judgment = .acceptable ↔ s.gap.Structured)) ∧
      (x.feature? "diagnostic" = some "contextResolved" →
        (x.judgment = .acceptable ↔ s.gap.ContextResolved)) := by
  decide +kernel

end Saab2026
