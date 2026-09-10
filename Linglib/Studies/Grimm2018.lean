import Linglib.Features.Individuation
import Linglib.Features.Prominence
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Grimm (2018): Grammatical Number and the Scale of Individuation

This file formalizes [grimm-2018]'s thesis that a language's grammatical number categories
partition the scale of individuation, substances below granular aggregates below collective
aggregates below individuals (`IndividuationType`), by an order-preserving map (section 3.4).
The consequence the paper draws, that no category spans two disconnected segments of the scale,
is the order-connectedness of the fibres of a monotone map (`ordConnected_fiber_of_monotone`),
and the impossible system of Table 21 fails it under every ordering of its classes
(`bad_not_monotone`). The systems of Table 20 and section 4.1, Dagaare with a class per type, the
tripartite Welsh, Turkana, Maltese, and Miraña, binary English, and Yudja with number on humans
alone, are monotone classifications (`welsh_monotone` and its siblings). Markedness follows the
scale: the zero-coded value of a class is single reference for individuals and multiple reference
for aggregates, with no contrast at the bottom (`welsh_default_monotone` and its siblings), and
Dagaare's inverse marking is one coded value read in the two directions. Animacy refines the
picture (section 4.2): on the product of the scale with the animacy hierarchy, the
collective/singulative class ascends from below, the inverse of [smith-stark-1974]'s plural
marking, and the regions of Maltese, Welsh, and Turkana nest (`collective_regions_nest`).

## Implementation notes

Each language's countability classes are an enumeration ordered by scale position, and the
classification of the four individuation types is the language's row of Table 20, 23, or 24.
Turkana and Maltese share Welsh's partition and differ in agreement and animacy reach, Yudja
shares English's and differs in restricting the contrast to humans; the classification does not
record these. The animacy tiers are the simplified hierarchy of Fig. 3, after
[haspelmath-2005]'s split of animates, mapped into the library's `AnimacyRank`; the full
animacy–individuation lattice, an [aissen-2003] product, and the connected region constraint
(28) over it are not formalized.

## References

* [grimm-2018]
* [smith-stark-1974]
* [aissen-2003]
* [haspelmath-2005]
-/

namespace Grimm2018

/-! ### The order-preservation thesis, section 3.4 -/

/-- A monotone classification has order-convex fibres: each countability class picks out a
contiguous segment of the scale. -/
theorem ordConnected_fiber_of_monotone {α C : Type*} [Preorder α] [PartialOrder C] {f : α → C}
    (hf : Monotone f) (c : C) : (f ⁻¹' {c}).OrdConnected :=
  Set.ordConnected_singleton.preimage_mono hf

/-! ### The number systems, Tables 20, 23, and 24 -/

/-- The tripartite systems: non-countable, collective/unit, singular/plural. -/
inductive TripartiteClass where
  | nonCountable
  | collectiveUnit
  | singularPlural
  deriving DecidableEq, Repr, Fintype

/-- The class's position on the scale. -/
def TripartiteClass.toNat : TripartiteClass → ℕ
  | .nonCountable => 0
  | .collectiveUnit => 1
  | .singularPlural => 2

instance : LinearOrder TripartiteClass :=
  .lift' TripartiteClass.toNat
    (λ a b h => by cases a <;> cases b <;> simp_all [TripartiteClass.toNat])

/-- Welsh (Table 20): substances are non-countable (*llefrith* 'milk'), granular and collective
aggregates take the singulative (*adar* ~ *aderyn* 'birds' ~ 'bird'), individuals the plural
(*cadair* ~ *cadeiriau* 'chair' ~ 'chairs'). -/
def welshClassify : IndividuationType → TripartiteClass
  | .substance => .nonCountable
  | .granularAggregate | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

theorem welsh_monotone : Monotone welshClassify := by decide

/-- Turkana (section 2.2) partitions the scale as Welsh does; its collective class reaches
types of people. -/
abbrev turkanaClassify := welshClassify

/-- Maltese (section 2.3) partitions the scale as Welsh does; its collective agrees in the
singular and reaches barely beyond insects. -/
abbrev malteseClassify := welshClassify

/-- Miraña (Table 23): granular aggregates join the substances as non-countable, collective
aggregates form the class whose bare form names a collection and whose class-marked form a
unit, individuals inflect for plural. -/
def miranaClassify : IndividuationType → TripartiteClass
  | .substance | .granularAggregate => .nonCountable
  | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

theorem mirana_monotone : Monotone miranaClassify := by decide

/-- Dagaare (Table 20): non-countable, optionally singulative (*-ruu*) non-countable,
plural-default with *-ri* coding the singular, and singular-default with *-ri* coding the
plural. -/
inductive DagaareClass where
  | nonCountable
  | singulativeNonCount
  | pluralDefault
  | singularDefault
  deriving DecidableEq, Repr, Fintype

/-- The class's position on the scale. -/
def DagaareClass.toNat : DagaareClass → ℕ
  | .nonCountable => 0
  | .singulativeNonCount => 1
  | .pluralDefault => 2
  | .singularDefault => 3

instance : LinearOrder DagaareClass :=
  .lift' DagaareClass.toNat (λ a b h => by cases a <;> cases b <;> simp_all [DagaareClass.toNat])

/-- Dagaare's classification (Table 20): a class for each individuation type. -/
def dagaareClassify : IndividuationType → DagaareClass
  | .substance => .nonCountable
  | .granularAggregate => .singulativeNonCount
  | .collectiveAggregate => .pluralDefault
  | .individualEntity => .singularDefault

theorem dagaare_monotone : Monotone dagaareClassify := by decide

/-- The binary systems: non-countable and singular/plural. -/
inductive BinaryClass where
  | nonCountable
  | singularPlural
  deriving DecidableEq, Repr, Fintype

/-- The class's position on the scale. -/
def BinaryClass.toNat : BinaryClass → ℕ
  | .nonCountable => 0
  | .singularPlural => 1

instance : LinearOrder BinaryClass :=
  .lift' BinaryClass.toNat (λ a b h => by cases a <;> cases b <;> simp_all [BinaryClass.toNat])

/-- English (Table 20): substances and both kinds of aggregate (*rice*, *foliage*) are
non-countable, individuals take the plural. -/
def englishClassify : IndividuationType → BinaryClass
  | .individualEntity => .singularPlural
  | _ => .nonCountable

theorem english_monotone : Monotone englishClassify := by decide

/-- Yudja (Table 24) cuts the scale where English does, with the optional plural *-i* on
individuals restricted to humans. -/
abbrev yudjaClassify := englishClassify

/-! ### The impossible system, Table 21

Granular aggregates and individuals share a singular/plural class while the collective
aggregates between them form a collective/singulative class, so the singular/plural class is
discontinuous on the scale. -/

/-- Table 21's bad system. -/
def badClassify : IndividuationType → TripartiteClass
  | .substance => .nonCountable
  | .granularAggregate | .individualEntity => .singularPlural
  | .collectiveAggregate => .collectiveUnit

/-- The bad system's singular/plural class is not a contiguous segment of the scale. -/
theorem bad_fiber_not_ordConnected :
    ¬ (badClassify ⁻¹' {TripartiteClass.singularPlural}).OrdConnected := by
  intro h
  have : badClassify .collectiveAggregate = .singularPlural :=
    h.out (x := .granularAggregate) rfl (y := .individualEntity) rfl ⟨by decide, by decide⟩
  exact absurd this (by decide)

/-- No ordering of the classes makes the bad system order-preserving, the paper's footnote 21
generalized from its two candidate orders to all. -/
theorem bad_not_monotone (po : PartialOrder TripartiteClass) :
    letI := po
    ¬ Monotone badClassify :=
  λ hf => bad_fiber_not_ordConnected (@ordConnected_fiber_of_monotone _ _ _ po _ hf _)

/-! ### Coding and markedness, sections 3.4 and 4.4

Each class codes one value of its contrast and leaves the other zero. The prediction: the
zero-coded default of a class tracks its individuation, multiple reference for aggregate classes
and single reference for individual classes, with no contrast at the bottom. -/

/-- The coding pattern of a countability class. -/
inductive ClassCoding where
  /-- No number contrast. -/
  | noContrast
  /-- A zero-coded aggregate and a coded unit, the singulative. -/
  | codedUnit
  /-- A zero-coded plural and a coded singular, Dagaare's inverse marking. -/
  | codedSingular
  /-- A zero-coded singular and a coded plural. -/
  | codedPlural
  deriving DecidableEq, Repr, Fintype

/-- The zero-coded default of a class: nothing, multiple referents, or a single referent. -/
inductive DefaultReference where
  | none
  | multiple
  | single
  deriving DecidableEq, Repr, Fintype

/-- The default's position on the scale. -/
def DefaultReference.toNat : DefaultReference → ℕ
  | .none => 0
  | .multiple => 1
  | .single => 2

instance : LinearOrder DefaultReference :=
  .lift' DefaultReference.toNat
    (λ a b h => by cases a <;> cases b <;> simp_all [DefaultReference.toNat])

/-- What a coding pattern leaves as the zero-coded default. -/
def ClassCoding.default : ClassCoding → DefaultReference
  | .noContrast => .none
  | .codedUnit | .codedSingular => .multiple
  | .codedPlural => .single

/-- Welsh coding by class (Table 20): nothing, the singulative *-yn*, the plural *-od*. -/
def welshCoding : TripartiteClass → ClassCoding
  | .nonCountable => .noContrast
  | .collectiveUnit => .codedUnit
  | .singularPlural => .codedPlural

/-- Dagaare coding by class (Table 20): nothing, the optional singulative *-ruu*, the singular
*-ri*, the plural *-ri*. -/
def dagaareCoding : DagaareClass → ClassCoding
  | .nonCountable => .noContrast
  | .singulativeNonCount => .codedUnit
  | .pluralDefault => .codedSingular
  | .singularDefault => .codedPlural

/-- English coding by class (Table 20): nothing, the plural *-s*. -/
def englishCoding : BinaryClass → ClassCoding
  | .nonCountable => .noContrast
  | .singularPlural => .codedPlural

/-- Along the scale the zero-coded default ascends from no contrast through multiple to single
reference. -/
theorem welsh_default_monotone : Monotone (λ i => (welshCoding (welshClassify i)).default) := by
  decide

theorem dagaare_default_monotone :
    Monotone (λ i => (dagaareCoding (dagaareClassify i)).default) := by
  decide

theorem english_default_monotone :
    Monotone (λ i => (englishCoding (englishClassify i)).default) := by
  decide

/-- Dagaare's two *-ri* classes differ only in the direction of coding, the content of inverse
number marking (section 2.4). -/
theorem dagaare_inverse_marking :
    (dagaareCoding .pluralDefault).default = .multiple ∧
      (dagaareCoding .singularDefault).default = .single ∧
      dagaareCoding .pluralDefault ≠ dagaareCoding .singularDefault := by
  decide

/-! ### Countability and animacy, section 4.2

Plural marking descends the animacy hierarchy from the top ([smith-stark-1974]); the
collective/singulative class ascends it from below, since the more animate an entity the more it
is construed as occurring singly. Welsh's collective class stops at small and middle-sized
animals, Turkana's reaches types of people, Maltese's barely passes insects (Fig. 4). -/

/-- The simplified animacy hierarchy of Fig. 3. -/
inductive AnimacyTier where
  | inanimate
  | lowerAnimate
  | higherAnimate
  | human
  deriving DecidableEq, Repr, Fintype

/-- The tier's position on the hierarchy. -/
def AnimacyTier.toNat : AnimacyTier → ℕ
  | .inanimate => 0
  | .lowerAnimate => 1
  | .higherAnimate => 2
  | .human => 3

instance : LinearOrder AnimacyTier :=
  .lift' AnimacyTier.toNat (λ a b h => by cases a <;> cases b <;> simp_all [AnimacyTier.toNat])

/-- The tiers within the library's animacy ranks. -/
def AnimacyTier.toRank : AnimacyTier → Features.Prominence.AnimacyRank
  | .inanimate => .discreteInanimate
  | .lowerAnimate => .lowerAnimal
  | .higherAnimate => .higherAnimal
  | .human => .human

theorem AnimacyTier.toRank_monotone : Monotone (λ t : AnimacyTier => t.toRank.toNat) := by
  decide

/-- The three tripartite languages of Fig. 4. -/
inductive CollectiveLang where
  | maltese
  | welsh
  | turkana
  deriving DecidableEq, Repr, Fintype

/-- The highest animacy tier each language's collective/singulative class reaches (Fig. 4); the
class covers everything from inanimate aggregates up to it. -/
def collectiveCeiling : CollectiveLang → AnimacyTier
  | .maltese => .lowerAnimate
  | .welsh => .higherAnimate
  | .turkana => .human

/-- The collective regions nest, Maltese within Welsh within Turkana: each is the down-set of
its ceiling. -/
theorem collective_regions_nest :
    collectiveCeiling .maltese ≤ collectiveCeiling .welsh ∧
      collectiveCeiling .welsh ≤ collectiveCeiling .turkana := by
  decide

end Grimm2018
