import Mathlib.Order.Interval.Set.OrdConnected
import Linglib.Features.MassCount
import Linglib.Features.Number.Basic
import Linglib.Features.Prominence

/-!
# Grimm (2018) — Grammatical Number and the Scale of Individuation
[grimm-2018]

Formalizes the core framework of:

  Grimm, S. (2018). Grammatical number and the scale of individuation.
  *Language* 94(3). 527–574.

## Core contributions

1. **The scale of individuation** (his (17)/(19)): individuation types —
   equivalence classes of nominal descriptions by individuation
   properties — are linearly ordered:
   substance < granular aggregate < collective aggregate < individual.

2. **The order-preservation thesis** (his §3.4): a language's grammatical
   countability classes also partition nominal descriptions, and the
   classification map from individuation types to countability classes is
   **order-preserving**. Consequently every countability class is a
   *contiguous segment* of the scale — formally, the fibers of a monotone
   classification are `Set.OrdConnected` (the same mathlib predicate that
   states [harbour-2014]'s convexity condition in
   `Syntax/Minimalist/Phi/Recursion.lean`). His hypothetical
   discontinuous system (Table 21) is refuted by `decide`.

3. **Countability beyond the binary** (his §2): Welsh, Turkana, Maltese
   (tripartite: non-countable, collective/singulative, singular/plural) and
   Dagaare (four classes, including an inverse-marked one) against
   English's binary cut and Yudja's near-absent cut.

4. **The markedness/coding prediction** (his §4.4, after Jakobson and
   Greenberg): which value of a class's contrast is zero-coded tracks the
   class's position on the scale — single-reference default for highly
   individuated classes, multiple-reference default for aggregate classes
   (the singulative), no contrast at the bottom. Dagaare's inverse number
   marking is this prediction at work, *not* a `Number` value — confirming
   the canonical inventory's exclusion of `UD.Number.Inv`.

5. **Animacy refinement** (his §4.2): collective/singulative classes
   *ascend* the animacy hierarchy (inverse of Smith-Stark plural marking);
   the per-language collective regions nest (Maltese ⊆ Welsh ⊆ Turkana).

## Connections

* Countability classes are not `Number` values: Welsh collectives take
  plural agreement while Maltese collectives take singular ([grimm-2018]
  §2.1, §2.3), so the unit/aggregate contrast cross-cuts the agreement
  values — vindicating the value space of `Features/Number/Basic.lean`.
* Each class carries a `Number.System` (`WelshClass.system` etc.), so
  Grimm's classes plug into the implicational universals; this generalizes
  the two-class `CountMassNumberInteraction` of `Studies/Corbett2000.lean`.
* English's binary partition is `Features.MassCount`
  (`english_matches_massCount`) — the binary feature becomes the 2-cell
  instance of the scale, not a primitive.
* `countable : Bool` as a lexical field is refuted twice over: structurally
  by [borer-2005] (see `Studies/Borer2005.lean`) and scalarly here.
-/

set_option autoImplicit false

namespace Grimm2018


/-! ### The scale of individuation -/

/-- Individuation types ([grimm-2018] (17)/(19)): equivalence classes of
    nominal descriptions by individuation properties, from entities with no
    perceptible minimal units to fully independent individuals. The
    mereotopological content of the middle types (units clumped together
    vs. connected but separable) is the `SelfConnected` apparatus of
    `Core/Mereotopology.lean`. -/
inductive IndividuationType where
  /-- No perceptible minimal units (liquids, substances: *water*). -/
  | substance
  /-- Perceptible units, typically not separated from one another
      (*rice*, *sand*). -/
  | granularAggregate
  /-- Perceptible units, separated but spatially or functionally connected
      (*ants*, *cherries*). -/
  | collectiveAggregate
  /-- Independent, free-standing units (*dog*, *chair*). -/
  | individualEntity
  deriving DecidableEq, Repr, Fintype

namespace IndividuationType

/-- Numeric embedding preserving the individuation order. -/
def toNat : IndividuationType → Nat
  | .substance => 0
  | .granularAggregate => 1
  | .collectiveAggregate => 2
  | .individualEntity => 3

instance : LinearOrder IndividuationType :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end IndividuationType

/-! ### The order-preservation thesis

[grimm-2018] §3.4: nominal descriptions are partitioned both into
individuation types (Π_I, ordered by the scale) and into a language's
grammatical countability classes (Π_G, ordered); the thesis is that the
classification map is order-preserving (`Monotone`). The structural
consequence — each grammatical class is a contiguous segment of the scale,
"no category spans two disconnected segments" — is the `Set.OrdConnected`-ness
of the classification's fibers. -/

/-- A monotone classification has order-convex fibers: each countability
    class picks out a contiguous segment of the scale. One composition of
    mathlib primitives (`Set.ordConnected_singleton.preimage_mono`); the
    predicate is the same `Set.OrdConnected` that states [harbour-2014]'s
    convexity condition (`Mereology.ordConnected_iff_convexClosure_eq`). -/
theorem ordConnected_fiber_of_monotone {α C : Type*} [Preorder α]
    [PartialOrder C] {f : α → C} (hf : Monotone f) (c : C) :
    (f ⁻¹' {c}).OrdConnected :=
  Set.ordConnected_singleton.preimage_mono hf

/-! ### Per-language countability systems ([grimm-2018] §2, Tables 19–20)

Each language's classes are ordered by their scale position; the
classification maps are the language rows of Table 20 (Dagaare, Welsh,
English) and the §2 descriptions (Turkana §2.2, Maltese §2.3, Yudja §4.1).
Monotonicity is checked by `decide`; convexity of every class follows from
`ordConnected_fiber_of_monotone`. -/

/-- Welsh ([grimm-2018] §2.1, Table 2): tripartite — non-countable
    (*llefrith* 'milk'), collective/unit (*adar*/*ader-yn* 'birds/bird'),
    singular/plural (*cadair*/*cadair-iau* 'chair/chairs'). -/
inductive WelshClass where
  | nonCountable | collectiveUnit | singularPlural
  deriving DecidableEq, Repr, Fintype

namespace WelshClass

def toNat : WelshClass → Nat
  | .nonCountable => 0
  | .collectiveUnit => 1
  | .singularPlural => 2

instance : LinearOrder WelshClass :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end WelshClass

/-- Welsh's classification of the scale ([grimm-2018] Table 20 and fn. 20):
    substances are non-countable, granular and collective aggregates fall in
    the collective/unit class, individuals in singular/plural. -/
def welshClassify : IndividuationType → WelshClass
  | .substance => .nonCountable
  | .granularAggregate => .collectiveUnit
  | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

/-- Welsh respects the scale ([grimm-2018] fn. 20 works this case). -/
theorem welsh_monotone : Monotone welshClassify := by decide

/-- Turkana ([grimm-2018] §2.2, Tables 5–7) patterns with Welsh: same
    tripartite shape, with the collective/singulative class reaching types
    of people (the animacy difference is §4.2 material, not a different
    class structure on the four-type scale). -/
abbrev turkanaClassify : IndividuationType → WelshClass := welshClassify

/-- Maltese ([grimm-2018] §2.3, Tables 8–11): same tripartite shape;
    differs in agreement (collective is formally singular) and in admitting
    foodstuffs/materials with conventional-portion singulatives. -/
abbrev malteseClassify : IndividuationType → WelshClass := welshClassify

/-- Dagaare ([grimm-2018] §2.4, Table 20): four classes — non-countable,
    optional-singulative non-countable (*-ruu*, granular aggregates),
    plural-default countable (*-ri* codes the singular: inverse marking),
    and singular-default countable (*-ri* codes the plural). -/
inductive DagaareClass where
  | nonCountable | singulativeNonCount | pluralDefault | singularDefault
  deriving DecidableEq, Repr, Fintype

namespace DagaareClass

def toNat : DagaareClass → Nat
  | .nonCountable => 0
  | .singulativeNonCount => 1
  | .pluralDefault => 2
  | .singularDefault => 3

instance : LinearOrder DagaareClass :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end DagaareClass

/-- Dagaare's classification ([grimm-2018] Table 20): each individuation
    type gets its own grammatical class — the partition is exactly as
    fine-grained as the scale. -/
def dagaareClassify : IndividuationType → DagaareClass
  | .substance => .nonCountable
  | .granularAggregate => .singulativeNonCount
  | .collectiveAggregate => .pluralDefault
  | .individualEntity => .singularDefault

theorem dagaare_monotone : Monotone dagaareClassify := by decide

/-- English ([grimm-2018] Table 20): binary — non-countable covers
    substances *and* aggregates (*foliage*, *rice*), singular/plural covers
    individuals. -/
inductive EnglishClass where
  | nonCountable | singularPlural
  deriving DecidableEq, Repr, Fintype

namespace EnglishClass

def toNat : EnglishClass → Nat
  | .nonCountable => 0
  | .singularPlural => 1

instance : LinearOrder EnglishClass :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end EnglishClass

def englishClassify : IndividuationType → EnglishClass
  | .individualEntity => .singularPlural
  | _ => .nonCountable

theorem english_monotone : Monotone englishClassify := by decide

/-- Yudja ([grimm-2018] §4.1, Table 24): the limiting case — only the most
    highly individuated nouns (humans) manifest grammatical number (optional
    *-i*); everything else is unspecified. Formally the same binary shape as
    English with the cut moved to the top of the scale; we record it through
    `EnglishClass` with its own classification. -/
def yudjaClassify : IndividuationType → EnglishClass
  | _ => .nonCountable

theorem yudja_monotone : Monotone yudjaClassify := by decide

/-! ### The impossible system ([grimm-2018] Table 21)

A hypothetical language whose singular/plural class covers granular
aggregates and individuals while a distinct collective/singulative class
intervenes. The singular/plural fiber is discontinuous on the scale, so no
order on the classes makes the classification monotone. -/

/-- Table 21's "Bad System": granular aggregates and individuals share a
    class that excludes the intervening collective aggregates. -/
def badClassify : IndividuationType → WelshClass
  | .substance => .nonCountable
  | .granularAggregate => .singularPlural
  | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

/-- The Bad System's singular/plural class is *not* a contiguous segment of
    the scale. -/
theorem bad_fiber_not_ordConnected :
    ¬ (badClassify ⁻¹' {WelshClass.singularPlural}).OrdConnected := by
  intro h
  have : badClassify .collectiveAggregate = .singularPlural :=
    h.out (x := .granularAggregate) rfl (y := .individualEntity) rfl
      ⟨by decide, by decide⟩
  exact absurd this (by decide)

/-- Hence no partial order on the classes makes the Bad System
    order-preserving ([grimm-2018] fn. 21): with the given class order it is
    not monotone, and `ordConnected_fiber_of_monotone` rules out every
    other order as well. -/
theorem bad_not_monotone (po : PartialOrder WelshClass) :
    letI := po
    ¬ Monotone badClassify := by
  letI := po
  exact fun hf =>
    bad_fiber_not_ordConnected (ordConnected_fiber_of_monotone hf _)

/-! ### Coding and markedness ([grimm-2018] §3.4 Table 20, §4.4)

Each class codes one value of its contrast overtly and leaves the other
zero. The prediction (after Jakobson, Greenberg via [grimm-2018] §4.4): the
default (zero-coded) designation tracks individuation — multiple-reference
default for aggregate classes, single-reference default for individual
classes. Dagaare's *inverse number marking* is the visible signature: the
same morpheme *-ri* codes plural on singular-default nouns and singular on
plural-default nouns. The inverse is a *coding* fact, not a number value —
`UD.Number.Inv` has no `Number` preimage by design
(`Features/Number/Basic.lean`). -/

/-- The coding pattern of a countability class ([grimm-2018] Table 20):
    which value, if any, is overtly coded against a zero-coded default. -/
inductive ClassCoding where
  /-- No number contrast (Welsh *llefrith* 'milk'). -/
  | noContrast
  /-- Zero-coded aggregate, coded unit — the singulative
      (Welsh *-yn*, Turkana, Maltese *-a*, Dagaare *-ruu*). -/
  | codedUnit
  /-- Zero-coded plural, coded singular (Dagaare *-ri* on plural-default
      nouns: inverse marking). -/
  | codedSingular
  /-- Zero-coded singular, coded plural (English *-s*, Welsh *-au*,
      Dagaare *-ri* on singular-default nouns). -/
  | codedPlural
  deriving DecidableEq, Repr, Fintype

/-- The default (zero-coded) designation of a class: nothing, multiple
    referents, or a single referent. -/
inductive DefaultReference where
  | none | multiple | single
  deriving DecidableEq, Repr, Fintype

namespace DefaultReference

def toNat : DefaultReference → Nat
  | .none => 0
  | .multiple => 1
  | .single => 2

instance : LinearOrder DefaultReference :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end DefaultReference

/-- What a coding pattern leaves as the zero-coded default. -/
def ClassCoding.default : ClassCoding → DefaultReference
  | .noContrast => .none
  | .codedUnit => .multiple
  | .codedSingular => .multiple
  | .codedPlural => .single

/-- Welsh coding by class (Table 20): 0 / 0+singulative *-yn* /
    0+plural *-au*. -/
def welshCoding : WelshClass → ClassCoding
  | .nonCountable => .noContrast
  | .collectiveUnit => .codedUnit
  | .singularPlural => .codedPlural

/-- Dagaare coding by class (Table 20): 0 / optional singulative *-ruu* /
    inverse singular *-ri* / plural *-ri*. -/
def dagaareCoding : DagaareClass → ClassCoding
  | .nonCountable => .noContrast
  | .singulativeNonCount => .codedUnit
  | .pluralDefault => .codedSingular
  | .singularDefault => .codedPlural

/-- English coding by class: 0 / plural *-s*. -/
def englishCoding : EnglishClass → ClassCoding
  | .nonCountable => .noContrast
  | .singularPlural => .codedPlural

/-! **The markedness prediction** ([grimm-2018] §4.4): along the scale, the
zero-coded default ascends none → multiple → single — the more individuated
the class, the more likely single reference is the default. Verified per
language. -/

theorem welsh_default_monotone :
    Monotone (fun i => (welshCoding (welshClassify i)).default) := by decide

theorem dagaare_default_monotone :
    Monotone (fun i => (dagaareCoding (dagaareClassify i)).default) := by
  decide

theorem english_default_monotone :
    Monotone (fun i => (englishCoding (englishClassify i)).default) := by
  decide

/-- Dagaare's two *-ri* classes differ only in coding direction — the
    formal content of "inverse number marking" ([grimm-2018] §2.4,
    Tables 15–17). -/
theorem dagaare_inverse_marking :
    (dagaareCoding .pluralDefault).default = .multiple ∧
    (dagaareCoding .singularDefault).default = .single ∧
    dagaareCoding .pluralDefault ≠ dagaareCoding .singularDefault := by
  decide

/-! ### Classes carry number systems

A countability class determines which `Number` values its nouns contrast —
the per-class generalization of `Corbett2000.CountMassNumberInteraction`
(count system vs. mass system). All class systems satisfy the implicational
universals. -/

/-- The `Number.System` a Welsh countability class makes available. The
    collective/unit class contrasts an aggregate with a unit; its
    *agreement* values are singular and plural ([grimm-2018] (5)–(6):
    collective *adar* takes plural agreement, singulative *ader-yn*
    singular), so its system coincides with singular/plural — the class
    difference lives in coding (`welshCoding`), not in the value
    inventory. -/
def WelshClass.system : WelshClass → Number.System
  | .nonCountable => { name := "Welsh non-countable", values := [] }
  | .collectiveUnit =>
      { name := "Welsh collective/unit", values := [.singular, .plural] }
  | .singularPlural =>
      { name := "Welsh singular/plural", values := [.singular, .plural] }

/-- Every Welsh class system satisfies the implicational universals. -/
theorem welsh_systems_wellFormed : ∀ c : WelshClass, c.system.WellFormed := by
  decide

/-! ### English's binary cut is `MassCount`

[grimm-2018]'s Table 20 row for English *is* the mass/count distinction:
the binary feature of `Features/MassCount.lean` is the 2-cell instance of a
scale partition, not an independent primitive. (Lexical `countable : Bool`
is refuted structurally by [borer-2005] and scalarly here — the field's
honest replacement is an individuation type.) -/

/-- English's countability classes through `MassCount`. -/
def englishMassCount : IndividuationType → MassCount
  | .individualEntity => .count
  | _ => .mass

/-- The English classification and the mass/count feature are the same
    partition. -/
theorem english_matches_massCount :
    ∀ i, englishClassify i = .singularPlural ↔ englishMassCount i = .count := by
  decide

/-! ### Animacy refinement ([grimm-2018] §4.2)

Collective/singulative classes interact with animacy *inversely* to
Smith-Stark plural marking: plural marking descends the animacy hierarchy
from the top, while collective classes ascend it from below — Welsh's
collective class stops at inanimates and small/mid animals, Turkana's
reaches types of people, Maltese's is essentially limited to insects.
Membership regions nest along animacy. We record the animacy reach of the
collective class on the simplified hierarchy [grimm-2018] adopts
(human > higher animate > lower animate > inanimate, after Haspelmath's
higher/lower animate split) and verify the nesting; the full
animacy-individuation product lattice (his Fig. 3) and the connectedness
conjecture over it are left as the documented next step. -/

/-- Simplified animacy tiers for the collective class ([grimm-2018] §4.2). -/
inductive AnimacyTier where
  | inanimate | lowerAnimate | higherAnimate | human
  deriving DecidableEq, Repr, Fintype

namespace AnimacyTier

def toNat : AnimacyTier → Nat
  | .inanimate => 0
  | .lowerAnimate => 1
  | .higherAnimate => 2
  | .human => 3

instance : LinearOrder AnimacyTier :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end AnimacyTier

/-- Grimm's simplified tiers refine into the library's animacy substrate
    (`Features.Prominence.AnimacyRank`, the scale `Studies/Corbett2000.lean`
    states the Animacy Hierarchy constraints over). -/
def AnimacyTier.toRank : AnimacyTier → Features.Prominence.AnimacyRank
  | .inanimate => .discreteInanimate
  | .lowerAnimate => .lowerAnimal
  | .higherAnimate => .higherAnimal
  | .human => .human

/-- The refinement preserves the animacy order (stated through
    `AnimacyRank.toNat`, the substrate's ranking). -/
theorem AnimacyTier.toRank_monotone :
    Monotone (fun t : AnimacyTier => (t.toRank).toNat) := by decide

/-- The three languages with tripartite systems, as anchors for the §4.2
    animacy data. -/
inductive CollectiveLang where
  | maltese | welsh | turkana
  deriving DecidableEq, Repr, Fintype

/-- The animacy ceiling of each language's collective/singulative class
    ([grimm-2018] §4.2, Fig. 4): Maltese ≈ insects (lower animates), Welsh
    ≈ small and mid-sized animals (higher animates), Turkana ≈ types of
    people (humans). The region is upward-bounded: everything from
    inanimate aggregates up to the ceiling. -/
def collectiveCeiling : CollectiveLang → AnimacyTier
  | .maltese => .lowerAnimate
  | .welsh => .higherAnimate
  | .turkana => .human

/-- The collective regions nest along animacy: Maltese ⊆ Welsh ⊆ Turkana
    ([grimm-2018] Fig. 4). Since each region is the down-set of its
    ceiling, nesting is ceiling order. -/
theorem collective_regions_nest :
    collectiveCeiling .maltese ≤ collectiveCeiling .welsh ∧
    collectiveCeiling .welsh ≤ collectiveCeiling .turkana := by decide

end Grimm2018
