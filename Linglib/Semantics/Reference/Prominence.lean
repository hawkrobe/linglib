import Mathlib.Order.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Referential prominence

This file defines the scales of referential prominence that condition differential argument
marking, and the marking grids over them.

The animacy and definiteness scales are those of Aissen. The fine-grained animacy hierarchy that
conditions nominal plural marking is that of Smith-Stark, as presented by Corbett. A marking
pattern says which cells of the grid of animacy and definiteness are marked, and Aissen's
staircase generalization says that the marked zone is an upper set in the product of the two
scales.

## Main declarations

* `AnimacyLevel`, `DefinitenessLevel`: the animacy and definiteness scales, as linear orders.
* `AnimacyRank`: the fine-grained hierarchy for plural marking, with the coarsening
  `AnimacyRank.toAnimacyLevel`.
* `MarkingPattern`: which cells of the grid of animacy and definiteness are marked, with the
  `MonotoneP` staircase, the cutoff constructors, and `monotoneP_iff_isUpperSet`.

What is specific to a paper lives with that paper: the scenario universals in
`Studies/Haspelmath2021.lean`, the OT typology in `Studies/Aissen2003.lean`, and the prominence
principle of differential indexing in `Studies/Just2024.lean`.

## References

* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
* [G. G. Corbett, *Number* (2000)][corbett-2000]
* [M. Haspelmath, *Role-Reference Associations and the Explanation of Argument Coding Splits*
  (2021)][haspelmath-2021]
* [T. C. Smith-Stark, *The Plurality Split* (1974)][smith-stark-1974]
-/

namespace Reference.Prominence

/-! ### The animacy scale -/

/-- The animacy prominence scale is Human > Animate > Inanimate. -/
inductive AnimacyLevel where
  /-- Human referents are the most prominent. -/
  | human
  /-- Non-human animates -/
  | animate
  /-- Inanimate referents are the least prominent. -/
  | inanimate
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The numeric rank on the animacy scale is 2 for Human, 1 for Animate and 0 for Inanimate. -/
def AnimacyLevel.rank : AnimacyLevel → Nat
  | .human     => 2
  | .animate   => 1
  | .inanimate => 0

/-- Inanimate < Animate < Human (ordered by prominence rank). -/
instance : LinearOrder AnimacyLevel :=
  LinearOrder.lift' AnimacyLevel.rank
    (fun a b h ↦ by cases a <;> cases b <;> simp_all [AnimacyLevel.rank])

/-- All animacy levels, most prominent first. -/
def AnimacyLevel.all : List AnimacyLevel := [.human, .animate, .inanimate]

/-! ### The fine-grained animacy hierarchy -/

/-- The fine-grained animacy hierarchy that conditions nominal plural marking is speaker > addressee
> 3rd person > kin > human > higher animals > lower animals > discrete inanimates > nondiscrete
inanimates. A language marking plural at a point on the scale marks it at all higher points. The
hierarchy refines the coarser `AnimacyLevel` through `toAnimacyLevel`. -/
inductive AnimacyRank where
  | speaker
  | addressee
  | thirdPerson
  | kin
  | human
  | higherAnimal
  | lowerAnimal
  | discreteInanimate
  | nondiscreteInanimate
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank (higher = more likely to be plural-marked). -/
def AnimacyRank.toNat : AnimacyRank → Nat
  | .speaker => 8
  | .addressee => 7
  | .thirdPerson => 6
  | .kin => 5
  | .human => 4
  | .higherAnimal => 3
  | .lowerAnimal => 2
  | .discreteInanimate => 1
  | .nondiscreteInanimate => 0

/-- Nondiscrete inanimate < ... < speaker (ordered by rank). -/
instance : LinearOrder AnimacyRank :=
  LinearOrder.lift' AnimacyRank.toNat
    (fun a b h ↦ by cases a <;> cases b <;> simp_all [AnimacyRank.toNat])

/-- All fine-grained ranks, most prominent first. -/
def AnimacyRank.all : List AnimacyRank :=
  [.speaker, .addressee, .thirdPerson, .kin, .human, .higherAnimal,
   .lowerAnimal, .discreteInanimate, .nondiscreteInanimate]

/-- Coarsen the fine-grained hierarchy to the three-level scale:
    speaker through human → `.human`, the animal ranks → `.animate`,
    the inanimate ranks → `.inanimate`. -/
def AnimacyRank.toAnimacyLevel : AnimacyRank → AnimacyLevel
  | .speaker | .addressee | .thirdPerson | .kin | .human => .human
  | .higherAnimal | .lowerAnimal => .animate
  | .discreteInanimate | .nondiscreteInanimate => .inanimate

/-- Coarsening preserves the scale order. -/
theorem AnimacyRank.toAnimacyLevel_monotone : Monotone AnimacyRank.toAnimacyLevel :=
  fun a b h ↦
    (by decide : ∀ a b : AnimacyRank, a ≤ b → a.toAnimacyLevel ≤ b.toAnimacyLevel) a b h

/-! ### The definiteness scale -/

/-- The definiteness prominence scale is Personal Pronoun > Proper Name > Definite NP > Indefinite
Specific > Non-specific. -/
inductive DefinitenessLevel where
  /-- Personal pronouns are the most prominent. -/
  | personalPronoun
  /-- Proper names -/
  | properName
  /-- Definite NPs (with article or demonstrative) -/
  | definite
  /-- Indefinite but specific NPs -/
  | indefiniteSpecific
  /-- Non-specific indefinites are the least prominent. -/
  | nonSpecific
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank on the definiteness scale:
    Pronoun (4) > Proper (3) > Definite (2) > IndSp (1) > NonSp (0). -/
def DefinitenessLevel.rank : DefinitenessLevel → Nat
  | .personalPronoun    => 4
  | .properName         => 3
  | .definite           => 2
  | .indefiniteSpecific => 1
  | .nonSpecific        => 0

/-- NonSpecific < IndefiniteSpecific < Definite < ProperName < PersonalPronoun
    (ordered by prominence rank). -/
instance : LinearOrder DefinitenessLevel :=
  LinearOrder.lift' DefinitenessLevel.rank
    (fun a b h ↦ by cases a <;> cases b <;> simp_all [DefinitenessLevel.rank])

/-- All definiteness levels, most prominent first. -/
def DefinitenessLevel.all : List DefinitenessLevel :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

/-! ### Differential marking patterns -/

/-- A differential-marking pattern says which cells in the grid of animacy and definiteness receive
overt differential marking, for whatever argument role and channel a consumer pairs the pattern
with. It is a `def` and not an `abbrev`, so that the checkers below are accessible by dot notation.
-/
def MarkingPattern := AnimacyLevel → DefinitenessLevel → Bool

namespace MarkingPattern

/-- Marking is closed under moving up both scales, the upper-set staircase appropriate to P/T
marking. -/
def MonotoneP (p : MarkingPattern) : Prop :=
  ∀ a a' d d', a ≤ a' → d ≤ d' → p a d = true → p a' d' = true

/-- The pattern depends only on animacy. -/
def AnimacyOnly (p : MarkingPattern) : Prop :=
  ∀ a d d', p a d = p a d'

/-- The pattern depends only on definiteness. -/
def DefinitenessOnly (p : MarkingPattern) : Prop :=
  ∀ a a' d, p a d = p a' d

instance : DecidablePred MonotoneP := fun p ↦ by unfold MonotoneP; infer_instance
instance : DecidablePred AnimacyOnly := fun p ↦ by unfold AnimacyOnly; infer_instance
instance : DecidablePred DefinitenessOnly := fun p ↦ by
  unfold DefinitenessOnly; infer_instance

/-- `MonotoneP` is upper-set closure of the marked zone in the product prominence order. -/
theorem monotoneP_iff_isUpperSet (p : MarkingPattern) :
    p.MonotoneP ↔
      IsUpperSet {c : AnimacyLevel × DefinitenessLevel | p c.1 c.2 = true} :=
  ⟨fun h _ _ hle hm ↦ h _ _ _ _ hle.1 hle.2 hm,
    fun h _ _ _ _ ha hd hm ↦ h (Prod.mk_le_mk.mpr ⟨ha, hd⟩) hm⟩

/-! ### One-dimensional cutoff patterns -/

/-- The pattern that marks the cells at or above an animacy cutoff, as in P/T-type marking. Its
marked zone is `Set.Ici cutoff` on the animacy axis. -/
def animacyAtLeast (cutoff : AnimacyLevel) : MarkingPattern :=
  fun a _ ↦ decide (cutoff ≤ a)

/-- Mark the cells at or above a definiteness cutoff (P/T-type marking). -/
def definitenessAtLeast (cutoff : DefinitenessLevel) : MarkingPattern :=
  fun _ d ↦ decide (cutoff ≤ d)

end MarkingPattern

end Reference.Prominence
