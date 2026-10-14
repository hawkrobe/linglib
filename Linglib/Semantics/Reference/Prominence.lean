module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Definiteness
public import Mathlib.Order.Nat
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Referential prominence

This file defines the scales of referential prominence that condition differential argument
marking, and the marking grids over them.

The animacy scale is `Reference.Animacy`. The definiteness scale is Aissen's, which extends the
definiteness hierarchy to proper names and personal pronouns and whose cut at the definites is
`Reference.Definiteness`. The animacy hierarchy that conditions nominal plural marking is
Haspelmath's, which refines Corbett's version of Smith-Stark's by splitting the animals into higher
and lower and the inanimates into discrete and nondiscrete. A marking pattern says which cells of
the grid of animacy and definiteness are marked, and Aissen's staircase generalization says that the
marked zone is an upper set in the product of the two scales.

## Main declarations

* `DefinitenessScale`: Aissen's definiteness scale, as a linear order, with its cut
  `DefinitenessScale.definiteness` at the definites.
* `AnimacyHierarchy`: the hierarchy of plural marking, from the speaker down to the nondiscrete
  inanimates.
* `atLeast`, `below`: the coding lengths of a cutoff split on a scale, the special coding on
  the values from a cutoff up, as P and T splits have it, or below it, as A and R splits do.
* `MarkingPattern`: which cells of the grid of animacy and definiteness are marked, with the
  `MonotoneP` staircase, the cutoff constructors, and `monotoneP_iff_isUpperSet`.

What is specific to a paper lives with that paper: the scenario universals in
`Studies/Haspelmath2021.lean`, the OT typology in `Studies/Aissen2003.lean`, and the prominence
principle of differential indexing in `Studies/Just2024.lean`.

## References

* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
* [G. G. Corbett, *Number* (2000)][corbett-2000]
* [M. Haspelmath, *Occurrence of Nominal Plurality* (2013)][haspelmath-2013b]
* [M. Haspelmath, *Role-Reference Associations and the Explanation of Argument Coding Splits*
  (2021)][haspelmath-2021]
* [T. C. Smith-Stark, *The Plurality Split* (1974)][smith-stark-1974]
-/

@[expose] public section

namespace Reference.Prominence

/-! ### The animacy hierarchy -/

/-- Haspelmath's animacy hierarchy of nominal plural marking runs speaker > addressee > third
person > kinship terms > other humans > higher animals > lower animals > discrete inanimates >
nondiscrete inanimates. Corbett's has one animate and one inanimate position, and splits the
animate one where Miya needs it. A language marking plural at a point on the hierarchy marks it
at all higher points. -/
inductive AnimacyHierarchy where
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

/-- The rank on the hierarchy, 8 for the speaker down to 0 for the nondiscrete inanimates. -/
def AnimacyHierarchy.rank : AnimacyHierarchy → ℕ
  | .speaker => 8
  | .addressee => 7
  | .thirdPerson => 6
  | .kin => 5
  | .human => 4
  | .higherAnimal => 3
  | .lowerAnimal => 2
  | .discreteInanimate => 1
  | .nondiscreteInanimate => 0

/-- The hierarchy is ordered by rank, the speaker at the top. -/
instance : LinearOrder AnimacyHierarchy := LinearOrder.lift' AnimacyHierarchy.rank (by decide)

/-! ### The definiteness scale -/

/-- A position on Aissen's definiteness scale, Pronoun > Name > Definite > Indefinite Specific >
NonSpecific, which extends the hierarchy definite > specific > non-specific to proper names and
personal pronouns. -/
inductive DefinitenessScale where
  | nonSpecific
  | indefiniteSpecific
  | definite
  | properName
  | personalPronoun
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace DefinitenessScale

/-- The rank on the scale, 0 for the non-specific indefinites up to 4 for the personal
pronouns. -/
def rank : DefinitenessScale → ℕ
  | .nonSpecific => 0
  | .indefiniteSpecific => 1
  | .definite => 2
  | .properName => 3
  | .personalPronoun => 4

instance : LinearOrder DefinitenessScale := LinearOrder.lift' rank (by decide)

/-- The positions, most prominent first. -/
def all : List DefinitenessScale :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

/-- The definiteness of a position: pronouns, names and definite NPs are definite, and the
indefinites, specific or not, indefinite. -/
def definiteness (d : DefinitenessScale) : Definiteness :=
  if .definite ≤ d then .definite else .indefinite

theorem definiteness_monotone : Monotone definiteness := by
  intro a b; revert a b; decide

end DefinitenessScale

/-! ### Cutoff splits -/

section Cutoff

variable {α : Type*} [LinearOrder α]

/-- The split that codes the values from `x` up specially is `1` at and above the cutoff and
`0` below it. -/
def atLeast (x y : α) : ℕ := if x ≤ y then 1 else 0

/-- The split that codes the values below `x` specially is `1` below the cutoff and `0` at and
above it. -/
def below (x y : α) : ℕ := if y < x then 1 else 0

theorem atLeast_monotone (x : α) : Monotone (atLeast x) := fun _ _ h ↦ by
  unfold atLeast
  split_ifs with h₁ h₂ <;> first | rfl | omega | exact absurd (h₁.trans h) h₂

theorem below_antitone (x : α) : Antitone (below x) := fun _ _ h ↦ by
  unfold below
  split_ifs with h₁ h₂ <;> first | rfl | omega | exact absurd (h.trans_lt h₁) h₂

end Cutoff

/-! ### Differential marking patterns -/

/-- A differential-marking pattern says which cells in the grid of animacy and definiteness receive
overt differential marking, for whatever argument role and channel a consumer pairs the pattern
with. It is a `def` and not an `abbrev`, so that the checkers below are accessible by dot notation.
-/
def MarkingPattern := Animacy → DefinitenessScale → Bool

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
      IsUpperSet {c : Animacy × DefinitenessScale | p c.1 c.2 = true} :=
  ⟨fun h _ _ hle hm ↦ h _ _ _ _ hle.1 hle.2 hm,
    fun h _ _ _ _ ha hd hm ↦ h (Prod.mk_le_mk.mpr ⟨ha, hd⟩) hm⟩

/-! ### One-dimensional cutoff patterns -/

/-- The pattern that marks the cells at or above an animacy cutoff, as in P/T-type marking. Its
marked zone is `Set.Ici cutoff` on the animacy axis. -/
def animacyAtLeast (cutoff : Animacy) : MarkingPattern :=
  fun a _ ↦ decide (cutoff ≤ a)

/-- Mark the cells at or above a definiteness cutoff (P/T-type marking). -/
def definitenessAtLeast (cutoff : DefinitenessScale) : MarkingPattern :=
  fun _ d ↦ decide (cutoff ≤ d)

end MarkingPattern

end Reference.Prominence
