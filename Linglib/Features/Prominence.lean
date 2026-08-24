import Mathlib.Order.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Markedness
import Linglib.Features.Person.Basic

/-!
# Referential prominence

The referential-prominence scales that condition differential argument
marking, and the marking grids over them.

## Main declarations

- `AnimacyLevel`, `DefinitenessLevel` — the animacy and definiteness
  scales, as `LinearOrder`s; `AnimacyRank` — the fine-grained
  plural-marking hierarchy, with the coarsening
  `AnimacyRank.toAnimacyLevel`.
- `Person.prominence` — graded person prominence over the canonical
  `Person` inventory.
- `MarkingPattern` — which cells of the animacy × definiteness grid are
  marked; the `MonotoneP`/`MonotoneA` staircases, cutoff constructors, and
  `monotoneP_iff_isUpperSet`.

Paper-specific apparatus lives with its papers: the scenario machinery and
frequency proxies in `Studies/Haspelmath2021.lean`, the OT typology in
`Studies/Aissen2003.lean`, the indexing survey in `Studies/Just2024.lean`.

## References

* [aissen-2003]
* [corbett-2000]
* [haspelmath-2021]
* [just-2024]
* [smith-stark-1974]
-/

namespace Features.Prominence

/-! ### The animacy scale -/

/-- The animacy prominence scale, [aissen-2003]'s (4a):
    Human > Animate > Inanimate. -/
inductive AnimacyLevel where
  /-- Most prominent: human referents -/
  | human
  /-- Non-human animates -/
  | animate
  /-- Least prominent: inanimate referents -/
  | inanimate
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank on the animacy scale: Human (2) > Animate (1) > Inanimate (0). -/
def AnimacyLevel.rank : AnimacyLevel → Nat
  | .human     => 2
  | .animate   => 1
  | .inanimate => 0

/-- Inanimate < Animate < Human (ordered by prominence rank). -/
instance : LinearOrder AnimacyLevel :=
  LinearOrder.lift' AnimacyLevel.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [AnimacyLevel.rank])

/-- All animacy levels, most prominent first. -/
def AnimacyLevel.all : List AnimacyLevel := [.human, .animate, .inanimate]

/-! ### The fine-grained animacy hierarchy -/

/-- The fine-grained animacy hierarchy conditioning nominal plural marking
    ([smith-stark-1974], as presented by [corbett-2000]):

      speaker > addressee > 3rd person > kin > human > higher animals >
      lower animals > discrete inanimates > nondiscrete inanimates

    A language marking plural at a point on the scale marks it at all
    higher points. Refines the coarser `AnimacyLevel` via
    `toAnimacyLevel`. -/
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
    (fun a b h => by cases a <;> cases b <;> simp_all [AnimacyRank.toNat])

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
  fun a b h =>
    (by decide : ∀ a b : AnimacyRank, a ≤ b → a.toAnimacyLevel ≤ b.toAnimacyLevel) a b h

/-! ### The definiteness scale -/

/-- The definiteness prominence scale, [aissen-2003]'s (4b):
    Personal Pronoun > Proper Name > Definite NP > Indefinite Specific >
    Non-specific. -/
inductive DefinitenessLevel where
  /-- Most prominent: personal pronouns -/
  | personalPronoun
  /-- Proper names -/
  | properName
  /-- Definite NPs (with article or demonstrative) -/
  | definite
  /-- Indefinite but specific NPs -/
  | indefiniteSpecific
  /-- Least prominent: non-specific indefinites -/
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
    (fun a b h => by cases a <;> cases b <;> simp_all [DefinitenessLevel.rank])

/-- All definiteness levels, most prominent first. -/
def DefinitenessLevel.all : List DefinitenessLevel :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

/-! ### Person prominence -/

/-- Graded person prominence over the canonical `Person` inventory:
    1st (2) > 2nd (1) > 3rd (0). The load-bearing cut is locuphoric
    (1st/2nd) > aliophoric (3rd) — [haspelmath-2021]'s person scale (8a);
    the ranking of 1st over 2nd within the locuphoric zone follows the
    person-hierarchy tradition and varies across languages.
    Clusivity-marked firsts rank with `first`; the impersonal `zero` is
    `[−participant]` and ranks with third. -/
def _root_.Person.prominence : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 2
  | .second => 1
  | .third | .zero => 0

/-! ### Differential marking patterns -/

/-- A differential-marking pattern: which cells in the animacy × definiteness
    grid receive overt differential marking, for whatever argument role and
    channel a consumer pairs the pattern with ([aissen-2003] flagging,
    [just-2024] indexing). A `def`, not an `abbrev`, so the checkers below
    are dot-accessible. -/
def MarkingPattern := AnimacyLevel → DefinitenessLevel → Bool

namespace MarkingPattern

/-- Marking is closed under moving up both scales — the upper-set staircase
    of [aissen-2003]'s (33b), appropriate to P/T marking and extended to
    P indexing by [just-2024]. -/
def MonotoneP (p : MarkingPattern) : Prop :=
  ∀ a a' d d', a ≤ a' → d ≤ d' → p a d = true → p a' d' = true

/-- Marking closed downward — the mirror image appropriate to A/R marking
    ([just-2024]). -/
def MonotoneA (p : MarkingPattern) : Prop :=
  ∀ a a' d d', a' ≤ a → d' ≤ d → p a d = true → p a' d' = true

/-- The pattern depends only on animacy. -/
def AnimacyOnly (p : MarkingPattern) : Prop :=
  ∀ a d d', p a d = p a d'

/-- The pattern depends only on definiteness. -/
def DefinitenessOnly (p : MarkingPattern) : Prop :=
  ∀ a a' d, p a d = p a' d

instance : DecidablePred MonotoneP := λ p => by unfold MonotoneP; infer_instance
instance : DecidablePred MonotoneA := λ p => by unfold MonotoneA; infer_instance
instance : DecidablePred AnimacyOnly := λ p => by unfold AnimacyOnly; infer_instance
instance : DecidablePred DefinitenessOnly := λ p => by
  unfold DefinitenessOnly; infer_instance

/-- **The transfer equation**: `MonotoneP` is upper-set closure of the marked
    zone in the product prominence order — [aissen-2003]'s (33b), with the
    product order of the paper's fn. 23. -/
theorem monotoneP_iff_isUpperSet (p : MarkingPattern) :
    p.MonotoneP ↔
      IsUpperSet {c : AnimacyLevel × DefinitenessLevel | p c.1 c.2 = true} :=
  ⟨λ h _ _ hle hm => h _ _ _ _ hle.1 hle.2 hm,
    λ h _ _ _ _ ha hd hm => h (Prod.mk_le_mk.mpr ⟨ha, hd⟩) hm⟩

/-! ### One-dimensional cutoff patterns -/

/-- Mark the cells at or above an animacy cutoff — P/T-type marking; the
    marked zone is `Core.Order.atOrAbove` on the animacy axis. -/
def animacyAtLeast (cutoff : AnimacyLevel) : MarkingPattern :=
  λ a _ => decide (cutoff ≤ a)

/-- Mark the cells at or above a definiteness cutoff (P/T-type marking). -/
def definitenessAtLeast (cutoff : DefinitenessLevel) : MarkingPattern :=
  λ _ d => decide (cutoff ≤ d)

/-- Mark the cells at or below an animacy cutoff — A/R-type marking; the
    marked zone is the complementary lower set. -/
def animacyAtMost (cutoff : AnimacyLevel) : MarkingPattern :=
  λ a _ => decide (a ≤ cutoff)

/-- Mark the cells at or below a definiteness cutoff (A/R-type marking). -/
def definitenessAtMost (cutoff : DefinitenessLevel) : MarkingPattern :=
  λ _ d => decide (d ≤ cutoff)

end MarkingPattern

end Features.Prominence
