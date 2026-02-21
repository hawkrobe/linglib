import Mathlib.Data.Rat.Defs

/-!
# Social Meaning and the Indexical Field @cite{eckert-2008}

Framework-agnostic types for the social meaning of linguistic variation,
following Eckert's (2008) theory of the indexical field.

A linguistic variable's social meaning is not a fixed correspondence to a
social category but a constellation of ideologically linked persona
traits — an *indexical field* — that can be selectively activated by
context.

## Core concepts

**Indexical order** (Silverstein 2003): variables accumulate layers of
social meaning. First-order (demographic correlation, below awareness) →
second-order (stylistic marker, available for manipulation) → third-order
(stereotype, subject to metapragmatic commentary).

**Stances vs. qualities** (Ochs 1992, Eckert 2008): variables directly
index interactional *stances* (momentary positions like "being precise
right now"). Habitual stances accrete into attributed *qualities* (stable
traits like "is meticulous"). Social meaning mediates between form and
identity through this stance → quality pathway.

**Indexical field**: the constellation of potential meanings associated
with a variant. Not a fixed meaning but a structured space — each use
activates a region of the field, contextually selecting among
ideologically linked traits (Figures 3–4 in Eckert 2008).

## Connections

* `Core.Register.SocialIndex`: competence/solidarity is one axis of the
  social space that indexical fields map into
* `RSA.CombinedUtility`: social utility as a component of speaker utility
* `RSA.NoncooperativeCommunication.SpeakerOrientation`: cooperative vs.
  argumentative as a coarse speaker-type dimension

## References

* Eckert, P. (2008). Variation and the indexical field.
  *J. Sociolinguistics* 12(4): 453–476.
* Silverstein, M. (2003). Indexical order and the dialectics of
  sociolinguistic life.
* Ochs, E. (1992). Indexing gender.
-/

namespace Core.SocialMeaning

-- ============================================================================
-- Indexical order (Silverstein 2003)
-- ============================================================================

/-- Silverstein's (2003) indexical order: how a variable's social meaning
    accumulates layers through use and metapragmatic awareness.

    Each order presupposes the previous: a variable must correlate with a
    social category (first-order) before speakers can consciously manipulate
    it (second-order), and must be a marker before it can become a stereotype
    subject to overt commentary (third-order). -/
inductive IndexicalOrder where
  /-- Correlates with a social category but below conscious awareness. -/
  | first
  /-- Noticed and available for stylistic manipulation (Labov's "marker"). -/
  | second
  /-- Stereotype: subject to metapragmatic commentary and performance. -/
  | third
  deriving DecidableEq, BEq, Repr

def IndexicalOrder.toNat : IndexicalOrder → Nat
  | .first => 0 | .second => 1 | .third => 2

instance : LT IndexicalOrder where
  lt a b := a.toNat < b.toNat

instance : LE IndexicalOrder where
  le a b := a.toNat ≤ b.toNat

instance (a b : IndexicalOrder) : Decidable (a < b) :=
  Nat.decLt a.toNat b.toNat

instance (a b : IndexicalOrder) : Decidable (a ≤ b) :=
  Nat.decLe a.toNat b.toNat

theorem first_lt_second : IndexicalOrder.first < IndexicalOrder.second := by decide
theorem second_lt_third : IndexicalOrder.second < IndexicalOrder.third := by decide

-- ============================================================================
-- Stances and qualities (Ochs 1992, Eckert 2008)
-- ============================================================================

/-- Eckert's distinction between momentary interactional positions and
    stable attributed characteristics.

    Variables directly index stances. Qualities are attributed on the basis
    of habitual stance-taking: a person who habitually takes precise stances
    gets attributed the quality "meticulous" (Beltrama & Schwarz 2024). -/
inductive StanceLevel where
  /-- Momentary interactional position (e.g., "being precise right now"). -/
  | stance
  /-- Stable attributed characteristic (e.g., "is a meticulous person").
      Accretes from habitual stances. -/
  | quality
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Indexical field (Eckert 2008)
-- ============================================================================

/-- An indexical field (Eckert 2008): the constellation of ideologically
    related meanings associated with a linguistic variable.

    Parameterized by:
    * `Variant`: variant forms of the variable (e.g., round vs. precise numeral)
    * `Trait`: persona traits in the field (e.g., meticulous, casual, ...)

    The `association` function maps each (variant, trait) pair to a rational
    value. Positive values mean the variant indexes *toward* the trait;
    negative values mean it indexes *away*. The field is context-dependent:
    the same variable may have different fields in different contexts
    (Eckert 2008: "the field is a space of potential meanings"). -/
structure IndexicalField (Variant : Type) (Trait : Type) where
  /-- How strongly using this variant indexes this trait.
      Positive = toward, negative = away from. -/
  association : Variant → Trait → ℚ
  /-- Indexical order of this variable. -/
  order : IndexicalOrder

/-- Two variants *contrast* on a trait when their associations differ. -/
def IndexicalField.contrasts {Variant Trait : Type}
    (field : IndexicalField Variant Trait) (v₁ v₂ : Variant) (t : Trait) : Prop :=
  field.association v₁ t ≠ field.association v₂ t

/-- A variant *positively indexes* a trait. -/
def IndexicalField.indexes {Variant Trait : Type}
    (field : IndexicalField Variant Trait) (v : Variant) (t : Trait) : Prop :=
  field.association v t > 0

-- ============================================================================
-- Social meaning dimensions
-- ============================================================================

-- `SocialDimension` (Fiske et al.'s competence/warmth/antiSolidarity axes)
-- has moved to `Theories/Sociolinguistics/SCM.lean`, where it belongs as part
-- of the Stereotype Content Model theory rather than framework-agnostic Core.

end Core.SocialMeaning
