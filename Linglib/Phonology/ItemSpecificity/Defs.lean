import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

/-!
# Lexical-frequency channels — the abstract interface

A *frequency channel* on a lexicon is an attachment of a per-item
log-frequency to lexical entries. Once a lexicon carries one, downstream
phonology can be conditioned on it; the sibling files
(`IndexedConstraints`, `ScaledWeights`, `UseListed`,
`RepresentationStrength`) each formalize one such conditioning theory
and carry their own foundational citations.

This file is `Defs.lean` in the mathlib sense: a thin typeclass layer
that diverse `Fragments/{Lang}/` lexical-entry types can implement
without inheriting from a single bundled record. Sibling files
(`IndexedConstraints.lean`, `ScaledWeights.lean`, `UseListed.lean`,
`RepresentationStrength.lean`) use only this interface.

## Why a typeclass and not a record

Each `Fragments/{Lang}/Prosody.lean` defines its own lexical-entry
record (`JLexicalEntry`, `ELexicalEntry`, ...). A bundled
`FrequencyAnnotated` super-record would force every fragment into a
single inheritance hierarchy. Instead, fragments **implement**
`HasTokenFreq` on their own types, mirroring mathlib's `HasAdd`,
`Mul`, `One`. Same logic as the project's existing typeclass
discipline (e.g., `HasAltList`, `IsBoundaryVacuous`).

A type-frequency analogue (`HasTypeFreq`) would be the natural
sibling typeclass for productivity / wug-test predictions
([albright-hayes-2003]); it is not declared here because no
current theory in the directory consumes it. Add it when the first
such consumer lands.

## Log scale

All frequency channels in this directory are `LogFreq := ℝ`. The
log-transform is built into the channel because (a) log-frequency is the
empirically standard predictor and (b) frequency-scaled-weight theories
([coetzee-pater-2008]) are linear in log-frequency. Theories that
want raw counts can `Real.exp ∘ tokenLogFreq`.
-/

namespace Constraints.ItemSpecificity

-- ============================================================================
-- § 1: Frequency channels
-- ============================================================================

/-- Log-frequency: by convention, log of corpus token count. `none` is
    not encoded here — `HasTokenFreq` requires *some* annotation; pass
    a sentinel (e.g., 0 = log 1 = once) for unannotated items, or wrap
    with `Option`. -/
abbrev LogFreq : Type := ℝ

/-- A type whose values carry a token log-frequency annotation. -/
class HasTokenFreq (α : Type) where
  tokenLogFreq : α → LogFreq

export HasTokenFreq (tokenLogFreq)

-- ============================================================================
-- § 2: Trivial / null channels
-- ============================================================================

/-- The all-zero token-frequency channel. Useful as a default when a
    fragment has not been frequency-annotated and the downstream theory
    needs *some* `HasTokenFreq` instance to typecheck.

    Returning 0 (= log 1) means "every item attested exactly once" — a
    no-information prior. -/
@[reducible] def trivialTokenFreq (α : Type) : HasTokenFreq α := ⟨fun _ => (0 : ℝ)⟩

-- ============================================================================
-- § 3: Threshold predicate (shared by Indexed and UseListed)
-- ============================================================================

/-- An item is *above threshold* iff its token log-frequency reaches
    `threshold`. The shared primitive used by `Indexed.isCore` (stratum
    membership for indexed-constraint theories) and `UseListed.isListed`
    (storage gate for whole-word retrieval theories).

    Declared `abbrev` (= `@[reducible] def`) so that consumer proofs
    can `show (n : ℝ) ≥ threshold` directly without an explicit
    unfold step. -/
abbrev isAboveThreshold {α : Type} [HasTokenFreq α] (threshold : ℝ) (a : α) : Prop :=
  tokenLogFreq a ≥ threshold

/-- Classical decidability for `isAboveThreshold`. `Real`'s order is
    decidable only via `Classical.dec`, so all consumers downstream
    become `noncomputable`. Acceptable for theory specifications;
    concrete fitting routines operate over rationals or use a
    thresholded comparison directly. -/
noncomputable instance {α : Type} [HasTokenFreq α] (threshold : ℝ) :
    DecidablePred (isAboveThreshold (α := α) threshold) := fun _ => Classical.dec _

end Constraints.ItemSpecificity
