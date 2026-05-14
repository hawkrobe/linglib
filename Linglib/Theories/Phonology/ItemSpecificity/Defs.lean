import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

/-!
# Lexical-frequency channels — the abstract interface

A *frequency channel* on a lexicon is an attachment of a per-item
log-frequency to lexical entries. Once a lexicon carries one, downstream
phonology can be conditioned on it: indexed constraints
(@cite{pater-2010}), frequency-scaled weights (@cite{coetzee-pater-2008},
@cite{coetzee-kawahara-2013}), gradient/listed representations
(@cite{moore-cantwell-2021}, @cite{smolensky-goldrick-2016}), or
whole-word retrieval (@cite{zuraw-2000}).

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
`HasTokenFreq` (and optionally `HasTypeFreq`) on their own types,
mirroring mathlib's `HasAdd`, `Mul`, `One`. Same logic as the project's
existing typeclass discipline (e.g., `HasAltList`, `IsBoundaryVacuous`).

## Token vs. type frequency

The two are conceptually orthogonal. Token frequency counts every
occurrence in a corpus (the central conditioning variable in usage-based
phonology); type frequency counts distinct lexical items in a pattern
(the central conditioning variable in productivity / wug-test
predictions). They sometimes correlate but theories diverge over which
matters for which alternation. Two separate classes keeps the
distinction explicit at the type level.

## Log scale

All frequency channels in this directory are `LogFreq := ℝ`. The
log-transform is built into the channel because (a) log-frequency is the
empirically standard predictor and (b) frequency-scaled-weight theories
(@cite{coetzee-pater-2008}) are linear in log-frequency. Theories that
want raw counts can `Real.exp ∘ tokenLogFreq`.
-/

namespace Phonology.LexicalFrequency

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

/-- A type whose values carry a type log-frequency annotation. Distinct
    from `HasTokenFreq`: type frequency counts wordforms exemplifying a
    pattern; token frequency counts running corpus occurrences. -/
class HasTypeFreq (α : Type) where
  typeLogFreq : α → LogFreq

export HasTokenFreq (tokenLogFreq)
export HasTypeFreq  (typeLogFreq)

-- ============================================================================
-- § 2: Trivial / null channels
-- ============================================================================

/-- The all-zero token-frequency channel. Useful as a default when a
    fragment has not been frequency-annotated and the downstream theory
    needs *some* `HasTokenFreq` instance to typecheck.

    Returning 0 (= log 1) means "every item attested exactly once" — a
    no-information prior. -/
@[reducible] def trivialTokenFreq (α : Type) : HasTokenFreq α := ⟨fun _ => (0 : ℝ)⟩

/-- The all-zero type-frequency analogue of `trivialTokenFreq`. -/
@[reducible] def trivialTypeFreq (α : Type) : HasTypeFreq α := ⟨fun _ => (0 : ℝ)⟩

end Phonology.LexicalFrequency
