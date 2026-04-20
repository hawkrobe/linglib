import Mathlib.Data.Rat.Defs

/-!
# Lexical Uncertainty: Core Types

The `Lexicon` type used by lexical uncertainty models in RSA.

For RSA models with lexical uncertainty, use `RSAConfig` with
`Latent := YourLexiconType` (see @cite{potts-etal-2016} and
@cite{potts-levy-2015} for examples). This file provides the
shared `Lexicon` type used by:
- `GrammarDist.lean` (Construction Grammar as distribution over lexica)
- `SDS/Marginalization.lean` (SDS ↔ LU-RSA bidirectional translation)
-/

/--
A lexicon maps each utterance to a truth function over worlds.

In @cite{bergen-levy-goodman-2016} notation:
  L(u, w) = 1 if w ∈ ⟦u⟧_L, else 0

For graded semantics, we allow values in [0,1].
-/
structure Lexicon (Utterance World : Type) where
  /-- The meaning function for this lexicon -/
  meaning : Utterance → World → ℚ

namespace Lexicon

variable {U W : Type}

/-- Two lexica are equivalent if they assign the same meanings -/
def equiv (L₁ L₂ : Lexicon U W) : Prop :=
  ∀ u w, L₁.meaning u w = L₂.meaning u w

/-- Check if a lexicon is a refinement of another (logically implies) -/
def refines (L_refined L_base : Lexicon U W) : Prop :=
  ∀ u w, L_base.meaning u w = 0 → L_refined.meaning u w = 0

/-- Notation: L' ≤ₗ L means L' refines (is more specific than) L -/
notation:50 L' " ≤ₗ " L => refines L' L

end Lexicon
