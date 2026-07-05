import Mathlib.Data.Rat.Defs

/-!
# Lexical uncertainty: the `Lexicon` type

The shared `Lexicon` type for lexical-uncertainty RSA models: models
marginalize over a latent lexicon (`Latent := YourLexiconType`; see
[potts-etal-2016] and [potts-levy-2015]). Consumed by
`Syntax/ConstructionGrammar/GrammarDist.lean` (grammars as distributions
over lexica) and `Studies/Clark1983.lean`.
-/

namespace RSA

/-- A lexicon maps each utterance to a graded truth function over worlds —
[bergen-levy-goodman-2016]'s `L(u, w)`, with values in `[0,1]` to allow
graded semantics. -/
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

end RSA
