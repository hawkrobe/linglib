import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Maximize Strength @cite{chierchia-2013}

@cite{chierchia-2013} "Logic in Grammar" proposes that scalar implicature
computation follows the Maximize Strength principle:

> "Don't add an implicature if it leads to weakening, unless you have to"

Upward-entailing contexts strengthen under exh; downward-entailing
contexts weaken. This file packages the consequence for `exhMW`.

A context is just `C : Set World → Set World` and "upward / downward
entailing" is `Monotone C` / `Antitone C` for the pointwise order on
`Set World` (which agrees with `⊆`). We use the mathlib primitives
directly rather than reintroducing local synonyms.

For decidable monomorphic-`World` reasoning over the toy 4-world type,
see `Theories/Semantics/Entailment/Polarity.lean`.
-/

namespace Exhaustification

variable {World : Type*}

/-- `exh_mw` strengthens the prejacent: `exhMW ALT φ ⊆ φ`. -/
theorem exhMW_strengthens (ALT : Set (Set World)) (φ : Set World) :
    exhMW ALT φ ⊆ φ :=
  fun _ ⟨hφ, _⟩ => hφ

/-- In a UE (monotone) context, `exh_mw` results in a stronger overall
    sentence. -/
theorem exhMW_strengthens_in_UE {C : Set World → Set World}
    (hUE : Monotone C) (ALT : Set (Set World)) (φ : Set World) :
    C (exhMW ALT φ) ⊆ C φ :=
  hUE (exhMW_strengthens ALT φ)

/-- In a DE (antitone) context, applying `exh_mw` weakens the overall
    sentence; Maximize Strength predicts no scalar implicature. -/
theorem exhMW_weakens_in_DE {C : Set World → Set World}
    (hDE : Antitone C) (ALT : Set (Set World)) (φ : Set World) :
    C φ ⊆ C (exhMW ALT φ) :=
  hDE (exhMW_strengthens ALT φ)

end Exhaustification
