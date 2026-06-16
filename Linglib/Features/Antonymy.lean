import Mathlib.Tactic.DeriveFintype

/-!
# Antonymy — Contradictory vs Contrary Distinction

[cruse-1986] [horn-1989] [kennedy-2007]

The classical lexical-semantic distinction between two kinds of opposite
pairs:

**Contradictories** (e.g., *clean* / *dirty*) — cannot both be true and
cannot both be false. Negation of one entails the other:
*not clean* ⟹ *dirty*. No extension gap between the two standards.

**Contraries** (e.g., *tall* / *short*, *large* / *small*) — cannot both
be true but can both be false. Negation of one does NOT entail the other:
*not large* ⊭ *small*. Extension gap between the two standards.

Note: The type is named `NegationType` for backward compatibility with
existing call sites; the linguistically accurate name is *antonymy
type*. The file is named `Antonymy.lean` to signal the right concept.
-/

namespace Features

/-- Antonymy type: contradictory (no gap) vs contrary (gap).

    See `Antonymy.lean` module docstring for the diagnostics. Used in
    gradable-adjective semantics to distinguish licensing patterns of
    the two-threshold model.

    **Cross-reference**: `Aristotelian.OppositionRel` (in
    `Core/Logic/Aristotelian/Basic.lean`) is the opposition-axis enum whose
    `contradictory` / `contrary` cells subsume both constructors here. A future
    cleanup could replace `NegationType` with
    `{ r : OppositionRel // r ∈ {.contradictory, .contrary} }` or have consumers
    take `OppositionRel` directly. Deferred until consumer demand pulls it. -/
inductive NegationType where
  | contradictory
  | contrary
  deriving Repr, DecidableEq, Fintype

/-- Predicted behaviour of an antonymic adjective pair under sentential
    negation: do positive and negative forms diverge under polarity
    (asymmetric — gap-licensed strengthening) or behave in parallel
    (symmetric — no gap available)?

    Used as the codomain of prediction signatures in studies of negated
    antonymic adjectives (Horn 1989, Krifka 2007, Tessler & Franke 2019,
    Alexandropoulou & Gotzner 2024). Anchored in
    `Semantics/Gradability/AntonymPrediction.lean`'s
    `predictionForAntonymy` map and its substrate witness theorems. -/
inductive Asymmetry where
  | asymmetric    -- diverging behavior under polarity
  | symmetric     -- parallel behavior under polarity
  deriving Repr, DecidableEq, Fintype

end Features
