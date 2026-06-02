import Mathlib.Tactic.DeriveFintype

/-!
# Antonym Quadruplet — Four Surface Forms of a Negated Antonymic Adjective Pair

[cruse-1986] [horn-1989] [krifka-2007b] [tessler-franke-2019]

Given an antonymic adjective pair (positive / negative — e.g., *happy* /
*unhappy*), sentential negation generates **four surface forms**:

    {happy, not happy, unhappy, not unhappy}

This file provides the theory-neutral substrate for that enumeration:

- `AntonymForm` — the four-constructor enum.
- `AntonymForm.complexity` — default morphological-syntactic complexity per
  form, matching [krifka-2007b]'s ordering and [tessler-franke-2019]'s
  cost function.

The two extensional **denotations** of these forms (contradictory base,
strengthened with `ThresholdPair` gap) live in `AntonymPrediction.lean`,
which depends on this file plus the threshold substrate in `Theory.lean`.

Per-paper analyses (Krifka's BiOT derivation, Tessler-Franke's RSA model,
Alexandropoulou-Gotzner's three-case typology) live in `Studies/` and consume
this substrate without redefining the form enumeration.
-/

namespace Semantics.Gradability

/-- The four surface forms generated from an antonymic adjective pair
    `(positive, negative)` by sentential negation. Four-cell substrate;
    no semantic commitment — a paper claiming all four forms collapse to
    two (contradictory analysis) and a paper claiming a four-way gap
    (contrary analysis) both consume this enum and provide their own
    denotations. -/
inductive AntonymForm where
  | positive       -- "happy"
  | notPositive    -- "not happy"
  | negative       -- "unhappy"
  | notNegative    -- "not unhappy"
  deriving Repr, DecidableEq, Fintype

/-- Default morphological-syntactic complexity of each form: count of
    negation operators (morphological *un-* + syntactic *not*), scaled to
    [krifka-2007b]'s integer ordering 0 < 2 < 3 < 5. Matches
    [tessler-franke-2019]'s `utteranceCost` exactly.

    Per-paper analyses may override the cost (TF2020 uses a `ℚ`-valued
    coercion of this; Krifka's Economy constraint reads it directly). -/
def AntonymForm.complexity : AntonymForm → Nat
  | .positive    => 0   -- monomorphemic
  | .negative    => 2   -- un- prefix (morphologically complex)
  | .notPositive => 3   -- syntactic not (syntactically complex)
  | .notNegative => 5   -- not + un- (both)

/-- The complexity ordering is strictly monotone across the quadruplet in
    the canonical order positive < negative < notPositive < notNegative. -/
theorem AntonymForm.complexity_strictMono :
    complexity .positive < complexity .negative ∧
    complexity .negative < complexity .notPositive ∧
    complexity .notPositive < complexity .notNegative := by
  decide

end Semantics.Gradability
