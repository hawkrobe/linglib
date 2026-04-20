import Linglib.Theories.Phonology.ParadigmUniformity.Defs

/-!
# Lexical Conservatism — Steriade 2000
@cite{steriade-2000}

The paper-specific Lexical Conservatism (LC) anchoring of the generic
`liftPairwise` combinator from `ParadigmUniformity/Defs.lean`. LC
differs from OP (@cite{mccarthy-2005}) by **anchoring on attestation**:
a candidate surfacing form preferentially aligns with the *attested*
wordform of the lexeme — and the strength of the alignment scales with
how well-attested the anchor is.

LC predicts that paradigms with **no attested anchor** (e.g., bound
stems with no free wordform) impose **no LC pressure**; the candidate
is free to satisfy markedness alone. Paradigms with a
**strongly-attested anchor** impose **strong LC pressure** that
preserves the anchor's segments. The Breiss-Katsuda-Kawahara
compounds (@cite{breiss-katsuda-kawahara-2026}) instantiate this: in
bound-N2 compounds the velar nasalises categorically; in free-N2
compounds, nasalisation is suppressed in proportion to the N2's free-
form attestation strength.

## Architecture

LC reuses the same `liftPairwise` combinator as OP — the difference is
**which forms enter the paradigm**. LC's `lcParadigm` constructor takes
a candidate plus an *optional* attested anchor, returning a singleton
when the anchor is absent (no LC pressure) and a pair when present
(LC pressure scales with the anchor's mismatch from the candidate).
The strength of the LC pressure is then a downstream
*frequency-conditioned* weight on the constraint, supplied by
`Theories/Phonology/LexicalFrequency/ScaledWeights.lean` or sibling
files.

## Connection to OP

The OP combinator (`mkOPMaxV` in
`ParadigmUniformity/OptimalParadigms.lean`) sums over **every** pair
in the paradigm, with no distinguished anchor. LC's `lcParadigm` makes
the anchor *structurally optional* — its absence yields a singleton
paradigm and zero LC violations. OP cannot model the bound/free split
without auxiliary stipulation; LC handles it by paradigm membership.

## Out of scope

- The specific shape of attestation strength (sigmoid, linear, step) —
  supplied externally via `LexicalFrequency/`. LC only commits to the
  qualitative claim that strength is monotone in attestation.
- Specific segment-level mismatch metrics — passed in as `mismatch :
  Form → Form → Nat`, with the only requirement that
  `mismatch f f = 0` (well-formedness on the diagonal).
-/

namespace Phonology.ParadigmUniformity

open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Anchored paradigm
-- ============================================================================

/-- Build an LC paradigm from a candidate form and an *optional*
    attested anchor. When the anchor is present, the paradigm is
    `[candidate, anchor]`; when absent, it is `[candidate]`. Anchor
    presence is the LC channel: bound/unattested → singleton, free/
    attested → pair. -/
def lcParadigm {Form : Type} (candidate : Form) (anchor : Option Form) :
    List Form :=
  match anchor with
  | none => [candidate]
  | some a => [candidate, a]

@[simp] theorem lcParadigm_none {Form : Type} (candidate : Form) :
    lcParadigm candidate (Option.none) = [candidate] := rfl

@[simp] theorem lcParadigm_some {Form : Type} (candidate anchor : Form) :
    lcParadigm candidate (some anchor) = [candidate, anchor] := rfl

-- ============================================================================
-- § 2: LC-FAITH constraint
-- ============================================================================

/-- Build an LC-FAITH constraint: per-pair faithfulness mismatch summed
    over the LC paradigm. The same `liftPairwise` is reused; what
    distinguishes LC from OP is the paradigm-construction discipline
    (`lcParadigm`), not the lift itself. -/
def mkLCFaith {Form : Type} (name : String) (mismatch : Form → Form → Nat) :
    NamedConstraint (List Form) :=
  liftPairwise name .faithfulness mismatch

-- ============================================================================
-- § 3: Unanchored paradigms have zero LC-FAITH violations
-- ============================================================================

/-- A paradigm with no attested anchor (singleton) has zero LC-FAITH
    violations: the only ordered pair is the diagonal, and a
    well-formed `mismatch` returns 0 on the diagonal. This is the
    structural source of the prediction that bound stems exhibit no
    LC effect — a *derived* consequence of paradigm construction, not
    a stipulation. -/
theorem lc_unanchored_zero {Form : Type} (name : String)
    (mismatch : Form → Form → Nat)
    (h_diagonal : ∀ f : Form, mismatch f f = 0)
    (candidate : Form) :
    (mkLCFaith name mismatch).eval (lcParadigm candidate none) = 0 := by
  simp [mkLCFaith, lcParadigm, liftPairwise, List.product, h_diagonal]

end Phonology.ParadigmUniformity
