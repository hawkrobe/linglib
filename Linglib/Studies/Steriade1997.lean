import Linglib.Phonology.Constraints.Lift

/-!
# Lexical Conservatism — Steriade 1997
[steriade-1997]

Lexical Conservatism (LC) is paradigm uniformity *anchored on attestation*: a
candidate surfacing form preferentially aligns with an **attested** wordform of
the lexeme, and the strength of the alignment scales with how well-attested the
anchor is. LC predicts that paradigms with **no attested anchor** (e.g. bound
stems with no free wordform) impose **no** LC pressure — the candidate is free to
satisfy markedness alone — while a **strongly-attested anchor** imposes strong
pressure preserving the anchor's segments.

This file holds the LC *substrate* — the paper's anchored-paradigm primitive,
anchored to its originating paper and consumed by later study files.
`Studies/BreissKatsudaKawahara2026.lean` instantiates it for Japanese velar
nasalisation: bound-N2 compounds nasalise categorically (no anchor), while in
free-N2 compounds nasalisation is suppressed in proportion to the N2's free-form
attestation strength.

## Architecture

LC reuses the generic symmetric lift `Constraints.liftPairwise`; what
distinguishes it from Optimal Paradigms ([mccarthy-2005], `Studies/McCarthy2005.lean`)
is **which forms enter the paradigm**, not the lift. `lcParadigm` takes a
candidate plus an *optional* attested anchor, returning a singleton when the
anchor is absent (no LC pressure) and a pair when present. OP sums over *every*
member with no distinguished anchor and so cannot model the bound/free split
without auxiliary stipulation; LC handles it by paradigm membership alone
(`lc_unanchored_zero`).

The strength of the LC pressure is a downstream *frequency-conditioned* weight on
the constraint, supplied by the consuming study.

## Main definitions

* `lcParadigm` — build an LC paradigm from a candidate and an optional anchor.
* `mkLCFaith` — an LC-FAITH constraint: per-pair mismatch summed over the LC
  paradigm.
* `lc_unanchored_zero` — an unanchored (singleton) paradigm has zero LC-FAITH
  violations; the structural source of "bound stems show no LC effect."

## Not the 2000 paper

[steriade-2000] ("Paradigm Uniformity and the Phonetics–Phonology Boundary") is a
*different* Steriade contribution, arguing PU effects are **gradient and
phonetically grounded**. This file formalises only the categorical 1997 Lexical
Conservatism account.

TODO (2026 currency): the LC-FAITH count here is `Nat`-valued, so all
gradient/probabilistic content is bolted on downstream as real-valued weights. A
similarity-graded (ℝ-valued) correspondence codomain — à la [steriade-2000] and
Burzio's scalar Multiple Correspondence ([burzio-1998]) — would let the
categorical constraint and the consuming studies' ℝ-valued PU pressures share one
substrate rather than multiplying a `Nat` count by a weight.

## Out of scope

- The specific shape of attestation strength (sigmoid, linear, step) — supplied
  externally by the consuming study. LC only commits to the qualitative claim
  that strength is monotone in attestation.
- Specific segment-level mismatch metrics — passed in as `mismatch`, with the
  only requirement that `mismatch f f = 0` (well-formedness on the diagonal).
-/

namespace Steriade1997

open Constraints

/-! ### Anchored paradigm -/

/-- Build an LC paradigm from a candidate form and an *optional* attested anchor.
    When the anchor is present, the paradigm is `[candidate, anchor]`; when
    absent, it is `[candidate]`. Anchor presence is the LC channel:
    bound/unattested → singleton, free/attested → pair. -/
def lcParadigm {Form : Type*} (candidate : Form) (anchor : Option Form) :
    List Form :=
  match anchor with
  | none => [candidate]
  | some a => [candidate, a]

@[simp] theorem lcParadigm_none {Form : Type*} (candidate : Form) :
    lcParadigm candidate Option.none = [candidate] := rfl

@[simp] theorem lcParadigm_some {Form : Type*} (candidate anchor : Form) :
    lcParadigm candidate (some anchor) = [candidate, anchor] := rfl

/-! ### LC-FAITH constraint -/

/-- Build an LC-FAITH constraint: per-pair faithfulness mismatch summed over the
    LC paradigm. The same `liftPairwise` is reused; what distinguishes LC from OP
    is the paradigm-construction discipline (`lcParadigm`), not the lift. -/
def mkLCFaith {Form : Type*} (name : String) (mismatch : Form → Form → Nat) :
    NamedConstraint (List Form) :=
  liftPairwise name .faithfulness mismatch

/-! ### Unanchored paradigms have zero LC-FAITH violations -/

/-- A paradigm with no attested anchor (singleton) has zero LC-FAITH violations:
    the only ordered pair is the diagonal, and a well-formed `mismatch` returns 0
    on the diagonal. This is the structural source of the prediction that bound
    stems exhibit no LC effect — a *derived* consequence of paradigm
    construction, not a stipulation. -/
theorem lc_unanchored_zero {Form : Type*} (name : String)
    (mismatch : Form → Form → Nat)
    (h_diagonal : ∀ f : Form, mismatch f f = 0)
    (candidate : Form) :
    (mkLCFaith name mismatch).eval (lcParadigm candidate none) = 0 := by
  simp [mkLCFaith, lcParadigm, liftPairwise, List.product, h_diagonal]

end Steriade1997
