import Linglib.Theories.Phonology.OptimalityTheory.Correspondence
import Linglib.Theories.Phonology.OptimalityTheory.StratalOT
import Linglib.Theories.Phonology.OptimalityTheory.TCT

/-!
# Stratal OT ↔ Corr ↔ TCT — Architectural Bridge
@cite{kiparsky-2000} @cite{benua-1997}

The substrate-level integration between Stratal OT (@cite{kiparsky-2000})
and TCT (@cite{benua-1997}) over the unifying `Corr Role α` substrate.

## The polemic of @cite{benua-1997}

Benua's thesis defends a strong architectural claim: **for every stratal
analysis there exists a TCT analysis producing the same surface
predictions**. The two architectures explain misapplication patterns
(over- and underapplication) for *different structural reasons* but
converge on the same outputs:

- **Stratal**: misapplication is *epiphenomenal* — at cycle 1 the
  rule applies (or doesn't) under the stratum's grammar; at cycle 2
  the rule sees the cycle-1 output as input, and IDENT-IO at the
  higher stratum preserves features. The misapplication "comes for
  free" from the chain of cycles.
- **TCT**: misapplication is *primitive* — a single parallel
  evaluation with high-ranked OO-Faith forcing the derivative to
  match the base. The cycles are eliminated; the chain becomes a
  pair of correspondence-related forms.

## What this file provides

The **structural bridge**: stratal derivations and TCT diagrams are
both `Corr Role α` instances over different role enums, with a
canonical projection between them. Specifically:

- `StratalRole` enum encodes the four salient time-points of a stratal
  derivation: stem-input, stem-output, word-output, phrase-output.
- `StratalDerivation.toCorr` packages a 3-stratum derivation as a
  `Corr StratalRole α` with feeding edges between adjacent strata.
- `stratalToTCTRole` projects a stratal role onto the corresponding TCT
  role: stem-output ↦ base, phrase-output ↦ derivative. The
  `project` function then carries this to a `Corr TCT.Role α`.
- The bridge theorem `project_preserves_phrase_as_derivative` makes the
  identification "stratal phrase-output = TCT derivative" true *by
  construction*.

## What this file does NOT yet provide

The **grammar-level bridge**: a constructive translation
`stratalToTCT : StratalGrammar → TCTGrammar` such that for all inputs,
their surface predictions agree. That requires modeling each
architecture's *grammar* (constraint rankings + GEN/EVAL machinery) as
a function `Input → Output`, then proving the translation respects
that function. Documented as the next major scientific step.

This file establishes the substrate so that future work can *state*
the grammar bridge in shared types — currently `StratalDerivation` and
`Corr TCT.Role α` live in non-communicating namespaces.
-/

namespace Phonology.StratalOT

open Phonology.Correspondence (Corr Side)

-- ============================================================================
-- § 1: StratalRole — the four salient time-points
-- ============================================================================

/-- Roles for a stratal correspondence diagram. Each stratum has an
    output (the result of evaluating that stratum's grammar); the
    stem also has an input (the underlying form). Word- and
    phrase-stratum *inputs* are identical to the previous stratum's
    output (the feeding relation), so they need no separate role.

    Four roles:
    - `.sIn`  — stem-stratum input (= underlying form)
    - `.sOut` — stem-stratum output
    - `.wOut` — word-stratum output
    - `.pOut` — phrase-stratum output (= surface form) -/
inductive StratalRole where
  | sIn
  | sOut
  | wOut
  | pOut
  deriving DecidableEq, Repr

/-- Display label for a stratal role. -/
def StratalRole.label : StratalRole → String
  | .sIn  => "Stem-In"
  | .sOut => "Stem-Out"
  | .wOut => "Word-Out"
  | .pOut => "Phrase-Out"

-- ============================================================================
-- § 2: Cross-stratum parallel edge construction
-- ============================================================================

/-- Build the parallel-pair edge between two equal-or-shorter forms:
    `(0, 0), (1, 1), …` up to the shorter length. The substrate edge
    type for both within-stratum (IO-correspondence) and cross-stratum
    (feeding) relations. -/
def parallelEdge (s₁ s₂ : List α) : Finset (ℕ × ℕ) :=
  (Finset.range (min s₁.length s₂.length)).image fun i => (i, i)

theorem parallelEdge_wf (s₁ s₂ : List α) :
    ∀ p ∈ parallelEdge s₁ s₂, p.1 < s₁.length ∧ p.2 < s₂.length := by
  intro p hmem
  simp only [parallelEdge, Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
         lt_of_lt_of_le hi (min_le_right _ _)⟩

-- ============================================================================
-- § 3: StratalDerivation → Corr StratalRole α
-- ============================================================================

/-- A stratal derivation over a *uniform* segment type `α`, packaged as
    a `Corr StratalRole α`. The cross-role edges encode:

    - `(.sIn ↔ .sOut)`: stem-stratum IO-correspondence
    - `(.sOut ↔ .wOut)`: stem feeds word
    - `(.wOut ↔ .pOut)`: word feeds phrase

    All other role pairs (e.g., `(.sIn, .wOut)` direct) are empty —
    the feeding chain is captured by composing adjacent edges, not by
    direct cross-stratum correspondence. (Direct edges would be
    available via `Quiver.Path`; see `RoleQuiv` in `Correspondence.lean`.)

    Specialized to homogeneous candidate types; the heterogeneous case
    `StratalDerivation S W P` doesn't fit `Corr Role α` directly without
    a uniform encoding. -/
/-- Adjacent strata in a 4-role chain: `.sIn ↔ .sOut`, `.sOut ↔ .wOut`,
    `.wOut ↔ .pOut`. The chain-shape predicate for `Corr.diagram`. -/
def adjacentStrata : StratalRole → StratalRole → Bool
  | .sIn,  .sOut | .sOut, .sIn
  | .sOut, .wOut | .wOut, .sOut
  | .wOut, .pOut | .pOut, .wOut => true
  | _, _ => false

/-- A stratal derivation as a 4-role `Corr StratalRole α`, with parallel-pair
    feeding edges along the adjacent-strata chain. Defined via `Corr.diagram`
    with the `adjacentStrata` predicate. The pre-Stage-2 hand-rolled version
    had ~50 LOC of `match` + `wf` boilerplate including 3 redundant
    swap-image clauses (no-ops since parallel-pair edges are symmetric). -/
def stratalDerivToCorr {α : Type}
    (input stemOut wordOut phraseOut : List α) : Corr StratalRole α :=
  Corr.diagram
    (fun | .sIn => input | .sOut => stemOut | .wOut => wordOut | .pOut => phraseOut)
    adjacentStrata

@[simp] theorem stratalDerivToCorr_form_sIn {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (stratalDerivToCorr input stemOut wordOut phraseOut).form .sIn = input := rfl

@[simp] theorem stratalDerivToCorr_form_sOut {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (stratalDerivToCorr input stemOut wordOut phraseOut).form .sOut = stemOut := rfl

@[simp] theorem stratalDerivToCorr_form_wOut {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (stratalDerivToCorr input stemOut wordOut phraseOut).form .wOut = wordOut := rfl

@[simp] theorem stratalDerivToCorr_form_pOut {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (stratalDerivToCorr input stemOut wordOut phraseOut).form .pOut = phraseOut := rfl

end Phonology.StratalOT

-- ============================================================================
-- § 4: StratalRole → TCT.Role projection
-- ============================================================================

namespace Phonology.StratalToTCT

open Phonology.Correspondence (Corr)
open Phonology.StratalOT (StratalRole stratalDerivToCorr parallelEdge parallelEdge_wf)
open Phonology.TCT (Role)

/-- The canonical projection from stratal roles to TCT roles, encoding
    Benua's identification:

    - `.sIn` (underlying form) → `.input`
    - `.sOut` (stem output, the morphologically simpler related word)
      → `.base`
    - `.pOut` (phrase output, the surface of the complex form) →
      `.derivative`

    The `.wOut` role has no TCT counterpart — TCT does not distinguish
    a "word stratum" between base and derivative. In Benua's reduction
    of stratal-to-parallel, the word-level evaluation is *folded into*
    the derivative's parallel evaluation against the frozen stem-output
    base.

    Returns `none` for `.wOut`; consumers must specify how to handle
    intermediate strata when projecting to TCT. -/
def stratalToTCTRole : StratalRole → Option Role
  | .sIn  => some .input
  | .sOut => some .base
  | .wOut => none           -- folded into TCT's derivative evaluation
  | .pOut => some .derivative

/-- Project a stratal correspondence diagram down to a 3-role TCT
    diagram. The `.wOut` form is dropped; the OO-correspondence between
    `.sOut` and `.pOut` is reconstructed as the parallel-pair correspondence
    between `c.form .sOut` and `c.form .pOut` (truncated by `min`).

    Defined via `Corr.diagram` with off-diagonal edge predicate. -/
def project {α : Type}
    (input stemOut wordOut phraseOut : List α) : Corr Role α :=
  Corr.diagram
    (fun | .input => input | .base => stemOut | .derivative => phraseOut)
    (fun r₁ r₂ => decide (r₁ ≠ r₂))

-- ============================================================================
-- § 5: Bridge Theorems
-- ============================================================================

/-- The phrase output of a stratal derivation equals the derivative form
    of its TCT projection. **The structural content of Benua's
    architectural-equivalence claim**: stratal's surface form *is*
    TCT's derivative output, by construction of the projection.

    True by `rfl` because the projection defines `.derivative ↦ phraseOut`
    directly. The empirical content — that *grammar-derived*
    surface forms agree under the translation — requires the deferred
    `stratalToTCT : StratalGrammar → TCTGrammar` constructive
    translation. -/
theorem project_preserves_phrase_as_derivative {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (project input stemOut wordOut phraseOut).form .derivative = phraseOut :=
  rfl

/-- The stem output of a stratal derivation equals the base form of its
    TCT projection. The other half of Benua's identification:
    stratal's stem-stratum result *is* TCT's frozen base. -/
theorem project_preserves_stem_as_base {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (project input stemOut wordOut phraseOut).form .base = stemOut :=
  rfl

/-- The underlying form (stem input) maps to TCT's input. -/
theorem project_preserves_underlying_as_input {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (project input stemOut wordOut phraseOut).form .input = input :=
  rfl

/-- **The bridge theorem**: the OO-correspondence edge in the projected
    TCT diagram (between `.base` and `.derivative`) is the parallel-pair
    correspondence between `stemOut` and `phraseOut`. This is the formal
    content of "stem-output IS the OO-base for the phrase output" —
    Benua's claim that the OO-correspondence in TCT *replaces* the
    chain of cycles in stratal. -/
theorem project_oo_edge_eq_parallel {α : Type}
    (input stemOut wordOut phraseOut : List α) :
    (project input stemOut wordOut phraseOut).edge .base .derivative =
      parallelEdge stemOut phraseOut :=
  rfl

end Phonology.StratalToTCT
