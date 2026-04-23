import Linglib.Theories.Phonology.OptimalityTheory.Correspondence
import Linglib.Core.Constraint.OT.Basic

/-!
# Antifaithfulness — Alderete 2001
@cite{alderete-2001}

Antifaithfulness is the *polarity flip* of faithfulness: rather than
penalizing positions where corresponding elements *differ*, it penalizes
positions where they *agree*. The same correspondence diagram is used —
the difference is purely in the sign of the comparator.

## Empirical motivation

Antifaithfulness derives **paradigmatic contrast effects**:

- Lexical-class alternations where two related stems must phonologically
  *differ* (e.g., English transitive/intransitive ablaut: `rise`/`raise`,
  `lie`/`lay`).
- Anti-homophony: morphologically-related forms surfacing with distinct
  phonologies even when default markedness would predict identity.

Standard faithfulness alone cannot derive these — under faithfulness,
the most harmonic outcome is *identity* between related forms. Antifaith
(¬OO-Ident) flips the polarity, so the most harmonic outcome is
*difference*. When ranked above OO-Ident-style preservation but below
markedness, antifaith forces a minimal contrast that satisfies markedness.

## Connection to OP / TCT / LC

OP (@cite{mccarthy-2005}) and TCT (@cite{benua-1997}) both posit OO-Faith
constraints that *prefer identity*. LC (@cite{steriade-2000}) is a
weighted/anchored variant. Antifaithfulness is the **opposite-polarity
sibling** in the same paradigm-uniformity family: same diagrams, same
edges, opposite comparator. It is the fourth corner of the four-corner
ParadigmUniformity taxonomy.

## Formal content

`antifaithViol c r₁ r₂` counts position pairs `(i, j) ∈ edge r₁ r₂`
where `(form r₁)[i] = (form r₂)[j]`. Compare `Corr.identViol`, which
counts pairs where they *differ*. Together they partition the edge:

  `identViol c r₁ r₂ + antifaithViol c r₁ r₂ = (edge r₁ r₂).card`
-/

namespace Phonology.ParadigmUniformity.Antifaithfulness

open Phonology.Correspondence (Corr)
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

variable {Role : Type*} {α : Type*}

-- ============================================================================
-- § 1: Antifaithfulness violation count
-- ============================================================================

/-- **¬IDENT** (antifaithfulness): the polarity-flipped sibling of
    `Corr.identViol`. Counts pairs `(i, j) ∈ edge r₁ r₂` where the
    corresponding elements *agree*. Under `¬IDENT-OO ≫ OO-Ident`,
    paradigmatically related forms are pushed apart rather than together. -/
def antifaithViol [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1]? = (c.form r₂)[p.2]?).card

-- ============================================================================
-- § 2: Polarity duality with IDENT
-- ============================================================================

/-- **Polarity duality**: IDENT and antifaith partition the edge. Every
    correspondence pair contributes to exactly one of the two violation
    counts. Together they sum to the edge cardinality.

    This is the formal content of "antifaith is the polarity flip of
    faith" — they share an underlying correspondence diagram and differ
    only in which subset of pairs is counted as a violation. -/
theorem antifaith_plus_ident_eq_edge_card [DecidableEq α]
    (c : Corr Role α) (r₁ r₂ : Role) :
    antifaithViol c r₁ r₂ + Corr.identViol c r₁ r₂ = (c.edge r₁ r₂).card :=
  Finset.card_filter_add_card_filter_not
    (s := c.edge r₁ r₂)
    (fun p => (c.form r₁)[p.1]? = (c.form r₂)[p.2]?)

-- ============================================================================
-- § 3: Identity correspondence is maximally antifaith-violating
-- ============================================================================

/-- The identity correspondence — input = output, all pairs identical —
    achieves *maximum* antifaith violations: every paired position counts. -/
theorem identity_antifaith_max [DecidableEq α] (s : List α) :
    antifaithViol (Corr.identity s) false true = s.length := by
  have hAdd := antifaith_plus_ident_eq_edge_card (Corr.identity s) false true
  rw [Corr.identity_ident_zero] at hAdd
  rw [Nat.add_zero] at hAdd
  rw [hAdd]
  show ((Corr.identity s).edge false true).card = s.length
  show ((Corr.parallel s s).edge false true).card = s.length
  rw [Corr.parallel_edge_off_diag]
  rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1)]
  simp

-- ============================================================================
-- § 4: NamedConstraint bridge
-- ============================================================================

/-- Wrap `antifaithViol` as a `NamedConstraint`. The dual of
    `Corr.toIdentConstraint`. -/
def toAntifaithConstraint {Role α : Type} [DecidableEq α] (r₁ r₂ : Role)
    (label : String) : NamedConstraint (Corr Role α) where
  name := "¬IDENT-" ++ label
  family := .faithfulness
  eval c := antifaithViol c r₁ r₂

end Phonology.ParadigmUniformity.Antifaithfulness
