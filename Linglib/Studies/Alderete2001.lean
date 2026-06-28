import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# Antifaithfulness — Alderete 2001
[alderete-2001] [alderete-1999]

Antifaithfulness is the *polarity flip* of faithfulness: rather than penalising
positions where corresponding elements *differ*, it penalises positions where
they *agree*. The same correspondence diagram is used — the difference is purely
in the sign of the comparator. Introduced in [alderete-1999] and developed as
transderivational anti-faithfulness in [alderete-2001].

## Empirical motivation

Antifaithfulness derives **paradigmatic contrast effects**:

- Lexical-class alternations where two related stems must phonologically
  *differ* (e.g. English transitive/intransitive ablaut: `rise`/`raise`,
  `lie`/`lay`).
- Anti-homophony: morphologically-related forms surfacing with distinct
  phonologies even when default markedness would predict identity.

Standard faithfulness alone cannot derive these — under faithfulness the most
harmonic outcome is *identity* between related forms. Antifaith (¬OO-Ident) flips
the polarity, so the most harmonic outcome is *difference*. Ranked above
OO-Ident-style preservation but below markedness, it forces a minimal contrast
that satisfies markedness.

## Relation to the paradigm-uniformity family

Optimal Paradigms ([mccarthy-2005], `Studies/McCarthy2005.lean`) and TCT
([benua-1997], `Studies/Benua1997.lean`) both posit OO-Faith constraints that
*prefer identity*; Lexical Conservatism ([steriade-1997], `Studies/Steriade1997.lean`)
is an attestation-anchored variant. Antifaithfulness is the opposite-polarity
sibling: the same correspondence diagrams and edges, the opposite comparator.

## Main definitions

* `antifaithViol` — the ¬IDENT violation count (agreeing corresponding pairs).
* `antifaith_plus_ident_eq_edge_card` — ¬IDENT and IDENT partition the edge.
* `identity_antifaith_max` — the identity correspondence is maximally
  antifaith-violating.
* `toAntifaithConstraint` — the `Constraint` bridge.

## Modeling note

`antifaithViol` here is the *gradient* count of every agreeing pair, so the most
harmonic outcome under ¬IDENT alone is **total** dissimilation. Alderete's ¬F is,
strictly, the logical negation of F (satisfied iff F is violated *at least
once*), which under TETU-of-dominance yields **minimal** differentiation — a
single change. A categorical-indicator variant (`1` iff `identViol = 0`) would
capture that minimal-contrast reading; the gradient count is kept here because it
composes with the `Corr.identViol` partition theorem below, and the two agree on
the qualitative claim (identity is dispreferred). Refining to the categorical
reading is left as a `TODO`.
-/

namespace Alderete2001

open OptimalityTheory.Correspondence (Corr Side)
open Constraints OptimalityTheory

variable {Role : Type*} {α : Type*}

/-! ### Antifaithfulness violation count -/

/-- **¬IDENT** (antifaithfulness): the polarity-flipped sibling of
    `Corr.identViol`. Counts pairs `(i, j) ∈ edge r₁ r₂` where the corresponding
    elements *agree*. Under `¬IDENT-OO ≫ OO-Ident`, paradigmatically related
    forms are pushed apart rather than together. -/
def antifaithViol [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1] = (c.form r₂)[p.2]).card

/-! ### Polarity duality with IDENT -/

/-- **Polarity duality**: IDENT and antifaith partition the edge. Every
    correspondence pair contributes to exactly one of the two violation counts,
    so together they sum to the edge cardinality. This is the formal content of
    "antifaith is the polarity flip of faith": shared correspondence diagram,
    opposite subset counted as a violation. -/
theorem antifaith_plus_ident_eq_edge_card [DecidableEq α]
    (c : Corr Role α) (r₁ r₂ : Role) :
    antifaithViol c r₁ r₂ + Corr.identViol c r₁ r₂ = (c.edge r₁ r₂).card :=
  Finset.card_filter_add_card_filter_not
    (s := c.edge r₁ r₂)
    (fun p => (c.form r₁)[p.1] = (c.form r₂)[p.2])

/-! ### Identity correspondence is maximally antifaith-violating -/

/-- The identity correspondence — input = output, all pairs identical — achieves
    *maximum* antifaith violations: every paired position counts. -/
theorem identity_antifaith_max [DecidableEq α] (s : List α) :
    antifaithViol (Corr.identity s) Side.lhs Side.rhs = s.length := by
  have hAdd := antifaith_plus_ident_eq_edge_card (Corr.identity s) Side.lhs Side.rhs
  rw [Corr.identity_ident_zero, Nat.add_zero] at hAdd
  rw [hAdd]
  simp only [Corr.identity, Corr.parallel_edge_lhs_rhs]
  exact (Corr.diagDiag_card s.length s.length).trans (min_self s.length)

/-! ### Constraint bridge -/

/-- Wrap `antifaithViol` as a `Constraint`. The dual of
    `Corr.toIdentConstraint`. -/
def toAntifaithConstraint [DecidableEq α] (r₁ r₂ : Role) :
    Constraint (Corr Role α) :=
  fun c => antifaithViol c r₁ r₂

/-! ### Worked example: English ablaut contrast -/

/-- A minimal segmental alphabet for the `rise`/`raise` ablaut contrast. -/
inductive Seg where
  | r | a | e | z
  deriving DecidableEq, Repr

/-- `rise` ≈ [r a z]. -/
def rise : List Seg := [.r, .a, .z]

/-- `raise` ≈ [r e z], differing from `rise` only at the vowel. -/
def raise : List Seg := [.r, .e, .z]

/-- The transitive/intransitive ablaut pair agrees at two of three positions
    (the `r` and the `z`), so ¬IDENT-OO scores **2** violations: the contrast is
    *not* yet maximal, which is exactly what an antifaith-driven minimal contrast
    looks like — distinct, but only as distinct as markedness forces. -/
example : antifaithViol (Corr.parallel rise raise) Side.lhs Side.rhs = 2 := by
  decide

/-- The paired forms differ at exactly one position, so OO-IDENT scores **1**:
    `rise`/`raise` are a *minimal* paradigmatic contrast. -/
example : Corr.identViol (Corr.parallel rise raise) Side.lhs Side.rhs = 1 := by
  decide

end Alderete2001
