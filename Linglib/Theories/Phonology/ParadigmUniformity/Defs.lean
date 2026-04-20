import Linglib.Core.Constraint.OT.Basic

/-!
# Paradigm Uniformity — generic lift combinators

Paradigm uniformity (PU) is the family of phonological theories on which
some constraint compares *related wordforms*, not individual segments,
preferring related forms to be alike. This file factors the *common
mathematical content* of PU theories — the lift from per-form ingredients
to per-paradigm violation sums — out of any specific 1990s-2000s paper
that proposed it.

The same two combinators appear in:

- McCarthy's *Optimal Paradigms* (@cite{mccarthy-2005}), where the
  comparison ranges over inflectional paradigm members and the
  constraints are output-to-output faithfulness.
- Benua's *Transderivational Identity* (1997) and Ito-Mester's
  correspondence-theoretic OO-faithfulness, where the comparison is
  base-derivative.
- Steriade's *Lexical Conservatism* (1997, 2000), where surfacing
  variants are pulled toward attested wordforms of the lexeme.
- Burzio's *Surface-to-surface* identity.

These differ over **which set of forms** the lift ranges and **which
form (if any) anchors** the comparison; they agree on the lift itself.
The lift sits in a `Defs.lean` à la mathlib's `Algebra/Order/Group/Defs`,
with paper-specific sibling files (`OptimalParadigms.lean` etc.) supplying
the anchoring.

## Connection to lexical-frequency theories

Once a `Theories/Phonology/LexicalFrequency` interface exists, paradigm
uniformity becomes one input to a frequency-conditioned grammar (the
other being `IndexedConstraints`/`ScaledWeights`/`UseListed`). PU and
frequency are orthogonal and frequently combined; the Breiss-Katsuda-
Kawahara compound study (@cite{breiss-katsuda-kawahara-2026}) is a
test case discriminating which pairing best fits Japanese velar
nasalisation.
-/

namespace Phonology.ParadigmUniformity

open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Generic lift combinators
-- ============================================================================

/-- Lift a per-form violation count to a per-paradigm constraint by summing
    violations across all members. The form-level analogue of mathlib's
    `Finset.sum`. Used for markedness: `*CCC` penalising tri-consonantal
    clusters in each member, summed over the paradigm. -/
def liftPerMember {Form : Type} (name : String) (family : ConstraintFamily)
    (viol : Form → Nat) : NamedConstraint (List Form) :=
  { name, family, eval := fun paradigm => (paradigm.map viol).sum }

/-- Lift a per-pair comparison to a paradigm-level constraint by summing
    over all ordered pairs in the paradigm. This is the mathematical
    content of paradigm uniformity: every pair is compared, and
    violations accrue. The lift is symmetric in pair order, matching the
    @cite{mccarthy-2005} violation count.

    Anchoring is *external*: pass a `compare` function that ranks
    base-anchored, attested-anchored, or symmetric comparisons; the
    lift is agnostic. -/
def liftPairwise {Form : Type} (name : String) (family : ConstraintFamily)
    (compare : Form → Form → Nat) : NamedConstraint (List Form) :=
  { name, family
    eval := fun paradigm =>
      ((paradigm.product paradigm).map (fun (a, b) => compare a b)).sum }

end Phonology.ParadigmUniformity
