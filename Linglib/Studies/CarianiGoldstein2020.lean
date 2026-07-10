import Linglib.Studies.Santorio2018

/-!
# Cariani & Goldstein 2020 — "Conditional Heresies"
[cariani-goldstein-2020]

*Philosophy and Phenomenological Research* 101(2): 251–282.

## Sibling homogeneity account

[cariani-goldstein-2020] and [santorio-2018] are sibling
homogeneity accounts of the conditional. [zani-ciardelli-sanfelici-2026]
(p. 8) writes the C&G truth conditions for `if A, C` as:

    ⟦if A, C⟧ʷ = 1   if ∀p ∈ Alt(A) : min_w(p) ⊆ C
                = 0   if ∀p ∈ Alt(A) : min_w(p) ⊆ ¬C
                = undef otherwise

This is **literally** Santorio 2018's `homogeneityEval` truth-table:
TRUE iff every alternative simplification holds, FALSE iff every
alternative simplification fails, GAP otherwise. The two accounts
coincide on truth-conditional content and diverge primarily on
motivation (C&G derive homogeneity from their projection theory of
conditionals; Santorio derives it from the truthmaker-stability
algorithm).

## Sole content

This file establishes the truth-conditional coincidence as a
near-`rfl` bridge: the C&G conditional verdict on a DAC equals
Santorio's `homogeneityEval`. Worked examples that differentiate the
two accounts (e.g., scope-of-`undef` for embedded conditionals, or the
projection-vs-stability mechanism distinction) require infrastructure
not yet present in linglib and are left as future work.
-/

namespace CarianiGoldstein2020

open Core.Order (SimilarityOrdering)
open Santorio2018 (DecAlt homogeneityEval)


-- ════════════════════════════════════════════════════
-- § 1. C&G Conditional Verdict
-- ════════════════════════════════════════════════════

/-- [cariani-goldstein-2020]'s trivalent conditional verdict for a
    DAC `if A, C` over an alternative set. Per [zani-ciardelli-sanfelici-2026]
    p. 8: TRUE iff all alternative simplifications hold, FALSE iff all
    fail, undefined otherwise. -/
def cgConditional {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (alts : List (DecAlt W))
    (C : W → Prop) [DecidablePred C] (w : W) : Trivalent :=
  homogeneityEval sim alts C w


-- ════════════════════════════════════════════════════
-- § 2. Trivalent-conditional coincidence with Santorio
-- ════════════════════════════════════════════════════

/-- **C&G ↔ Santorio coincidence.** [cariani-goldstein-2020]'s
    trivalent conditional and [santorio-2018]'s `homogeneityEval`
    deliver the same verdict on every alternative set. The two accounts
    diverge on **mechanism** (projection vs. truthmaker stability) but
    agree on **truth-conditional content** — a load-bearing fact for
    the [zani-ciardelli-sanfelici-2026] acquisition study, which
    treats both as members of the homogeneity-of-DACs family. -/
theorem cgConditional_eq_santorioHomogeneityEval {W : Type*}
    [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C] (w : W) :
    cgConditional sim alts C w = homogeneityEval sim alts C w := rfl


end CarianiGoldstein2020
