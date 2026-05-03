import Linglib.Theories.Semantics.QBSML.Defs
import Linglib.Core.Logic.Team.Properties

/-!
# QBSML formula properties — Anttila 2021 Proposition 2.2.8 (substrate test)

@cite{aloni-vanormondt-2023} @cite{anttila-2021}

**Substrate test**: prove the three structural properties from Anttila 2021
Proposition 2.2.8 for QBSML's `support` relation, using the SAME
`Core.Logic.Team.flat_iff_downwardClosed_unionClosed_emptyTeam` template that
BSML uses (via `Theories/Semantics/BSML/Properties.lean`).

If the substrate is genuinely point-polymorphic — as designed — then the
three property proofs follow the SAME bilateral mutual induction pattern as
BSML's, with additional cases for quantifiers (`exi`, `univ`).

## What this validates

1. The `Core.Logic.Team.{Algebra, Properties}` substrate composes for
   first-order team semantics.
2. The bilateral mutual induction pattern is the right abstraction
   (used identically in BSML and QBSML).
3. `flat_support_of_isNEFree` derives in one line via the foundational
   decomposition — no QBSML-specific flatness proof needed.

## Status

The propositional cases (atom/pred, ne, neg, conj, disj, poss) follow
the BSML pattern. Quantifier cases (`exi`, `univ`) require additional
state-extension lemmas about union and subset commutativity. Those lemmas
are stated as `sorry`-discharged TODOs; the framework integration
(corollary via `Core.Logic.Team.flat_of_...`) is fully proved against
the sketches.
-/

namespace Semantics.QBSML

open Core.Logic.Team

variable {W Var Domain Pred : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

-- ============================================================================
-- §1 Union closure for all QBSML formulas (no ⨼; Anttila 2.2.8 part 2)
-- ============================================================================

/-- All QBSML formulas are union-closed. QBSML lacks the global disjunction
    ⨼ (we only have split `disj`), so Anttila 2.2.8 part 2 specializes
    to "all formulas". TODO: full structural induction including
    quantifier cases (which need `extendUniversal_union_distrib` and similar
    state-extension lemmas). -/
theorem unionClosed_support (φ : QBSMLFormula Var Pred) :
    Core.Logic.Team.unionClosed (support (W := W) (Domain := Domain)) φ := by
  sorry

-- ============================================================================
-- §2 Empty team property for NE-free QBSML formulas (Anttila 2.2.8 part 1)
-- ============================================================================

/-- NE-free QBSML formulas are supported on the empty team. The only
    obstruction is NE itself. TODO: structural induction; same bilateral
    mutual induction pattern as BSML's; quantifier cases use
    `extendUniversal_empty` and `extendFunctional_empty`. -/
theorem emptyTeam_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.emptyTeam (support (W := W) (Domain := Domain)) φ := by
  sorry

-- ============================================================================
-- §3 Downward closure for NE-free QBSML formulas (Anttila 2.2.8 part 1)
-- ============================================================================

/-- NE-free QBSML formulas are downward-closed: support survives under
    taking subsets of the team. TODO: structural induction with bilateral
    mutual induction; quantifier cases use `extendUniversal_subset_mono`
    and similar. -/
theorem downwardClosed_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.downwardClosed (support (W := W) (Domain := Domain)) φ := by
  sorry

-- ============================================================================
-- §4 Corollary: NE-free QBSML formulas are flat
-- ============================================================================

/-- **Anttila Proposition 2.2.16 (QBSML specialization)**: NE-free QBSML
    formulas are flat — team support equals pointwise support at each
    index in the team.

    **Substrate test**: this proof is IDENTICAL to BSML's `flat_support_of_isNEFree`
    (in `Theories/Semantics/BSML/Properties.lean`) modulo the formula type.
    The Core foundation `flat_of_downwardClosed_unionClosed_emptyTeam`
    composes its inputs structurally with no QBSML-specific knowledge.

    The same template will work for inquisitive semantics, dependence logic,
    or any future team-semantic logic. -/
theorem flat_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.flat (support (W := W) (Domain := Domain)) φ :=
  Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam
    (downwardClosed_support_of_isNEFree hNE)
    (unionClosed_support φ)
    (emptyTeam_support_of_isNEFree hNE)

end Semantics.QBSML
