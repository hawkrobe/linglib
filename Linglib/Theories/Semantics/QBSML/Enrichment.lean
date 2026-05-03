import Linglib.Theories.Semantics.QBSML.Defs

/-!
# Pragmatic enrichment for QBSML — Aloni & van Ormondt 2023 Definition 4.13

@cite{aloni-vanormondt-2023} @cite{aloni-2022}

The first-order extension of BSML's pragmatic enrichment function `[·]⁺`
(Aloni 2022 Definition 7), adding quantifier cases.

Per Aloni & van Ormondt 2023 Definition 4.13, `[·]⁺` recursively inserts
`NE` conjuncts into every clause of an NE-free formula:

    [Pt₁...tₙ]⁺  =  Pt₁...tₙ ∧ NE
    [¬φ]⁺        =  ¬[φ]⁺ ∧ NE
    [φ ∧ ψ]⁺     =  ([φ]⁺ ∧ [ψ]⁺) ∧ NE
    [φ ∨ ψ]⁺     =  ([φ]⁺ ∨ [ψ]⁺) ∧ NE
    [□φ]⁺        =  □[φ]⁺ ∧ NE
    [◇φ]⁺        =  ◇[φ]⁺ ∧ NE
    [∃xφ]⁺       =  ∃x[φ]⁺ ∧ NE
    [∀xφ]⁺       =  ∀x[φ]⁺ ∧ NE

The intuition (from Aloni 2022's "neglect-zero" hypothesis): conversational
participants systematically ignore empty configurations when interpreting,
so each clause must witness a non-empty state. Combined with split
disjunction, this derives ignorance, distribution, free choice, and the
behavior-under-negation pattern via the QBSML facts in §5 of
Aloni & van Ormondt 2023.

## Why this lives in `QBSML/` rather than as an extension of BSML's

BSML's `enrich` operates on `BSMLFormula Atom` (no quantifiers, no `pred`).
QBSML's `enrich` operates on `QBSMLFormula Var Pred` (with `exi`/`univ`
and predicate atoms). The two are structurally parallel but operate on
distinct formula types. A future unification would parameterise enrichment
over an arbitrary "team-semantic formula language" with an `NE` constructor.

## Status

Slim file: just the recursive definition + `enriched_support_implies_nonempty`.
The substrate FC theorems (universal `narrowScopeFC`, `wideScopeFC`,
`universalFC`, etc., parallel to BSML's) are deferred to a future
`QBSML/FreeChoice.lean`. The study file `AloniVanOrmondt2023.lean`
proves facts directly on a concrete model.
-/

namespace Semantics.QBSML

variable {Var Pred : Type*}

-- ============================================================================
-- §1 The enrichment function
-- ============================================================================

/-- Pragmatic enrichment `[·]⁺` for QBSML formulas (Aloni & van Ormondt 2023
    Definition 4.13). Recursively conjoins `NE` to every clause. -/
def QBSMLFormula.enrich : QBSMLFormula Var Pred → QBSMLFormula Var Pred
  | .pred P x   => .conj (.pred P x) .ne
  | .ne         => .ne  -- NE is its own enrichment (Aloni 2022 §3.3 convention)
  | .neg φ      => .conj (.neg φ.enrich) .ne
  | .conj φ ψ   => .conj (.conj φ.enrich ψ.enrich) .ne
  | .disj φ ψ   => .conj (.disj φ.enrich ψ.enrich) .ne
  | .poss φ     => .conj (.poss φ.enrich) .ne
  | .exi x φ    => .conj (.exi x φ.enrich) .ne
  | .univ x φ   => .conj (.univ x φ.enrich) .ne

-- ============================================================================
-- §2 Structural unfolding lemmas (mirror BSML/Enrichment §2)
-- ============================================================================

theorem QBSMLFormula.enrich_pred (P : Pred) (x : Var) :
    (QBSMLFormula.pred P x).enrich = .conj (.pred P x) .ne := rfl

theorem QBSMLFormula.enrich_neg (φ : QBSMLFormula Var Pred) :
    (QBSMLFormula.neg φ).enrich = .conj (.neg φ.enrich) .ne := rfl

theorem QBSMLFormula.enrich_conj (φ ψ : QBSMLFormula Var Pred) :
    (QBSMLFormula.conj φ ψ).enrich = .conj (.conj φ.enrich ψ.enrich) .ne := rfl

theorem QBSMLFormula.enrich_disj (φ ψ : QBSMLFormula Var Pred) :
    (QBSMLFormula.disj φ ψ).enrich = .conj (.disj φ.enrich ψ.enrich) .ne := rfl

theorem QBSMLFormula.enrich_poss (φ : QBSMLFormula Var Pred) :
    (QBSMLFormula.poss φ).enrich = .conj (.poss φ.enrich) .ne := rfl

theorem QBSMLFormula.enrich_exi (x : Var) (φ : QBSMLFormula Var Pred) :
    (QBSMLFormula.exi x φ).enrich = .conj (.exi x φ.enrich) .ne := rfl

theorem QBSMLFormula.enrich_univ (x : Var) (φ : QBSMLFormula Var Pred) :
    (QBSMLFormula.univ x φ).enrich = .conj (.univ x φ.enrich) .ne := rfl

-- ============================================================================
-- §3 Enriched support forces non-emptiness
-- ============================================================================

variable {W Domain : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- A QBSML state supporting an enriched formula must be non-empty. The NE
    conjunct guards every clause of `enrich φ`, forcing the witnessing state
    to satisfy `Nonempty`. -/
theorem enriched_support_implies_nonempty (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain))
    (h : support M φ.enrich s) : s.Nonempty := by
  cases φ with
  | ne => exact h
  | _  => exact h.2

end Semantics.QBSML
