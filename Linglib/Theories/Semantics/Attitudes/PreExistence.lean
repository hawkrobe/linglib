import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Pre-Existence and Modal Insertion in Factive Complements
@cite{williams-2025} @cite{white-2014}
@misc{white-2014}

@cite{ippolito-kiss-williams-2025} argues that the distribution of the covert modal in
non-finite complements of *forget* is governed by the **pre-existence
presupposition**.

## Pre-Existence

Pre-existence says: the lower event must have **started before** the
attitude event. For *forget*: the event of forgetting must be preceded
by the start of whatever event the complement describes.

    PreEx(Q)(e)(w) ≡ ∃(e'', t). Q(λe'. e'=e'')(t)(w) ∧ LB(τ(e'')) < LB(τ(e))

## Temporal Satisfaction

Whether a complement type **inherently satisfies** pre-existence
depends on its temporal profile:

| Complement | Temporal Profile | Satisfies PreEx? |
|------------|-----------------|------------------|
| Finite CP | Past/present tense → event before/at matrix | yes |
| PRO-ing gerund | Gerund aspect → event before/at matrix | yes |
| Perfect infinitive | Perfect → event before matrix | yes |
| Plain infinitive | No tense → forward-oriented | no |

When pre-existence is NOT inherently satisfied (plain infinitives),
a covert modal (Mod) is inserted to shift the presupposition from
"the event started" to "the obligation/plan started" — which DOES
precede the forgetting.

## SMINC Generalization

**Selectivity of Modal Insertion in Non-finite Contexts** (@cite{ippolito-kiss-williams-2025}, p. 8, (15)): the covert modal Mod heads the complement of
*forget* just in case the complement is a plain infinitive.

-/

namespace Semantics.Attitudes.PreExistence

open Core.Verbs (ComplementType)

-- ============================================================================
-- §1. Temporal Satisfaction of Pre-Existence
-- ============================================================================

/-- Does this complement type's temporal profile inherently satisfy the
    pre-existence presupposition?

    Finite CPs and questions have tense morphology that locates the embedded
    event before or at the matrix event time. Gerunds have aspectual content
    that does the same. Plain infinitives lack both, so their embedded event
    is forward-oriented — violating pre-existence.

    Note: this is a simplification. The paper's full analysis uses event
    semantics with temporal traces (LB(τ(e)) comparisons). This predicate
    captures the key prediction without the event-semantic machinery.

    The current `ComplementType` does not distinguish perfect from plain
    infinitives. For English, `.infinitival` corresponds to the plain
    to-infinitive; the Spanish/Italian perfect infinitive would need a
    new constructor. -/
def satisfiesPreExistence : ComplementType → Bool
  | .finiteClause => true    -- Tense locates event ≤ matrix time
  | .gerund       => true    -- Gerundive aspect → event ≤ matrix time
  | _             => false   -- Plain infinitives, small clauses, NP args

-- ============================================================================
-- §2. Modal Insertion
-- ============================================================================

/-- Whether a factive verb's complement requires covert modal insertion
    to satisfy the pre-existence presupposition.

    Un@cite{ippolito-kiss-williams-2025}: Mod is inserted iff the complement type does
    not inherently satisfy pre-existence. This is the SMINC generalization
    (Selectivity of Modal Insertion in Non-finite Contexts). -/
def needsModalInsertion (ct : ComplementType) : Bool :=
  !satisfiesPreExistence ct

-- ============================================================================
-- §3. Properties of Pre-Existence Satisfaction
-- ============================================================================

/-- Finite clauses satisfy pre-existence (tense locates event in past). -/
theorem finiteClause_satisfies_preExistence :
    satisfiesPreExistence .finiteClause = true := rfl

/-- Not all non-finite types violate pre-existence: gerunds satisfy it.
    This is the key prediction that distinguishes @cite{ippolito-kiss-williams-2025} from the
    Modalized Complement Analysis. -/
theorem gerund_satisfies_preExistence :
    satisfiesPreExistence .gerund = true := rfl

/-- Plain infinitives violate pre-existence. -/
theorem infinitival_violates_preExistence :
    satisfiesPreExistence .infinitival = false := rfl

/-- SMINC: modal insertion occurs with infinitivals but not gerunds. -/
theorem sminc_infinitival_needs_modal :
    needsModalInsertion .infinitival = true := rfl

theorem sminc_gerund_no_modal :
    needsModalInsertion .gerund = false := rfl

theorem sminc_finite_no_modal :
    needsModalInsertion .finiteClause = false := rfl

-- ============================================================================
-- §4. Comparison with Modalized Complement Analysis (@cite{white-2014})
-- ============================================================================

/-- The MCA predicts modal insertion for ALL non-finite
    complements. @cite{ippolito-kiss-williams-2025} shows this overgenerates: gerunds
    don't get modalized. -/
def mcaPrediction (ct : ComplementType) : Bool :=
  !ct.isFinite

/-- MCA and Williams agree on finite complements: no modal. -/
theorem mca_williams_agree_finite :
    mcaPrediction .finiteClause = needsModalInsertion .finiteClause := rfl

/-- MCA and Williams agree on plain infinitives: modal. -/
theorem mca_williams_agree_infinitival :
    mcaPrediction .infinitival = needsModalInsertion .infinitival := rfl

/-- MCA and Williams DIVERGE on gerunds: MCA predicts modal, Williams does not.
    The gerund case is the paper's central empirical argument against the MCA. -/
theorem mca_williams_diverge_gerund :
    mcaPrediction .gerund ≠ needsModalInsertion .gerund := by decide

/-- The divergence decomposed: MCA predicts modal for gerunds but
    pre-existence analysis correctly does not. -/
theorem mca_overpredicts_gerund :
    mcaPrediction .gerund = true ∧ needsModalInsertion .gerund = false :=
  ⟨rfl, rfl⟩

end Semantics.Attitudes.PreExistence
