import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Presuppositions of *forget* Across Complement Frames
@cite{kiparsky-kiparsky-1970} @cite{williams-2025} @cite{white-2014}
@misc{white-2014}

Theory-neutral empirical data from @cite{ippolito-kiss-williams-2025}, who shows that
*forget* is uniformly factive across all complement types, but the
**content** of the presupposition varies:

- With finite CPs and PRO-ing gerunds: the presupposition is **non-modal**
  (directly presupposes complement truth)
- With plain to-infinitives: the presupposition is **modal**
  (presupposes an obligation or plan)

This file records the empirical judgments that motivate the
**SMINC generalization** (Selectivity of Modal Insertion in Non-finite
Contexts): the covert modal only appears with plain infinitives.

## Key Data (Table 1, p. 8)

| Complement | Example | Presup content |
|------------|---------|----------------|
| finite CP | "forgot that she stopped" | non-modal (she stopped) |
| PRO-ing gerund | "forgot stopping by" | non-modal (stopped) |
| plain infinitive | "forgot to stop by" | modal (was supposed to stop) |

## Uniform Factivity

The paper follows @cite{white-2014} in arguing that *forget* is canonically
factive in ALL uses — both the cognition reading ("forgot that p")
and the psych-action reading ("forgot to VP"). There is no lexical
ambiguity. What varies is the content of the presupposition, not its
presence.

-/

namespace Phenomena.Presupposition.ForgetPresuppositions

open Core.Verbs (ComplementType)

-- ============================================================================
-- §1. Data Structure
-- ============================================================================

/-- Whether a factive presupposition has modal content.

    @cite{ippolito-kiss-williams-2025} shows that *forget* always presupposes, but the
    content varies by complement type:
    - `.nonModal`: directly presupposes complement truth
    - `.modal`: presupposes a modalized version (obligation/plan) -/
inductive PresupContent where
  /-- Directly presupposes complement truth: "forgot that p" → presupposes p -/
  | nonModal
  /-- Presupposes a modalized version: "forgot to VP" → presupposes should VP -/
  | modal
  deriving DecidableEq, Repr, BEq

/-- An empirical judgment about *forget*'s presupposition in a particular
    complement frame.

    Every entry has a presupposition (uniform factivity); what varies
    is the content (modal vs. non-modal). -/
structure ForgetJudgment where
  /-- Complement frame being tested -/
  frame : ComplementType
  /-- Example sentence -/
  sentence : String
  /-- What is presupposed (paraphrase) -/
  presupParaphrase : String
  /-- Is the presupposition modal or non-modal? -/
  content : PresupContent
  deriving Repr, BEq

-- ============================================================================
-- §2. Core Data: *forget* Across Complement Frames
-- ============================================================================

/-! ### Cognition reading (finite CP)

"Forgot that p" presupposes p (non-modal). This is the canonical
factive reading recognized since @cite{kiparsky-kiparsky-1970}.

@cite{ippolito-kiss-williams-2025}, ex. (1): "Ana forgot that she stopped by the
flower shop." Presupposes: Ana stopped by the flower shop. -/

def forget_finiteCP : ForgetJudgment where
  frame := .finiteClause
  sentence := "Ana forgot that she stopped by the flower shop"
  presupParaphrase := "Ana stopped by the flower shop"
  content := .nonModal

/-! ### Cognition reading (PRO-ing gerund)

"Forgot V-ing" presupposes V-ing occurred (non-modal). This is the
critical evidence against the Modalized Complement Analysis's
overprediction: the gerund is non-finite but NOT modalized.

@cite{ippolito-kiss-williams-2025}, ex. (12): "Ana forgot stopping by the flower shop."
Presupposes: Ana stopped by the flower shop. -/

def forget_gerund : ForgetJudgment where
  frame := .gerund
  sentence := "Ana forgot stopping by the flower shop"
  presupParaphrase := "Ana stopped by the flower shop"
  content := .nonModal

/-! ### Psych-action reading (plain infinitive)

"Forgot to VP" presupposes a plan or obligation to VP (modal).
Un@cite{ippolito-kiss-williams-2025}, this arises because the plain infinitive's
forward-oriented temporal profile violates the pre-existence
presupposition, triggering covert modal insertion.

@cite{ippolito-kiss-williams-2025}, ex. (3): "Ana forgot to stop by the flower shop."
Presupposes: Ana was supposed to / had a plan to stop. -/

def forget_infinitival : ForgetJudgment where
  frame := .infinitival
  sentence := "Ana forgot to stop by the flower shop"
  presupParaphrase := "Ana was supposed to stop by the flower shop"
  content := .modal

-- ============================================================================
-- §3. Collected Data
-- ============================================================================

/-- All *forget* judgments across complement frames. -/
def allForgetJudgments : List ForgetJudgment :=
  [forget_finiteCP, forget_gerund, forget_infinitival]

-- ============================================================================
-- §4. Data-Level Properties (Theory-Neutral)
-- ============================================================================

/-- Uniform factivity: *forget* has a presupposition in every frame.
    (All entries exist — there is no "absent presupposition" case.) -/
theorem forget_uniformly_factive :
    allForgetJudgments.length = 3 := rfl

/-- Not all presuppositions are modal: finite and gerund cases are non-modal. -/
theorem not_all_modal :
    allForgetJudgments.all (·.content == .modal) = false := by native_decide

/-- Not all presuppositions are non-modal: the infinitival case is modal. -/
theorem not_all_nonModal :
    allForgetJudgments.all (·.content == .nonModal) = false := by native_decide

/-- The modal presupposition arises with exactly one frame (the infinitival). -/
theorem modal_count :
    (allForgetJudgments.filter (·.content == .modal)).length = 1 := by native_decide

/-- The non-modal presupposition arises with exactly two frames. -/
theorem nonModal_count :
    (allForgetJudgments.filter (·.content == .nonModal)).length = 2 := by native_decide

end Phenomena.Presupposition.ForgetPresuppositions
