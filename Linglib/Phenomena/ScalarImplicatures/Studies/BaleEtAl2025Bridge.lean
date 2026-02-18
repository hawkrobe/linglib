import Linglib.Phenomena.ScalarImplicatures.Studies.BaleEtAl2025
import Linglib.Theories.Pragmatics.NeoGricean.Core.Basic
import Linglib.Theories.Pragmatics.NeoGricean.Core.Competence

/-!
# Bale et al. (2025) — Bridge Theorems

Connects Bale et al.'s experimental findings to the NeoGricean competence
formalization in `Theories.Pragmatics.NeoGricean.Core`.

## Structure

1. **Belief-state mapping**: speaker knowledge → NeoGricean `BeliefState`
2. **Processing outcomes**: what `processAlternative` yields for each state
3. **Default competence model**: formalizes the competence-by-default
   processing account — listeners default to treating speakers as competent,
   and only override this via effortful context integration
4. **Connection to CompetenceContext**: `.simpleAssertion` = competence
   assumed by default, validated by Bale et al. as a *processing* default
-/

namespace Phenomena.ScalarImplicatures.Studies.BaleEtAl2025

open NeoGricean NeoGricean.Competence


/-! ## Section 1: Speaker Knowledge → Belief State -/

/-- Map speaker knowledge to the speaker's actual belief state about the
    stronger alternative ψ.

    An FK speaker who said "some" (not "all") believes ¬ψ: they know not
    all marbles are red, having inspected every section of the box.

    A PK speaker has no opinion about ψ: they only saw some sections and
    cannot determine whether all marbles are red. -/
def toBeliefState : SpeakerKnowledge → BeliefState
  | .fullKnowledge    => .disbelief   -- Bel_S(¬ψ): knows not-all
  | .partialKnowledge => .noOpinion   -- ¬Bel_S(ψ) ∧ ¬Bel_S(¬ψ)

/-- FK speaker is competent (knows whether ψ). -/
theorem fk_competent : competent (toBeliefState .fullKnowledge) = true := rfl

/-- PK speaker is not competent (does not know whether ψ). -/
theorem pk_not_competent : competent (toBeliefState .partialKnowledge) = false := rfl


/-! ## Section 2: Processing Outcomes

    What `processAlternative` yields for each speaker type, connecting
    to the existing outcome theorems in `Competence.lean`. -/

/-- FK speaker: `processAlternative true .disbelief` yields a strong SI.
    This matches `outcome_ii_strong`. -/
theorem fk_yields_strong :
    let p := processAlternative true (toBeliefState .fullKnowledge)
    p.weakHolds = true ∧ p.competenceAssumed = true ∧ p.strongDerived = true := by
  native_decide

/-- PK speaker (correctly identified): `processAlternative true .noOpinion`
    yields weak-only. Competence check fails because speaker genuinely
    lacks knowledge. This matches `outcome_iii_incompetent`. -/
theorem pk_yields_weak_only :
    let p := processAlternative true (toBeliefState .partialKnowledge)
    p.weakHolds = true ∧ p.competenceAssumed = false ∧ p.strongDerived = false := by
  native_decide


/-! ## Section 3: Default Competence Model

    Formalizes the competence-by-default processing account:
    - The listener's default is to treat the speaker as competent
    - Integrating contextual evidence (e.g., "speaker only saw some sections")
      can override this default to reveal `.noOpinion`
    - Under cognitive load, context integration fails, so the default persists -/

/-- The default belief state: listeners assume speakers are competent.
    For a speaker who said "some" (not "all"), competence + Quantity
    yields `.disbelief` (speaker knows ¬ψ). -/
def defaultBeliefState : BeliefState := .disbelief

/-- Context integration: can the listener use contextual cues to override
    the default? No load → yes; load → no (simplified). -/
def canIntegrateContext : LoadCondition → Bool
  | .noLoad => true
  | .load   => false

/-- The effective belief state after (possibly failed) context integration.

    If the listener can integrate context, they correctly identify the
    speaker's actual state. If not, they fall back to the default
    (competent speaker). -/
def effectiveBeliefState (k : SpeakerKnowledge) (l : LoadCondition) : BeliefState :=
  if canIntegrateContext l then
    toBeliefState k
  else
    defaultBeliefState

/-- No load + FK: listener correctly identifies competent speaker. -/
theorem noLoad_fk_correct :
    effectiveBeliefState .fullKnowledge .noLoad = .disbelief := rfl

/-- No load + PK: listener correctly identifies ignorant speaker. -/
theorem noLoad_pk_correct :
    effectiveBeliefState .partialKnowledge .noLoad = .noOpinion := rfl

/-- Load + FK: listener defaults to competence — happens to be correct. -/
theorem load_fk_default :
    effectiveBeliefState .fullKnowledge .load = .disbelief := rfl

/-- Load + PK: listener defaults to competence — incorrectly, because
    the speaker is actually ignorant. This is the key prediction. -/
theorem load_pk_defaults_to_competent :
    effectiveBeliefState .partialKnowledge .load = .disbelief := rfl


/-! ## Section 4: The Key Prediction

    Under load with an ignorant speaker, the listener's default competence
    assumption produces a strong SI — matching the observed increase in
    SSI rate in the PK+Load condition. -/

/-- Under load + PK, the default competence yields a strong SI.
    This matches the observed increase: 10% → 23.3%. -/
theorem load_pk_yields_strong :
    let b := effectiveBeliefState .partialKnowledge .load
    let p := processAlternative true b
    p.strongDerived = true := by native_decide

/-- Under no-load + PK, correct context integration yields weak-only.
    This matches the low baseline: 10% SSI. -/
theorem noLoad_pk_yields_weak :
    let b := effectiveBeliefState .partialKnowledge .noLoad
    let p := processAlternative true b
    p.strongDerived = false := by native_decide

/-- The crossover prediction: load flips the PK outcome from weak to strong,
    but leaves the FK outcome unchanged (strong → strong). -/
theorem crossover_prediction :
    let pk_noLoad := processAlternative true (effectiveBeliefState .partialKnowledge .noLoad)
    let pk_load   := processAlternative true (effectiveBeliefState .partialKnowledge .load)
    let fk_noLoad := processAlternative true (effectiveBeliefState .fullKnowledge .noLoad)
    let fk_load   := processAlternative true (effectiveBeliefState .fullKnowledge .load)
    -- PK flips from no-strong to strong under load
    pk_noLoad.strongDerived = false ∧ pk_load.strongDerived = true ∧
    -- FK stays strong regardless of load
    fk_noLoad.strongDerived = true ∧ fk_load.strongDerived = true := by
  native_decide


/-! ## Section 5: Connection to CompetenceContext

    `CompetenceContext.simpleAssertion` = competence assumed by default.
    Bale et al. validate this as a *processing* default, not merely a
    theoretical stipulation: it is what listeners do automatically, and
    overriding it costs cognitive resources. -/

/-- Simple assertion context = competence assumed by default. -/
theorem simpleAssertion_assumes_competence :
    shouldAssumeCompetence .simpleAssertion = true := rfl

/-- The default belief state IS what you get when competence is assumed
    and the speaker obeyed Quantity (didn't say "all"). -/
theorem default_matches_competent_disbelief :
    defaultBeliefState = .disbelief := rfl

/-- Bale et al.'s result validates `.simpleAssertion` as the cognitive
    default: only an effortful process can move the listener from
    `.simpleAssertion` (competence assumed) to `.uncertain` (competence
    not assumed), and cognitive load blocks this transition. -/
theorem competence_default_is_simpleAssertion :
    shouldAssumeCompetence .simpleAssertion = true ∧
    shouldAssumeCompetence .uncertain = false := by
  exact ⟨rfl, rfl⟩


end Phenomena.ScalarImplicatures.Studies.BaleEtAl2025
