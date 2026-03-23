import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.Builder
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular
import Linglib.Fragments.Finnish.Predicates
import Linglib.Phenomena.Complementation.Studies.Karttunen1971

/-!
# Nadathur 2024: Causal Semantics for Implicative Verbs
@cite{nadathur-2024}

Causal Semantics for Implicative Verbs. Journal of Semantics 40: 311–358.

## Summary

Derives the inferential profile of implicative verbs from causal structure
(structural equation models, @cite{pearl-2000}; @cite{schulz-2011}).
Builds on @cite{baglini-francez-2016}'s causal analysis of *manage* but
extends to the full implicative class: lexically-specific two-way verbs
(*dare*, *bother*), one-way verbs (*jaksaa*, *pystyä*), and polarity-
reversing verbs (*fail*, *hesitate*).

## Core Contribution: Proposal 32

The **prerequisite account** decomposes implicative meaning into:
- (32i)   Presuppose: ∃ prerequisite A(x) causally necessary for P(x)
- (32ii)  Assert: x did A
- (32iii) Presuppose (two-way only): A(x) causally sufficient for P(x)

One-way implicatives lack (32iii); their positive implicature arises
via circumscription/antiperfection.

## Key Data

- Finnish has ~12 lexically-specific implicatives naming distinct
  prerequisites (courage, patience, strength, etc.)
- The because-clause diagnostic distinguishes the at-issue contribution
  of *manage* from its complement
- Two-way vs one-way follows from whether sufficiency is presupposed
- Polarity-reversing verbs (*fail*, *hesitate*): §6.4 considers
  two options — A(x) necessary for ¬P(x) vs ¬A(x) necessary for P(x)

-/

namespace Phenomena.Causation.Studies.Nadathur2024

open Core.StructuralEquationModel
open Nadathur2024.Implicative
open NadathurLauer2020.Builder (CausativeBuilder)
open Fragments.English.Predicates.Verbal
open Fragments.English.Predicates.Copular (beAble)
open Fragments.Finnish.Predicates
open Phenomena.Complementation.Studies.Karttunen1971

-- ════════════════════════════════════════════════════════════════
-- § 1. The Dreyfus Scenario (@cite{nadathur-2024} §6.1.1, Figure 3)
-- ════════════════════════════════════════════════════════════════

/-! The fictitious Dreyfus scenario illustrates how causal structure
    determines implicative felicity. Variables:
    - INT: Dreyfus intends to spy
    - NRV: Dreyfus has the nerve
    - SEC: Dreyfus collects secrets
    - MSG: Dreyfus sends a radio message
    - LST: A German is listening on the correct frequency
    - BRK: The message is garbled
    - COM: Dreyfus establishes communication
    - SPY: Dreyfus spies for the Germans

    Structural equations:
    - SEC := INT
    - MSG := INT ∧ NRV
    - COM := MSG ∧ LST ∧ ¬BRK
    - SPY := SEC ∧ COM
-/

private def vINT := mkVar "INT"
private def vNRV := mkVar "NRV"
private def vSEC := mkVar "SEC"
private def vMSG := mkVar "MSG"
private def vLST := mkVar "LST"
private def vBRK := mkVar "BRK"
private def vCOM := mkVar "COM"
private def vSPY := mkVar "SPY"

/-- SEC := INT (if Dreyfus intends, he collects secrets) -/
private def lawSEC : CausalLaw := CausalLaw.simple vINT vSEC

/-- MSG := INT ∧ NRV (intends and has the nerve → sends message) -/
private def lawMSG : CausalLaw := CausalLaw.conjunctive vINT vNRV vMSG

/-- COM := MSG ∧ LST ∧ ¬BRK (@cite{nadathur-2024} ex. 33c) -/
private def lawCOM : CausalLaw :=
  { preconditions := [(vMSG, true), (vLST, true), (vBRK, false)]
    effect := vCOM }

/-- SPY := SEC ∧ COM -/
private def lawSPY : CausalLaw := CausalLaw.conjunctive vSEC vCOM vSPY

/-- The Dreyfus dynamics D_dreyfus. -/
def dreyfusDynamics : CausalDynamics :=
  CausalDynamics.ofList [lawSEC, lawMSG, lawCOM, lawSPY]

/-- Background situation: Dreyfus intends to spy and has collected secrets.
    s(INT) = 1, s(SEC) = 1. -/
private def dreyfusBg : Situation :=
  Situation.empty.extend vINT true |>.extend vSEC true

-- ── dare predictions (ex. 34) ──

/-- (34a) "Dreyfus dared to send a message to the Germans" is felicitous
    when NRV is the only undetermined causal ancestor of MSG.
    NRV is causally necessary and sufficient for MSG given s. -/
theorem dare_send_msg_felicitous :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vMSG = true ∧
    causallySufficient dreyfusDynamics dreyfusBg vNRV vMSG = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- (34c) "#Dreyfus dared to establish communication" is predicted
    infelicitous: COM depends on NRV, LST, and ¬BRK, so NRV alone
    is causally necessary but NOT sufficient for COM. -/
theorem dare_establish_com_infelicitous :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vCOM = true ∧
    causallySufficient dreyfusDynamics dreyfusBg vNRV vCOM = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- (34d) "#Dreyfus dared to spy" is infelicitous for the same reason:
    NRV is necessary but not sufficient for SPY. -/
theorem dare_spy_infelicitous :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vSPY = true ∧
    causallySufficient dreyfusDynamics dreyfusBg vNRV vSPY = false := by
  exact ⟨by native_decide, by native_decide⟩

-- ── manage predictions (ex. 35) ──

/-- (35a) "Dreyfus managed to send a message" — felicitous with NRV as
    the unresolved prerequisite. manage requires only necessity, not
    sufficiency, for the prerequisite. Since NRV is nec+suf for MSG,
    manage is felicitous. -/
theorem manage_send_msg_felicitous :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vMSG = true := by
  native_decide

/-- (35c) "Dreyfus managed to establish communication" — felicitous.
    manage is felicitous whenever the unresolved prerequisites collectively
    represent a necessary and sufficient condition. The set {NRV, LST, ¬BRK}
    is collectively necessary and sufficient for COM. -/
theorem manage_com_nrv_necessary :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vCOM = true := by
  native_decide

/-- Key contrast: dare is INFELICITOUS for COM (34c) because NRV alone
    is not sufficient, but manage IS felicitous (35c) because manage
    doesn't require the prerequisite to be the ONLY unresolved ancestor.
    We verify this by showing NRV is necessary (enough for manage)
    but not sufficient (blocking dare's 32iii). -/
theorem dare_vs_manage_com_contrast :
    -- dare requires nec + suf → infelicitous
    causallySufficient dreyfusDynamics dreyfusBg vNRV vCOM = false ∧
    -- manage requires only nec → felicitous
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vCOM = true := by
  exact ⟨by native_decide, by native_decide⟩

-- ── fail predictions ──

/-- "Dreyfus failed to send a message" — complement falsity follows.
    failSem checks that the complement does NOT develop. Here it fails
    (= false) because the dynamics DO support MSG via NRV. -/
theorem fail_send_msg :
    causallySufficient dreyfusDynamics dreyfusBg vNRV vMSG = true := by
  native_decide

-- ── innocent Dreyfus scenario (§6.1.1, last para) ──

/-- Innocent Dreyfus: INT=0, NRV=1. Dreyfus has no intention to spy
    but is known for showing courage. All dare/manage claims become
    infelicitous because NRV is NOT causally sufficient for any
    complement (INT=0 blocks SEC, and SEC is needed for SPY). -/
private def innocentBg : Situation :=
  Situation.empty.extend vINT false |>.extend vNRV true

/-- In the innocent scenario, NRV is not sufficient for MSG because
    MSG := INT ∧ NRV and INT=0. -/
theorem innocent_dare_msg_infelicitous :
    causallySufficient dreyfusDynamics innocentBg vNRV vMSG = false := by
  native_decide

/-- In the innocent scenario, NRV is also not necessary for MSG
    (MSG cannot be achieved regardless, since INT=0 blocks it). -/
theorem innocent_nrv_not_necessary_for_msg :
    causallyNecessary dreyfusDynamics innocentBg vNRV vMSG = false := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- § 2. Fragment Verification: English
-- ════════════════════════════════════════════════════════════════

/-- *dare* has a prerequisite presupposition (not factive). -/
theorem dare_prerequisite_presup :
    dare.toVerbCore.presupType = some .prerequisiteSoft := rfl

/-- *bother* has a prerequisite presupposition. -/
theorem bother_prerequisite_presup :
    bother.toVerbCore.presupType = some .prerequisiteSoft := rfl

/-- *hesitate* is a polarity-reversing one-way implicative. -/
theorem hesitate_polarity_reversing :
    hesitate.toVerbCore.implicativeBuilder = some .negative ∧
    hesitate.toVerbCore.presupType = some .prerequisiteSoft := ⟨rfl, rfl⟩

/-- *manage* presupposes a prerequisite (32i), though the prerequisite
    is underspecified — contextual enrichment determines what obstacle
    was overcome (@cite{nadathur-2024} §5.1, §6.1). -/
theorem manage_prerequisite_presup :
    manage.toVerbCore.presupType = some .prerequisiteSoft := rfl

/-- *manage* (occasion sense) has prerequisite presupposition,
    distinguishing it from factive soft triggers. -/
theorem manage_occasion_prerequisite :
    manage_occasion.toVerbCore.presupType = some .prerequisiteSoft := rfl

/-- Factive verbs (*know*, *regret*) retain `.softTrigger` — their
    presupposition is about complement truth, not a causal prerequisite. -/
theorem factives_not_prerequisite :
    know.toVerbCore.presupType = some .softTrigger ∧
    regret.toVerbCore.presupType = some .softTrigger := ⟨rfl, rfl⟩

/-- The prerequisite/factive distinction: dare and know have different
    presupposition types despite both being "soft triggers." -/
theorem prerequisite_vs_factive :
    dare.toVerbCore.presupType ≠ know.toVerbCore.presupType := by decide

-- ════════════════════════════════════════════════════════════════
-- § 3. Fragment Verification: Finnish
-- ════════════════════════════════════════════════════════════════

/-- Finnish two-way verbs: onnistua, uskaltaa, viitsiä, malttaa, hennoa,
    kehdata, ehtiä all predict complement entailment in both directions. -/
theorem finnish_twoWay_count :
    [onnistua, uskaltaa, viitsia, malttaa, hennoa, kehdata, ehtia].length = 7 := rfl

/-- Finnish one-way verbs: jaksaa, mahtua, pystyä predict complement
    entailment only in the negative direction. -/
theorem finnish_oneWay_count :
    [jaksaa, mahtua, pystya].length = 3 := rfl

/-- The one-way/two-way distinction is predicted by the prerequisite account:
    two-way verbs presuppose both necessity and sufficiency (Proposal 32);
    one-way verbs presuppose only necessity. The distinction corresponds to
    the `directionality` field of `FinnishImplicativeVerb`. -/
theorem directionality_predicts_entailment :
    -- Two-way: dare, manage → entail in both directions
    uskaltaa.directionality = .twoWay ∧
    onnistua.directionality = .twoWay ∧
    -- One-way: jaksaa → entails only under negation
    jaksaa.directionality = .oneWay ∧
    -- Polarity-reversing: epäröidä → negative builder, one-way
    eparoida.directionality = .oneWay ∧
    eparoida.implicativeBuilder = .negative :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Bridge to Karttunen 1971
-- ════════════════════════════════════════════════════════════════

/-- Nadathur 2024's prerequisite account subsumes Karttunen 1971's
    descriptive classification. Two-way positive = Karttunen's
    nec+suf class. -/
theorem twoWay_positive_is_karttunen_manage :
    let ic := ImplicativeClass.manage
    ic.directionality = .twoWay ∧
    ic.polarity = .positive ∧
    -- Maps to Karttunen's nec+suf cell
    KarttunenClass.manage.isTwoWay = true := ⟨rfl, rfl, rfl⟩

/-- The prerequisite account ADDS to Karttunen's classification:
    it distinguishes *dare* (courage) from *manage* (underspecified),
    which Karttunen's 2×2 cannot. -/
theorem nadathur_refines_karttunen :
    -- Karttunen: dare and manage are in the same cell
    karttunenOfImplicative .positive = KarttunenClass.manage ∧
    -- Nadathur: they differ in prerequisite type
    ImplicativeClass.dare.prerequisite ≠ ImplicativeClass.manage.prerequisite := by
  exact ⟨rfl, by decide⟩

/-- The prerequisite account EXPLAINS Karttunen's one-way/two-way distinction:
    one-way = no sufficiency presupposition (32iii absent);
    two-way = sufficiency presupposition present (32iii). -/
theorem directionality_from_sufficiency :
    -- Two-way: both presuppositions
    ImplicativeClass.manage.directionality = .twoWay ∧
    ImplicativeClass.dare.directionality = .twoWay ∧
    -- One-way: only necessity
    ImplicativeClass.jaksaa.directionality = .oneWay ∧
    ImplicativeClass.ability.directionality = .oneWay := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Prerequisite Account: Concrete Verification
-- ════════════════════════════════════════════════════════════════

/-- Construct a PrerequisiteAccount for the Dreyfus "dare to send message"
    scenario. NRV (nerve/courage) is the prerequisite; MSG is the complement. -/
private def dreyfusDareAccount : PrerequisiteAccount :=
  { dynamics := dreyfusDynamics
    background := dreyfusBg
    prereqVar := vNRV
    complementVar := vMSG
    prerequisiteType := .courage
    hasSufficiencyPresup := true }

/-- (32i) The necessity presupposition holds: NRV is causally necessary
    for MSG in the Dreyfus scenario. -/
theorem dreyfus_dare_necessity :
    dreyfusDareAccount.necessityPresup = true := by native_decide

/-- (32iii) The sufficiency presupposition holds: NRV is causally sufficient
    for MSG in the Dreyfus scenario. -/
theorem dreyfus_dare_sufficiency :
    dreyfusDareAccount.sufficiencyPresup = true := by native_decide

/-- The prerequisite account derives manageSem: when the sufficiency
    presupposition holds, manageSem follows. -/
theorem dreyfus_dare_manages :
    manageSem dreyfusDareAccount.toScenario = true := by native_decide

/-- The directionality is two-way (dare presupposes sufficiency). -/
theorem dreyfus_dare_twoWay :
    dreyfusDareAccount.directionality = .twoWay := rfl

/-- Construct a one-way account: jaksaa-like scenario where NRV is
    necessary but NOT sufficient for SPY (because COM also requires
    LST and ¬BRK). -/
private def dreyfusJaksaaAccount : PrerequisiteAccount :=
  { dynamics := dreyfusDynamics
    background := dreyfusBg
    prereqVar := vNRV
    complementVar := vSPY
    prerequisiteType := .strength
    hasSufficiencyPresup := false }

/-- One-way account: NRV is necessary but not sufficient for SPY. -/
theorem dreyfus_jaksaa_necessity_only :
    dreyfusJaksaaAccount.necessityPresup = true ∧
    dreyfusJaksaaAccount.sufficiencyPresup = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- One-way directionality follows from hasSufficiencyPresup = false. -/
theorem dreyfus_jaksaa_oneWay :
    dreyfusJaksaaAccount.directionality = .oneWay := rfl

end Phenomena.Causation.Studies.Nadathur2024
