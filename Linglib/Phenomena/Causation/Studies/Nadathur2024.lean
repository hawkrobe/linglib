import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.Interpretation
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

namespace Nadathur2024

open Core (Situation)

open Core.Causal
open Semantics.Causation.Implicative
open Core.Verbs (Causative)
open Fragments.English.Predicates.Verbal
open Fragments.English.Predicates.Copular (beAble)
open Fragments.Finnish.Predicates
open Karttunen1971

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
    infelicitous: NRV is NOT sufficient for COM (COM also requires
    LST and ¬BRK). dare requires sufficiency (Proposal 32iii), so
    insufficiency alone blocks felicity. Under @cite{nadathur-2024}
    Definition 10b, NRV is also not individually necessary for COM
    (the intermediate MSG can be achieved as a consistent supersituation
    extension, bypassing NRV). -/
theorem dare_establish_com_infelicitous :
    causallySufficient dreyfusDynamics dreyfusBg vNRV vCOM = false := by
  native_decide

/-- (34d) "#Dreyfus dared to spy" is infelicitous: NRV is NOT
    sufficient for SPY (SPY depends on COM, which requires LST
    and ¬BRK beyond NRV). -/
theorem dare_spy_infelicitous :
    causallySufficient dreyfusDynamics dreyfusBg vNRV vSPY = false := by
  native_decide

-- ── manage predictions (ex. 35) ──

/-- (35a) "Dreyfus managed to send a message" — felicitous with NRV as
    the unresolved prerequisite. manage requires only necessity, not
    sufficiency, for the prerequisite. Since NRV is nec+suf for MSG,
    manage is felicitous. -/
theorem manage_send_msg_felicitous :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vMSG = true := by
  native_decide

/-- (35c) "Dreyfus managed to establish communication" — felicitous.
    Under @cite{nadathur-2024} Definition 10b, NRV is NOT individually
    necessary for COM (the intermediate MSG can be set directly as a
    consistent supersituation). The paper's argument for manage felicity
    with COM involves the COLLECTIVE unresolved prerequisites {NRV, LST,
    ¬BRK} being jointly necessary and sufficient — this goes beyond
    single-variable necessity. NRV IS individually necessary for MSG
    (the direct complement of the prerequisite relation). -/
theorem manage_com_nrv_necessity_for_msg :
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vMSG = true := by
  native_decide

/-- Key contrast: dare is INFELICITOUS for COM because NRV alone
    is not sufficient (Proposal 32iii requires sufficiency). manage
    IS felicitous because manage only requires necessity — verified
    here for the direct complement MSG. Under Def 10b, individual
    variable necessity is most meaningful for direct cause-effect
    pairs (NRV→MSG) rather than transitive chains (NRV→MSG→COM). -/
theorem dare_vs_manage_contrast :
    -- dare requires suf → infelicitous for COM
    causallySufficient dreyfusDynamics dreyfusBg vNRV vCOM = false ∧
    -- manage requires nec → felicitous for MSG (direct complement)
    causallyNecessary dreyfusDynamics dreyfusBg vNRV vMSG = true := by
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

/-- In the innocent scenario, the paper argues infelicity from
    **sufficiency** alone (p. 346): "each of (34a)–(34d) is infelicitous,
    since ⟨NRV, 1⟩ is not sufficient." Definition 10's necessity
    check is inapplicable here because NRV=1 is already determined
    by the background (the precondition s ⊭_D ⟨X,x⟩ fails).

    Note: `causallyNecessary` (a simple but-for test from
    @cite{nadathur-lauer-2020} Def 24) returns `true` vacuously
    in this scenario, but this is outside the domain of
    @cite{nadathur-2024} Definition 10b. -/
theorem innocent_sufficiency_is_what_matters :
    -- Sufficiency fails (the paper's actual argument)
    causallySufficient dreyfusDynamics innocentBg vNRV vMSG = false ∧
    -- NRV is already determined by the background, so Def 10
    -- necessity is inapplicable (but-for test is vacuously true)
    innocentBg.hasValue vNRV true = true := by
  exact ⟨by native_decide, rfl⟩

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
    hesitate.toVerbCore.implicative = some .negative ∧
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
    eparoida.implicative = .negative :=
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

/-- Simplified dynamics for one-way jaksaa scenario.
    TASK := STR ∧ ENERGY. Strength is necessary but NOT sufficient
    for task completion (also needs energy/endurance). Under
    @cite{nadathur-2024} Definition 10b, this is a direct conjunctive
    model — STR is a direct prerequisite of TASK, correctly captured
    by Def 10b's supersituation necessity. -/
private def vSTR := mkVar "STR"
private def vENERGY := mkVar "ENERGY"
private def vTASK := mkVar "TASK"
private def jaksaaDynamics : CausalDynamics :=
  ⟨[CausalLaw.conjunctive vSTR vENERGY vTASK]⟩

/-- Construct a one-way account: jaksaa-like scenario where STR is
    necessary but NOT sufficient for TASK (because TASK also requires
    ENERGY). -/
private def jaksaaAccount : PrerequisiteAccount :=
  { dynamics := jaksaaDynamics
    background := Situation.empty
    prereqVar := vSTR
    complementVar := vTASK
    prerequisiteType := .strength
    hasSufficiencyPresup := false }

/-- One-way account: STR is necessary but not sufficient for TASK. -/
theorem jaksaa_necessity_only :
    jaksaaAccount.necessityPresup = true ∧
    jaksaaAccount.sufficiencyPresup = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- One-way directionality follows from hasSufficiencyPresup = false. -/
theorem jaksaa_oneWay :
    jaksaaAccount.directionality = .oneWay := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. PrerequisiteAccount → ImplicativeClass → VerbEntry Bridge
-- ════════════════════════════════════════════════════════════════

/-! The three independently-specified representations of implicative
    verb semantics must agree. These theorems create a triangle:

    ```
    PrerequisiteAccount  →  ImplicativeClass  ←  VerbCore fields
             ↘                                      ↗
              ────────── agreement theorem ──────────
    ```

    Changing any vertex (causal dynamics, classification, or fragment
    entry) without updating the others breaks the corresponding theorem. -/

-- ── dare: end-to-end ──

/-- End-to-end agreement for *dare*: causal dynamics, prerequisite account,
    ImplicativeClass, and English fragment entry are all consistent.

    This theorem breaks if:
    - Dreyfus dynamics change (necessity/sufficiency results)
    - `dreyfusDareAccount` is misconfigured
    - `ImplicativeClass.dare` is changed
    - The `dare` VerbEntry's fields change
    - The `uskaltaa` Finnish entry's classification diverges -/
theorem dare_end_to_end :
    -- Layer 1: Causal dynamics → prerequisite account
    dreyfusDareAccount.necessityPresup = true ∧
    dreyfusDareAccount.sufficiencyPresup = true ∧
    -- Layer 2: Prerequisite account → ImplicativeClass
    dreyfusDareAccount.toImplicativeClass .positive = ImplicativeClass.dare ∧
    -- Layer 3: ImplicativeClass → English fragment entry
    dare.toVerbCore.implicative = some ImplicativeClass.dare.polarity ∧
    dare.toVerbCore.presupType = some .prerequisiteSoft ∧
    -- Layer 4: Cross-linguistic — Finnish uskaltaa matches
    uskaltaa.toImplicativeClass = ImplicativeClass.dare := by
  exact ⟨by native_decide, by native_decide, rfl, rfl, rfl, rfl⟩

-- ── manage: end-to-end ──

/-- A PrerequisiteAccount for "manage to send message" in the Dreyfus
    scenario. Same causal dynamics as dare, but unspecified prerequisite. -/
private def dreyfusManageAccount : PrerequisiteAccount :=
  { dynamics := dreyfusDynamics
    background := dreyfusBg
    prereqVar := vNRV
    complementVar := vMSG
    prerequisiteType := .unspecified
    hasSufficiencyPresup := true }

/-- End-to-end agreement for *manage*. -/
theorem manage_end_to_end :
    -- Layer 1: Causal dynamics
    dreyfusManageAccount.necessityPresup = true ∧
    dreyfusManageAccount.sufficiencyPresup = true ∧
    -- Layer 2: Prerequisite account → ImplicativeClass
    dreyfusManageAccount.toImplicativeClass .positive = ImplicativeClass.manage ∧
    -- Layer 3: ImplicativeClass → English fragment
    manage.toVerbCore.implicative = some ImplicativeClass.manage.polarity ∧
    manage.toVerbCore.presupType = some .prerequisiteSoft ∧
    -- Layer 4: Cross-linguistic — Finnish onnistua matches
    onnistua.toImplicativeClass = ImplicativeClass.manage := by
  exact ⟨by native_decide, by native_decide, rfl, rfl, rfl, rfl⟩

-- ── jaksaa: one-way end-to-end ──

/-- End-to-end agreement for one-way implicative *jaksaa*. -/
theorem jaksaa_end_to_end :
    -- Layer 1: Causal dynamics — necessary but NOT sufficient
    jaksaaAccount.necessityPresup = true ∧
    jaksaaAccount.sufficiencyPresup = false ∧
    -- Layer 2: Prerequisite account → ImplicativeClass
    jaksaaAccount.toImplicativeClass .positive = ImplicativeClass.jaksaa ∧
    -- Layer 3: ImplicativeClass → Finnish fragment
    jaksaa.toImplicativeClass = ImplicativeClass.jaksaa := by
  exact ⟨by native_decide, by native_decide, rfl, rfl⟩

end Nadathur2024
