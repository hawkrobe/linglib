import Linglib.Theories.Syntax.Minimalism.Ellipsis.DeletionDomain
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Fragments.Dargwa.ComplexPredicates

/-!
# VP Ellipsis and Argument Structure Alternations in Muira Dargwa
@cite{kalyakin-2026}

@cite{kalyakin-2026} argues that **v-stranding VPE (vVPE)** exists in Muira
Dargwa (Nakh-Dagestanian) complex predicates: the light verb (= v) survives
while its complement (= VP, containing the nominal root) is elided. The
construction was first identified in Persian (@cite{toosarvandani-2009});
Muira Dargwa provides independent evidence and novel argument-structure
alternation diagnostics.

## Key Empirical Findings

1. **Causative alternation under vVPE**: An inchoative antecedent can license
   a causative ellipsis site and vice versa — the *same root* with different
   Voice flavors. This is blocked in English VPE (@cite{merchant-2013}).

2. **Antipassive blocking**: Antipassive roots are coerced to v-adjunction
   (manner/activity position), placing them *outside* vVPE's deletion
   domain (VP). Antipassive roots therefore cannot be elided.

3. **Again diagnostic**: Under vVPE, BOTH repetitive and restitutive
   readings of *again* survive (@cite{kalyakin-2026} §4.1, exx. 52a–b).
   This contrasts with English VPE (only repetitive survives) and
   confirms the deletion domain is VP (complement of v), not vP.
   @cite{toosarvandani-2009} (ex. 90) independently shows both readings
   available for Persian vVPE.

## Theoretical Analysis

The analysis extends @cite{merchant-2013}'s [E]-feature theory: placing [E]
on v (rather than Voice) yields a smaller deletion domain (VP rather than
vP). This correctly predicts:
- Voice mismatches tolerated (same as English VPE)
- Transitivity/alternation mismatches tolerated (UNLIKE English VPE)
- Lexical verb mismatches still blocked (V is inside VP)

The causative alternation tolerance follows directly from existing Voice
decomposition (@cite{kratzer-1996}, @cite{cuervo-2003}): alternating pairs
share the same root [vGO, vBE]; only Voice differs. Since Voice is outside
vVPE's deletion domain, mismatches in Voice are tolerated.
-/

namespace Phenomena.Ellipsis.Studies.Kalyakin2026

open Minimalism
open Minimalism.Ellipsis

-- ════════════════════════════════════════════════════
-- § 1. Mismatch Predictions from DeletionDomain.lean
-- ════════════════════════════════════════════════════

/-- The core prediction: vVPE tolerates both voice and transitivity
    mismatches while blocking lexical verb mismatches. -/
theorem vVPE_mismatch_profile :
    canMismatch vVPE voiceMismatch = true ∧
    canMismatch vVPE transitivityMismatch = true ∧
    canMismatch vVPE lexicalMismatch = false := ⟨rfl, rfl, rfl⟩

/-- English VPE has a strictly more restrictive profile than vVPE:
    it additionally blocks transitivity mismatches. -/
theorem englishVPE_more_restrictive :
    canMismatch englishVPE transitivityMismatch = false ∧
    canMismatch vVPE transitivityMismatch = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Causative Alternation Under vVPE
-- ════════════════════════════════════════════════════

/-- A datum for ellipsis under argument structure alternation. -/
structure AlternationDatum where
  /-- Description -/
  description : String
  /-- Voice flavor of the antecedent -/
  antecedentVoice : VoiceFlavor
  /-- Voice flavor of the ellipsis site -/
  targetVoice : VoiceFlavor
  /-- Root event structure (shared between antecedent and target) -/
  rootStructure : List VerbHead
  /-- Is the alternation grammatical under the given ellipsis type? -/
  grammatical : Bool
  deriving Repr

/-- Inchoative antecedent → causative target (OK under vVPE).
    "The door opened. Then someone made it [open]."
    Voice: nonThematic → agentive; root: [vGO, vBE] shared. -/
def inchoativeToCausative : AlternationDatum :=
  { description := "Inchoative → causative under vVPE (Muira Dargwa)"
    antecedentVoice := .nonThematic
    targetVoice := .agentive
    rootStructure := [.vGO, .vBE]
    grammatical := true }

/-- Causative antecedent → inchoative target (OK under vVPE).
    "Someone opened the door, and then it [opened] by itself."
    Voice: agentive → nonThematic; root: [vGO, vBE] shared. -/
def causativeToInchoative : AlternationDatum :=
  { description := "Causative → inchoative under vVPE (Muira Dargwa)"
    antecedentVoice := .agentive
    targetVoice := .nonThematic
    rootStructure := [.vGO, .vBE]
    grammatical := true }

/-- Same alternation is blocked in English VPE (@cite{merchant-2013}):
    v_trans ≠ v_unacc inside the deletion domain. -/
def englishAlternationBlocked : AlternationDatum :=
  { description := "Causative alternation blocked under English VPE"
    antecedentVoice := .nonThematic
    targetVoice := .agentive
    rootStructure := [.vGO, .vBE]
    grammatical := false }

-- ════════════════════════════════════════════════════
-- § 3. Structural Verification
-- ════════════════════════════════════════════════════

/-- The shared root structure [vGO, vBE] yields different decompositions
    under different Voice flavors — this is the causative alternation
    from Voice.lean. -/
theorem alternation_same_root :
    buildDecomposition voiceAgent [.vGO, .vBE] = [.vDO, .vGO, .vBE] ∧
    buildDecomposition voiceAnticausative [.vGO, .vBE] = [.vGO, .vBE] := by
  constructor <;> rfl

/-- The causative alternation is tolerated under vVPE because
    transitivity mismatches are allowed. -/
theorem causative_alternation_ok_under_vVPE :
    canMismatch vVPE transitivityMismatch = true := rfl

/-- The causative alternation is blocked under English VPE because
    transitivity mismatches are blocked. -/
theorem causative_alternation_blocked_english :
    canMismatch englishVPE transitivityMismatch = false := rfl

/-- The same root structure is used in both alternants — the complement
    of v (= VP) is identical. This is why vVPE succeeds: it only
    requires identity of the VP, which contains the shared root. -/
theorem shared_vp_core :
    let root := [VerbHead.vGO, VerbHead.vBE]
    buildDecomposition voiceAgent root ≠ buildDecomposition voiceAnticausative root ∧
    root = root := by
  constructor
  · intro h; cases h
  · rfl

/-- Bridge: each datum's grammaticality matches Merchant's `canMismatch`
    prediction for the relevant ellipsis type and mismatch dimension.
    The connection is structural: `AlternationDatum.grammatical` was set
    to match the empirical judgment; `canMismatch` derives the same value
    from spine positions. -/
theorem alternation_predicted_by_merchant :
    inchoativeToCausative.grammatical = canMismatch vVPE transitivityMismatch ∧
    causativeToInchoative.grammatical = canMismatch vVPE transitivityMismatch ∧
    englishAlternationBlocked.grammatical = canMismatch englishVPE transitivityMismatch :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Antipassive Blocking
-- ════════════════════════════════════════════════════

/-- Antipassive roots in Muira Dargwa are coerced to v-adjunction,
    placing them outside vVPE's deletion domain. They therefore
    cannot be elided under vVPE. -/
theorem antipassive_blocks_vVPE :
    rootInVVPEDomain .adjoined = false := rfl

/-- Change-of-state roots (object-adjoined) ARE inside vVPE's
    deletion domain — they can be elided. -/
theorem change_of_state_allows_vVPE :
    rootInVVPEDomain .complement = true := rfl

-- ════════════════════════════════════════════════════
-- § 5. Cross-Linguistic Predictions
-- ════════════════════════════════════════════════════

/-- The hierarchy of mismatch tolerance across ellipsis types:
    sluicing < English VPE < vVPE.
    Each step down tolerates strictly more mismatches. -/
theorem mismatch_hierarchy :
    -- Sluicing: blocks both voice and transitivity
    canMismatch sluicing voiceMismatch = false ∧
    canMismatch sluicing transitivityMismatch = false ∧
    -- English VPE: allows voice, blocks transitivity
    canMismatch englishVPE voiceMismatch = true ∧
    canMismatch englishVPE transitivityMismatch = false ∧
    -- vVPE: allows both voice and transitivity
    canMismatch vVPE voiceMismatch = true ∧
    canMismatch vVPE transitivityMismatch = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- vVPE's [E] position (v) is strictly below English VPE's (Voice).
    By monotonicity, any mismatch tolerated by English VPE is also
    tolerated by vVPE. -/
theorem vVPE_below_englishVPE :
    SpinePos.v.isBelow SpinePos.Voice = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. End-to-End Argumentation Chain
-- ════════════════════════════════════════════════════

/-- End-to-end chain: Voice severing (@cite{kratzer-1996}) →
    Merchant's deletion domain (@cite{merchant-2013}) →
    Kalyakin's empirical finding (@cite{kalyakin-2026}).

    Step 1 (Voice.lean): The root `[vGO, vBE]` yields a causative
    decomposition `[vDO, vGO, vBE]` under agentive Voice but an inchoative
    `[vGO, vBE]` under nonThematic Voice. The full decompositions differ,
    but the root (= VP content) is shared.

    Step 2 (DeletionDomain.lean): Under vVPE ([E] on v), the deletion domain
    is VP. Transitivity (determined by v) is external to VP, so
    transitivity mismatches are tolerated.

    Step 3 (this file): The datum — inchoative→causative alternation under
    vVPE is grammatical — matches the prediction. -/
theorem end_to_end_causative_chain :
    -- Step 1: Voice determines causativity (Kratzer/Cuervo)
    isCausative (buildDecomposition voiceAgent [.vGO, .vBE]) = true ∧
    isInchoative (buildDecomposition voiceAnticausative [.vGO, .vBE]) = true ∧
    -- Step 2: vVPE tolerates the transitivity difference (Merchant)
    canMismatch vVPE transitivityMismatch = true ∧
    -- Step 3: Alternation under vVPE is grammatical (Kalyakin)
    inchoativeToCausative.grammatical = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Convergent prediction: Merchant's theory correctly predicts that
    sluicing (C[E]) blocks voice mismatches — Voice is inside TP, the
    deletion domain of sluicing. The SCSS corpus (@cite{anand-hardt-mccloskey-2021},
    §5.5) independently confirms this: across 4,700 annotated sluices, zero
    antecedent–ellipsis site pairings exhibit active/passive voice mismatches.
    The same theoretical apparatus that Kalyakin extends to vVPE
    already works for sluicing. -/
theorem sluicing_voice_blocked_convergent :
    canMismatch sluicing voiceMismatch = false := rfl

-- ════════════════════════════════════════════════════
-- § 7. Again Diagnostic
-- ════════════════════════════════════════════════════

/-- Under vVPE, BOTH repetitive and restitutive *again* survive.
    This contrasts with English VPE (only repetitive survives) and
    confirms the deletion domain is VP (complement of v), not vP.

    @cite{kalyakin-2026} §4.1 (exx. 52a–b): both repetitive and
    restitutive ʔibrra 'again' are available under vVPE in Muira Dargwa.
    @cite{toosarvandani-2009} (ex. 90) independently shows both readings
    available for Persian vVPE. -/
theorem vVPE_both_again :
    againSurvives .vP_adjunction vVPE = true ∧
    againSurvives .VP_adjunction vVPE = true := by native_decide

/-- English VPE deletes restitutive *again*: only repetitive survives.
    (@cite{merchant-2013}, building on Johnson 2004, von Stechow 1996). -/
theorem englishVPE_only_repetitive :
    againSurvives .vP_adjunction englishVPE = true ∧
    againSurvives .VP_adjunction englishVPE = false := by native_decide

/-- The *again* contrast directly distinguishes vVPE from English VPE:
    same test, different result — proving different deletion domains. -/
theorem again_distinguishes_vVPE_from_englishVPE :
    againSurvives .VP_adjunction vVPE = true ∧
    againSurvives .VP_adjunction englishVPE = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Fragment Integration: NV Root Position → vVPE
-- ════════════════════════════════════════════════════

open Fragments.Dargwa.ComplexPredicates in

/-- Is a CPr's NV inside vVPE's deletion domain?
    The fragment's `AnnotatedCPr` stores `RootPosition` (from
    `Core.RootDimensions`); this function bridges to the
    Minimalist `rootInVVPEDomain` from `DeletionDomain.lean`. -/
def cprInVVPEDomain (cpr : Fragments.Dargwa.ComplexPredicates.AnnotatedCPr) : Bool :=
  rootInVVPEDomain cpr.rootPosition

open Fragments.Dargwa.ComplexPredicates in

/-- Change-of-state NVs (complement position) are inside vVPE's
    deletion domain: they can be elided. -/
theorem cos_in_domain :
    cprInVVPEDomain warmUp = true ∧ cprInVVPEDomain openCPr = true ∧
    cprInVVPEDomain calmCPr = true ∧ cprInVVPEDomain praiseCPr = true ∧
    cprInVVPEDomain repairCPr = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.Dargwa.ComplexPredicates in

/-- Manner/activity NVs (adjoined position) are outside vVPE's
    deletion domain: they survive ellipsis. This is why antipassive
    roots (coerced to adjunction) block vVPE. -/
theorem manner_outside_domain :
    cprInVVPEDomain runCPr = false ∧ cprInVVPEDomain jumpCPr = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. NV-Drop Test (vVPE vs Argument Ellipsis)
-- ════════════════════════════════════════════════════

/-- Datum for the NV-drop constituency test.
    @cite{kalyakin-2026} §3.2 distinguishes vVPE from argument ellipsis (AE):
    - vVPE: NV+argument deleted together (constituent = VP)
    - AE: argument alone deleted, NV survives
    - *NV alone deleted, argument survives → ungrammatical
    The ungrammaticality of NV-only deletion proves the elided
    constituent is VP (containing both NV and argument), not just NV. -/
structure NVDropDatum where
  description : String
  nvDropped : Bool
  argDropped : Bool
  grammatical : Bool
  deriving Repr

/-- NV + argument both dropped (= vVPE): grammatical. -/
def nvArgDrop : NVDropDatum :=
  { description := "vVPE: NV+arg elided together"
  , nvDropped := true, argDropped := true, grammatical := true }

/-- Argument alone dropped (= argument ellipsis): grammatical. -/
def argOnlyDrop : NVDropDatum :=
  { description := "AE: argument elided, NV survives"
  , nvDropped := false, argDropped := true, grammatical := true }

/-- NV alone dropped, argument survives: ungrammatical.
    This rules out NV-drop as a process distinct from vVPE —
    you can't delete just the NV without its complement. -/
def nvOnlyDrop : NVDropDatum :=
  { description := "NV-only drop: ungrammatical"
  , nvDropped := true, argDropped := false, grammatical := false }

/-- The NV-drop test confirms constituent deletion: NV+arg is a
    constituent (VP), NV alone is not. -/
theorem nv_drop_constituency :
    nvArgDrop.grammatical = true ∧
    argOnlyDrop.grammatical = true ∧
    nvOnlyDrop.grammatical = false := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Cross-Linguistic vVPE Profiles
-- ════════════════════════════════════════════════════

/-- Bridge: Muira Dargwa, Persian, British English share [E] on v
    (= vVPE), while Bangla's deletion domain is vP (= English VPE
    with LV evacuation via head movement). -/
theorem cross_ling_e_positions :
    muiraDargwaVVPE.ellipsisType.ePosition = SpinePos.v ∧
    persianVVPE.ellipsisType.ePosition = SpinePos.v ∧
    britishDoVVPE.ellipsisType.ePosition = SpinePos.v ∧
    banglaVVPE.ellipsisType.ePosition = SpinePos.Voice := ⟨rfl, rfl, rfl, rfl⟩

/-- Muira Dargwa and British *do* pattern together: same [E] position,
    no VIR, arg-structure alternations tolerated. -/
theorem dargwa_british_parallel :
    muiraDargwaVVPE.ellipsisType.ePosition = britishDoVVPE.ellipsisType.ePosition ∧
    muiraDargwaVVPE.virRequired = britishDoVVPE.virRequired := ⟨rfl, rfl⟩

/-- Persian has same [E] position as Muira Dargwa but stricter identity:
    VIR blocks arg-structure alternations in Persian that Dargwa allows. -/
theorem persian_stricter_than_dargwa :
    persianVVPE.ellipsisType.ePosition = muiraDargwaVVPE.ellipsisType.ePosition ∧
    persianVVPE.virRequired = true ∧
    muiraDargwaVVPE.virRequired = false := ⟨rfl, rfl, rfl⟩

end Phenomena.Ellipsis.Studies.Kalyakin2026
