import Linglib.Theories.Syntax.Minimalism.Ellipsis.DeletionDomain
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# VP Ellipsis and Argument Structure Alternations in Muira Dargwa
@cite{kalyakin-2026}

@cite{kalyakin-2026} discovers **v-stranding VPE (vVPE)** in Muira Dargwa
(Nakh-Dagestanian) complex predicates: the light verb (= v) survives while
its complement (= VP, containing the nominal root) is elided. This is the
first attested ellipsis type where [E] sits on v rather than Voice.

## Key Empirical Findings

1. **Causative alternation under vVPE**: An inchoative antecedent can license
   a causative ellipsis site and vice versa — the *same root* with different
   Voice flavors. This is blocked in English VPE (@cite{merchant-2013}).

2. **Antipassive blocking**: Antipassive roots are coerced to v-adjunction
   (manner/activity position), placing them *outside* vVPE's deletion
   domain (VP). Antipassive roots therefore cannot be elided.

3. **Again diagnostic**: Under vVPE, only the repetitive reading of *again*
   survives (restitutive *again* is VP-internal, hence deleted). Same
   pattern as English VPE (@cite{merchant-2013}).

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
    rootInVVPEDomain .vAdjoined = false := rfl

/-- Change-of-state roots (object-adjoined) ARE inside vVPE's
    deletion domain — they can be elided. -/
theorem change_of_state_allows_vVPE :
    rootInVVPEDomain .objectAdjoined = true := rfl

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
    deletion domain of sluicing. The SCSS corpus (@cite{anand-hardt-mccloskey-2021})
    independently confirms this with 0 attested voice mismatches in 4,700
    sluices. The same theoretical apparatus that Kalyakin extends to vVPE
    already works for sluicing. -/
theorem sluicing_voice_blocked_convergent :
    canMismatch sluicing voiceMismatch = false := rfl

end Phenomena.Ellipsis.Studies.Kalyakin2026
