import Linglib.Theories.Pragmatics.Dialogue.KOS.Basic
import Linglib.Phenomena.Ellipsis.ClarificationEllipsis

/-!
# Ginzburg & Cooper (2004): Clarification, Ellipsis, and Contextual Updates
@cite{ginzburg-cooper-2004}

Formalization of the core running example from @cite{ginzburg-cooper-2004}:

  A: "Did Bo leave?"
  B: "Bo?"

This study applies the KOS framework (DGB, IS, C-PARAMS, coercion operations)
to derive both CE readings — clausal and constituent — from the same antecedent
sign, and demonstrates the speaker/addressee IS asymmetry.

## Key Claims Formalized

1. Proper names introduce C-PARAMS (referent binding) — ex. 28
2. The running example has 5 C-PARAMS — ex. 32
3. Parameter focussing yields clausal CE reading — ex. 53/54
4. Parameter identification yields constituent CE reading — ex. 59/60
5. Both coercions take the antecedent sign and target the same SAL-UTT
6. Existential generalization removes a parameter without clarification — ex. 77/78
7. Speaker resolves all params; addressee may not — ex. 82
8. Partial assignment triggers PENDING, not grounding
9. Updates require structured representations (Hybrid Content Hypothesis) — ex. 2/16

-/

namespace GinzburgCooper2004

open Pragmatics.Dialogue.KOS
open Phenomena.Ellipsis.ClarificationEllipsis

-- ════════════════════════════════════════════════════
-- § 1. C-PARAMS for "Did Bo leave?" (paper ex. 28/32)
-- ════════════════════════════════════════════════════

/-- C-PARAM for "Bo": binds variable b to the referent named "Bo".
@cite{ginzburg-cooper-2004} ex. 28. -/
def cpBo : CParam where
  index := "b"
  restriction := "named(Bo)(b)"

/-- C-PARAM for temporal precedence. -/
def cpTime : CParam where
  index := "t"
  restriction := "precedes(t,k)"

/-- C-PARAM for speaker. -/
def cpSpkr : CParam where
  index := "i"
  restriction := "spkr(i)"

/-- C-PARAM for addressee. -/
def cpAddr : CParam where
  index := "j"
  restriction := "addr(j)"

/-- C-PARAM for utterance time. -/
def cpUttTime : CParam where
  index := "k"
  restriction := "utt-time(k)"

/-- The full C-PARAMS set for "Did Bo leave?" — 5 parameters.
@cite{ginzburg-cooper-2004} ex. 32. -/
def didBoLeaveCParams : CParamSet := [cpBo, cpTime, cpSpkr, cpAddr, cpUttTime]

-- ════════════════════════════════════════════════════
-- § 2. Sub-Utterances and Skeleton (paper ex. 32)
-- ════════════════════════════════════════════════════

def suDid : SubUtterance where
  phon := "Did"
  cat := "AUX"
  cont := "ask"

def suBo : SubUtterance where
  phon := "Bo"
  cat := "NP"
  cont := "b"

def suLeave : SubUtterance where
  phon := "leave"
  cat := "V"
  cont := "leave-rel"

def suDidBoLeave : SubUtterance where
  phon := "Did Bo leave"
  cat := "S"
  cont := "ask(i,j,?.leave-rel(b,t))"

/-- Full utterance skeleton for "Did Bo leave?" with all 5 C-PARAMS.
@cite{ginzburg-cooper-2004} ex. 32. -/
def didBoLeave : UttSkeleton where
  phon := "did bo leave"
  cat := "V[+fin]"
  cont := "ask(i,j,?.leave-rel(b,t))"
  cparams := didBoLeaveCParams
  constits := [suDid, suBo, suLeave, suDidBoLeave]

-- ════════════════════════════════════════════════════
-- § 3. Contextual Assignments (paper ex. 82)
-- ════════════════════════════════════════════════════

/-- Speaker (A) resolves all parameters: she knows who Bo is, who she is,
who the addressee is, and the temporal parameters.
@cite{ginzburg-cooper-2004} ex. 82b. -/
def speakerAssignment : CtxtAssignment where
  bindings := [("b", "B"), ("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1")]

/-- Addressee (B) resolves all parameters EXCEPT b (Bo's referent).
B doesn't know who "Bo" refers to.
@cite{ginzburg-cooper-2004} ex. 82c. -/
def addresseeAssignment : CtxtAssignment where
  bindings := [("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1")]

-- ════════════════════════════════════════════════════
-- § 4. IS Update: Speaker vs Addressee (paper ex. 82)
-- ════════════════════════════════════════════════════

/-- A's IS after uttering "Did Bo leave?": fully grounded.
Speaker resolves all C-PARAMS, so the utterance goes straight to FACTS. -/
def speakerIS : IS String String :=
  IS.initial.integrateUtteranceStr didBoLeave speakerAssignment

/-- B's IS after hearing "Did Bo leave?": partial assignment → pending.
Addressee cannot resolve b, so the utterance goes to PENDING. -/
def addresseeIS : IS String String :=
  IS.initial.integrateUtteranceStr didBoLeave addresseeAssignment

-- ════════════════════════════════════════════════════
-- § 5. Coercion Operations (paper ex. 53–54, 59–60)
-- ════════════════════════════════════════════════════

/-- Parameter focussing on "Bo" (parameter b): clausal CE reading.
@cite{ginzburg-cooper-2004} ex. 53–54.
Output: SAL-UTT = "Bo" constituent, MAX-QUD = ?b.ask(i,j,?.leave-rel(b,t))
Paraphrase: "Are you asking if b left?" -/
def focussingOnBo : Option CoercionOutput :=
  parameterFocussing didBoLeave "b"

/-- Parameter identification on "Bo" (parameter b): constituent CE reading.
@cite{ginzburg-cooper-2004} ex. 59–60.
Output: SAL-UTT = "Bo" constituent, MAX-QUD = ?c.spkr-meaning-rel(addr,Bo,c)
Paraphrase: "Who do you mean by Bo?" -/
def identificationOnBo : Option CoercionOutput :=
  parameterIdentification didBoLeave "b"

/-- Existential generalization on "Bo" (parameter b).
@cite{ginzburg-cooper-2004} ex. 77–78.
Removes b from C-PARAMS, weakens content to ∃b.ask(i,j,?.leave-rel(b,t)). -/
def existGenOnBo : UttSkeleton :=
  existentialGeneralization didBoLeave "b"

-- ════════════════════════════════════════════════════
-- § 6. B's IS after coercion
-- ════════════════════════════════════════════════════

/-- B applies parameter focussing to set up clarification context. -/
def addresseeISAfterFocussing : Option (IS String String) :=
  focussingOnBo.map addresseeIS.applyCoercionStr

/-- B applies parameter identification to set up clarification context. -/
def addresseeISAfterIdentification : Option (IS String String) :=
  identificationOnBo.map addresseeIS.applyCoercionStr

-- ════════════════════════════════════════════════════
-- § 7. Verification Theorems
-- ════════════════════════════════════════════════════

-- Running example structure

/-- The running example has exactly 5 C-PARAMS. -/
theorem five_cparams : didBoLeave.cparams.length = 5 := rfl

/-- The running example has 4 constituents (Did, Bo, leave, Did Bo leave). -/
theorem four_constits : didBoLeave.constits.length = 4 := rfl

-- Speaker/addressee assignment asymmetry

/-- Speaker resolves all C-PARAMS. -/
theorem speaker_resolves_all :
    speakerAssignment.resolvesAll didBoLeaveCParams = true := by native_decide

/-- Addressee does NOT resolve all C-PARAMS (missing b). -/
theorem addressee_partial :
    addresseeAssignment.resolvesAll didBoLeaveCParams = false := by native_decide

/-- The unresolved parameter for B is exactly {b}. -/
theorem addressee_unresolved_is_bo :
    (addresseeAssignment.unresolved didBoLeaveCParams).map CParam.index = ["b"] := by
  native_decide

-- IS update asymmetry (paper ex. 82)

/-- Speaker's utterance is grounded (added to FACTS). -/
theorem speaker_grounds :
    speakerIS.dgb.facts = ["ask(i,j,?.leave-rel(b,t))"] := by native_decide

/-- Addressee's utterance is NOT grounded (no new facts). -/
theorem addressee_no_facts :
    addresseeIS.dgb.facts = [] := by native_decide

/-- Addressee's utterance goes to PENDING. -/
theorem addressee_has_pending :
    addresseeIS.pending.length = 1 := by native_decide

-- Coercion availability

/-- Parameter focussing succeeds on "Bo". -/
theorem focussing_available : focussingOnBo.isSome = true := by native_decide

/-- Parameter identification succeeds on "Bo". -/
theorem identification_available : identificationOnBo.isSome = true := by native_decide

/-- Both coercions target the same SAL-UTT (the "Bo" constituent). -/
theorem coercions_same_salUtt :
    focussingOnBo.map CoercionOutput.salUtt =
    identificationOnBo.map CoercionOutput.salUtt := by native_decide

/-- The SAL-UTT is "Bo". -/
theorem salUtt_is_bo :
    focussingOnBo.map (·.salUtt.phon) = some "Bo" := by native_decide

/-- Focussing and identification produce different operation types. -/
theorem different_ops :
    focussingOnBo.map CoercionOutput.op ≠
    identificationOnBo.map CoercionOutput.op := by native_decide

-- Existential generalization (paper ex. 77–78)

/-- Existential generalization removes exactly one parameter. -/
theorem exist_gen_removes_bo :
    existGenOnBo.cparams.length = 4 := by native_decide

/-- The removed parameter is b. -/
theorem exist_gen_keeps_others :
    existGenOnBo.cparams.map CParam.index = ["t", "i", "j", "k"] := by native_decide

/-- Existential generalization wraps content with ∃. -/
theorem exist_gen_weakens_content :
    existGenOnBo.cont = "∃b.ask(i,j,?.leave-rel(b,t))" := rfl

-- Coercion output content

/-- Focussing MAX-QUD is a question about the antecedent content. -/
theorem focussing_maxqud :
    focussingOnBo.map (·.maxQud) =
    some "?b.ask(i,j,?.leave-rel(b,t))" := by native_decide

/-- Identification MAX-QUD is a speaker-meaning question. -/
theorem identification_maxqud :
    identificationOnBo.map (·.maxQud) =
    some "?c.spkr-meaning-rel(addr,Bo,c)" := by native_decide

-- Bridge: CoercionOp ↔ CEReading

/-- The KOS theory's coercion operations correspond to the empirical CE readings:
parameterFocussing ↔ clausal, parameterIdentification ↔ constituent.
@cite{ginzburg-cooper-2004} §5. -/
def coercionToReading : CoercionOp → CEReading
  | .paramFocussing => .clausal
  | .paramIdentification => .constituent
  | .existentialGeneralization => .clausal  -- acknowledgement variant (ex. 73)

/-- The CE data's two readings map to distinct coercion operations. -/
theorem readings_biject_coercions :
    coercionToReading .paramFocussing ≠ coercionToReading .paramIdentification := by
  decide

-- Hybrid Content Hypothesis

/-- **Hybrid Content Hypothesis** (@cite{ginzburg-cooper-2004} ex. 2/16):
The content updated in dynamic semantics consists of structure expressing
detailed relationships between the content and formal properties (syntax,
phonology etc) of the various parts of an utterance.

Evidence: The same propositional content ("Bo left") yields different
clarification potentials depending on phonological/syntactic structure.
The utterance skeleton encodes this structure via CONSTITS and C-PARAMS. -/
theorem hybrid_content_evidence :
    -- Two skeletons with identical CONT but different CONSTITS
    -- would have different clarification potential (different constitForParam results).
    -- We demonstrate this with our skeleton: the constituent lookup is non-trivial.
    didBoLeave.constitForParam "b" = some suBo ∧
    didBoLeave.constitForParam "leave-rel" = some suLeave := by native_decide

-- Integration with CE data

/-- The CE proper name example matches our running example. -/
theorem running_example_matches_ce_data :
    ceProperName.readings = [CEReading.clausal, CEReading.constituent] := rfl

end GinzburgCooper2004
