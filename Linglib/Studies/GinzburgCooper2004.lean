import Linglib.Discourse.Gameboard.Defs
import Linglib.Data.Examples.GinzburgCooper2004

/-!
# Ginzburg & Cooper (2004): Clarification, Ellipsis, and Contextual Updates
[ginzburg-cooper-2004]

Formalization of the core running example from [ginzburg-cooper-2004]:

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

open Discourse.Gameboard

/-- The two readings of a clarification ellipsis.
[ginzburg-cooper-2004] ex. 4b–c. -/
inductive CEReading where
  /-- "Are you asking whether p?" — polar question about propositional content.
      Paraphrasable as a polar interrogative. Presupposes shared belief about
      the sub-utterance's content. -/
  | clausal
  /-- "Who/what do you mean by X?" — wh-question about the referent/predicate.
      Paraphrasable as a wh-interrogative. No shared-belief presupposition. -/
  | constituent
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 0. Apparatus (demoted from former KOS substrate)
-- ════════════════════════════════════════════════════

/-! ## 1994/2004 Clarification Ellipsis Apparatus

This section was previously in `Discourse/Gameboard/Basic.lean`
§§6, 7, 8, 9, 10, 12, 15. It is paper-specific to
[ginzburg-cooper-2004]: in [ginzburg-2012], the corresponding
machinery uses dgb-params (record types built on the shared `CParam`)
rather than `CtxtAssignment`, and CCURs (Clarification Context Update
Rules) rather than the three coercion operations
(parameterFocussing, parameterIdentification, existentialGeneralization).

We preserve the 2004 formulation here because this study replicates the
2004 paper directly — the apparatus is single-consumer paper-specific
content, demoted from substrate to consumer per the linglib pattern
(cf. `Core/FormFrequency.lean → Studies/Haspelmath2021.lean §0`).

The shared substrate primitives — `CParam`, `CParamSet`, `SubUtterance` —
remain in `Gameboard/Defs.lean` since they survive into the 2012 framework as
the dgb-params/sub-constituents apparatus.

The four general theorems about coercion operations are namespaced under
`Apparatus` to avoid colliding with this file's specific-instance theorems
on the running example. -/

namespace Apparatus

-- ─── Contextual Assignment ─────────────────────────────────

/-- A contextual assignment maps parameter indices to values.

Grounding requires a *total* assignment (all C-PARAMS resolved).
Clarification arises when the assignment is *partial*.
[ginzburg-cooper-2004] §6, ex. 81–82. -/
structure CtxtAssignment where
  bindings : List (String × String) := []
  deriving Repr, DecidableEq

/-- Does the assignment resolve a given parameter? -/
def CtxtAssignment.resolves (f : CtxtAssignment) (cp : CParam) : Bool :=
  f.bindings.any (·.1 == cp.index)

/-- Does the assignment resolve all parameters in a set? -/
def CtxtAssignment.resolvesAll (f : CtxtAssignment) (ps : CParamSet) : Bool :=
  ps.all f.resolves

/-- Which parameters remain unresolved? -/
def CtxtAssignment.unresolved (f : CtxtAssignment) (ps : CParamSet) : CParamSet :=
  ps.filter (!f.resolves ·)

-- ─── Utterance Skeletons ───────────────────────────────────

/-- An utterance skeleton: a sign with C-PARAMS and CONSTITS.

The CONSTITS feature (ex. 30) provides access to all sub-utterances.
C-PARAMS (ex. 28–29) are the contextual dependencies introduced by the
sign, amalgamated from daughters via the Non-local Amalgamation Constraint.
[ginzburg-cooper-2004] §3. -/
structure UttSkeleton where
  phon : String
  cat : String
  cont : String
  cparams : CParamSet := []
  constits : List SubUtterance := []
  deriving Repr, DecidableEq

/-- Find the constituent whose CONT matches a parameter index. -/
def UttSkeleton.constitForParam (u : UttSkeleton) (paramIdx : String) :
    Option SubUtterance :=
  u.constits.find? (·.cont == paramIdx)

-- ─── CE Processing State ───────────────────────────────────

/-- A sign paired with a contextual assignment.

[ginzburg-cooper-2004] ex. 81 p.353. The assignment f records which
C-PARAMS have been resolved. Grounding checks whether f is total. -/
structure SignAssignment where
  sign : UttSkeleton
  assignment : CtxtAssignment
  deriving Repr, DecidableEq

/-- Clarification Ellipsis processing state.

[ginzburg-cooper-2004]: MAX-QUD and SAL-UTT are processing state for
the CE analysis. These are NOT part of the [ginzburg-2012] DGB or TIS
(in 2012, MaxQUD is computed from the QUD poset's maximal element, not
stored separately).

This state can be used alongside the 2012 TIS when CE processing is needed. -/
structure CEState (QContent : Type) where
  /-- The currently maximal question — for CE coercion operations -/
  maxQud : Option QContent := none
  /-- The salient sub-utterance — target of clarification -/
  salUtt : Option SubUtterance := none
  /-- Pending utterances awaiting C-PARAMS resolution -/
  pendingUtts : List SignAssignment := []

-- ─── Coercion Operations ───────────────────────────────────

/-- The three coercion operations on signs with unresolved C-PARAMS.
[ginzburg-cooper-2004] §5. -/
inductive CoercionOp where
  /-- Clausal CE reading: polar question about content (ex. 53) -/
  | paramFocussing
  /-- Constituent CE reading: wh-question about speaker meaning (ex. 59) -/
  | paramIdentification
  /-- Ground without clarification: ∃-quantify a parameter (ex. 77) -/
  | existentialGeneralization
  deriving Repr, DecidableEq

/-- Output of a coercion operation: partial specification for the
    clarification context. -/
structure CoercionOutput where
  op : CoercionOp
  /-- SAL-UTT: the sub-utterance to be echoed -/
  salUtt : SubUtterance
  /-- MAX-QUD: the question raised (string representation) -/
  maxQud : String
  deriving Repr, DecidableEq

/-- Parameter focussing ([ginzburg-cooper-2004] ex. 53):
derive clausal CE reading.

Takes the *antecedent sign* and a problematic parameter index.
Finds the constituent that introduced the parameter.
Produces MAX-QUD = polar question about the antecedent content. -/
def parameterFocussing (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramFocussing
    salUtt := constit
    maxQud := s!"?{paramIdx}.{antecedent.cont}"
  }

/-- Parameter identification ([ginzburg-cooper-2004] ex. 59):
derive constituent CE reading.

Produces MAX-QUD = wh-question about speaker meaning. -/
def parameterIdentification (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramIdentification
    salUtt := constit
    maxQud := s!"?c.spkr-meaning-rel(addr,{constit.phon},c)"
  }

/-- Contextual existential generalization ([ginzburg-cooper-2004] ex. 77):
ground without clarifying.

Removes a parameter from C-PARAMS by existentially quantifying it. -/
def existentialGeneralization (sk : UttSkeleton) (paramIdx : String) : UttSkeleton :=
  { sk with
    cparams := sk.cparams.filter (·.index != paramIdx)
    cont := s!"∃{paramIdx}.{sk.cont}" }

-- ─── 2004-era Information State ────────────────────────────

/-- Information State for the [ginzburg-cooper-2004] model.

Bundles a DGB with CE processing state (pending utterances). Uses `String`
for both Fact and QContent, matching the string-based representations in
the 2004 paper. The `Participant` type parameter is set to `String`,
and the LocProp `Cont` is set to `String` since this is a 2004-era model.

This is NOT the [ginzburg-2012] TIS — it predates the genre/agenda
private state. It exists to support the CE running example. -/
structure IS (Fact QContent : Type) where
  dgb : DGB String Fact QContent String := {}
  /-- Utterances awaiting full C-PARAMS resolution -/
  pending : List SignAssignment := []
  ce : CEState QContent := {}

/-- An empty IS. -/
def IS.initial {Fact QContent : Type} : IS Fact QContent := {}

/-- Integrate an utterance into the IS.

If the assignment fully resolves all C-PARAMS, the utterance is grounded:
its content goes to FACTS. Otherwise, it goes to PENDING.
[ginzburg-cooper-2004] §6, ex. 82. -/
def IS.integrateUtterance {Fact QContent : Type} [BEq Fact]
    (is_ : IS Fact QContent) (skel : UttSkeleton) (assign : CtxtAssignment)
    (toFact : String → Fact) : IS Fact QContent :=
  if assign.resolvesAll skel.cparams then
    { is_ with dgb := { is_.dgb with facts := is_.dgb.facts ++ [toFact skel.cont] } }
  else
    { is_ with pending := is_.pending ++ [{ sign := skel, assignment := assign }] }

/-- String-specialized integration (content IS the fact). -/
def IS.integrateUtteranceStr (is_ : IS String String)
    (skel : UttSkeleton) (assign : CtxtAssignment) : IS String String :=
  is_.integrateUtterance skel assign id

/-- Apply a coercion output to the IS: set MAX-QUD and SAL-UTT. -/
def IS.applyCoercion {Fact QContent : Type}
    (is_ : IS Fact QContent) (co : CoercionOutput)
    (toQ : String → QContent) : IS Fact QContent :=
  { is_ with ce := { is_.ce with maxQud := some (toQ co.maxQud), salUtt := some co.salUtt } }

/-- String-specialized coercion application. -/
def IS.applyCoercionStr (is_ : IS String String) (co : CoercionOutput) : IS String String :=
  is_.applyCoercion co id

-- ─── LocProp ↔ UttSkeleton converters ──────────────────────

/-- Convert an `UttSkeleton` to a string-content `LocProp`.
    Subsumes the 2004 skeleton representation in the 2012 LocProp framework. -/
def UttSkeleton.toLocProp (sk : UttSkeleton) : LocProp String where
  phon := sk.phon
  cat := sk.cat
  cont := sk.cont
  cparams := sk.cparams
  constits := sk.constits

/-- Convert a `LocProp String` back to an `UttSkeleton`.
    Plain function (not `LocProp.toSkeleton`) because `LocProp` lives in
    `Discourse.Gameboard` and dot notation looks there for the method, not in
    `Apparatus`. Use as `locPropToSkeleton lp`. -/
def locPropToSkeleton (lp : LocProp String) : UttSkeleton where
  phon := lp.phon
  cat := lp.cat
  cont := lp.cont
  cparams := lp.cparams
  constits := lp.constits

/-- Round-trip: UttSkeleton → LocProp → UttSkeleton is identity. -/
theorem skeleton_locprop_roundtrip (sk : UttSkeleton) :
    locPropToSkeleton sk.toLocProp = sk := rfl

-- ─── General theorems on coercion operations ───────────────

/-- Both coercion operations target the same SAL-UTT. -/
theorem coercions_same_salUtt (ant : UttSkeleton) (idx : String) :
    (parameterFocussing ant idx).map CoercionOutput.salUtt =
    (parameterIdentification ant idx).map CoercionOutput.salUtt := by
  unfold parameterFocussing parameterIdentification
  cases ant.constitForParam idx <;> rfl

/-- The two coercion operations produce different operation types. -/
theorem coercions_different_op (ant : UttSkeleton) (idx : String)
    (r1 r2 : CoercionOutput)
    (h1 : parameterFocussing ant idx = some r1)
    (h2 : parameterIdentification ant idx = some r2) :
    r1.op ≠ r2.op := by
  unfold parameterFocussing at h1; unfold parameterIdentification at h2
  cases h : ant.constitForParam idx with
  | none => rw [h] at h1; simp at h1
  | some _ =>
    rw [h] at h1 h2; simp only [Option.some.injEq] at h1 h2
    subst h1; subst h2; exact CoercionOp.noConfusion

/-- A fully resolved assignment leaves no unresolved parameters. -/
theorem resolved_means_no_unresolved (f : CtxtAssignment) (ps : CParamSet)
    (h : f.resolvesAll ps = true) :
    f.unresolved ps = [] := by
  unfold CtxtAssignment.unresolved CtxtAssignment.resolvesAll at *
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.filter_cons, h.1]
    exact ih h.2

/-- Existential generalization never increases the parameter count. -/
theorem existential_gen_weakens (sk : UttSkeleton) (idx : String) :
    (existentialGeneralization sk idx).cparams.length ≤ sk.cparams.length := by
  simp [existentialGeneralization]
  exact List.length_filter_le _ _

end Apparatus

open Apparatus

-- ════════════════════════════════════════════════════
-- § 1. C-PARAMS for "Did Bo leave?" (paper ex. 28/32)
-- ════════════════════════════════════════════════════

/-- C-PARAM for "Bo": binds variable b to the referent named "Bo".
[ginzburg-cooper-2004] ex. 28. -/
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
[ginzburg-cooper-2004] ex. 32. -/
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
[ginzburg-cooper-2004] ex. 32. -/
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
[ginzburg-cooper-2004] ex. 82b. -/
def speakerAssignment : CtxtAssignment where
  bindings := [("b", "B"), ("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1")]

/-- Addressee (B) resolves all parameters EXCEPT b (Bo's referent).
B doesn't know who "Bo" refers to.
[ginzburg-cooper-2004] ex. 82c. -/
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
[ginzburg-cooper-2004] ex. 53–54.
Output: SAL-UTT = "Bo" constituent, MAX-QUD = ?b.ask(i,j,?.leave-rel(b,t))
Paraphrase: "Are you asking if b left?" -/
def focussingOnBo : Option CoercionOutput :=
  parameterFocussing didBoLeave "b"

/-- Parameter identification on "Bo" (parameter b): constituent CE reading.
[ginzburg-cooper-2004] ex. 59–60.
Output: SAL-UTT = "Bo" constituent, MAX-QUD = ?c.spkr-meaning-rel(addr,Bo,c)
Paraphrase: "Who do you mean by Bo?" -/
def identificationOnBo : Option CoercionOutput :=
  parameterIdentification didBoLeave "b"

/-- Existential generalization on "Bo" (parameter b).
[ginzburg-cooper-2004] ex. 77–78.
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
[ginzburg-cooper-2004] §5. -/
def coercionToReading : CoercionOp → CEReading
  | .paramFocussing => .clausal
  | .paramIdentification => .constituent
  | .existentialGeneralization => .clausal  -- acknowledgement variant (ex. 73)

/-- The CE data's two readings map to distinct coercion operations. -/
theorem readings_biject_coercions :
    coercionToReading .paramFocussing ≠ coercionToReading .paramIdentification := by
  decide

-- Hybrid Content Hypothesis

/-- **Hybrid Content Hypothesis** ([ginzburg-cooper-2004] ex. 2/16):
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

/-- The proper-name CE (ex. 4a) carries both readings, in the order the
coercion bridge predicts: clausal, then constituent. -/
theorem running_example_matches_ce_data :
    Examples.ex_4a_bo.readings.map (·.1) = ["clausal", "constituent"] := rfl

/-- Shared-belief minimal pair (ex. 11 vs 12): when A and B are in different
locations, "Here?" lacks the clausal reading (no shared belief about the
content of "here"); when co-located, both readings survive. -/
theorem shared_belief_gates_clausal :
    Examples.ex_11.readings = [("clausal", .unacceptable), ("constituent", .acceptable)] ∧
    Examples.ex_12.readings = [("clausal", .acceptable), ("constituent", .acceptable)] := by
  decide

/-- Indexical CE (ex. 13a): "I?" across speakers shifts reference, so shared
belief about content fails and the clausal reading is blocked. -/
theorem indexical_blocks_clausal :
    Examples.ex_13a.readings.lookup "clausal" = some .unacceptable := by decide

end GinzburgCooper2004
