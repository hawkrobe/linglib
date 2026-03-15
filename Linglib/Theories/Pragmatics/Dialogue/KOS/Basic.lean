import Linglib.Core.Semantics.CommonGround
import Linglib.Theories.Syntax.HPSG.Core.HeadFiller

/-!
# KOS: Dialogue Gameboards and Clarification Ellipsis
@cite{ginzburg-cooper-2004} @cite{ginzburg-2012}

KOS models multi-party dialogue via per-participant **Information States** (IS),
each containing a **Dialogue Gameboard** (DGB). The DGB tracks shared
conversational state; the IS adds processing state for utterance integration.

## DGB vs IS (paper ex. 34, 82)

The DGB has exactly three fields (@cite{ginzburg-cooper-2004} ex. 34):
- **FACTS**: shared commitments (projects to common ground)
- **LATEST-MOVE**: sign + contextual assignment pair ⟨σ, f⟩
- **QUD**: partially ordered set of questions under discussion

The IS wraps the DGB and adds processing state:
- **PENDING**: utterances awaiting grounding
- **MAX-QUD**: the currently maximal question
- **SAL-UTT**: the salient sub-utterance (for clarification)

## Type Parameterization

`DGB` and `IS` are parameterized over content types:
- `Fact`: the type of accumulated facts (e.g., `String` for the string-based
  coercion machinery, `BProp W` for the typed `HasContextSet` bridge)
- `QContent`: the type of QUD entries (e.g., `String` for coercion outputs,
  `QUD M` for the partition-based QUD infrastructure)

This makes explicit which operations are inherently string-based (coercion,
utterance integration) and which are generic (the DGB structure itself,
context set extraction).

## C-PARAMS and SLASH

C-PARAMS (contextual parameters) model referential dependencies that
propagate non-locally through signs. The propagation mechanism is
structurally identical to SLASH amalgamation for extraction
(@cite{ginzburg-cooper-2004} ex. 29, cf. @cite{pollard-sag-1994} Ch. 4):
both are non-local features (sets) that union from daughters to mother
and get discharged at specific sites.

## Coercion Operations (paper §5)

Three coercion operations on signs with unresolved C-PARAMS:

1. **Parameter focussing** (ex. 53) → clausal CE reading: MAX-QUD = polar
   question about whether the antecedent content holds
2. **Parameter identification** (ex. 59) → constituent CE reading: MAX-QUD =
   wh-question about what the speaker meant by the sub-utterance
3. **Contextual existential generalization** (ex. 77) → existentially quantify
   away a parameter to ground without clarification

All three take the *antecedent sign* (not the CE fragment) as input.
-/

namespace Theories.Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. Contextual Parameters
-- ════════════════════════════════════════════════════

/-- A contextual parameter with INDEX and RESTR(ICTION).

Each C-PARAM has an index variable (e.g., "b" for the referent of "Bo")
and a restriction characterizing what values are acceptable (e.g.,
"named(Bo)(b)"). @cite{ginzburg-cooper-2004} ex. 28. -/
structure CParam where
  index : String
  restriction : String
  deriving Repr, DecidableEq, BEq

/-- A set of contextual parameters, analogous to `HPSG.SlashValue`.

Both are non-local features (sets of outstanding dependencies):
- SLASH tracks syntactic gaps (filler-gap dependencies)
- C-PARAMS tracks contextual dependencies (referent resolution)

Both propagate via the same amalgamation mechanism (ex. 29 ≈ Nonlocal
Feature Principle) and get discharged at specific sites. -/
abbrev CParamSet := List CParam

-- ════════════════════════════════════════════════════
-- § 2. Contextual Assignment
-- ════════════════════════════════════════════════════

/-- A contextual assignment maps parameter indices to values.

Grounding requires a *total* assignment (all C-PARAMS resolved).
Clarification arises when the assignment is *partial*.
@cite{ginzburg-cooper-2004} §6, ex. 81–82. -/
structure CtxtAssignment where
  bindings : List (String × String) := []
  deriving Repr, DecidableEq, BEq

/-- Does the assignment resolve a given parameter? -/
def CtxtAssignment.resolves (f : CtxtAssignment) (cp : CParam) : Bool :=
  f.bindings.any (·.1 == cp.index)

/-- Does the assignment resolve all parameters in a set? -/
def CtxtAssignment.resolvesAll (f : CtxtAssignment) (ps : CParamSet) : Bool :=
  ps.all f.resolves

/-- Which parameters remain unresolved? -/
def CtxtAssignment.unresolved (f : CtxtAssignment) (ps : CParamSet) : CParamSet :=
  ps.filter (!f.resolves ·)

-- ════════════════════════════════════════════════════
-- § 3. Utterance Skeletons
-- ════════════════════════════════════════════════════

/-- A sub-utterance: the minimal addressable unit for clarification.

Every sub-utterance encodes PHON, CAT, and CONT — this **fractal
heterogeneity** is what makes clarification of any constituent possible.
@cite{ginzburg-cooper-2004} §2. -/
structure SubUtterance where
  phon : String
  cat : String
  cont : String
  deriving Repr, DecidableEq, BEq

/-- An utterance skeleton: a sign with C-PARAMS and CONSTITS.

The CONSTITS feature (ex. 30) provides access to all sub-utterances.
C-PARAMS (ex. 28–29) are the contextual dependencies introduced by the
sign, amalgamated from daughters via the Non-local Amalgamation Constraint.
@cite{ginzburg-cooper-2004} §3. -/
structure UttSkeleton where
  phon : String
  cat : String
  cont : String
  cparams : CParamSet := []
  constits : List SubUtterance := []
  deriving Repr, DecidableEq, BEq

/-- Find the constituent whose CONT matches a parameter index.

This is how coercion operations identify which sub-utterance
introduced a problematic parameter: they match the constituent's
semantic content to the parameter's index variable. -/
def UttSkeleton.constitForParam (u : UttSkeleton) (paramIdx : String) :
    Option SubUtterance :=
  u.constits.find? (·.cont == paramIdx)

-- ════════════════════════════════════════════════════
-- § 4. Dialogue Gameboard (paper ex. 34)
-- ════════════════════════════════════════════════════

/-- LATEST-MOVE: a sign paired with a contextual assignment.

This is the structured value of LATEST-MOVE (@cite{ginzburg-cooper-2004}
ex. 81, p.353). The assignment f records which C-PARAMS have been resolved.
Grounding checks whether f is total (resolves all C-PARAMS of the sign). -/
structure LatestMove where
  sign : UttSkeleton
  assignment : CtxtAssignment
  deriving Repr, DecidableEq, BEq

/-- The Dialogue Gameboard: {FACTS, LATEST-MOVE, QUD}.

@cite{ginzburg-cooper-2004} ex. 34, p.325. @cite{ginzburg-2012} Ch. 4.
This is the *public* component of a participant's conversational state.
Processing state (PENDING, MAX-QUD, SAL-UTT) lives in the broader
Information State.

The type parameters make the content types explicit:
- `Fact`: type of accumulated facts in the common ground. Use `String`
  for the string-based coercion machinery, `BProp W` for typed CG access.
- `QContent`: type of QUD entries. Use `String` for coercion outputs,
  or a richer question type for the partition-based QUD infrastructure. -/
structure DGB (Fact QContent : Type) where
  facts : List Fact := []
  latestMove : Option LatestMove := none
  qud : List QContent := []

def DGB.initial {Fact QContent : Type} : DGB Fact QContent := {}

-- ════════════════════════════════════════════════════
-- § 5. Information State
-- ════════════════════════════════════════════════════

/-- A pending utterance: sign + partial assignment, awaiting grounding. -/
structure PendingUtt where
  sign : UttSkeleton
  assignment : CtxtAssignment
  deriving Repr, DecidableEq, BEq

/-- A participant's Information State, wrapping the DGB.

The IS adds utterance-processing state to the public DGB:
- **PENDING**: utterances not yet grounded (p.350, ex. 79)
- **MAX-QUD**: the currently maximal question (p.327)
- **SAL-UTT**: the salient sub-utterance for clarification (p.327)

@cite{ginzburg-cooper-2004} ex. 82 shows that speaker and addressee
maintain *distinct* information states after the same utterance. -/
structure IS (Fact QContent : Type) where
  dgb : DGB Fact QContent := {}
  pending : List PendingUtt := []
  maxQud : Option QContent := none
  salUtt : Option SubUtterance := none

def IS.initial {Fact QContent : Type} : IS Fact QContent := {}

-- ════════════════════════════════════════════════════
-- § 6. Coercion Operations
-- ════════════════════════════════════════════════════

/-- The three coercion operations on signs with unresolved C-PARAMS. -/
inductive CoercionOp where
  /-- Clausal CE reading: polar question about content (ex. 53) -/
  | paramFocussing
  /-- Constituent CE reading: wh-question about speaker meaning (ex. 59) -/
  | paramIdentification
  /-- Ground without clarification: ∃-quantify a parameter (ex. 77) -/
  | existentialGeneralization
  deriving Repr, DecidableEq, BEq

/-- Output of a coercion operation: partial specification for the
    clarification context.

The `maxQud` field is `String` because coercion operations construct
question content via string interpolation. When the IS uses a richer
`QContent` type, a conversion step mediates. -/
structure CoercionOutput where
  op : CoercionOp
  /-- SAL-UTT: the sub-utterance to be echoed -/
  salUtt : SubUtterance
  /-- MAX-QUD: the question raised (string representation) -/
  maxQud : String
  deriving Repr, DecidableEq, BEq

/-- Parameter focussing (ex. 53): derive clausal CE reading.

Takes the *antecedent sign* and a problematic parameter index.
Finds the constituent that introduced the parameter.
Produces MAX-QUD = polar question about the antecedent content (?i.p).

Example: antecedent "Did Bo leave?", parameter "b" (referent of Bo)
→ MAX-QUD = "?b.ask(i,j,?.leave(b,t))", SAL-UTT = "Bo" constituent
→ Paraphrasable as "Are you asking whether Bo left?" -/
def parameterFocussing (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramFocussing
    salUtt := constit
    maxQud := s!"?{paramIdx}.{antecedent.cont}"
  }

/-- Parameter identification (ex. 59): derive constituent CE reading.

Takes the *antecedent sign* and a problematic parameter index.
Finds the constituent that introduced the parameter.
Produces MAX-QUD = wh-question about speaker meaning (spkr-meaning-rel).

Example: antecedent "Did Bo leave?", parameter "b" (referent of Bo)
→ MAX-QUD = "?c.spkr-meaning-rel(addr, Bo, c)", SAL-UTT = "Bo" constituent
→ Paraphrasable as "Who do you mean by Bo?" -/
def parameterIdentification (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramIdentification
    salUtt := constit
    maxQud := s!"?c.spkr-meaning-rel(addr,{constit.phon},c)"
  }

/-- Contextual existential generalization (ex. 77): ground without clarifying.

Removes a parameter from C-PARAMS by existentially quantifying it,
weakening the content. This is how *most* utterances get grounded —
addressees typically don't seek clarification for every parameter. -/
def existentialGeneralization (sk : UttSkeleton) (paramIdx : String) : UttSkeleton :=
  { sk with
    cparams := sk.cparams.filter (·.index != paramIdx)
    cont := s!"∃{paramIdx}.{sk.cont}" }

-- ════════════════════════════════════════════════════
-- § 7. IS Update Protocol (paper ex. 79/81/84)
-- ════════════════════════════════════════════════════

/-- Integrate an utterance into the IS.

If the assignment resolves all C-PARAMS → **ground**: add content to
FACTS and clear processing state.
If the assignment is partial → **pending**: add to PENDING for
subsequent clarification.

This operation is inherently string-based: it adds `sk.cont` (a String)
to the DGB's facts. For typed DGBs, use a conversion step.

@cite{ginzburg-cooper-2004} ex. 81, p.353. -/
def IS.integrateUtterance {QContent : Type} (is_ : IS String QContent) (sk : UttSkeleton)
    (f : CtxtAssignment) : IS String QContent :=
  let lm : LatestMove := { sign := sk, assignment := f }
  if f.resolvesAll sk.cparams then
    { is_ with
      dgb := { is_.dgb with
        facts := sk.cont :: is_.dgb.facts
        latestMove := some lm }
      maxQud := none
      salUtt := none }
  else
    { is_ with
      dgb := { is_.dgb with latestMove := some lm }
      pending := { sign := sk, assignment := f } :: is_.pending }

/-- Apply a coercion to set MAX-QUD and SAL-UTT on the IS.

This operation requires `QContent = String` because coercion outputs
produce string-valued question content. -/
def IS.applyCoercion {Fact : Type} (is_ : IS Fact String) (co : CoercionOutput) : IS Fact String :=
  { is_ with maxQud := some co.maxQud, salUtt := some co.salUtt }

-- ════════════════════════════════════════════════════
-- § 8. Structural Theorems
-- ════════════════════════════════════════════════════

/-- Both coercion operations target the same SAL-UTT (the constituent
    that introduced the problematic parameter). -/
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

/-- Grounding adds exactly one fact. -/
theorem grounding_adds_fact {QContent : Type}
    (is_ : IS String QContent) (sk : UttSkeleton) (f : CtxtAssignment)
    (h : f.resolvesAll sk.cparams = true) :
    (is_.integrateUtterance sk f).dgb.facts = sk.cont :: is_.dgb.facts := by
  simp only [IS.integrateUtterance, h, ↓reduceIte]

/-- A partial assignment does not add facts. -/
theorem partial_no_facts {QContent : Type}
    (is_ : IS String QContent) (sk : UttSkeleton) (f : CtxtAssignment)
    (h : f.resolvesAll sk.cparams = false) :
    (is_.integrateUtterance sk f).dgb.facts = is_.dgb.facts := by
  unfold IS.integrateUtterance; simp [h]

/-- A partial assignment adds to PENDING. -/
theorem partial_adds_pending {QContent : Type}
    (is_ : IS String QContent) (sk : UttSkeleton) (f : CtxtAssignment)
    (h : f.resolvesAll sk.cparams = false) :
    (is_.integrateUtterance sk f).pending.length = is_.pending.length + 1 := by
  unfold IS.integrateUtterance; simp [h]

-- ════════════════════════════════════════════════════
-- § 9. SLASH Analogy Bridge
-- ════════════════════════════════════════════════════

/-- Structural analogy: discharging a SLASH gap and resolving a C-PARAM
    both reduce the count of outstanding dependencies.

    `HPSG.SlashValue.discharge` removes a category from SLASH.
    `CParamSet.filter (·.index != idx)` removes a parameter from C-PARAMS.

    Both follow the Non-local Amalgamation Constraint: the mother's
    non-local feature value is the union of its daughters' values. -/
theorem slash_cparams_both_decrease
    (sv : HPSG.SlashValue) (cat : UD.UPOS)
    (ps : CParamSet) (idx : String) :
    (sv.discharge cat).gaps.length ≤ sv.gaps.length ∧
    (ps.filter (·.index != idx)).length ≤ ps.length := by
  constructor
  · simp only [HPSG.SlashValue.discharge]; exact List.length_erase_le
  · exact List.length_filter_le _ _

-- ════════════════════════════════════════════════════
-- § 10. HasContextSet Bridge
-- ════════════════════════════════════════════════════

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- DGB with `BProp W` facts projects to a context set: the worlds
    compatible with all accumulated facts. This connects the dialogue
    gameboard to the unified common ground interface.

    @cite{ginzburg-2012} Ch. 4: the DGB's FACTS field IS the common ground. -/
instance {W : Type} {QContent : Type} :
    HasContextSet (DGB (BProp W) QContent) W where
  toContextSet dgb := λ w => dgb.facts.all (· w)

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- IS with `BProp W` facts inherits the DGB's context set. -/
instance {W : Type} {QContent : Type} :
    HasContextSet (IS (BProp W) QContent) W where
  toContextSet is_ := λ w => is_.dgb.facts.all (· w)

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- IS context set is extracted from the DGB. -/
theorem is_contextSet_eq_dgb {W : Type} {QContent : Type}
    (is_ : IS (BProp W) QContent) :
    HasContextSet.toContextSet is_ = HasContextSet.toContextSet is_.dgb := rfl

-- ════════════════════════════════════════════════════
-- § 11. DGB Content Mapping
-- ════════════════════════════════════════════════════

/-- Map over a DGB's fact type, preserving structure. -/
def DGB.mapFacts {Fact Fact' QContent : Type} (f : Fact → Fact')
    (dgb : DGB Fact QContent) : DGB Fact' QContent where
  facts := dgb.facts.map f
  latestMove := dgb.latestMove
  qud := dgb.qud

/-- Map over a DGB's question type, preserving structure. -/
def DGB.mapQud {Fact QContent QContent' : Type} (f : QContent → QContent')
    (dgb : DGB Fact QContent) : DGB Fact QContent' where
  facts := dgb.facts
  latestMove := dgb.latestMove
  qud := dgb.qud.map f

/-- Mapping facts preserves fact count. -/
theorem DGB.mapFacts_length {Fact Fact' QContent : Type} (f : Fact → Fact')
    (dgb : DGB Fact QContent) :
    (dgb.mapFacts f).facts.length = dgb.facts.length := by
  simp only [DGB.mapFacts, List.length_map]

end Theories.Pragmatics.Dialogue.KOS
