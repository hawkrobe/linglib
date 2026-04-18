import Linglib.Theories.Semantics.Modality.Assert
import Linglib.Theories.Syntax.Minimalism.SpeechActs
import Linglib.Fragments.French.Modals

/-!
# @cite{ruytenbeek-etal-2017}: Indirect Request Processing, Sentence Types
  and Illocutionary Forces

Journal of Pragmatics 119 (2017) 46–62.

Two French eye-tracking experiments testing the **literalist** view that
sentence types encode illocutionary force at the semantic level.

## Core Finding

Non-literalist theories are supported: directive illocutionary force is
not encoded in sentence type but arises from **shared semantic features**
between imperatives and deontic modals. Specifically:

1. Non-conventionalized indirect requests (*Est-il possible de VP?*) are
   processed as fast as conventionalized ones (*Pouvez-vous VP?*) and
   imperatives for directive interpretations.
2. Deontic necessity modals (*Vous devez VP*) receive directive force as
   readily as imperatives — same response times, no fixation on true/false
   buttons — unlike ability modals (*Vous pouvez VP*) or existential modals
   (*Il est possible de VP*).

## Two Mechanisms for Directive Force

The paper distinguishes two routes to directive illocutionary force:

1. **Shared deontic semantics** (@cite{kaufmann-2012}): *Vous devez VP*
   shares deontic necessity with imperatives → directive force is
   *direct* (Study 2). Modeled by `directiveCompatible`.

2. **Convention of means** (@cite{clark-1979}): *Pouvez-vous VP?* and
   *Est-il possible de VP?* question a preparatory condition for the
   request (addressee's ability) → directive force is *indirect* (Study 1).
   Not modeled by `directiveCompatible` — these constructions get directive
   force through pragmatic inference, not shared modal flavor.

## Connection to Assert.lean

The paper experimentally validates what `Semantics.Modality.Assert`
already encodes: `primaryFlavor .imperative = .deontic`. @cite{kaufmann-2012}'s
thesis — that imperatives have the semantics of deontic necessity modals —
predicts that deontic necessity declaratives should receive directive force
as readily as imperatives. Study 2 confirms exactly this.

## Connection to ClauseType

The paper reveals a gap in the `SAPMood → ClauseType` mapping:
`SAPMood.toClauseType` treats the mapping as 1-to-1, but indirect
speech acts involve a mismatch — a declarative or interrogative sentence
type receiving directive illocutionary force.
-/

namespace RuytenbeekEtAl2017

open Core.Modality (ModalFlavor ModalForce)
open Core.Mood (IllocutionaryMood)
open Semantics.Modality.Assert (primaryFlavor SpeechActType)
open Minimalism.Phenomena.SpeechActs (SAPMood)


-- ════════════════════════════════════════════════════
-- § 1. Sentence Types and Modal Flavors
-- ════════════════════════════════════════════════════

/-- Sentence types used in the experiments. These are morphosyntactic
    categories (sentence types), NOT illocutionary forces — the paper's
    core point is that these come apart. -/
inductive SentType where
  | imperative       -- "Mettez le cercle rouge..."
  | canYouInterrog   -- "Pouvez-vous VP?" (conventionalized IR)
  | possibleInterrog -- "Est-il possible de VP?" (non-conventionalized IR)
  | ctrlInterrog     -- "Le cercle rouge est-il...?" (control interrogative)
  | mustDeclarative  -- "Vous devez VP" (deontic necessity)
  | canDeclarative   -- "Vous pouvez VP" (ability/permission)
  | possibleDecl     -- "Il est possible de VP" (existential possibility)
  | plainDeclarative -- "Le cercle rouge est..." (control declarative)
  deriving DecidableEq, Repr

/-- The morphosyntactic mood of each sentence type. -/
def SentType.mood : SentType → SAPMood
  | .imperative       => .imperative
  | .canYouInterrog   => .interrogative
  | .possibleInterrog => .interrogative
  | .ctrlInterrog     => .interrogative
  | .mustDeclarative  => .declarative
  | .canDeclarative   => .declarative
  | .possibleDecl     => .declarative
  | .plainDeclarative => .declarative

/-- The contextually salient modal flavor contributed by the modal (if any).

    NB: *pouvoir* and *il est possible de* are polysemous across epistemic,
    deontic, and circumstantial readings (see `Fragments.French.Modals`).
    The flavor assigned here is the contextually salient one in the
    experimental setting (2nd person, action-oriented context). -/
def SentType.modalFlavor : SentType → Option ModalFlavor
  | .imperative       => some .deontic         -- imperative = deontic (Kaufmann 2012)
  | .canYouInterrog   => some .circumstantial  -- ability/dynamic possibility
  | .possibleInterrog => some .circumstantial  -- modal existential possibility
  | .ctrlInterrog     => none
  | .mustDeclarative  => some .deontic         -- deontic necessity
  | .canDeclarative   => some .circumstantial  -- ability/permission
  | .possibleDecl     => some .circumstantial  -- existential possibility
  | .plainDeclarative => none

/-- The modal force (if any). -/
def SentType.modalForce : SentType → Option ModalForce
  | .imperative       => some .necessity
  | .canYouInterrog   => some .possibility
  | .possibleInterrog => some .possibility
  | .ctrlInterrog     => none
  | .mustDeclarative  => some .necessity
  | .canDeclarative   => some .possibility
  | .possibleDecl     => some .possibility
  | .plainDeclarative => none


-- ════════════════════════════════════════════════════
-- § 2. Directive Compatibility (Mechanism 1: Shared Deontic Semantics)
-- ════════════════════════════════════════════════════

/-- A construction is directive-compatible when its modal flavor matches
    the imperative's primary flavor (deontic).

    This models **mechanism 1** (shared deontic semantics): deontic modals
    in declaratives receive directive force because they share the relevant
    semantic feature with imperatives (@cite{kaufmann-2012}).

    This does NOT model **mechanism 2** (convention of means / preparatory
    condition questioning): *Pouvez-vous VP?* and *Est-il possible de VP?*
    get directive force by questioning the addressee's ability, which is a
    preparatory condition for requests (@cite{clark-1979}). That mechanism
    operates via pragmatic inference, not modal flavor matching. -/
def directiveCompatible (flavor : ModalFlavor) : Bool :=
  flavor == .deontic

/-- Directive compatibility for a sentence type via mechanism 1 (shared
    deontic semantics). Returns false for interrogative IRs, which use
    mechanism 2 (preparatory condition questioning) instead. -/
def SentType.isDirectiveCompatible : SentType → Bool
  | s => match s.modalFlavor with
    | some f => directiveCompatible f
    | none   => false


-- ════════════════════════════════════════════════════
-- § 3. Corpus Data (Frantext)
-- ════════════════════════════════════════════════════

/-- Corpus usage distribution for a construction, classified by
    illocutionary force in context. -/
structure CorpusDistribution where
  construction : String
  nTokens      : Nat
  directiveN   : Nat
  questionN    : Nat
  rhetoricalN  : Nat
  deriving Repr

def CorpusDistribution.directiveRate (d : CorpusDistribution) : Rat :=
  d.directiveN / d.nTokens

/-- Frantext corpus data: *Pouvez-vous VP?* with singular addressee.
    N = 365. Directive uses = 71%, questions = 25%, rhetorical = 4%. -/
def frantextCanYou : CorpusDistribution :=
  { construction := "Pouvez-vous VP?"
  , nTokens := 365, directiveN := 259, questionN := 91, rhetoricalN := 15 }

/-- Frantext corpus data: *Est-il possible de VP?* with singular addressee.
    N = 63. Directive uses = 16%, questions = 70%, rhetorical = 14%. -/
def frantextPossible : CorpusDistribution :=
  { construction := "Est-il possible de VP?"
  , nTokens := 63, directiveN := 10, questionN := 44, rhetoricalN := 9 }

/-- Corpus category counts sum to the total. -/
theorem frantextCanYou_total :
    frantextCanYou.directiveN + frantextCanYou.questionN +
    frantextCanYou.rhetoricalN = frantextCanYou.nTokens := by native_decide

theorem frantextPossible_total :
    frantextPossible.directiveN + frantextPossible.questionN +
    frantextPossible.rhetoricalN = frantextPossible.nTokens := by native_decide

/-- *Pouvez-vous VP?* is significantly more conventionalized as a directive
    construction than *Est-il possible de VP?* (χ²(2, N=428) = 66.75,
    p < 0.001). -/
theorem canYou_more_conventionalized :
    frantextCanYou.directiveRate > frantextPossible.directiveRate := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 4. Study 1: Conventionalized vs Non-Conventionalized IRs
-- ════════════════════════════════════════════════════

/-! Study 1 (N = 41) tests whether non-conventionalized indirect requests
    can be indirect but primary. 24 trials: 6 imperatives, 6 control
    interrogatives, 6 *Can you VP?*, 6 *Is it possible to VP?*.
    Participants hear French sentences paired with a grid of colored shapes
    and respond by either moving a shape (directive) or clicking yes/no
    (question).

    For *Can you* and *Is it possible* interrogatives, half the trials
    have the correct answer = yes and the move is possible; for the other
    half the correct answer = no. Analysis restricted to move-possible
    trials: 6/2 × 41 = 123 per interrogative type.

    Key finding: directive interpretations of both *Can you* and *Is it
    possible* sentences are processed as fast as imperatives, with no
    fixation on the yes/no area for either. -/

/-- Response types in Study 1. -/
inductive Study1Response where
  | move  -- Directive interpretation: participant moves a shape
  | yesNo -- Question interpretation: participant clicks yes or no
  deriving DecidableEq, Repr

/-- Study 1 result: mean response time (ms) and proportion of directive
    (move) responses for each sentence type.

    RTs are β coefficients from the linear mixed effects model (exact
    from the paper's text). Proportions are approximate, estimated from
    Fig. 3 (exact counts not reported). -/
structure Study1Result where
  sentType     : SentType
  moveRT       : Nat    -- Mean RT for move responses (ms), from β estimates
  yesNoRT      : Nat    -- Mean RT for yes/no responses (ms)
  moveProp     : Rat    -- Proportion of move (directive) responses (APPROXIMATE)
  deriving Repr

def study1Imperative : Study1Result :=
  { sentType := .imperative
  , moveRT := 2833, yesNoRT := 0
  , moveProp := 1 }

def study1CanYou : Study1Result :=
  { sentType := .canYouInterrog
  , moveRT := 2990, yesNoRT := 4729
  , moveProp := 98 / 123 }  -- APPROXIMATE from Fig. 3

def study1Possible : Study1Result :=
  { sentType := .possibleInterrog
  , moveRT := 2878, yesNoRT := 4409
  , moveProp := 80 / 123 }  -- APPROXIMATE from Fig. 3

def study1CtrlInterrog : Study1Result :=
  { sentType := .ctrlInterrog
  , moveRT := 0, yesNoRT := 3707
  , moveProp := 0 }  -- control interrogatives only have yes/no responses

/-- Study 1 key finding: no significant difference in RT between imperative,
    *Can you*, and *Is it possible* for directive (move) interpretations
    (all p's > 0.99 in post hoc comparisons). -/
theorem study1_directive_rts_similar :
    let imp := study1Imperative.moveRT
    let can := study1CanYou.moveRT
    let pos := study1Possible.moveRT
    (Int.natAbs (can - imp) < 200) ∧
    (Int.natAbs (pos - imp) < 200) ∧
    (Int.natAbs (can - pos) < 200) := by
  native_decide

/-- Study 1: *Can you* elicits more directive interpretations than
    *Is it possible* (β = 0.79, z = 2.031, p = 0.043). -/
theorem study1_canYou_more_directive :
    study1CanYou.moveProp > study1Possible.moveProp := by
  native_decide

/-- Study 1: despite conventionalization difference, directive RTs are
    indistinguishable — non-conventionalized IRs don't require extra
    processing. This contradicts the literalist prediction that
    non-conventionalized IRs must activate the question force first. -/
theorem study1_no_rt_penalty :
    study1Possible.moveRT ≤ study1CanYou.moveRT := by
  native_decide

/-- Study 1: question interpretations of *Can you* take longer than control
    interrogatives (β = 4729 vs 3707, t(29.34) = 3.49, p = 0.03). The
    conventionalized directive reading BLOCKS the question reading. -/
theorem study1_canYou_question_slower_than_ctrl :
    study1CanYou.yesNoRT > study1CtrlInterrog.yesNoRT := by native_decide


-- ════════════════════════════════════════════════════
-- § 4b. Study 1: Eye-Tracking (Fixation Duration)
-- ════════════════════════════════════════════════════

/-! The strongest anti-literalist evidence: fixation duration on the yes/no
    buttons (AOI). If the literalist view is correct, directive interpretations
    of interrogatives should FIRST activate the question force, yielding
    fixation on the yes/no area. The data show the opposite.

    Fixation durations from Fig. 5 (approximate, in ms):
    - Imperatives (move): ~5ms (near zero)
    - *Can you* (move): ~5ms (near zero)
    - *Is it possible* (move): ~0ms
    - Control interrogatives (yes/no): ~280ms
    - *Can you* (yes/no): ~280ms
    - *Is it possible* (yes/no): ~230ms

    The linear mixed effects model found no difference between control
    interrogatives and question interpretations of *Can you* and *Is it
    possible* (χ²(2) = 1.66, p = 0.43). -/

/-- Fixation data for a sentence type and response type. -/
structure FixationResult where
  sentType   : SentType
  isDirective : Bool     -- true = move response, false = yes-no/true-false
  fixationMs : Nat       -- Mean fixation duration on response buttons (ms)
  deriving Repr

-- Study 1 fixation data (approximate from Fig. 5)
def fix1_imp_move : FixationResult :=
  { sentType := .imperative, isDirective := true, fixationMs := 5 }
def fix1_can_move : FixationResult :=
  { sentType := .canYouInterrog, isDirective := true, fixationMs := 5 }
def fix1_pos_move : FixationResult :=
  { sentType := .possibleInterrog, isDirective := true, fixationMs := 0 }
def fix1_can_yesno : FixationResult :=
  { sentType := .canYouInterrog, isDirective := false, fixationMs := 280 }
def fix1_pos_yesno : FixationResult :=
  { sentType := .possibleInterrog, isDirective := false, fixationMs := 230 }
def fix1_ctrl_yesno : FixationResult :=
  { sentType := .ctrlInterrog, isDirective := false, fixationMs := 280 }

/-- Directive interpretations show virtually NO fixation on the yes/no
    buttons — the question meaning is not activated. -/
theorem study1_directive_no_fixation :
    fix1_imp_move.fixationMs < 10 ∧
    fix1_can_move.fixationMs < 10 ∧
    fix1_pos_move.fixationMs < 10 := by native_decide

/-- Question interpretations DO show fixation on yes/no buttons. -/
theorem study1_question_has_fixation :
    fix1_can_yesno.fixationMs > 200 ∧
    fix1_pos_yesno.fixationMs > 200 ∧
    fix1_ctrl_yesno.fixationMs > 200 := by native_decide

/-- The fixation gap is massive: question interpretations fixate on the
    response buttons 40–60× longer than directive interpretations. This
    is the smoking gun against literalism. -/
theorem study1_fixation_gap :
    fix1_can_yesno.fixationMs > fix1_can_move.fixationMs * 40 ∧
    fix1_pos_yesno.fixationMs > fix1_pos_move.fixationMs * 40 := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 5. Study 2: Imperatives, Modals, and Declaratives
-- ════════════════════════════════════════════════════

/-! Study 2 (N = 40) tests whether deontic necessity modals (*Vous devez VP*)
    are processed as directives in the same way as imperatives. 24 trials:
    3 *You must*, 3 control imperatives, 6 *You can/may*, 6 *It is possible*,
    6 control declaratives. Task identical to Study 1, but yes/no replaced
    by true/false (enabling both directive and assertive responses).

    Trial counts: Must and imperatives always allow move (3 × 40 = 120 each).
    Can and Possible: half allow move (6/2 × 40 = 120 each).

    Key finding: *You must* sentences receive overwhelmingly directive
    interpretations, just like imperatives, with identical response times.
    The paper reports n = 21 true/false responses to Must (out of 120). -/

/-- Response types in Study 2. -/
inductive Study2Response where
  | move      -- Directive interpretation: participant moves a shape
  | trueFalse -- Assertive interpretation: participant clicks true or false
  deriving DecidableEq, Repr

/-- Study 2 result for each sentence type.

    RTs are β coefficients from the linear mixed effects model (exact from
    text). Proportions use 120 as denominator (3 × 40 for must/imperative,
    6/2 × 40 for can/possible). Numerators for must are derived from the
    text (n = 21 true/false out of 120 → 99 move). Numerators for can
    and possible are approximate from Fig. 6. -/
structure Study2Result where
  sentType      : SentType
  moveRT        : Nat    -- Mean RT for move responses (ms), from β estimates
  trueFalseRT   : Nat    -- Mean RT for true/false responses (ms)
  moveProp      : Rat    -- Proportion of move (directive) responses
  deriving Repr

def study2Imperative : Study2Result :=
  { sentType := .imperative
  , moveRT := 2953, trueFalseRT := 0
  , moveProp := 1 }  -- n = 9 true/false excluded as errors

def study2Must : Study2Result :=
  { sentType := .mustDeclarative
  , moveRT := 3133, trueFalseRT := 0
  , moveProp := 99 / 120 }  -- n = 21 true/false out of 120 (from text)

def study2Can : Study2Result :=
  { sentType := .canDeclarative
  , moveRT := 3146, trueFalseRT := 3184
  , moveProp := 35 / 120 }  -- APPROXIMATE from Fig. 6

def study2PossibleDecl : Study2Result :=
  { sentType := .possibleDecl
  , moveRT := 3184, trueFalseRT := 3184
  , moveProp := 15 / 120 }  -- APPROXIMATE from Fig. 6

/-- Study 2 core finding: *You must* response times are indistinguishable
    from imperatives (p > 0.99 in post hoc comparison). -/
theorem study2_must_equals_imperative_rt :
    Int.natAbs (study2Must.moveRT - study2Imperative.moveRT) < 200 := by
  native_decide

/-- Study 2: *You must* receives the vast majority of directive
    interpretations. -/
theorem study2_must_mostly_directive :
    study2Must.moveProp > 4 / 5 := by
  native_decide

/-- Study 2: *You can* and *It is possible* receive far fewer directive
    interpretations than *You must*. -/
theorem study2_must_more_directive_than_can :
    study2Must.moveProp > study2Can.moveProp := by
  native_decide

theorem study2_must_more_directive_than_possible :
    study2Must.moveProp > study2PossibleDecl.moveProp := by
  native_decide

/-- Study 2: *You can* triggers more directive readings than *It is possible*
    (z = −3.29, p = 0.0028). Permission (deontic possibility) is closer to
    directive force than pure circumstantial possibility. -/
theorem study2_can_more_directive_than_possible :
    study2Can.moveProp > study2PossibleDecl.moveProp := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 5b. Study 2: Eye-Tracking (Fixation Duration)
-- ════════════════════════════════════════════════════

/-! Fixation on the true/false buttons (Fig. 8, approximate in ms):
    - Imperatives (move): ~10ms
    - *You must* (move): ~15ms
    - *You can* (move): ~0ms
    - *It is possible* (move): ~0ms
    - *You can* (true/false): ~270ms
    - *It is possible* (true/false): ~265ms
    - Control declaratives (true/false, yes): ~270ms

    Critically: imperatives, *You must* directive, and *You can*/*It is
    possible* directive interpretations all show ~0ms fixation on the
    true/false buttons. The assertive meaning is NOT activated. -/

-- Study 2 fixation data (approximate from Fig. 8)
def fix2_imp_move : FixationResult :=
  { sentType := .imperative, isDirective := true, fixationMs := 10 }
def fix2_must_move : FixationResult :=
  { sentType := .mustDeclarative, isDirective := true, fixationMs := 15 }
def fix2_can_move : FixationResult :=
  { sentType := .canDeclarative, isDirective := true, fixationMs := 0 }
def fix2_can_tf : FixationResult :=
  { sentType := .canDeclarative, isDirective := false, fixationMs := 270 }
def fix2_pos_tf : FixationResult :=
  { sentType := .possibleDecl, isDirective := false, fixationMs := 265 }

/-- Study 2: directive interpretations show virtually no fixation on the
    true/false buttons — the assertive/statement meaning is not activated.
    This holds for *You must* (a declarative!) just as for imperatives. -/
theorem study2_directive_no_fixation :
    fix2_imp_move.fixationMs < 20 ∧
    fix2_must_move.fixationMs < 20 ∧
    fix2_can_move.fixationMs < 20 := by native_decide

/-- Study 2: statement interpretations DO show fixation on true/false. -/
theorem study2_statement_has_fixation :
    fix2_can_tf.fixationMs > 200 ∧
    fix2_pos_tf.fixationMs > 200 := by native_decide

/-- The core anti-literalist evidence from Study 2: *You must* is a
    DECLARATIVE sentence, yet directive interpretations show the same near-
    zero fixation on the statement-response buttons as IMPERATIVES. If
    literalism were correct, interpreting a declarative as a directive should
    first activate the assertive force → fixation on true/false. It doesn't. -/
theorem study2_must_declarative_no_statement_activation :
    SentType.mood .mustDeclarative = .declarative ∧
    fix2_must_move.fixationMs < 20 := ⟨rfl, by native_decide⟩


-- ════════════════════════════════════════════════════
-- § 6. Bridge Theorems: Connecting to Assert.lean
-- ════════════════════════════════════════════════════

/-! The paper's core theoretical contribution connects to `Assert.lean`:
    imperatives and deontic necessity modals share a modal flavor, which
    is why they both license directive force (mechanism 1). -/

/-- Imperatives and deontic necessity modals share the same modal flavor.
    This is the semantic basis for the Study 2 finding that *You must VP*
    is processed identically to imperatives.

    @cite{kaufmann-2012} makes this claim explicitly; the paper validates
    it experimentally. -/
theorem imperative_must_share_flavor :
    SentType.modalFlavor .imperative = SentType.modalFlavor .mustDeclarative := rfl

/-- Imperatives and deontic necessity modals share the same modal force. -/
theorem imperative_must_share_force :
    SentType.modalForce .imperative = SentType.modalForce .mustDeclarative := rfl

/-- The `primaryFlavor` from Assert.lean already encodes the imperative–deontic
    link: imperative speech acts have deontic content. This is the theory-layer
    fact that the paper experimentally validates. -/
theorem assert_imperative_is_deontic :
    primaryFlavor .imperative = .deontic := rfl

/-- Both imperatives and *You must* declaratives are directive-compatible
    (mechanism 1). Follows from both having deontic modal flavor. -/
theorem imperative_directive_compatible :
    SentType.isDirectiveCompatible .imperative = true := rfl

theorem must_directive_compatible :
    SentType.isDirectiveCompatible .mustDeclarative = true := rfl

/-- Ability and existential possibility modals are NOT directive-compatible
    via mechanism 1. They have circumstantial (not deontic) flavor. This
    predicts the Study 2 finding: *You can* and *It is possible* receive
    fewer directive interpretations than *You must*.

    NB: these constructions CAN still receive directive force via
    mechanism 2 (questioning a preparatory condition), which explains
    the non-zero directive rate (~30% for can, ~13% for possible). -/
theorem can_not_directive_compatible :
    SentType.isDirectiveCompatible .canDeclarative = false := rfl

theorem possible_not_directive_compatible :
    SentType.isDirectiveCompatible .possibleDecl = false := rfl

/-- Directive compatibility (mechanism 1) correctly predicts the ranking
    of directive response rates in Study 2: deontic-flavored constructions
    (imperative, *you must*) get high directive rates; circumstantial-
    flavored constructions (*you can*, *it is possible*) get low rates. -/
theorem directive_compatibility_predicts_study2 :
    (SentType.isDirectiveCompatible .imperative = true ∧
     study2Imperative.moveProp = 1) ∧
    (SentType.isDirectiveCompatible .mustDeclarative = true ∧
     study2Must.moveProp > 4 / 5) ∧
    (SentType.isDirectiveCompatible .canDeclarative = false ∧
     study2Can.moveProp < 1 / 2) ∧
    (SentType.isDirectiveCompatible .possibleDecl = false ∧
     study2PossibleDecl.moveProp < 1 / 2) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩ <;> native_decide


-- ════════════════════════════════════════════════════
-- § 7. Bridge: SAPMood ≠ Illocutionary Force
-- ════════════════════════════════════════════════════

/-! The paper demonstrates that `SAPMood.toClauseType` is the
    DEFAULT force mapping, not the only possible one. Indirect speech acts
    involve a sentence type receiving a non-default illocutionary force. -/

/-- The default illocutionary force for declaratives is NOT directive. -/
theorem declarative_default_not_directive :
    (SAPMood.toClauseType .declarative).force ≠ .imperative := by decide

/-- But deontic necessity declaratives CAN receive directive force.
    The force mismatch (declarative sentence type + directive force) is
    exactly what the paper demonstrates for *Vous devez VP*.

    This is modeled by the `isDirectiveCompatible` predicate, which
    bypasses sentence type and checks the modal semantics directly. -/
theorem must_declarative_force_mismatch :
    SentType.mood .mustDeclarative = .declarative ∧
    SentType.isDirectiveCompatible .mustDeclarative = true := ⟨rfl, rfl⟩

/-- Interrogative IRs also exhibit force mismatch: interrogative sentence
    type with directive force (via mechanism 2). -/
theorem canYou_force_mismatch :
    SentType.mood .canYouInterrog = .interrogative ∧
    study1CanYou.moveProp > 1 / 2 := by
  exact ⟨rfl, by native_decide⟩


-- ════════════════════════════════════════════════════
-- § 8. Bridge to French Fragment
-- ════════════════════════════════════════════════════

/-! The study's `SentType.modalFlavor` assignments are not stipulated in
    isolation — they derive from the fragment entries in
    `Fragments.French.Modals`. These bridge theorems ensure the study
    and fragment stay in sync: changing a fragment entry's flavor list
    will break the corresponding theorem here. -/

open Fragments.French.Modals (devoir pouvoir ilEstPossible)

/-- *Vous devez VP* uses *devoir*, which has deontic as an available
    flavor. The study assigns deontic to `.mustDeclarative`. -/
theorem must_flavor_from_fragment :
    .deontic ∈ devoir.flavors ∧
    SentType.modalFlavor .mustDeclarative = some .deontic := by
  exact ⟨by decide, rfl⟩

/-- *Vous pouvez VP* uses *pouvoir*. The study assigns circumstantial
    to `.canDeclarative` (the default non-epistemic reading in 2nd person
    declaratives — ability/permission). *Pouvoir* has circumstantial
    in its flavor inventory. -/
theorem can_flavor_from_fragment :
    .circumstantial ∈ pouvoir.flavors ∧
    SentType.modalFlavor .canDeclarative = some .circumstantial := by
  exact ⟨by decide, rfl⟩

/-- *Il est possible de VP* uses the impersonal construction. The study
    assigns circumstantial to `.possibleDecl`. -/
theorem possible_flavor_from_fragment :
    .circumstantial ∈ ilEstPossible.flavors ∧
    SentType.modalFlavor .possibleDecl = some .circumstantial := by
  exact ⟨by decide, rfl⟩

/-- The force contrast between *devoir* and *pouvoir* is the structural
    explanation for the Study 2 asymmetry: necessity (obligation) licenses
    directive force more readily than possibility (permission). -/
theorem fragment_force_explains_study2 :
    devoir.force = .necessity ∧ pouvoir.force = .possibility ∧
    study2Must.moveProp > study2Can.moveProp := by
  refine ⟨rfl, rfl, ?_⟩; native_decide

/-- The fragment's force-flavor pair for *devoir* includes deontic
    necessity — the same combination as the imperative speech act. -/
theorem devoir_matches_imperative_speech_act :
    (⟨.necessity, .deontic⟩ : Core.Modality.ForceFlavor) ∈
    devoir.forceFlavors ∧
    primaryFlavor .imperative = .deontic := by
  exact ⟨by decide, rfl⟩


-- ════════════════════════════════════════════════════
-- § 9. Bridge to Preparatory Conditions (@cite{francik-clark-1985})
-- ════════════════════════════════════════════════════

/-! Mechanism 2 (convention of means) IS the questioning of a preparatory
    condition. @cite{francik-clark-1985} show that speakers choose among
    indirect request forms by targeting the specific preparatory condition
    most at risk — the "greatest obstacle to compliance."

    The bridge: `directiveCompatible` (mechanism 1) checks whether the
    modal flavor matches the imperative's deontic semantics. Mechanism 2
    operates on constructions whose flavor does NOT match — circumstantial
    (ability) rather than deontic. These constructions get directive force
    by questioning the addressee's ability, a preparatory condition. -/

open Core.Discourse (PreparatoryCondition)

/-- Mechanism 2 constructions query circumstantial (ability) modality,
    which maps to the `ability` preparatory condition. This is exactly
    the preparatory condition that @cite{francik-clark-1985}'s obstacle
    model identifies as the target of "Can you?" forms. -/
theorem mechanism2_queries_ability_condition :
    SentType.modalFlavor .canYouInterrog = some .circumstantial ∧
    SentType.modalFlavor .possibleInterrog = some .circumstantial ∧
    SentType.isDirectiveCompatible .canYouInterrog = false ∧
    SentType.isDirectiveCompatible .possibleInterrog = false := ⟨rfl, rfl, rfl, rfl⟩

end RuytenbeekEtAl2017
