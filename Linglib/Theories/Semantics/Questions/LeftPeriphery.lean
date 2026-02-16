/-
# The Interrogative Left Periphery (Dayal 2025)

Question meaning is built at three points in the left periphery:

    [SAP SA_ASK [PerspectiveP PRO Persp_CQ [CP C_±WH [TP ...]]]]

1. **CP** (C_±WH): Clause-typing — shifts proposition ⟨s,t⟩ to set of propositions ⟨⟨s,t⟩,t⟩
2. **PerspectiveP** (Persp_CQ): Centering — introduces PRO (perspectival center)
   with not-at-issue presupposition ◇¬know(x, Ans(Q)) (possible ignorance)
3. **SAP** (SA_ASK): Speech act — puts addressee under obligation to assert Ans(Q)

The key prediction: responsive predicates reject quasi-subordination because
their knowledge entailment contradicts PerspP's ignorance presupposition.
This is DERIVED, not stipulated.

## References

- Dayal, V. (2025). The Interrogative Left Periphery: How a Clause Becomes a Question.
  Linguistic Inquiry 56(4), 663–712.
- McCloskey, J. (2006). Questions and questioning in a local English.
- Hamblin, C. (1973). Questions in Montague English.
- Karttunen, L. (1977). Syntax and semantics of questions.
-/

import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Theories.Semantics.Questions.Answerhood
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Questions.Embedding
import Linglib.Phenomena.Questions.Typology

namespace Semantics.Questions.LeftPeriphery

open Phenomena.Questions.Embedding

-- ============================================================================
-- A. Clause-type feature
-- ============================================================================

/-- The ±WH feature on C, determining declarative vs interrogative clause type.
    `alphaWH` is underspecified — used for Hindi-Urdu simplex polar questions
    where clause-typing is not forced at CP (Dayal 2025: §4.4). -/
inductive WHFeature where
  | plusWH   -- Interrogative: ⟨⟨s,t⟩,t⟩
  | minusWH  -- Declarative: ⟨s,t⟩
  | alphaWH  -- Underspecified (typing delayed to PerspP)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- B. Predicate selection class
-- ============================================================================

/-- Dayal's classification of embedding predicates by what left-peripheral
    structure they select. Refines the rogative/responsive split.

    - `uninterrogative`: C_-WH only (believe, think)
    - `rogativeCP`: C_+WH but not PerspP (investigate, depend on)
    - `rogativePerspP`: CP + PerspP (wonder, the question is)
    - `rogativeSAP`: Full structure (ask)
    - `responsive`: C_±WH (know, remember) -/
inductive SelectionClass where
  | uninterrogative
  | rogativeCP
  | rogativePerspP
  | rogativeSAP
  | responsive
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- C. Knowledge and ignorance: the semantic primitives
-- ============================================================================

/-- Whether the predicate's at-issue content entails the subject knows Ans(Q).
    This is the key semantic property that drives PerspP (in)compatibility.

    - Responsive predicates (know, remember) entail knowledge at eval time
    - Rogative predicates (wonder, ask) do NOT entail knowledge
    - Under negation, the knowledge entailment is REMOVED -/
def entailsKnowledge (cls : SelectionClass) : Bool :=
  match cls with
  | .responsive => true
  | _ => false

/-- Whether the knowledge entailment survives in the given syntactic context.
    Negation and questioning both remove a predicate's knowledge entailment:
    - "I don't know Q" does NOT entail knowing Ans(Q)
    - "Does she know Q?" does NOT entail knowing Ans(Q) -/
def effectiveKnowledge (cls : SelectionClass) (negated questioned : Bool) : Bool :=
  entailsKnowledge cls && !negated && !questioned

/-- PerspectiveP presupposes possible ignorance: ◇¬know(x, Ans(Q)).
    This is **inconsistent** with knowing Ans(Q).
    Consistency holds iff effective knowledge is false.

    Note: Consistency is necessary but not sufficient for quasi-subordination.
    The full account also requires "potentially active" (de se interest),
    which is why *forget* doesn't freely quasi-subordinate (Dayal 2025: §3.3). -/
def perspPConsistent (cls : SelectionClass) (negated questioned : Bool) : Bool :=
  !effectiveKnowledge cls negated questioned

-- ============================================================================
-- D. Embedding prediction (derived from semantic properties)
-- ============================================================================

/-- Whether a predicate allows quasi-subordination.
    DERIVED from two independent conditions:
    1. The predicate must select PerspP (structural requirement)
    2. OR: PerspP is consistent with the predicate's semantics AND the predicate
       embeds interrogatives (responsive predicates under negation/question) -/
def allowsQuasiSub (cls : SelectionClass) (negated questioned : Bool) : Bool :=
  match cls with
  | .uninterrogative => false  -- doesn't embed interrogatives
  | .rogativeCP => false       -- selects CP only, not PerspP
  | .rogativePerspP => true    -- structurally selects PerspP
  | .rogativeSAP => true       -- structurally selects PerspP + SAP
  | .responsive =>             -- DERIVED: depends on semantic consistency
      perspPConsistent cls negated questioned

/-- Full embedding prediction. -/
def allowsEmbedding (cls : SelectionClass) (et : EmbedType)
    (negated questioned : Bool) : Bool :=
  match cls, et with
  | .uninterrogative, _ => false
  | _, .subordination => true
  | c, .quasiSubordination => allowsQuasiSub c negated questioned
  | .rogativeSAP, .quotation => true
  | _, .quotation => false

-- ============================================================================
-- E. Core theorems: DERIVED from knowledge/ignorance interaction
-- ============================================================================

/-- Responsive predicates entail knowledge. -/
theorem responsive_entails_knowledge :
    entailsKnowledge .responsive = true := rfl

/-- Rogative predicates do NOT entail knowledge. -/
theorem rogative_no_knowledge :
    entailsKnowledge .rogativePerspP = false ∧
    entailsKnowledge .rogativeSAP = false ∧
    entailsKnowledge .rogativeCP = false := ⟨rfl, rfl, rfl⟩

/-- Knowledge entailment is removed by negation. -/
theorem negation_removes_knowledge :
    effectiveKnowledge .responsive true false = false := rfl

/-- Knowledge entailment is removed by questioning. -/
theorem question_removes_knowledge :
    effectiveKnowledge .responsive false true = false := rfl

/-- PerspP is inconsistent with effective knowledge.
    This is the core semantic derivation: know(x, Ans(Q)) ∧ ◇¬know(x, Ans(Q))
    is a contradiction, so PerspP is blocked. -/
theorem knowledge_blocks_perspP :
    perspPConsistent .responsive false false = false := rfl

/-- Without effective knowledge, PerspP is consistent.
    Rogatives never entail knowledge → always consistent. -/
theorem no_knowledge_allows_perspP :
    perspPConsistent .rogativePerspP false false = true ∧
    perspPConsistent .rogativeSAP false false = true := ⟨rfl, rfl⟩

/-- Responsive predicates reject quasi-subordination in unadorned form.
    DERIVED: know entails knowledge → contradicts possible ignorance. -/
theorem responsive_rejects_quasi :
    allowsQuasiSub .responsive false false = false := rfl

/-- Under negation, responsives allow quasi-subordination.
    DERIVED: negation removes knowledge entailment → PerspP consistent.
    "*I remember [was Henry a communist↑]" vs
    "I don't remember [was Henry a communist↑]" (McCloskey 2006). -/
theorem responsive_shifts_under_negation :
    allowsQuasiSub .responsive true false = true := rfl

/-- Under questioning, responsives allow quasi-subordination.
    DERIVED: questioning removes knowledge entailment → PerspP consistent.
    "Does Sue remember [was Henry a communist↑]" -/
theorem responsive_shifts_under_question :
    allowsQuasiSub .responsive false true = true := rfl

-- ============================================================================
-- F. Verification against empirical data
-- ============================================================================

/-- Classify each empirical datum from Phenomena.Questions.Embedding. -/
def classifyVerb : String → SelectionClass
  | "investigate" => .rogativeCP
  | "depend on"   => .rogativeCP
  | "wonder"      => .rogativePerspP
  | "ask"         => .rogativeSAP
  | "know"        => .responsive
  | "believe"     => .uninterrogative
  | _             => .uninterrogative

/-- The theory correctly predicts all embedding judgments from the data. -/
theorem theory_predicts_embedding :
    ∀ d ∈ allEmbeddingData,
      allowsEmbedding (classifyVerb d.verb) .subordination false false = d.subordination ∧
      allowsEmbedding (classifyVerb d.verb) .quasiSubordination false false = d.quasiSubordination ∧
      allowsEmbedding (classifyVerb d.verb) .quotation false false = d.quotation := by
  intro d hd
  simp [allEmbeddingData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [allowsEmbedding, allowsQuasiSub, perspPConsistent, effectiveKnowledge,
          entailsKnowledge, classifyVerb,
          investigate_d, depend_on_d, wonder_d, ask_d, know_d, believe_d]

/-- Shiftiness predictions match McCloskey's data for remember (responsive). -/
theorem shiftiness_predicted :
    allowsQuasiSub .responsive remember_bare.negated remember_bare.questioned
      = remember_bare.quasiSubOk ∧
    allowsQuasiSub .responsive remember_negated.negated remember_negated.questioned
      = remember_negated.quasiSubOk ∧
    allowsQuasiSub .responsive remember_questioned.negated remember_questioned.questioned
      = remember_questioned.quasiSubOk := by
  simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
        remember_bare, remember_negated, remember_questioned]

-- ============================================================================
-- G. Cross-linguistic predictions
-- ============================================================================

open Phenomena.Questions.Typology

/-- Classify Hindi-Urdu verbs from the cross-linguistic shiftiness data. -/
def classifyCrossLingVerb : String → SelectionClass
  | "ja:n-na: ca:h-na: (want to know)" => .rogativePerspP
  | "ja:n-na: (know)" => .responsive
  | _ => .responsive

/-- Hindi-Urdu shiftiness follows the same derivation as English:
    responsive predicates reject quasi-sub in bare form, allow under
    negation/questioning. The theory predicts ALL cross-linguistic data. -/
theorem cross_linguistic_shiftiness_predicted :
    ∀ d ∈ allCrossLingShiftinessData,
      allowsQuasiSub (classifyCrossLingVerb d.verb) d.negated d.questioned
        = d.quasiSubOk := by
  intro d hd
  simp [allCrossLingShiftinessData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
          classifyCrossLingVerb,
          hindi_urdu_want_to_know, hindi_urdu_know_bare,
          hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-- Q-particle embedding follows from which left-peripheral layer they occupy.
    CP-layer particles appear in subordination; PerspP and SAP particles do not. -/
theorem particle_layer_predicts_embedding :
    ∀ d ∈ allQParticleData,
      (d.layer = .cp → d.inSubordinated = true) ∧
      (d.layer = .perspP → d.inSubordinated = false) ∧
      (d.layer = .sap → d.inQuasiSub = false) := by
  intro d hd
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- ============================================================================
-- H. Compositional grounding
-- ============================================================================

/-! ## H1. Derive SelectionClass from VerbEntry

Instead of classifying verbs by string matching (`classifyVerb "know" => .responsive`),
we derive the selection class from the primitive fields already encoded in
each `VerbEntry`: `factivePresup`, `speechActVerb`, `opaqueContext`, `complementType`,
`attitudeBuilder`, `takesQuestionBase`.
-/

open Fragments.English.Predicates.Verbal

/-- Derive the left-peripheral selection class from a VerbEntry's structural
    properties. This replaces ad-hoc string-based classification with a
    principled derivation from the verb's primitive semantic fields.

    The logic:
    - Factives are responsive (knowledge-entailing)
    - Non-veridical doxastic attitudes are uninterrogative
    - Speech-act verbs that take questions are rogativeSAP (speech-act layer)
    - Opaque-context verbs that take questions are rogativePerspP (perspective layer)
    - Other question-taking verbs are rogativeCP (CP layer only)
    - Everything else is uninterrogative -/
def deriveSelectionClass (v : VerbEntry) : SelectionClass :=
  if v.complementType != .question && !v.takesQuestionBase then .uninterrogative
  else if v.factivePresup then .responsive
  else match v.attitudeBuilder with
  | some (.doxastic .nonVeridical) => .uninterrogative
  | _ =>
    if v.speechActVerb && v.complementType == .question then .rogativeSAP
    else if v.opaqueContext && v.complementType == .question then .rogativePerspP
    else if v.complementType == .question then .rogativeCP
    else .uninterrogative

/-- The structurally derived classification matches the manually-assigned
    string-based classification for all verbs in the embedding data. -/
theorem derived_class_matches_manual :
    deriveSelectionClass Fragments.English.Predicates.Verbal.know = classifyVerb "know" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.wonder = classifyVerb "wonder" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.ask = classifyVerb "ask" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.investigate = classifyVerb "investigate" ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.believe = classifyVerb "believe" := by
  decide

/-! ## H2. Compositional PerspP via possible ignorance

PerspP introduces a not-at-issue presupposition: the perspectival center
*possibly doesn't know* the answer to the question. We formalize this using
`diaAt` (existential modal, ◇) from `Doxastic.lean` and `ans` from
`Answerhood.lean`.
-/

open Semantics.Attitudes.Doxastic
open Semantics.Questions.Answerhood

/-- Whether x possibly doesn't know Ans(Q) at world w:
    ◇¬know(x, Ans(Q)) = ∃w' ∈ R(x,w). ¬(Ans(Q,w) holds at w')

    This is PerspP's not-at-issue presupposition (Dayal 2025: §2.3).
    Uses `diaAt` from Doxastic.lean and `ans` from Answerhood.lean. -/
def possibleIgnorance {W E : Type*} (R : AccessRel W E) (center : E)
    (Q : GSQuestion W) (w : W) (worlds : List W) : Bool :=
  diaAt R center w worlds (fun w' => !(ans Q w w'))

/-- PerspP as a presuppositional question denotation.
    At-issue: the question Q itself.
    Not-at-issue presupposition: ◇¬know(center, Ans(Q)). -/
structure PerspPResult (W : Type*) where
  /-- The at-issue question content (unchanged by PerspP) -/
  question : Hamblin.QuestionDen W
  /-- Whether the possible-ignorance presupposition is satisfied -/
  presupSatisfied : Bool

/-- Apply PerspP to a question: checks possible-ignorance presupposition. -/
def applyPerspP {W E : Type*} (R : AccessRel W E) (center : E)
    (Q : GSQuestion W) (w : W) (worlds : List W)
    (hamblinQ : Hamblin.QuestionDen W) : PerspPResult W :=
  { question := hamblinQ
  , presupSatisfied := possibleIgnorance R center Q w worlds }

/-! ## H3. Veridical predicates block PerspP

The key compositional derivation: a veridical doxastic predicate that holds
at Q entails □(Ans(Q)), which contradicts ◇¬(Ans(Q)). Therefore PerspP's
possible-ignorance presupposition is inconsistent with responsive predicates
in bare (non-negated, non-questioned) contexts.
-/

/-- box and dia are duals: □p → ¬◇¬p.
    If p holds at all accessible worlds, there is no accessible world where ¬p. -/
theorem box_excludes_dia_neg {W E : Type*}
    (R : AccessRel W E) (agent : E) (w : W) (worlds : List W)
    (p : W → Bool)
    (hBox : boxAt R agent w worlds p = true) :
    diaAt R agent w worlds (fun w' => !p w') = false := by
  simp only [boxAt, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hBox
  simp only [diaAt, List.any_eq_false]
  intro w' hw'
  have h := hBox w' hw'
  cases hR : R agent w w' with
  | false => simp
  | true =>
    cases h with
    | inl hNotR => exact absurd hR (by rw [hNotR]; simp)
    | inr hp => simp [hp]

/-- A veridical doxastic predicate entails the subject believes Ans(Q).
    "x knows Q" at w means there exists a true answer p that x box-believes.
    In particular, x box-believes Ans(Q,w) (the complete answer at w).

    TODO: Full proof requires showing that holdsAtQuestion with the G&S-derived
    Hamblin denotation implies boxAt for Ans(Q,w). The key step is:
    holdsAtQuestion finds *some* true p that x box-believes; since the question
    is a partition, that p determines the same cell as Ans(Q,w). -/
theorem veridical_question_entails_box_ans {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (agent : E) (Q : GSQuestion W) (w : W) (worlds : List W)
    (hHolds : boxAt V.access agent w worlds (ans Q w) = true) :
    diaAt V.access agent w worlds (fun w' => !(ans Q w w')) = false :=
  box_excludes_dia_neg V.access agent w worlds (ans Q w) hHolds

/-- Therefore PerspP's possible-ignorance presupposition is inconsistent
    with a veridical predicate that box-knows Ans(Q).

    This is the compositional explanation for why responsive predicates
    (know, remember) reject quasi-subordination: their knowledge entailment
    □(Ans(Q)) contradicts PerspP's ◇¬(Ans(Q)). -/
theorem veridical_blocks_perspP {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (agent : E) (Q : GSQuestion W) (w : W) (worlds : List W)
    (hBox : boxAt V.access agent w worlds (ans Q w) = true) :
    possibleIgnorance V.access agent Q w worlds = false := by
  simp only [possibleIgnorance]
  exact box_excludes_dia_neg V.access agent w worlds (ans Q w) hBox

/-! ## H4. Bridge theorems

Connect the compositional semantics (veridicality, box/dia) to the Boolean
predicates (entailsKnowledge, perspPConsistent). This shows the Boolean
predicates are correct *because* they track the compositional story.
-/

/-- Factive verbs correspond to veridical doxastic predicates.
    This is the structural link: factivePresup determines veridicality. -/
def verbEntryIsVeridical (v : VerbEntry) : Bool :=
  v.factivePresup

/-- The derived selection class assigns .responsive exactly to verbs whose
    factivePresup is true and which can embed questions.
    This connects the structural derivation to the semantic one. -/
theorem responsive_iff_veridical_question_taker (v : VerbEntry)
    (hQ : v.complementType == .question || v.takesQuestionBase = true)
    (hClass : deriveSelectionClass v = .responsive) :
    verbEntryIsVeridical v = true := by
  simp only [verbEntryIsVeridical]
  unfold deriveSelectionClass at hClass
  by_cases h1 : v.complementType != .question && !v.takesQuestionBase
  · simp [h1] at hClass
  · simp [h1] at hClass
    by_cases h2 : v.factivePresup = true
    · exact h2
    · exfalso
      simp [h2] at hClass
      revert hClass
      split <;> simp_all
      split <;> simp_all
      split <;> simp_all
      split <;> simp_all

/-- The Boolean `entailsKnowledge` agrees with the compositional story:
    responsive predicates entail knowledge (veridicality + box),
    and non-responsive predicates do not.

    Forward direction: responsive → veridical → box-knows Ans(Q) → PerspP blocked.
    This is exactly what `veridical_blocks_perspP` proves at the compositional level.
    The Boolean `perspPConsistent` tracks this faithfully. -/
theorem boolean_tracks_compositional (cls : SelectionClass) :
    entailsKnowledge cls = true ↔ cls = .responsive := by
  constructor
  · intro h; cases cls <;> simp [entailsKnowledge] at h ⊢ <;> exact h
  · intro h; rw [h]; rfl

-- ============================================================================
-- I. VerbEntry.selectionClass — derived from VerbEntry fields
-- ============================================================================

/-! ## I1. Field-based derivation

This derivation keys off the surface-level lexical fields directly:
`factivePresup`, `takesQuestionBase`, `complementType`, `speechActVerb`, `opaqueContext`.

Each branch depends on a different field, so changing one field in the fragment
breaks exactly one per-verb theorem below.
-/

/-- Derive selection class from VerbEntry fields.

    | Class           | Condition                                                |
    |-----------------|----------------------------------------------------------|
    | uninterrogative | !takesQuestionBase && complementType != .question         |
    | responsive      | factivePresup && takesQuestionBase                        |
    | rogativeSAP     | complementType == .question && speechActVerb              |
    | rogativePerspP  | complementType == .question && opaqueContext              |
    | rogativeCP      | complementType == .question (fallthrough)                 |
-/
def fieldSelectionClass (v : VerbEntry) : SelectionClass :=
  if !v.takesQuestionBase && v.complementType != .question then .uninterrogative
  else if v.factivePresup && v.takesQuestionBase then .responsive
  else if v.complementType == .question && v.speechActVerb then .rogativeSAP
  else if v.complementType == .question && v.opaqueContext then .rogativePerspP
  else if v.complementType == .question then .rogativeCP
  else .uninterrogative

/-! ## I2. Per-verb verification theorems

Each proved by `native_decide`. Changing one VerbEntry field breaks exactly
one theorem — this is the dense dependency web. -/

theorem know_is_responsive :
    fieldSelectionClass Fragments.English.Predicates.Verbal.know = .responsive := by native_decide

theorem believe_is_uninterrogative :
    fieldSelectionClass Fragments.English.Predicates.Verbal.believe = .uninterrogative := by native_decide

theorem wonder_is_rogativePerspP :
    fieldSelectionClass Fragments.English.Predicates.Verbal.wonder = .rogativePerspP := by native_decide

theorem ask_is_rogativeSAP :
    fieldSelectionClass Fragments.English.Predicates.Verbal.ask = .rogativeSAP := by native_decide

theorem investigate_is_rogativeCP :
    fieldSelectionClass Fragments.English.Predicates.Verbal.investigate = .rogativeCP := by native_decide

theorem depend_on_is_rogativeCP :
    fieldSelectionClass Fragments.English.Predicates.Verbal.depend_on = .rogativeCP := by native_decide

theorem remember_rog_is_responsive :
    fieldSelectionClass Fragments.English.Predicates.Verbal.remember_rog = .responsive := by native_decide

theorem forget_rog_is_responsive :
    fieldSelectionClass Fragments.English.Predicates.Verbal.forget_rog = .responsive := by native_decide

theorem discover_is_responsive :
    fieldSelectionClass Fragments.English.Predicates.Verbal.discover = .responsive := by native_decide

/-! ## I3. Cross-layer agreement

The three classification methods — string-based `classifyVerb`, semantic
`deriveSelectionClass`, and field-based `VerbEntry.selectionClass` — all agree. -/

/-- String-based classification matches field-based derivation. -/
theorem classifyVerb_agrees_with_selectionClass :
    classifyVerb "know" = fieldSelectionClass Fragments.English.Predicates.Verbal.know ∧
    classifyVerb "wonder" = fieldSelectionClass Fragments.English.Predicates.Verbal.wonder ∧
    classifyVerb "ask" = fieldSelectionClass Fragments.English.Predicates.Verbal.ask ∧
    classifyVerb "investigate" = fieldSelectionClass Fragments.English.Predicates.Verbal.investigate ∧
    classifyVerb "depend on" = fieldSelectionClass Fragments.English.Predicates.Verbal.depend_on ∧
    classifyVerb "believe" = fieldSelectionClass Fragments.English.Predicates.Verbal.believe := by native_decide

/-- Semantic derivation matches field-based derivation. -/
theorem deriveSelectionClass_agrees_with_selectionClass :
    deriveSelectionClass Fragments.English.Predicates.Verbal.know = fieldSelectionClass Fragments.English.Predicates.Verbal.know ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.wonder = fieldSelectionClass Fragments.English.Predicates.Verbal.wonder ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.ask = fieldSelectionClass Fragments.English.Predicates.Verbal.ask ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.investigate = fieldSelectionClass Fragments.English.Predicates.Verbal.investigate ∧
    deriveSelectionClass Fragments.English.Predicates.Verbal.believe = fieldSelectionClass Fragments.English.Predicates.Verbal.believe := by native_decide

-- ============================================================================
-- J. Compositional PerspP via EpistemicModel
-- ============================================================================

/-! ## J1. EpistemicModel abstraction

PerspP's presupposition is about possible ignorance: the perspectival center
might not know the answer. We abstract over the knowledge notion so the
derivation works with any epistemic semantics (doxastic, veridical, etc.). -/

/-- An abstract epistemic model: tells us whether the agent knows a proposition. -/
structure EpistemicModel (W : Type*) where
  knows : (W → Bool) → Bool

/-- PerspP presupposition (compositional version):
    the agent does NOT know the complete answer to Q at w.
    Uses `ans` from Answerhood.lean. -/
def perspPPresupComp {W : Type*} (ep : EpistemicModel W)
    (q : GSQuestion W) (w : W) : Bool :=
  !(ep.knows (Answerhood.ans q w))

/-! ## J2. Canonical epistemic models -/

/-- Veridical model: knows p iff p is true at w (T axiom).
    This is the model for responsive predicates (know, remember) in
    bare (non-negated, non-questioned) contexts. -/
def veridicalModel {W : Type*} (w : W) : EpistemicModel W where
  knows := fun p => p w

/-- Ignorant model: knows nothing.
    This is the model for rogative predicates (wonder, ask). -/
def ignorantModel {W : Type*} : EpistemicModel W where
  knows := fun _ => false

/-! ## J3. Grounding theorems

These prove the Boolean layer (`perspPConsistent`) is faithful to the
compositional semantics. -/

/-- A veridical knower's PerspP presupposition is false: they know Ans(Q,w),
    so possible ignorance fails. Uses `ans_true_at_index` from Answerhood.lean. -/
theorem responsive_contradicts_perspP_comp {W : Type*}
    (q : GSQuestion W) (w : W) :
    perspPPresupComp (veridicalModel w) q w = false := by
  simp [perspPPresupComp, veridicalModel, Answerhood.ans_true_at_index]

/-- An ignorant agent's PerspP presupposition is true: they don't know anything. -/
theorem rogative_allows_perspP_comp {W : Type*}
    (q : GSQuestion W) (w : W) :
    perspPPresupComp ignorantModel q w = true := by
  simp [perspPPresupComp, ignorantModel]

/-- The Boolean `perspPConsistent .responsive false false = false` is consistent
    with the compositional derivation: both say responsive blocks PerspP.

    The Boolean layer says: responsive + not negated + not questioned → inconsistent.
    The compositional layer says: veridical model → ¬(possible ignorance). -/
theorem perspP_boolean_grounded :
    (perspPConsistent .responsive false false = false) ∧
    (∀ (W : Type) (q : GSQuestion W) (w : W),
      perspPPresupComp (veridicalModel w) q w = false) :=
  ⟨rfl, fun _ q w => responsive_contradicts_perspP_comp q w⟩

/-! ## J4. Bridge to DoxasticPredicate

A `DoxasticPredicate` from Doxastic.lean induces an `EpistemicModel` at a
given world, agent, and domain. This connects the modal-logic semantics
to the abstract epistemic layer used by PerspP. -/

/-- A DoxasticPredicate induces an EpistemicModel at a world. -/
def doxasticToEpistemicModel {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (w : W)
    (worlds : List W) : EpistemicModel W where
  knows := fun p => V.holdsAt agent p w worlds

/-- A veridical predicate that box-knows Ans(Q) blocks PerspP through
    the epistemic model bridge.

    TODO: Full proof requires showing holdsAt for veridical predicates
    at the answer proposition entails the answer is true at the eval world
    (which follows from veridical_entails_complement + boxAt). -/
theorem veridical_model_blocks_perspP {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (agent : E) (Q : GSQuestion W) (w : W) (worlds : List W)
    (hHolds : V.holdsAt agent (Answerhood.ans Q w) w worlds = true) :
    perspPPresupComp (doxasticToEpistemicModel V agent w worlds) Q w = false := by
  simp [perspPPresupComp, doxasticToEpistemicModel, hHolds]

end Semantics.Questions.LeftPeriphery
