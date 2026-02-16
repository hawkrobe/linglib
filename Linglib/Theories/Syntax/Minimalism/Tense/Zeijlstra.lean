import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Core.Tense

/-!
# Zeijlstra (2012): SOT as Upward Agree

Zeijlstra's theory: Sequence of Tense is syntactic concord, structurally
parallel to Negative Concord. Subordinate past morphemes carry
uninterpretable [uPAST]; they Agree upward with matrix [iPAST]. The
subordinate verb's past morphology is semantically vacuous -- it is
Agree spell-out, not semantic past.

## Core Mechanisms

1. **Tense feature interpretability**: [iPAST] contributes past semantics;
   [uPAST] is checked by Agree, semantically vacuous
2. **Upward Agree**: the goal c-commands the probe (reverse of standard
   Chomsky 2000 Agree where probe c-commands goal)
3. **SOT as concord**: SOT languages allow [uT] on embedded T; non-SOT
   languages do not, so embedded tense is always interpretable
4. **Parametric variation**: whether a language has SOT = whether it
   allows uninterpretable tense features on embedded T heads

## Derivation Theorems

- Simultaneous reading: [uPAST] is semantically vacuous, so the
  embedded clause is interpreted at matrix event time
- Shifted reading: embedded T has [iPAST] (independent tense, no Agree)
- SOT parameter: SOT languages allow [uT]; non-SOT do not
- SOT is concord: structural parallel with Negative Concord

## Limitations

- Temporal de re: not addressed (syntactic, not semantic mechanism)
- Counterfactual tense: not directly handled
- Relative clause tense: would require extending Agree domain

## References

- Zeijlstra, H. (2012). There is only one way to agree. *The Linguistic
  Review* 29(3): 491--539.
- Chomsky, N. (2000). Minimalist Inquiries.
-/

namespace Minimalism.Tense.Zeijlstra

open Core.Tense
open Core.Reichenbach
open Semantics.Tense
open Minimalism (FeatureVal GramFeature)


-- ════════════════════════════════════════════════════════════════
-- § Tense Feature Interpretability
-- ════════════════════════════════════════════════════════════════

/-- Tense feature interpretability. Following Zeijlstra (2012):
    - Interpretable [iPAST]: contributes past semantics
    - Uninterpretable [uPAST]: checked by Agree, semantically vacuous -/
inductive TenseFeatureStatus where
  /-- [iT] -- semantically active -/
  | interpretable
  /-- [uT] -- checked by Agree, semantically vacuous -/
  | uninterpretable
  deriving DecidableEq, Repr, BEq

/-- A tense head with its feature specification. -/
structure TenseHead where
  /-- The tense value (past/present/future) -/
  tense : GramTense
  /-- Whether this tense feature is interpretable or uninterpretable -/
  status : TenseFeatureStatus
  deriving DecidableEq, Repr, BEq

/-- Is a tense head semantically active? Only interpretable features
    contribute to meaning. -/
def TenseHead.isSemanticallyActive (th : TenseHead) : Bool :=
  th.status == .interpretable


-- ════════════════════════════════════════════════════════════════
-- § Upward Agree
-- ════════════════════════════════════════════════════════════════

/-- Zeijlstra's upward Agree: the goal c-commands the probe.
    Standard Agree (Chomsky 2000): probe c-commands goal.
    Zeijlstra: reverse -- [uF] is valued by a c-commanding [iF].

    This is the key innovation: the c-command direction is reversed.
    The uninterpretable feature (probe) sits low in the structure and
    is valued by a c-commanding interpretable feature (goal). -/
structure UpwardAgree where
  /-- The embedded T with [uT] (probe) -/
  probe : TenseHead
  /-- The matrix T with [iT] (goal) -/
  goal : TenseHead
  /-- The probe carries an uninterpretable feature -/
  probe_uninterpretable : probe.status = .uninterpretable
  /-- The goal carries an interpretable feature -/
  goal_interpretable : goal.status = .interpretable
  /-- The tense values match (both past, both present, etc.) -/
  tense_match : probe.tense = goal.tense
  deriving Repr

/-- Upward Agree makes the probe semantically vacuous: since the probe's
    feature is uninterpretable, it does not contribute to LF interpretation. -/
theorem upwardAgree_probe_vacuous (ua : UpwardAgree) :
    ua.probe.isSemanticallyActive = false := by
  simp only [TenseHead.isSemanticallyActive, ua.probe_uninterpretable]; decide

/-- The goal's tense IS semantically active. -/
theorem upwardAgree_goal_active (ua : UpwardAgree) :
    ua.goal.isSemanticallyActive = true := by
  simp only [TenseHead.isSemanticallyActive, ua.goal_interpretable]; decide


-- ════════════════════════════════════════════════════════════════
-- § SOT Agree Configuration
-- ════════════════════════════════════════════════════════════════

/-- SOT configuration: [iPAST] > [uPAST] > [uPAST]
    (Zeijlstra 2012, ex. 22--23).

    In an SOT language, the matrix T carries [iPAST] (the only
    semantically active past), and all embedded T heads carry [uPAST]
    (semantically vacuous, valued by upward Agree with [iPAST]). -/
structure SOTAgreeConfig where
  /-- Matrix T head with [iPAST] -/
  matrixT : TenseHead
  /-- Embedded T heads with [uPAST] -/
  embeddedTs : List TenseHead
  /-- Matrix T is interpretable -/
  matrix_is_interpretable : matrixT.status = .interpretable
  /-- All embedded T heads are uninterpretable -/
  embedded_all_uninterpretable :
    ∀ t ∈ embeddedTs, t.status = .uninterpretable
  deriving Repr

/-- In an SOT configuration, only the matrix T contributes past semantics.
    All embedded past morphology is concord (semantically vacuous). -/
theorem sotConfig_only_matrix_active (cfg : SOTAgreeConfig) :
    cfg.matrixT.isSemanticallyActive = true ∧
    ∀ t ∈ cfg.embeddedTs, t.isSemanticallyActive = false := by
  constructor
  · simp only [TenseHead.isSemanticallyActive, cfg.matrix_is_interpretable]; decide
  · intro t ht
    simp only [TenseHead.isSemanticallyActive, cfg.embedded_all_uninterpretable t ht]; decide


-- ════════════════════════════════════════════════════════════════
-- § SOT Parameter via Feature Interpretability
-- ════════════════════════════════════════════════════════════════

/-- Whether a language allows uninterpretable tense on embedded T.
    SOT languages (English): yes → simultaneous reading available.
    Non-SOT languages (Japanese): no → all tense is interpretable. -/
def allowsUninterpretableTense (param : SOTParameter) : Bool :=
  match param with
  | .relative => true   -- SOT: [uT] allowed on embedded T
  | .absolute => false  -- non-SOT: all tense is [iT]

/-- SOT languages allow uninterpretable tense. -/
theorem sot_allows_uT :
    allowsUninterpretableTense .relative = true := rfl

/-- Non-SOT languages do not allow uninterpretable tense. -/
theorem nonSOT_no_uT :
    allowsUninterpretableTense .absolute = false := rfl


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Zeijlstra derives the simultaneous reading:
    [uPAST] is semantically vacuous → the embedded clause has no
    independent past semantics → it is interpreted at the matrix
    event time → R' = P' (simultaneous).

    Concretely: the embedded frame with a vacuous [uPAST] has
    R' = P' = matrix E, which is `simultaneousFrame`. -/
theorem zeijlstra_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time)
    (embeddedT : TenseHead)
    (h_u : embeddedT.status = .uninterpretable) :
    embeddedT.isSemanticallyActive = false ∧
    (simultaneousFrame matrixFrame embeddedE).isPresent := by
  constructor
  · simp only [TenseHead.isSemanticallyActive, h_u]; decide
  · rfl

/-- Zeijlstra derives the shifted reading:
    When embedded T has [iPAST] (independent tense, no Agree),
    it contributes genuine past semantics → R' < P' (shifted). -/
theorem zeijlstra_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time)
    (embeddedT : TenseHead)
    (h_i : embeddedT.status = .interpretable)
    (h_past : embeddedT.tense = .past)
    (h_shifted : embeddedR < matrixFrame.eventTime) :
    embeddedT.isSemanticallyActive = true ∧
    (shiftedFrame matrixFrame embeddedR embeddedE).isPast := by
  constructor
  · simp only [TenseHead.isSemanticallyActive, h_i]; decide
  · simp only [shiftedFrame, ReichenbachFrame.isPast]
    exact h_shifted

/-- SOT is parametric: SOT languages allow [uT] on embedded T;
    non-SOT languages do not. This bridges Zeijlstra's feature-based
    account to the SOTParameter type. -/
theorem zeijlstra_SOT_parametric :
    (allowsUninterpretableTense .relative = true) ∧
    (allowsUninterpretableTense .absolute = false) := ⟨rfl, rfl⟩

/-- Upward Agree explains the directionality: embedded tense depends on
    matrix (not reverse) because [uPAST] must be c-commanded by [iPAST].
    The c-command relation is asymmetric: matrix c-commands embedded. -/
theorem zeijlstra_upward_direction (ua : UpwardAgree) :
    ua.goal.isSemanticallyActive = true ∧
    ua.probe.isSemanticallyActive = false :=
  ⟨upwardAgree_goal_active ua, upwardAgree_probe_vacuous ua⟩


-- ════════════════════════════════════════════════════════════════
-- § SOT–Negative Concord Parallel
-- ════════════════════════════════════════════════════════════════

/-- The structural parallel between SOT and Negative Concord.

    Just as Negative Concord languages have [uNEG] on n-words that
    Agree with [iNEG] on the sentential negation, SOT languages have
    [uPAST] on embedded T heads that Agree with [iPAST] on matrix T.

    Both involve:
    - One interpretable feature (semantically active)
    - Multiple uninterpretable copies (concord, semantically vacuous)
    - Upward Agree as the licensing mechanism -/
structure ConcordParallel where
  /-- The interpretable feature bearer -/
  iFeatureBearer : String
  /-- The uninterpretable concord items -/
  uFeatureBearers : List String
  /-- The domain -/
  domain : String
  deriving Repr

/-- SOT as tense concord. -/
def sotAsConcord : ConcordParallel where
  iFeatureBearer := "matrix T [iPAST]"
  uFeatureBearers := ["embedded T [uPAST]"]
  domain := "tense"

/-- Negative Concord parallel. -/
def negativeConcord : ConcordParallel where
  iFeatureBearer := "sentential negation [iNEG]"
  uFeatureBearers := ["n-word [uNEG]"]
  domain := "negation"


-- ════════════════════════════════════════════════════════════════
-- § Bridge: TenseHead ↔ Minimalism Agree Infrastructure
-- ════════════════════════════════════════════════════════════════

/-- Map a TenseHead to the Minimalism Agree infrastructure.
    An interpretable [iPAST] maps to `GramFeature.valued (.tense true)`;
    an uninterpretable [uPAST] maps to `GramFeature.unvalued (.tense true)`. -/
def TenseHead.toGramFeature (th : TenseHead) : GramFeature :=
  match th.status with
  | .interpretable => .valued (.tense true)
  | .uninterpretable => .unvalued (.tense true)

/-- Interpretable tense heads map to valued features. -/
theorem zeijlstra_bridge_interpretable (th : TenseHead)
    (h : th.status = .interpretable) :
    th.toGramFeature = .valued (.tense true) := by
  simp [TenseHead.toGramFeature, h]

/-- Uninterpretable tense heads map to unvalued features. -/
theorem zeijlstra_bridge_uninterpretable (th : TenseHead)
    (h : th.status = .uninterpretable) :
    th.toGramFeature = .unvalued (.tense true) := by
  simp [TenseHead.toGramFeature, h]

/-- Agree-valued [uPAST] produces the same Reichenbach frame as
    `simultaneousFrame`: the embedded tense contributes no independent
    temporal ordering, so R' = P' = matrix E. -/
theorem zeijlstra_simultaneousFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).referenceTime =
    (simultaneousFrame matrixFrame embeddedE).perspectiveTime := rfl


-- ════════════════════════════════════════════════════════════════
-- § Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Zeijlstra (2012) identity card. -/
def Zeijlstra : TenseTheory where
  name := "Zeijlstra 2012"
  citation := "Zeijlstra, H. (2012). There is only one way to agree. The Linguistic Review 29(3): 491-539."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := false
  hasAgreeBasedSOT := true
  simultaneousMechanism := "uninterpretable [uPAST] Agrees upward with [iPAST]"


end Minimalism.Tense.Zeijlstra
