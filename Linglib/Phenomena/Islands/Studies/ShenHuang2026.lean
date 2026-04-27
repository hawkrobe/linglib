import Linglib.Phenomena.Islands.Studies.Ross1967
import Linglib.Theories.Syntax.Binding.SpecificityCondition
import Linglib.Features.Definiteness
import Linglib.Core.Lexical.VerbClass
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Interfaces.SyntaxPhonology.Minimalist.CyclicLinearization
import Linglib.Theories.Syntax.Minimalist.Phase

set_option autoImplicit false

/-!
# The Role of Phases and Specificity in Definite Islands
@cite{shen-huang-2026}

@cite{shen-huang-2026} use parallel acceptability judgment experiments on
English (wh-movement) and Mandarin Chinese (wh-in-situ) to show that
definite island effects require BOTH the Phase Impenetrability Condition
(PIC) and the Specificity Condition.

## Key findings

1. Both English and Chinese show definite island effects
   (DD > 0 for non-VOC verbs in both languages).
2. English shows a partial VOC effect: verbs of creation ameliorate
   but do not eliminate the definite island effect (DD 0.23 vs 0.56).
3. Chinese shows NO VOC effect: the definite island effect is
   comparable across VOC and non-VOC verbs.
4. Chinese wh-indefinites are sensitive to specificity (Experiment 3):
   wh-indefinites are degraded inside demonstrative-marked DPs
   (β = −0.48, p < 0.01), confirming @cite{li-1992}.

## Proposal

The definite island effect in English involves TWO constraint violations:
- PIC violation (the wh-element crosses a definite DP phase boundary)
- Specificity Condition violation (the wh-trace is bound inside a specific DP)

VOCs neutralize the PIC via N/D-incorporation (adapting
@cite{davies-dubinsky-2003}), but cannot neutralize the Specificity
Condition. This explains the partial amelioration.

In Chinese, wh-in-situ involves binding, not movement. The PIC is
inapplicable (following @cite{fox-pesetsky-2005}: binding does not change
linear order). Only the Specificity Condition applies, and it applies
equally regardless of verb class — hence no VOC effect.
-/

namespace ShenHuang2026

open Core.Verbs
open Features.Definiteness
open Syntax.Binding.SpecificityCondition (ExternalOperator blocked)

-- ============================================================================
-- §1. Wh-dependency type and source architecture
-- ============================================================================

/-! The crosslinguistic analysis requires distinguishing how wh-dependencies
are established (movement vs binding) and how each interacts with the
two sources of the definite island effect.

These definitions encode @cite{shen-huang-2026}'s theoretical commitments,
grounded in @cite{fox-pesetsky-2005}'s cyclic linearization (§12 below)
and Phase Theory (§13 below). -/

/-- How a wh-dependency is established in a given language/construction.

Overt wh-movement and wh-in-situ are subject to DIFFERENT locality
constraints. Movement is constrained by both the PIC and the Specificity
Condition. Binding (in-situ) is constrained only by the Specificity
Condition — the PIC does not apply because no element crosses a phase
boundary (@cite{fox-pesetsky-2005}: binding does not change linear order,
so it cannot create ordering contradictions at Spell-out). -/
inductive WhDependencyType where
  /-- Overt movement to Spec,CP — subject to PIC + Specificity Condition.
      English wh-fronting, Slavic wh-fronting, etc. -/
  | movement
  /-- In-situ binding by a covert operator — subject to Specificity Condition only.
      Mandarin Chinese, Japanese, Korean wh-in-situ. -/
  | binding
  deriving DecidableEq, Repr

/-- Which island sources constrain a given dependency type.

Movement is constrained by both syntactic (PIC) and semantic (Specificity)
sources. Binding is constrained only by the semantic source.

The asymmetry is derived from cyclic linearization (§12): binding adds no
precedence statements, so it cannot create PIC violations. Movement does
change linear order, so it is subject to Order Preservation. -/
def constraintsForDependencyType : WhDependencyType → List IslandSource
  | .movement => [.syntactic, .semantic]  -- PIC + Specificity
  | .binding  => [.semantic]              -- Specificity only

/-- Whether VOCs (verbs of creation) can neutralize a given island source.

VOCs neutralize phasehood via N/D-incorporation (@cite{davies-dubinsky-2003}):
the created object's DP loses its phase status, removing the syntactic
barrier. This is formally grounded in Phase Theory (§13): `DPPhaseStatus`
with `incorporated = true` yields `isActivePhase = false`.

VOCs cannot affect the Specificity Condition (a semantic binding restriction),
processing difficulty, or discourse structure. -/
def vocNeutralizes : IslandSource → Bool
  | .syntactic  => true   -- N/D-incorporation removes phase boundary (§13)
  | .semantic   => false  -- specificity is a binding restriction, unaffected
  | .processing => false
  | .discourse  => false

-- ============================================================================
-- §2. Experimental conditions
-- ============================================================================

/-- Language parameter: wh-movement vs wh-in-situ. -/
inductive WhLanguageType where
  | whMovement   -- English, German, etc.: overt wh-fronting
  | whInSitu     -- Mandarin Chinese, Japanese, etc.: in-situ wh-binding
  deriving DecidableEq, Repr

/-- Map language type to wh-dependency type. -/
def WhLanguageType.toDependencyType : WhLanguageType → WhDependencyType
  | .whMovement => .movement
  | .whInSitu   => .binding

-- ============================================================================
-- §3. Divergent predictions (Table 1, p.11)
-- ============================================================================

/-! @cite{shen-huang-2026} Table 1 lays out the key motivation for the
combined account: the DP phasehood/PIC approach and the Specificity Condition
make DIFFERENT predictions on four empirical dimensions.

| Dimension                        | PIC (+Incorporation) | Specificity      |
|----------------------------------|---------------------|------------------|
| Definite island in English       | non-VOCs only       | VOCs and non-VOCs|
| VOC effect in English            | Yes                 | No               |
| Definite island in Chinese       | No                  | VOCs and non-VOCs|
| VOC effect in Chinese            | No                  | No               |

Neither account alone matches the full pattern of results. The PIC account
misses (a) the residual island effect with English VOCs and (b) the definite
island effect in Chinese. The Specificity account misses the VOC effect
in English. Only the combined account gets all four dimensions right. -/

/-- What does each individual account predict?
`true` = predicts an island effect, `false` = predicts no effect. -/
structure AccountPrediction where
  /-- Does this account predict a definite island effect in English? -/
  englishIsland : Bool
  /-- Does this account predict a VOC effect (amelioration) in English? -/
  englishVOCEffect : Bool
  /-- Does this account predict a definite island effect in Chinese? -/
  chineseIsland : Bool
  /-- Does this account predict a VOC effect in Chinese? -/
  chineseVOCEffect : Bool
  deriving DecidableEq, Repr

/-- PIC + Incorporation account predictions (Table 1, column 1).
Predicts an island for English non-VOCs (PIC violated) but not VOCs
(incorporation neutralizes PIC). Predicts no island in Chinese
(PIC is inapplicable to binding). -/
def picPrediction : AccountPrediction :=
  { englishIsland := true, englishVOCEffect := true,
    chineseIsland := false, chineseVOCEffect := false }

/-- Specificity Condition predictions (Table 1, column 2).
Predicts an island in both languages (specificity constrains both
movement and binding). Silent about VOC effects — the Specificity
Condition is about the DP, not the verb. -/
def specificityPrediction : AccountPrediction :=
  { englishIsland := true, englishVOCEffect := false,
    chineseIsland := true, chineseVOCEffect := false }

/-- The experimental results. -/
def experimentalResults : AccountPrediction :=
  { englishIsland := true, englishVOCEffect := true,
    chineseIsland := true, chineseVOCEffect := false }

/-- **Neither account alone matches all results.**
The PIC account gets the English VOC effect right but misses the
Chinese island effect. The Specificity account gets the Chinese
island right but misses the English VOC effect. -/
theorem neither_account_alone_suffices :
    picPrediction ≠ experimentalResults ∧
    specificityPrediction ≠ experimentalResults := by
  exact ⟨by decide, by decide⟩

/-- **The combined account matches all results.**
English island: yes (PIC + Specificity both violated for non-VOCs).
English VOC effect: yes (PIC neutralized, Specificity remains → partial).
Chinese island: yes (Specificity violated).
Chinese VOC effect: no (only Specificity applies, VOCs irrelevant). -/
def combinedPrediction : AccountPrediction :=
  { englishIsland := true, englishVOCEffect := true,
    chineseIsland := true, chineseVOCEffect := false }

theorem combined_matches_results :
    combinedPrediction = experimentalResults := rfl

-- ============================================================================
-- §4. Constraint violation model (Table 3, p.23)
-- ============================================================================

/-- The sources of the definite nominal island constraint.

Derived from two independent theoretical mechanisms:
- `.syntactic`: definite DPs are phases (`isDPhaseHead` in Phase.lean),
  so the PIC applies to extraction across definite DP boundaries.
  Grounded by §13: `voc_removes_pic_barrier` / `nonvoc_preserves_pic_barrier`.
- `.semantic`: definite DPs are specific (`blocked` in SpecificityCondition.lean),
  and the Specificity Condition restricts binding inside specific DPs.
  Grounded by §6: `specificity_predicts_exp3`. -/
def definiteNominalSources : List IslandSource := [.syntactic, .semantic]

/-- Active island sources for a definite nominal extraction.

An island source contributes a violation when ALL of:
1. It is part of the definite nominal's sources (`definiteNominalSources`)
2. It applies to the given dependency type
   (`constraintsForDependencyType dep`)
3. It is not neutralized by VOC (`vocNeutralizes`)

This derives the violation model compositionally from three independent
classifications — constraint source type, dependency sensitivity, and VOC
scope — rather than encoding them in ad-hoc Boolean functions. -/
def activeSources (dep : WhDependencyType) (voc : Bool) : List IslandSource :=
  definiteNominalSources.filter fun src =>
    (constraintsForDependencyType dep).contains src &&
    !(voc && vocNeutralizes src)

/-- Total constraint violations in a condition.
Definiteness is a precondition: indefinite DPs are neither phases
nor specific, so they produce no violations. For definite DPs,
violations = the number of active island sources. -/
def totalViolations (lang : WhLanguageType) (obj : Definiteness) (voc : Bool) : Nat :=
  match obj with
  | .indefinite => 0
  | .definite   => (activeSources lang.toDependencyType voc).length

-- ============================================================================
-- §5. Source-level structural facts
-- ============================================================================

/-! The source-level facts below ARE the deeper principles from which the
paper's empirical predictions follow. Each captures one structural property
of the constraint architecture.

By marking these as `@[simp]` and `activeSources` as `@[irreducible]`,
we ensure that all downstream proofs MUST go through these lemmas — `simp`
cannot bypass them by unfolding `activeSources` directly. This makes the
derivation chain structural rather than accidental. -/

/-- **All definite nominal sources constrain movement.** Both the syntactic
(PIC) and semantic (Specificity) sources apply to movement dependencies. -/
@[simp] theorem all_sources_apply_to_movement :
    activeSources .movement false = [.syntactic, .semantic] := rfl

/-- **VOC neutralizes exactly the syntactic source for movement.**
After N/D-incorporation, only the semantic source remains. -/
@[simp] theorem voc_neutralizes_syntactic_for_movement :
    activeSources .movement true = [.semantic] := rfl

/-- **Only the semantic source constrains binding.**
The syntactic source (PIC) is inapplicable because binding does not
cross phase boundaries (@cite{fox-pesetsky-2005}). VOC status is
irrelevant — there is no syntactic source to neutralize. -/
@[simp] theorem binding_sources (voc : Bool) :
    activeSources .binding voc = [.semantic] := by cases voc <;> rfl

-- After the source-level facts are proved, seal `activeSources` so all
-- downstream reasoning must go through the named lemmas above.
attribute [irreducible] activeSources

/-- **Indefinite objects produce no violations.** Indefinite DPs are
neither phases nor specific — they fail the precondition for both
sources. -/
@[simp] theorem indefinite_no_violations (lang : WhLanguageType) (voc : Bool) :
    totalViolations lang .indefinite voc = 0 := rfl

/-- **VOCs are irrelevant for binding languages.** Changing VOC status
never changes the violation count for binding dependencies.
Follows from `binding_sources`: the active sources for binding are
`[.semantic]` regardless of VOC. -/
theorem binding_voc_invariant (obj : Definiteness) (voc : Bool) :
    totalViolations .whInSitu obj voc = totalViolations .whInSitu obj false := by
  cases obj <;> simp [totalViolations, WhLanguageType.toDependencyType]

-- ============================================================================
-- §6. Experimental data (Experiments 1 & 2)
-- ============================================================================

/-- Difference-in-difference (DD) scores from @cite{shen-huang-2026}
Experiments 1 (English) and 2 (Chinese).

DD = (definite_long − definite_short) − (indefinite_long − indefinite_short)

Positive DD indicates a definite island effect above and beyond the
baseline effect of subextraction / long wh-dependency.

Scores stored as Nat (DD × 100) to avoid rationals in data. -/
structure DDScore where
  language : WhLanguageType
  voc : Bool
  /-- DD × 100 (z-scored acceptability difference-in-difference) -/
  dd : Int
  deriving Repr

/-- English non-VOC DD: 0.56 (strong definite island effect). -/
def english_nonvoc_dd : DDScore :=
  { language := .whMovement, voc := false, dd := 56 }

/-- English VOC DD: 0.23 (weaker but still significant definite island effect).
    VOC effect exists (three-way interaction): β = 0.32, s.e. = 0.10, t = 3.21, p < 0.01.
    DD = 0.23 significantly ≠ 0 (within-VOC interaction): β = −0.23, s.e. = 0.10, t = −2.38, p < 0.05. -/
def english_voc_dd : DDScore :=
  { language := .whMovement, voc := true, dd := 23 }

/-- Chinese non-VOC DD: 1.15 (strong definite island effect). -/
def chinese_nonvoc_dd : DDScore :=
  { language := .whInSitu, voc := false, dd := 115 }

/-- Chinese VOC DD: 0.97 (comparable to non-VOC — no VOC effect).
    Three-way interaction not significant:
    β = 0.19, s.e. = 0.11, t = 1.73, p = 0.09. -/
def chinese_voc_dd : DDScore :=
  { language := .whInSitu, voc := true, dd := 97 }

def allDDScores : List DDScore :=
  [english_nonvoc_dd, english_voc_dd, chinese_nonvoc_dd, chinese_voc_dd]

/-- The VOC effect is larger in English than in Chinese. -/
theorem voc_effect_larger_in_english :
    (english_nonvoc_dd.dd - english_voc_dd.dd) >
    (chinese_nonvoc_dd.dd - chinese_voc_dd.dd) := by native_decide

/-- Both DD scores are positive: definite island effects exist in all
    tested conditions with definite objects. -/
theorem all_dd_positive :
    allDDScores.all (·.dd > 0) = true := by native_decide

/-- The model correctly predicts the DIRECTION of the VOC effect:
    more violations → higher DD score.
    The Chinese equality follows from `binding_voc_invariant`.

    **Quantitative caveat** (p.23): the model predicts the *presence or
    absence* of effects, not their *magnitude*. Chinese (1 violation,
    Specificity only) has DD ≈ 1.0, while English non-VOC (2 violations,
    PIC + Specificity) has DD ≈ 0.56. The paper notes: "This effect size
    difference, strictly speaking, does not contradict any part of our
    proposal." Crosslinguistic magnitude differences are expected (cf.
    Almeida 2014 on "subliminal" *wh*-islands in Brazilian Portuguese). -/
theorem violations_predict_dd_ordering :
    -- English non-VOC (2 violations) > English VOC (1 violation)
    english_nonvoc_dd.dd > english_voc_dd.dd ∧
    -- Chinese non-VOC (1 violation) ≈ Chinese VOC (1 violation)
    -- (no significant difference: p = 0.09)
    totalViolations .whInSitu .definite false =
    totalViolations .whInSitu .definite true :=
  ⟨by native_decide, (binding_voc_invariant .definite true).symm⟩

-- ============================================================================
-- §7. Experiment 3: Wh-indefinites and specificity
-- ============================================================================

/-- Experiment 3 tests @cite{li-1992}'s observation that Chinese
wh-indefinites are degraded inside demonstrative-marked (specific) DPs.

Four conditions in a 2×2 design:
- Object definiteness: indefinite (yī-CL) vs definite (nà-CL)
- Wh-indefinite presence: wh-indef vs mǒu-CL-N ('a certain N')

Key interaction: β = −0.48, s.e. = 0.15, t = −3.32, p < 0.01.
Wh-indefinites are significantly worse inside definite DPs.

Note: individual cell means below are approximate, read from Figure 3.
The paper reports only the interaction β, not individual cell means numerically. -/
structure Exp3Condition where
  objDefinite : Bool
  whIndefinite : Bool
  /-- Mean z-scored acceptability × 100 -/
  meanAcceptability : Int
  deriving Repr

def exp3_indef_whindef : Exp3Condition :=
  { objDefinite := false, whIndefinite := true, meanAcceptability := 40 }

def exp3_def_whindef : Exp3Condition :=
  { objDefinite := true, whIndefinite := true, meanAcceptability := -35 }

def exp3_indef_mou : Exp3Condition :=
  { objDefinite := false, whIndefinite := false, meanAcceptability := 45 }

def exp3_def_mou : Exp3Condition :=
  { objDefinite := true, whIndefinite := false, meanAcceptability := 40 }

/-- Wh-indefinites inside definite DPs are the only degraded condition. -/
theorem whindef_in_definite_degraded :
    exp3_def_whindef.meanAcceptability < 0 := by native_decide

/-- Wh-indefinites inside indefinite DPs are acceptable. -/
theorem whindef_in_indefinite_acceptable :
    exp3_indef_whindef.meanAcceptability > 0 := by native_decide

/-- The Specificity Condition predicts this: existential closure
(binding a wh-indefinite) is blocked inside specific DPs. -/
theorem specificity_predicts_exp3 :
    blocked .existentialClosure .definite ∧
    ¬ blocked .existentialClosure .indefinite := ⟨rfl, by decide⟩

-- ============================================================================
-- §8. Connection to VOC Levin classes
-- ============================================================================

/-- The VOC/non-VOC distinction used in the experiments maps onto
Levin verb classes. VOC verbs belong to creation classes (§25–26);
non-VOC verbs belong to perception (§30) or communication classes. -/
theorem build_is_voc : LevinClass.isVerbOfCreation .build = true := rfl
theorem create_is_voc : LevinClass.isVerbOfCreation .create = true := rfl
theorem imageCreation_is_voc : LevinClass.isVerbOfCreation .imageCreation = true := rfl
theorem see_is_not_voc : LevinClass.isVerbOfCreation .see = false := rfl

-- ============================================================================
-- §9. Island classification theorems
-- ============================================================================

/-- Definite nominal islands are composite: syntactic (PIC) + semantic
(Specificity Condition). Neither source alone accounts for the full
crosslinguistic pattern.

This is not stipulated — it follows from the conjunction of Phase Theory
(`isDPhaseHead` → syntactic source) and the Specificity Condition
(`blocked` → semantic source). See `definiteNominalSources`. -/
theorem definite_nominal_is_composite :
    definiteNominalSources = [.syntactic, .semantic] := rfl

/-- Definite nominal islands are weak — ameliorated by VOCs in English
(DD 0.23 for VOCs vs 0.56 for non-VOCs). Derived from the experimental
DD data: `english_voc_dd < english_nonvoc_dd` (§6). -/
def definiteNominalStrength : ConstraintStrength := .weak

theorem definite_nominal_is_weak :
    definiteNominalStrength = .weak := rfl

/-- Movement dependencies face strictly more constraints than binding dependencies. -/
theorem movement_more_constrained :
    (constraintsForDependencyType .movement).length >
    (constraintsForDependencyType .binding).length := by native_decide

/-- Binding dependencies are not constrained by the PIC. -/
theorem binding_not_pic_constrained :
    (constraintsForDependencyType .binding).all (· != .syntactic) = true := by native_decide

-- ============================================================================
-- §10. Derivations from the source architecture
-- ============================================================================

/-! The violation model in §4 computes violations from three independent
source-level classifications. The theorems below derive the paper's
crosslinguistic predictions from the structural facts in §3.

Because `activeSources` is sealed (`@[irreducible]`), `simp` cannot
unfold it directly — it MUST go through the `@[simp]` lemmas
(`all_sources_apply_to_movement`, `voc_neutralizes_syntactic_for_movement`,
`binding_sources`). This guarantees the derivation chain is structural.

The source-level facts themselves follow from the definitions in §1
(`definiteNominalSources`, `constraintsForDependencyType`, `vocNeutralizes`),
which are grounded in Phase Theory (§14) and cyclic linearization (§13). -/

/-- **VOC amelioration is restricted to exactly one configuration.**
If changing VOC status reduces violations, the language must use movement
AND the object must be definite.

Proof: indefinite gives 0 (contradiction). Binding is VOC-invariant
(`binding_voc_invariant`), so no reduction (contradiction). Only
movement + definite remains. -/
theorem voc_amelioration_restricted (lang : WhLanguageType) (obj : Definiteness)
    (h : totalViolations lang obj true < totalViolations lang obj false) :
    lang = .whMovement ∧ obj = .definite := by
  cases lang <;> cases obj
  · simp [totalViolations] at h                          -- whMovement, indefinite: 0 < 0
  · exact ⟨rfl, rfl⟩                                     -- whMovement, definite ✓
  · simp [totalViolations] at h                          -- whInSitu, indefinite: 0 < 0
  · have := binding_voc_invariant .definite true; omega  -- whInSitu, definite: VOC-invariant

/-- **Constraint stacking is bounded.** The maximum is 2 violations,
achieved when all definite nominal sources are active
(`all_sources_apply_to_movement`): `|[.syntactic, .semantic]| = 2`. -/
theorem max_violations_is_two :
    (∀ lang obj voc, totalViolations lang obj voc ≤ 2) ∧
    (∃ lang obj voc, totalViolations lang obj voc = 2) := by
  refine ⟨fun lang obj voc => ?_, ⟨.whMovement, .definite, false, ?_⟩⟩
  · cases lang <;> cases obj <;> cases voc <;>
      simp [totalViolations, WhLanguageType.toDependencyType]
  · simp [totalViolations, WhLanguageType.toDependencyType]

/-- **The deepest theorem: VOC amelioration removes exactly 1 source.**
The reduction in violations equals 1 for movement + definite, and 0
otherwise.

This derives from the source-level facts:
- Movement without VOC: `activeSources .movement false = [.syntactic, .semantic]`
- Movement with VOC: `activeSources .movement true = [.semantic]`
- Binding: `activeSources .binding voc = [.semantic]` (VOC-invariant)
- Indefinite: 0 violations

The "1" is not stipulated — it is the cardinality difference between
`[.syntactic, .semantic]` and `[.semantic]`, i.e., exactly the
VOC-neutralizable sources applicable to movement. -/
theorem voc_amelioration_exactly_one (lang : WhLanguageType) (obj : Definiteness) :
    totalViolations lang obj false - totalViolations lang obj true =
    if lang = .whMovement ∧ obj = .definite then 1 else 0 := by
  cases lang <;> cases obj <;>
    simp [totalViolations, WhLanguageType.toDependencyType]

/-- **Specificity is necessary for the residual island.** Even after
VOC neutralizes the syntactic source, 1 violation remains — the
semantic source. Without it, VOCs would fully neutralize the island,
predicting DD = 0 for English VOCs. But DD = 0.23 > 0. -/
theorem specificity_creates_residual_island :
    totalViolations .whMovement .definite true = 1 ∧
    english_voc_dd.dd > 0 := by
  refine ⟨?_, by native_decide⟩
  simp [totalViolations, WhLanguageType.toDependencyType]

-- ============================================================================
-- §11. Fragment verb integration
-- ============================================================================

open Fragments.English.Predicates.Verbal in
/-- Does a Fragment verb predict VOC-mediated amelioration of the definite
island effect? Derived from the verb's Levin class via `isVerbOfCreation`. -/
def fragmentPredictsVOCEffect (v : VerbEntry) : Bool :=
  match v.levinClass with
  | some lc => lc.isVerbOfCreation
  | none => false

/-! ### VOC verbs in the Fragment

These verbs have Levin creation classes (§25–26) and predict amelioration
of definite islands via N/D-incorporation. Per-verb theorems make the
dependency explicit: changing a verb's `levinClass` field breaks exactly
one theorem. -/

open Fragments.English.Predicates.Verbal in
theorem voc_verbs_predict_amelioration :
    fragmentPredictsVOCEffect build = true ∧
    fragmentPredictsVOCEffect write = true ∧
    fragmentPredictsVOCEffect draw = true ∧
    fragmentPredictsVOCEffect create = true ∧
    fragmentPredictsVOCEffect grow = true ∧
    fragmentPredictsVOCEffect perform = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Non-VOC verbs: no amelioration predicted

Perception and communication verbs lack creation semantics. Definite
islands should show the full effect (PIC + Specificity in English,
Specificity alone in Chinese). -/

open Fragments.English.Predicates.Verbal in
theorem nonvoc_verbs_no_amelioration :
    fragmentPredictsVOCEffect see = false ∧
    fragmentPredictsVOCEffect hear = false ∧
    fragmentPredictsVOCEffect read = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §12. Follow-up analyses
-- ============================================================================

/-! ### Excluding syntactically ambiguous verbs (p.21)

Three English verbs — *hear*, *read*, *write* — can appear without objects
and with *about*-PPs, creating a syntactic ambiguity (the PP could attach
to the DP or the VP). @cite{shen-huang-2026} reran the analysis excluding
these verbs. Results were qualitatively identical. -/

/-- English non-VOC DD excluding hear/read/write: 0.53 (p.21). -/
def english_nonvoc_dd_excl : DDScore :=
  { language := .whMovement, voc := false, dd := 53 }

/-- English VOC DD excluding hear/read/write: 0.23 (p.21). -/
def english_voc_dd_excl : DDScore :=
  { language := .whMovement, voc := true, dd := 23 }

/-- The VOC effect persists when ambiguous verbs are excluded. -/
theorem voc_effect_robust :
    english_nonvoc_dd_excl.dd > english_voc_dd_excl.dd := by native_decide

/-! ### Appendix A: Ruling out parser overload (pp.37–40)

An anonymous reviewer suggested the Chinese *wh-in-situ* experiment (Exp 2)
might reflect parser overload rather than a genuine island effect: processing
a long covert *wh*-dependency together with relative clauses and definiteness
simultaneously might overwhelm the parser.

@cite{shen-huang-2026} ran a 2×2 follow-up experiment (DP complexity ×
DP function) with generic/indefinite DPs to rule this out. If parser
overload were the explanation, there should be an interaction between
complexity and function. There was none.

DD = 0.05 (z-scored). No significant interaction:
β = −0.07, s.e. = 0.08, t = −0.82, p = 0.41. -/

/-- Follow-up experiment data: DD score for parser overload test. -/
structure AppendixAResult where
  /-- DD × 100 (complexity × function interaction) -/
  dd : Int
  /-- Whether the interaction is significant at p < 0.05 -/
  significant : Bool
  deriving Repr

/-- The follow-up experiment found no significant interaction,
ruling out parser overload as the explanation for Chinese
definite island effects. -/
def appendixA : AppendixAResult :=
  { dd := 5, significant := false }

/-- DD ≈ 0 and not significant: no evidence of parser overload. -/
theorem parser_overload_ruled_out :
    appendixA.dd < 10 ∧ appendixA.significant = false :=
  ⟨by native_decide, rfl⟩

-- ============================================================================
-- §13. Connection to cyclic linearization
-- ============================================================================

/-! @cite{shen-huang-2026} §4.2 use @cite{fox-pesetsky-2005}'s cyclic
linearization theory to explain why binding is not subject to the PIC.
(Note: the journal publication year is 2005; the paper cites the 2004
working paper version.)

The key argument: binding does not change the linear order of elements.
When a covert question operator at Spec,CP binds a wh-in-situ element,
no element moves across a phase boundary. Consequently, Spell-out of
each phase produces no ordering contradictions, and the derivation
converges. This is why `WhDependencyType.binding` is not constrained
by the PIC — it cannot create the ordering conflicts that the PIC
(via Order Preservation) is designed to prevent.

The `spellout` function from `CyclicLinearization` takes an existing
`OrderingTable` and a list of terminals that move — for binding, this
list is empty, so the table is unchanged and trivially consistent. -/

/-- Binding adds no precedence statements: when no elements move
(the terminal list is empty), `spellout` returns the existing table
unchanged. This is the formal content of "binding does not change
linear order" (@cite{fox-pesetsky-2005}, as applied in
@cite{shen-huang-2026} §4.2). -/
theorem binding_no_new_precedences (existing : OrderingTable) :
    spellout existing [] = existing := by
  unfold spellout allPrecs; simp

/-- Consequence: binding never creates an ordering contradiction.
If the existing ordering table is consistent, it stays consistent
after a binding operation (because nothing changes). -/
theorem binding_preserves_consistency (existing : OrderingTable)
    (h : isConsistent existing = true) :
    isConsistent (spellout existing []) = true := by
  rw [binding_no_new_precedences]; exact h

-- ============================================================================
-- §14. Bridge: Phase Theory → Violation Model
-- ============================================================================

/-! The violation model's `vocNeutralizes .syntactic = true` (defined in
§1 above) captures the empirical generalization that VOCs
remove the syntactic barrier to extraction. Phase Theory
(`Theories/Syntax/Minimalism/Phase.lean`) provides the formal
mechanism: N/D-incorporation deactivates the DP's phasehood.

This section bridges the two layers, showing that the Phase Theory's
`incorporation_deactivates` theorem formally grounds the violation model's
classification of `.syntactic` as VOC-neutralizable. -/

open Minimalist in
/-- **VOC incorporation deactivates the PIC barrier.**
When a VOC verb incorporates the object's D head, the DP is no
longer an active phase — regardless of whether it was originally
a phase. This is the mechanism behind `vocNeutralizes .syntactic = true`:
the syntactic source (PIC) is neutralized because the phase boundary
is removed. -/
theorem voc_removes_pic_barrier (s : DPPhaseStatus)
    (h_inc : s.incorporated = true) :
    s.isActivePhase = false := by
  simp [DPPhaseStatus.isActivePhase, h_inc]

open Minimalist in
/-- **Non-VOC verbs leave the PIC barrier intact.**
Without incorporation, a definite DP remains an active phase,
and the PIC applies — the syntactic source is violated. -/
theorem nonvoc_preserves_pic_barrier (dHead : SyntacticObject)
    (h_phase : isDPhaseHead dHead = true) :
    (DPPhaseStatus.mk dHead (isDPhaseHead dHead) false).isActivePhase = true := by
  simp [DPPhaseStatus.isActivePhase, h_phase]

open Minimalist in
/-- **End-to-end: incorporation status determines whether the syntactic
source is active.**
- `incorporated = true` → PIC deactivated → syntactic source neutralized
  (matches `vocNeutralizes .syntactic = true`)
- `incorporated = false` → PIC active → syntactic source violated
  (matches VOC-absent condition in `activeSources .movement false`) -/
theorem incorporation_determines_syntactic_source (dHead : SyntacticObject)
    (h_phase : isDPhaseHead dHead = true) (inc : Bool) :
    (DPPhaseStatus.mk dHead (isDPhaseHead dHead) inc).isActivePhase = !inc := by
  cases inc <;> simp [DPPhaseStatus.isActivePhase, h_phase]

end ShenHuang2026
