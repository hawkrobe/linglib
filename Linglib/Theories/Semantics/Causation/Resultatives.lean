import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergJackendoff2004
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Causation.ProductionDependence

/-!
# Resultatives as Concealed Causatives
@cite{baglini-bar-asher-siegal-2025} @cite{goldberg-jackendoff-2004} @cite{levin-2019} @cite{martin-rose-nichols-2025}

Theory-side connection between the resultative construction and the
causative semantics infrastructure. Per-scenario `BoolSEM` witnesses
(HammerFlat, IndependentSourceBreaksNecessity, etc.) live with the paper
that uses them — see `Phenomena.Constructions.Resultatives.Studies.Levin2026`
and `Studies.Tay2024`.

Sections:

1. **Causative bridge**: `deriveCausativeBuilder` derives the resultative's
   `Causative` value from the @cite{goldberg-jackendoff-2004} MEANS subevent
   relation + constructional CAUSE flag. Specialized to MEANS-relation
   causative resultatives; @cite{goldberg-jackendoff-2004}'s sound-emission
   and disappearance subtypes (RESULT/INSTANCE relations) are out of scope
   for the derivation here and would need their own builders.
2. **CC-selection**: resultatives select via completion of a sufficient set
   (@cite{baglini-bar-asher-siegal-2025}, alongside change-of-state verbs).
3. **Three-way convergence**: @cite{martin-rose-nichols-2025} thick manner ↔
   `.production` ↔ `.make` builder ↔ resultative builder. Independently
   motivated paths converge on `.make`.
4. **Aspect**: bounded RP telicizes activity → accomplishment.
5. **ChangeOfState**: constructional BECOME maps to `CoSType.inception`.
6. **Compositional decomposition**: subconstructions decompose into
   universal schemata (`isFullyCompositional`).
7. **Cross-linguistic typological parameters**: `ResultativeRealization`,
   `ResultOrientation`. Mandarin-specific phase-complement morpheme data
   (`PhaseComplement` enum + `cosType`) lives in
   `Fragments.Mandarin.Resultatives`.
-/

namespace Semantics.Causation.Resultatives

open ConstructionGrammar
open ConstructionGrammar.Studies.GoldbergJackendoff2004
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Verb.ChangeOfState
open Core.Verbs (Causative)
open Semantics.Causation.ProductionDependence
open Semantics.Causation.CCSelection

/-! ## Agreement with Boolean flags -/

/-- isCausative ↔ hasCause — derived from the subconstruction, not stipulated. -/
theorem causative_iff_has_cause (sc : ResultativeSubconstruction) :
    sc.isCausative = sc.constructionalDesc.hasCause := by
  cases sc <;> rfl

/-- All causative entries in the data have CAUSE. -/
theorem causative_resultative_has_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subeventRelation == .means
    )).all (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-! ## CC-selection (@cite{baglini-bar-asher-siegal-2025})

Resultatives select via completion of a sufficient set: the verbal subevent
must be the final condition that makes the result inevitable. -/

/-- Resultatives select via completion (like CoS verbs). -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-! ## Causative bridge: derived from SubeventRelation + CAUSE

The resultative's `Causative` is `.make`, derived from two
independently-motivated properties:

1. **MEANS relation** (@cite{goldberg-jackendoff-2004}): the verbal subevent
   is the means by which the constructional subevent is brought about.
   MEANS ↔ causal sufficiency.
2. **CAUSE in constructional subevent**: causative subconstructions have
   `hasCause = true`.

MEANS + CAUSE → sufficiency. Among sufficiency builders, `.make` is
uniquely the neutral builder (no coercion `.force`, no barrier-removal
`.enable`).

Note: this derivation handles MEANS-relation resultatives only. Sound-
emission and disappearance subtypes (`SubeventRelation.result`/`.instance_`)
would map to different builders or remain unanalyzed here. -/

/-- Derive the Causative from MEANS subevent relation + CAUSE flag.
    Always yields `.make` for MEANS+CAUSE; non-MEANS yields `none`. -/
def deriveCausativeBuilder (rel : SubeventRelation) (desc : SubeventDesc) :
    Option Causative :=
  match rel, desc.hasCause with
  | .means, true => some .make
  | _, _ => none

/-- `.make` is the unique builder asserting neutral sufficiency. -/
theorem make_unique_neutral_sufficiency (b : Causative)
    (hs : b.assertsSufficiency = true)
    (hc : b.isCoercive = false)
    (hp : b.isPermissive = false) :
    b = .make := by
  cases b <;> simp_all [Causative.assertsSufficiency,
    Causative.isCoercive, Causative.isPermissive]

/-- MEANS + CAUSE derives `.make`. -/
theorem means_cause_derives_make (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc = some .make := by
  simp [deriveCausativeBuilder, h]

/-- For any causative subconstruction with MEANS relation, the derived
    builder is `.make`. -/
theorem causative_means_derives_make (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    deriveCausativeBuilder .means sc.constructionalDesc = some .make := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Noncausative subconstructions don't derive a Causative. -/
theorem noncausative_no_builder (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false) :
    deriveCausativeBuilder .means sc.constructionalDesc = none := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Non-MEANS relations never derive a Causative. -/
theorem non_means_no_builder (desc : SubeventDesc) :
    deriveCausativeBuilder .result desc = none ∧
    deriveCausativeBuilder .instance_ desc = none ∧
    deriveCausativeBuilder .coOccurrence desc = none := by
  simp [deriveCausativeBuilder]

/-- When `deriveCausativeBuilder` succeeds, the result asserts sufficiency. -/
theorem derived_asserts_sufficiency (rel : SubeventRelation) (desc : SubeventDesc)
    (b : Causative) (h : deriveCausativeBuilder rel desc = some b) :
    b.assertsSufficiency = true := by
  unfold deriveCausativeBuilder at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

/-- The resultative Causative, derived from MEANS + CAUSE. -/
def resultativeCausativeBuilder : Causative :=
  match deriveCausativeBuilder .means
    ResultativeSubconstruction.causativeProperty.constructionalDesc with
  | some b => b
  | none => .cause

/-- The derived builder is `.make`. -/
theorem resultative_is_make :
    resultativeCausativeBuilder = .make := rfl

/-- `.prevent` is incompatible with resultatives. -/
theorem prevent_incompatible_with_resultative :
    Causative.prevent ≠ resultativeCausativeBuilder := by decide

/-! ## Three-Way Convergence: Thick ↔ P-CAUSE ↔ Resultative -/

/-- Three independent paths converge on `.make`:
    @cite{martin-rose-nichols-2025} thick manner classification +
    `.production` analogous-builder + the resultative-from-MEANS+CAUSE
    derivation above. -/
theorem thick_manner_resultative_convergence :
    productionConstraint .thickManner = .production ∧
    CausationType.production.analogousBuilder = .make ∧
    resultativeCausativeBuilder = .make ∧
    CausationType.production.analogousBuilder = resultativeCausativeBuilder :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Thin → `.cause` ≠ resultative `.make` (*kill open). -/
theorem thin_incompatible_with_resultative_cause :
    productionConstraint .thin = .dependence ∧
    CausationType.dependence.analogousBuilder = .cause ∧
    Causative.cause ≠ resultativeCausativeBuilder :=
  ⟨rfl, rfl, by decide⟩

/-! ## Aspect: activity + bounded RP → accomplishment -/

/-- Bounded RP telicizes activity. -/
theorem resultative_telicizes :
    activityProfile.telicize.toVendlerClass = .accomplishment :=
  telicize_activity

/-- The resultative construction's aspect shift. -/
theorem resultative_aspect_shift :
    resultativeVendlerClass .bounded = .accomplishment :=
  rfl

theorem resultative_aspect_agrees_with_telicize :
    resultativeVendlerClass .bounded =
    activityProfile.telicize.toVendlerClass :=
  rfl

/-- Activity verbs in the data with bounded RPs become accomplishments. -/
theorem activity_entries_become_accomplishments :
    (allEntries.filter (λ e =>
      e.bareVerbClass == .activity && e.rpBoundedness == .bounded
    )).all (λ e =>
      resultativeVendlerClass e.rpBoundedness == .accomplishment
    ) = true := by
  native_decide

/-! ## ChangeOfState: BECOME = inception (¬P → P) -/

/-- Constructional BECOME = CoS inception. -/
def resultStateMapsToCoS : CoSType := .inception

/-- All resultative entries have BECOME. -/
theorem all_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  native_decide

/-- Inception presupposes ¬P before. -/
theorem inception_presupposes_not_prior {W : Type*} (P : W → Prop) (w : W) :
    priorStatePresup .inception P w ↔ ¬P w := Iff.rfl

/-- Inception asserts P after. -/
theorem inception_asserts_result {W : Type*} (P : W → Prop) :
    resultStateAssertion .inception P = P := rfl

/-! ## Compositional decomposition -/

/-- All four subconstructions are fully compositional. -/
theorem allResultativesFullyCompositional :
    resultativeFamily.all (λ c =>
      isFullyCompositional c.construction) = true := by
  decide

/-- Causative subconstructions decompose like the parent resultative. -/
theorem causative_decompose_like_parent :
    decompose causativePropertyConstruction = decompose resultative ∧
    decompose causativePathConstruction = decompose resultative := by
  constructor <;> decide

/-- Noncausative subconstructions decompose into fewer combination steps. -/
theorem noncausative_fewer_steps :
    (decompose noncausativePropertyConstruction).length <
    (decompose causativePropertyConstruction).length ∧
    (decompose noncausativePathConstruction).length <
    (decompose causativePathConstruction).length := by
  constructor <;> decide

theorem decomposition_reflects_transitivity :
    (decompose causativePropertyConstruction).length = 3 ∧
    (decompose noncausativePropertyConstruction).length = 2 := by
  constructor <;> decide

/-! ## Cross-linguistic Resultative Parameters

`ResultativeRealization` and `ResultOrientation` are theory-neutral
typological parameters. Mandarin-specific phase complements
(`PhaseComplement` enum + per-morpheme `cosType`) live in
`Fragments.Mandarin.Resultatives`. -/

inductive ResultativeRealization where
  | syntacticAdjunct
  | verbCompound
  | deComplement
  deriving DecidableEq, Repr

inductive ResultOrientation where
  | objectOriented
  | subjectOriented
  deriving DecidableEq, Repr

end Semantics.Causation.Resultatives
