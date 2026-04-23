import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergJackendoff2004
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Causation.ProductionDependence
import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Resultatives as Concealed Causatives
@cite{baglini-bar-asher-siegal-2025} @cite{goldberg-jackendoff-2004} @cite{levin-2019} @cite{martin-rose-nichols-2025} @cite{nadathur-lauer-2020}

Connects the resultative construction to the causative semantics
infrastructure:

1. **Causal Models**: causative resultatives modeled as concrete `BoolSEM`
   instances with structural sufficiency proofs (HammerFlat, KickIntoField,
   LaughSilly, ...)
2. **Tightness via causal necessity**: @cite{levin-2019} concealed causative
   constraint — intervening causers with independent energy sources disrupt
   necessity. The `KickDoorViaBall` model witnesses the not-tight case.
3. **Thick/Thin Convergence**: three independent paths
   (@cite{martin-rose-nichols-2025}, @cite{goldberg-jackendoff-2004},
   @cite{embick-2009}) converge on `.make`/`causallySufficient`.
4. **Aspect**: resultative telicizes activity verbs via bounded RP.
5. **ChangeOfState**: constructional BECOME maps to `CoSType.inception`.
6. **Müller decomposability**: all subconstructions decompose into
   universal schemata.

Per-scenario `BoolSEM` models live at top level (HammerFlat, KickIntoField,
etc.). Each scenario gets its own enum (`Fintype + DecidableEq + Repr`)
so `developDetOn` reduces structurally without `native_decide`.

The legacy `CausalDynamics`-based body — including the 150-LOC
`independent_source_disrupts_tightness` proof over `applyLawsOnce`/
`isFixpoint` — was deleted in Phase D-H. The qualitative not-tight claim
is witnessed concretely by `KickDoorViaBall.kick_door_via_ball_not_tight`.
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
open Core.Causal Core.Causal.Mechanism Core.Causal.SEM

/-! ## Causal Models (BoolSEM)

Each causative resultative maps to a concrete `BoolSEM V` where the
verbal subevent vertex causally determines the result vertex. The local
`sufficient`/`completes` predicates use `developDetOn` directly so kernel
reduction closes the structural theorems via `rfl` / `Bool.false_ne_true`. -/

/-- Local sufficiency predicate: with `cause = true` under `bg`,
    `developDetOn` of `M` produces `effect = true`. -/
noncomputable def sufficient {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool)) (n : Nat)
    (cause effect : W) : Prop :=
  (developDetOn M vs n (bg.extend cause true)).hasValue effect true

/-- Local completion predicate: sufficient + but-for. -/
noncomputable def completes {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool)) (n : Nat)
    (cause effect : W) : Prop :=
  sufficient M vs bg n cause effect ∧
  ¬ (developDetOn M vs n (bg.extend cause false)).hasValue effect true

namespace HammerFlat

inductive V | hammering | flat
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.hammering, .flat]

def graph : CausalGraph V := ⟨fun | .hammering => ∅ | .flat => {.hammering}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .hammering => const (G := graph) false
      | .flat => deterministic (fun ρ => ρ ⟨.hammering, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .hammering => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .flat => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem hammer_sufficient_for_flat :
    sufficient model varList Valuation.empty 1 .hammering .flat := by
  unfold sufficient; rfl

theorem hammer_completes_flat :
    completes model varList Valuation.empty 1 .hammering .flat := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end HammerFlat

namespace KickIntoField

inductive V | kicking | in_field
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .in_field]

def graph : CausalGraph V := ⟨fun | .kicking => ∅ | .in_field => {.kicking}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .in_field => deterministic (fun ρ => ρ ⟨.kicking, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .in_field => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem kick_sufficient_for_field :
    sufficient model varList Valuation.empty 1 .kicking .in_field := by
  unfold sufficient; rfl

theorem kick_completes_field :
    completes model varList Valuation.empty 1 .kicking .in_field := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end KickIntoField

namespace LaughSilly

inductive V | laughing | silly
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.laughing, .silly]

def graph : CausalGraph V := ⟨fun | .laughing => ∅ | .silly => {.laughing}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .laughing => const (G := graph) false
      | .silly => deterministic (fun ρ => ρ ⟨.laughing, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .laughing => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .silly => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem laugh_sufficient_for_silly :
    sufficient model varList Valuation.empty 1 .laughing .silly := by
  unfold sufficient; rfl

end LaughSilly

namespace FreezeSolid

/-! "The river froze solid" — noncausative resultative. Empty graph
    captures the absence of constructional CAUSE. -/

inductive V | freezing | solid
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.freezing, .solid]

/-- Empty graph: no causal relations (noncausative resultative). -/
def graph : CausalGraph V := ⟨fun _ => ∅⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun _ => const (G := graph) false }

noncomputable instance : SEM.IsDeterministic model where
  mech_det _ := inferInstanceAs (Mechanism.IsDeterministic (const _))

/-- Freezing is NOT sufficient for solidity in the empty-edge model. -/
theorem freeze_not_sufficient :
    ¬ sufficient model varList Valuation.empty 1 .freezing .solid := by
  intro h
  unfold sufficient at h
  exact Bool.false_ne_true (Option.some.inj h)

end FreezeSolid

namespace DrinkTeapotDry

/-! "Drink the teapot dry" — passive chain: drinking → tea_removal →
    teapot_dry. Tight because tea_removal has no independent source. -/

inductive V | drinking | tea_removal | teapot_dry
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.drinking, .tea_removal, .teapot_dry]

def graph : CausalGraph V := ⟨fun
  | .drinking => ∅
  | .tea_removal => {.drinking}
  | .teapot_dry => {.tea_removal}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .drinking => const (G := graph) false
      | .tea_removal => deterministic (fun ρ => ρ ⟨.drinking, by simp [graph]⟩)
      | .teapot_dry => deterministic (fun ρ => ρ ⟨.tea_removal, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .drinking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .tea_removal => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .teapot_dry => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Tight despite being a chain: removing drinking leaves tea_removal
    undetermined (no independent source), so teapot_dry doesn't fire. -/
theorem drink_completes_dry :
    completes model varList Valuation.empty 1 .drinking .teapot_dry := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end DrinkTeapotDry

namespace KickDoorDirect

inductive V | kicking | door_open
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .door_open]

def graph : CausalGraph V := ⟨fun | .kicking => ∅ | .door_open => {.kicking}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .door_open => deterministic (fun ρ => ρ ⟨.kicking, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .door_open => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem kick_door_completes_direct :
    completes model varList Valuation.empty 1 .kicking .door_open := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end KickDoorDirect

namespace KickDoorViaBall

/-! NOT-tight case: kick → ball_motion → door_open + ball_energy →
    ball_motion. Ball has its own independent energy source, so kicking
    is not necessary. Witnesses @cite{levin-2019}'s prediction that
    intervening causers with independent energy break tightness. -/

inductive V | kicking | ball_motion | ball_energy | door_open
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .ball_energy, .ball_motion, .door_open]

def graph : CausalGraph V := ⟨fun
  | .kicking => ∅
  | .ball_energy => ∅
  | .ball_motion => {.kicking, .ball_energy}
  | .door_open => {.ball_motion}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .ball_energy => const (G := graph) false
      | .ball_motion => deterministic (fun ρ =>
          ρ ⟨.kicking, by simp [graph]⟩ || ρ ⟨.ball_energy, by simp [graph]⟩)
      | .door_open => deterministic (fun ρ => ρ ⟨.ball_motion, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .ball_energy => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .ball_motion => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .door_open => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def ballHasEnergyBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .ball_energy true

/-- NOT tight: removing kicking still allows ball_energy → ball_motion
    → door_open. The kick is not necessary. -/
theorem kick_door_via_ball_not_tight :
    ¬ completes model varList ballHasEnergyBg 1 .kicking .door_open := by
  intro ⟨_, hNot⟩
  apply hNot
  rfl

end KickDoorViaBall

/-! ## Agreement with Boolean flags -/

/-- isCausative ↔ hasCause — derived from the subconstruction, not stipulated. -/
theorem causative_iff_has_cause (sc : ResultativeSubconstruction) :
    sc.isCausative = sc.constructionalDesc.hasCause := by
  cases sc <;> rfl

/-- All causative entries in the data have CAUSE. -/
theorem causativeResultativeHasCAUSE :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subeventRelation == .means
    )).all (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-! ## CC-selection (Baglini & Bar-Asher @cite{baglini-bar-asher-siegal-2025})

Resultatives select via completion of a sufficient set (the verbal
subevent must be the final condition that makes the result inevitable). -/

/-- Resultatives select via completion (like CoS verbs). -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-! ## Causative bridge: derived from SubeventRelation + CAUSE

The resultative's `Causative` is `.make`, but DERIVED from two
independently-motivated properties:

1. **MEANS relation** (@cite{goldberg-jackendoff-2004}): the verbal
   subevent is the means by which the constructional subevent is brought
   about. MEANS ↔ causal sufficiency.
2. **CAUSE in constructional subevent**: causative subconstructions have
   `hasCause = true`.

MEANS + CAUSE → sufficiency. Among sufficiency builders, `.make` is
uniquely identified by lacking coercion (`.force`) and barrier-removal
(`.enable`). -/

/-- Derive the Causative from subevent relation + constructional desc
    + force-dynamic properties. -/
def deriveCausativeBuilder (rel : SubeventRelation) (desc : SubeventDesc)
    (coercive : Bool := false) (permissive : Bool := false) :
    Option Causative :=
  match rel, desc.hasCause with
  | .means, true =>
    some (if coercive then .force
          else if permissive then .enable
          else .make)
  | _, _ => none

/-- `.make` is the unique builder asserting neutral sufficiency. -/
theorem make_unique_neutral_sufficiency (b : Causative)
    (hs : b.assertsSufficiency = true)
    (hc : b.isCoercive = false)
    (hp : b.isPermissive = false) :
    b = .make := by
  cases b <;> simp_all [Causative.assertsSufficiency,
    Causative.isCoercive, Causative.isPermissive]

/-- Neutral derivation yields `.make`. -/
theorem neutral_derives_make (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc = some .make := by
  simp [deriveCausativeBuilder, h]

/-- Coercive derivation yields `.force`. -/
theorem coercive_derives_force (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (coercive := true) = some .force := by
  simp [deriveCausativeBuilder, h]

/-- Permissive derivation yields `.enable`. -/
theorem permissive_derives_enable (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (permissive := true) = some .enable := by
  simp [deriveCausativeBuilder, h]

/-- Coercive takes priority over permissive (force > enable). -/
theorem coercive_overrides_permissive (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (coercive := true) (permissive := true) =
      some .force := by
  simp [deriveCausativeBuilder, h]

/-- For any causative subconstruction with MEANS relation,
    the derived builder is `.make`. -/
theorem causative_means_derives_make (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    deriveCausativeBuilder .means sc.constructionalDesc = some .make := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Noncausative subconstructions don't derive a Causative. -/
theorem noncausative_no_builder (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false)
    (coercive permissive : Bool) :
    deriveCausativeBuilder .means sc.constructionalDesc coercive permissive = none := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Non-MEANS relations never derive a Causative. -/
theorem non_means_no_builder (desc : SubeventDesc) (coercive permissive : Bool) :
    deriveCausativeBuilder .result desc coercive permissive = none ∧
    deriveCausativeBuilder .instance_ desc coercive permissive = none ∧
    deriveCausativeBuilder .coOccurrence desc coercive permissive = none := by
  simp [deriveCausativeBuilder]

/-- When `deriveCausativeBuilder` succeeds, the resulting builder asserts
    causal sufficiency. -/
theorem derived_asserts_sufficiency (rel : SubeventRelation) (desc : SubeventDesc)
    (coercive permissive : Bool)
    (b : Causative) (h : deriveCausativeBuilder rel desc coercive permissive = some b) :
    b.assertsSufficiency = true := by
  unfold deriveCausativeBuilder at h
  split at h
  · simp only [Option.some.injEq] at h
    cases coercive <;> cases permissive <;>
      simp_all <;> subst h <;> rfl
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

/-- Three independent paths converge on `.make`. -/
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
    Causative.cause ≠ resultativeCausativeBuilder := by
  exact ⟨rfl, rfl, by decide⟩

/-! ## Aspect: activity + bounded RP → accomplishment -/

/-- Bounded RP telicizes activity. -/
theorem resultativeTelicizes :
    activityProfile.telicize.toVendlerClass = .accomplishment :=
  telicize_activity

/-- The resultative construction's aspect shift. -/
theorem resultativeAspectShift :
    resultativeVendlerClass .bounded = .accomplishment :=
  rfl

theorem resultative_aspect_agrees_with_telicize :
    resultativeVendlerClass .bounded =
    activityProfile.telicize.toVendlerClass := by
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

/-! ## Müller Decomposability -/

/-- All four subconstructions are fully compositional. -/
theorem allResultativesFullyCompositional :
    resultativeFamily.all (λ c =>
      isFullyCompositional c.construction) = true := by
  native_decide

/-- Causative subconstructions decompose like the parent resultative. -/
theorem causative_decompose_like_parent :
    decompose causativePropertyConstruction = decompose resultative ∧
    decompose causativePathConstruction = decompose resultative := by
  constructor <;> native_decide

/-- Noncausative subconstructions decompose into fewer combination steps. -/
theorem noncausative_fewer_steps :
    (decompose noncausativePropertyConstruction).length <
    (decompose causativePropertyConstruction).length ∧
    (decompose noncausativePathConstruction).length <
    (decompose causativePathConstruction).length := by
  constructor <;> native_decide

theorem decomposition_reflects_transitivity :
    (decompose causativePropertyConstruction).length = 3 ∧
    (decompose noncausativePropertyConstruction).length = 2 := by
  constructor <;> native_decide

/-! ## Cross-linguistic Resultative Parameters (@cite{tay-2024}) -/

section CrossLinguistic

inductive ResultativeRealization where
  | syntacticAdjunct
  | verbCompound
  | deComplement
  deriving DecidableEq, Repr

inductive ResultOrientation where
  | objectOriented
  | subjectOriented
  deriving DecidableEq, Repr

inductive PhaseComplement where
  | dao
  | wan
  | hao
  | diao
  | zhu
  deriving DecidableEq, Repr

def PhaseComplement.cosType : PhaseComplement → CoSType
  | .dao  => .inception
  | .wan  => .cessation
  | .hao  => .inception
  | .diao => .inception
  | .zhu  => .continuation

theorem inceptive_phases_share_presup :
    PhaseComplement.dao.cosType = .inception ∧
    PhaseComplement.hao.cosType = .inception ∧
    PhaseComplement.diao.cosType = .inception := ⟨rfl, rfl, rfl⟩

theorem phase_complements_cover_cos_types :
    PhaseComplement.dao.cosType = .inception ∧
    PhaseComplement.wan.cosType = .cessation ∧
    PhaseComplement.zhu.cosType = .continuation := ⟨rfl, rfl, rfl⟩

end CrossLinguistic

end Semantics.Causation.Resultatives
