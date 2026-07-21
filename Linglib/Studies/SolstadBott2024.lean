import Linglib.Semantics.Presupposition.Context
import Linglib.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Semantics.Presupposition.ProjectiveContent
import Linglib.Studies.SolstadBott2022
import Linglib.Fragments.German.Predicates
import Linglib.Data.Generalizations.Projectivity
import Linglib.Studies.TonhauserBeaverDegen2018

/-!
# [solstad-bott-2024]: Cataphoric resolution of projective content — occasion verbs

[solstad-bott-2024] [tonhauser-beaver-roberts-simons-2013] [tonhauser-beaver-degen-2018]
[heim-1983] [schlenker-2008] [schlenker-2009]

Three rating experiments (*S&P* 17:11) establish **occasion verbs** (German
*bestrafen* "punish", *kritisieren* "criticise", *danken* "thank", …) as a new
class of projective-content trigger. Occasion verbs are interpersonal action
verbs whose agent acts in response to a presupposed prior eventuality — the
**occasion**. "The judge punished Peter" asserts a punishing action and
presupposes that Peter did something wrong.

This file formalizes the paper's **structural claims**, not its statistics:

* **Projectivity** (Exps 1–2, Block 2): occasion verbs pattern with established
  triggers — high projectivity, low at-issueness — and separate from psych verbs.
  The per-expression means feed `Generalizations.Projectivity` (see below).
* **Cataphoric resolution** (Exps 1–2, Block 1): occasion verbs are felicitous
  in both *m*-anaphoric and *m*-cataphoric contexts (the resolving material may
  precede *or* follow the trigger). This is unique to occasion verbs among the
  triggers tested. Effect sizes (e.g. neutral→anaphoric β ≈ 22, neutral→cataphoric
  β ≈ 18 on the 0–100 scale, both p < .001) are reported in prose, per project
  convention; the qualitative claim is encoded by `ContextPolarity`.
* **Symmetric filtering** (Exp 3): in conjoined conditional antecedents, occasion
  verbs filter regardless of conjunct order (trigger-first ≈ trigger-last,
  |t| ≈ 1), whereas factive/aspectual ([mandelkern-etal-2020]) triggers filter
  only left-to-right (trigger-last ≪ trigger-first, |t| ≈ 16). Encoded by
  `FilteringDirection`.

## Tonhauser et al. (2013) classification

Occasion verbs are **Class C** (SCF=no, OLE=yes), with factives (*know*) and
change-of-state verbs (*stop*), but are distinguished by bidirectional context
resolution and symmetric filtering — "a cage of their own".

## Main declarations

* `FilteringDirection`, `ContextPolarity` — the typed axes that encode the
  cataphoric-resolution and symmetric-filtering findings.
* `occasionVerbProfile` vs `factiveProfile` — `cage_of_their_own` proves they
  differ despite sharing Class C.
* `occasionEventPhase`, `symmetricLocalCtxAntecedent` — the presupposition as an
  `EventPhase` and the Heim/Schlenker filtering models.
* `gpp_underpredicts_above_diagonal` — occasion verbs project *above* the GPP
  diagonal (the mirror of [tonhauser-beaver-degen-2018]'s `establish`).
-/

namespace SolstadBott2024

open Semantics.Presupposition.OntologicalPreconditions
open Semantics.Presupposition.ProjectiveContent
open SolstadBott2022
open German.Predicates
open Semantics.Presupposition
open Semantics.Presupposition.Context
open CommonGround
open Core.Order (Rat01)
open Generalizations.Projectivity

/-! ### Filtering direction and context resolution -/

/-- Filtering direction for presupposition triggers. [solstad-bott-2024] Exp 3
    shows occasion verbs allow symmetric filtering, while factives and
    change-of-state verbs only allow left-to-right filtering. -/
inductive FilteringDirection where
  | leftToRight
  | symmetric
  deriving DecidableEq, Repr

/-- Context-resolution direction, refining
    [tonhauser-beaver-roberts-simons-2013]'s "m-positive" by where the resolving
    material can appear. -/
inductive ContextPolarity where
  | mNeutral
  | mAnaphoric
  | mCataphoric
  deriving DecidableEq, Repr

/-! ### Occasion verbs are Class C triggers -/

/-- Occasion verbs are Class C in the [tonhauser-beaver-roberts-simons-2013]
    taxonomy: SCF=no (can be informative), OLE=yes (attributed to attitude holder). -/
theorem occasion_verb_is_classC :
    ProjectiveTrigger.occasion_verb.toClass = .classC := rfl

/-- Class C triggers do not require prior establishment in context. -/
theorem classC_no_scf : ProjectiveClass.classC.scf = .noRequires := rfl

/-- Class C triggers have obligatory local effect under belief embedding. -/
theorem classC_has_ole : ProjectiveClass.classC.ole = .obligatory := rfl

/-- Occasion verbs pattern with *stop* and *know* — all Class C. -/
theorem occasion_verb_patterns_with_stop_know :
    ProjectiveTrigger.occasion_verb.toClass =
      ProjectiveTrigger.stop_prestate.toClass ∧
    ProjectiveTrigger.occasion_verb.toClass =
      ProjectiveTrigger.know_complement.toClass := ⟨rfl, rfl⟩

/-! ### German occasion-verb inventory -/

/-- The 16 German occasion verbs tested in [solstad-bott-2024], derived from
    Fragment entries with the `.occasion` sense tag. -/
def occasionVerbEntries : List GermanVerbEntry :=
  [bestrafen, belohnen, loben, kritisieren, danken,
   verklagen, gratulieren, zurechtweisen,
   anzeigen, auszeichnen, belangen, ehren, entlassen,
   raechen, revanchieren, zurVerantwortungZiehen]

/-- 16 occasion verbs were tested. -/
theorem occasion_verb_count : occasionVerbEntries.length = 16 := by decide

/-- All entries in the occasion-verb list use the `.occasion` sense tag. -/
theorem all_occasion_entries_tagged :
    occasionVerbEntries.all (·.senseTag == .occasion) = true := by decide

/-- All entries in the occasion-verb list are soft presupposition triggers. -/
theorem all_occasion_entries_soft_trigger :
    occasionVerbEntries.all (·.presupType == some .softTrigger) = true := by decide

/-! ### "A cage of their own"

The cataphoric-resolution and symmetric-filtering findings are encoded as typed
profile fields, so the paper's qualitative result — occasion verbs differ from
factives despite sharing Class C — is a theorem about the profiles rather than a
threshold on regression estimates. -/

/-- Profile of a trigger across the dimensions tested by [solstad-bott-2024]. -/
structure TriggerProfile where
  projectiveClass : ProjectiveClass
  contextPolarities : List ContextPolarity
  filteringDirection : FilteringDirection
  deriving DecidableEq, Repr

/-- Occasion verbs: Class C, bidirectional (anaphoric + cataphoric) resolution,
    symmetric filtering. -/
def occasionVerbProfile : TriggerProfile where
  projectiveClass := .classC
  contextPolarities := [.mAnaphoric, .mCataphoric]
  filteringDirection := .symmetric

/-- Factives/aspectuals: Class C, no SCF constraint (neutral ≈ anaphoric in
    Exp 1), left-to-right filtering only ([mandelkern-etal-2020]). -/
def factiveProfile : TriggerProfile where
  projectiveClass := .classC
  contextPolarities := []
  filteringDirection := .leftToRight

/-- Occasion verbs share Class C with factives. -/
theorem same_projective_class :
    occasionVerbProfile.projectiveClass = factiveProfile.projectiveClass := rfl

/-- Despite sharing Class C, occasion verbs differ from factives — the "cage of
    their own" result. -/
theorem cage_of_their_own : occasionVerbProfile ≠ factiveProfile := by decide

/-- The distinguishing features are filtering direction and bidirectional
    resolution, not the projective class. -/
theorem distinguished_by_filtering_not_class :
    occasionVerbProfile.filteringDirection ≠ factiveProfile.filteringDirection ∧
    occasionVerbProfile.contextPolarities ≠ factiveProfile.contextPolarities := by
  decide

/-! ### Occasion-verb presupposition as `EventPhase` -/

/-- Model an occasion verb's presupposition as an `EventPhase`. "The judge
    punished Peter": precondition = Peter did something wrong (the occasion);
    eventOccurs = the punishing action; consequence = Peter is punished. The
    precondition projects. -/
def occasionEventPhase {W : Type*}
    (occasion engagement outcome : W → Prop) : EventPhase W where
  precondition := occasion
  eventOccurs := engagement
  consequence := outcome

/-- The occasion presupposition projects through negation: "The judge didn't
    punish Peter" still presupposes Peter did something wrong. -/
theorem occasion_presup_projects {W : Type*}
    (occasion engagement outcome : W → Prop) :
    (affirmative (occasionEventPhase occasion engagement outcome)).presupposition =
      (negative (occasionEventPhase occasion engagement outcome)).presupposition := rfl

/-! ### Asymmetric filtering ([heim-1983]) -/

/-- Under Heim's asymmetric filtering, the local context at a conditional
    antecedent is the global context, so an occasion verb there projects.
    "If the judge punishes Peter, he was convicted": at "punishes" the
    presupposition is not entailed → projects. -/
theorem heim_antecedent_projects {W : Type*}
    (c : ContextSet W) (trigger _consequence : PartialProp W)
    (h : ∃ w, c w ∧ ¬trigger.presup w) :
    presupProjects c trigger := by
  obtain ⟨w, hw_in, hpresup_false⟩ := h
  intro hfilter
  exact hpresup_false (hfilter hw_in)

/-! ### Symmetric filtering ([schlenker-2008], [schlenker-2009]) -/

/-- Symmetric filtering makes the consequent's assertion available to the local
    context at the antecedent. -/
def symmetricLocalCtxAntecedent {W : Type*}
    (c : ContextSet W) (consequent : PartialProp W) : ContextSet W :=
  ContextSet.update c consequent.assertion

/-- When the consequent entails the occasion presupposition, symmetric filtering
    predicts it is filtered. -/
theorem symmetric_filters_when_consequent_entails {W : Type*}
    (c : ContextSet W) (trigger consequent : PartialProp W)
    (h : ∀ w, c w → consequent.assertion w → trigger.presup w) :
    presupSatisfied (symmetricLocalCtxAntecedent c consequent) trigger := by
  intro w hw
  have ⟨hw_in, hcons⟩ := hw
  exact h w hw_in hcons

/-! ### Bridge to [solstad-bott-2022]

Occasion verbs are the agent-evocator class of [solstad-bott-2022]: the same
underspecified eventuality that drives the NP2 implicit-causality bias is the
projecting occasion. The IC bias and the presupposition are distinct — occasion
verbs and experiencer-stimulus psych verbs share the NP2 bias, yet occasion
verbs are far more projective (Exp 2: .69 vs .52; see the prediction section). -/

/-- Occasion verbs are the agent-evocator class; their predicted IC bias is NP2. -/
theorem occasion_is_agent_evocator_bias :
    VerbClass.agentEvocator.predictedBias = .np2 := rfl

/-- IC bias and projectivity dissociate: occasion verbs share the NP2 bias with
    experiencer-stimulus psych verbs, yet (by the Exp 2 data pooled in
    `Generalizations.Projectivity`) project more strongly. The shared bias is
    structural; the projectivity gap is empirical. -/
theorem ic_bias_shared_with_expStim :
    VerbClass.agentEvocator.predictedBias = VerbClass.expStim.predictedBias := rfl

/-! ### Predicting against the data

The Exp 1–2 projectivity/at-issueness means are artifact-sourced rows in
`Data.Examples.SolstadBott2024`, pooled into `Generalizations.Projectivity.allData`
alongside [tonhauser-beaver-degen-2018]. Occasion verbs (proj .79/.69,
at-issueness .32/.35) sit in the high-projectivity / low-at-issueness quadrant —
patterning with established triggers and **above** the GPP diagonal (they project
*more* than their at-issueness predicts, the mirror of `establish`). Psychological
verbs (SE .54/.52, ES .52/.46) are midrange, off the GPP pattern. These per-row
facts are computed over `allData`; the provable content is the account's
systematic error. -/

/-- Content that projects above its not-at-issueness — occasion verbs — is
    *under*-predicted by the GPP's tight reading (`gppProjection`). The mirror of
    [tonhauser-beaver-degen-2018]'s below-diagonal `establish`. -/
theorem gpp_underpredicts_above_diagonal (d : ProjectionDatum)
    (h : d.notAtIssueness.val < d.projectivity.val) :
    (TonhauserBeaverDegen2018.gppProjection d.atIssueness).val < d.projectivity.val := by
  simp only [TonhauserBeaverDegen2018.gppProjection,
    ProjectionDatum.notAtIssueness, Rat01.compl_val] at *
  linarith

end SolstadBott2024
