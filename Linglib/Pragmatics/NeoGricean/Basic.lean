import Mathlib.Data.Finset.Basic
import Linglib.Semantics.Entailment.AsymStronger
import Linglib.Core.Logic.Modal.Defs

/-!
# Neo-Gricean pragmatics: epistemic states and the Standard Recipe
[sauerland-2004] [geurts-2010]

The epistemic layer of Neo-Gricean implicature: an `EpistemicState` (the
worlds compatible with the speaker's knowledge) with `knows` (K) and
`possible` (P) realized as `box`/`diamond` over a serial accessibility
from `Core.Logic.Modal`, and the Standard Recipe run over the derived
three-way `BeliefState` classification.

[sauerland-2004] distinguishes **primary implicatures** ¬Kψ from
**secondary implicatures** K¬ψ, a secondary arising only when K¬ψ is
consistent with the assertion together with all primary implicatures.
The epistemic modalization ¬Kψ goes back to [soames-1982] and
[horn-1989]; the competence step Kψ ∨ K¬ψ strengthening primaries to
secondaries is formalized by [sauerland-2004], [vanrooij-schulz-2004],
and [spector-2006]; [geurts-2010] is the textbook presentation.

This file provides the modal substrate and the recipe over the
classification it induces. The full Sauerland derivation — computing the
secondary implicatures jointly consistent with the assertion and the
primary set — is TODO; `secondary_blocked_if_possible` and
`primary_possibility` are instances of K/P duality, not that consistency
check.

The asymmetric-entailment primitive characterizing primary-implicature
alternatives is `asymStrongerOn` in `Semantics/Entailment/AsymStronger.lean`;
a consumer writes `alts.filter (asymStrongerOn e.possible · φ)` directly.
For the graded counterpart of competence (the RSA knowledgeability
parameter) see `Pragmatics/RSA/`; `Studies/Franke2011/RSABridge.lean`
relates RSA speakers to IBR argmax behaviour.
-/

namespace NeoGricean

open Core.Logic.Modal (AccessRel box diamond IsSerial)

variable {W : Type*}

/-! ### Epistemic states and the K/P operators -/

/-- An epistemic state: the (nonempty, finite) set of worlds compatible
with the speaker's knowledge. -/
structure EpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's knowledge -/
  possible : Finset W
  /-- Non-empty (speaker knows something is true) -/
  nonempty : possible.Nonempty

/-- K operator: the speaker knows φ iff φ holds in all epistemically
possible worlds. -/
def knows (e : EpistemicState W) (φ : W → Prop) : Prop :=
  ∀ w ∈ e.possible, φ w

instance (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] :
    Decidable (knows e φ) :=
  inferInstanceAs (Decidable (∀ w ∈ e.possible, φ w))

/-- P operator: the speaker considers φ possible. -/
def possible (e : EpistemicState W) (φ : W → Prop) : Prop :=
  ∃ w ∈ e.possible, φ w

instance (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] :
    Decidable (possible e φ) :=
  inferInstanceAs (Decidable (∃ w ∈ e.possible, φ w))

/-! ### `K`/`P` as restricted modality

`knows`/`possible` are `box`/`diamond` over the (world-independent)
epistemic accessibility `accessFrom e`, serial because `e.possible` is
nonempty. The epistemic square of opposition is
`Core.Logic.Modal.modalSquare (accessFrom e)` with `modalSquare_relations`
discharged by this `IsSerial` instance. -/

/-- Epistemic accessibility: from any world, the speaker's live possibilities. -/
def accessFrom (e : EpistemicState W) : AccessRel W := fun _ w' => w' ∈ e.possible

instance (e : EpistemicState W) : IsSerial (accessFrom e) := ⟨fun _ => e.nonempty⟩

/-- `K` is `□` over epistemic accessibility. -/
theorem knows_eq_box (e : EpistemicState W) (φ : W → Prop) (w : W) :
    knows e φ = box (accessFrom e) φ w := rfl

/-- `P` is `◇` over epistemic accessibility. -/
theorem possible_eq_diamond (e : EpistemicState W) (φ : W → Prop) (w : W) :
    possible e φ = diamond (accessFrom e) φ w := rfl

/-- Epistemic duality: ¬K¬φ ↔ Pφ — the box–diamond duality underlying
the modal square of opposition (`Core.Logic.Modal.modalSquare_relations`). -/
theorem duality (e : EpistemicState W) (φ : W → Prop) :
    ¬ knows e (fun w => ¬ φ w) ↔ possible e φ := by
  simp only [knows, possible, not_forall, not_not, exists_prop]

/-- Secondary implicature: the speaker knows the alternative is false. -/
def hasSecondaryImplicature (e : EpistemicState W) (ψ : W → Prop) : Prop :=
  knows e (fun w => ¬ ψ w)

instance (e : EpistemicState W) (ψ : W → Prop) [DecidablePred ψ] :
    Decidable (hasSecondaryImplicature e ψ) :=
  inferInstanceAs (Decidable (∀ w ∈ e.possible, ¬ ψ w))

/-- If ψ is epistemically possible, K¬ψ fails. An instance of `duality`;
the substrate fact used when checking a candidate secondary implicature
against the speaker's state. -/
theorem secondary_blocked_if_possible (e : EpistemicState W) (ψ : W → Prop) :
    possible e ψ → ¬ hasSecondaryImplicature e ψ := by
  rintro ⟨w, hw, hψ⟩ hknow
  exact hknow w hw hψ

/-- A primary implicature ¬Kψ entails that ¬ψ is epistemically possible.
An instance of `duality`. -/
theorem primary_possibility (e : EpistemicState W) (ψ : W → Prop) :
    ¬ knows e ψ → possible e (fun w => ¬ ψ w) := by
  intro h
  simp only [knows, not_forall] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw.1, hw.2⟩

/-! ### The three-way belief-state classification

`BeliefState` is the decidable classification of a speaker's attitude
toward one alternative ψ: `Bel_S(ψ)`, `Bel_S(¬ψ)`, or no opinion.
`EpistemicState.beliefState` grounds the enum in the modal substrate, so
the Standard Recipe below is a projection of K/P reasoning, not a
parallel encoding. -/

/-- Speaker's belief state about a proposition ψ: belief `Bel_S(ψ)`,
disbelief `Bel_S(¬ψ)`, or no opinion `¬Bel_S(ψ) ∧ ¬Bel_S(¬ψ)`. -/
inductive BeliefState where
  | belief
  | disbelief
  | noOpinion
  deriving DecidableEq, Repr

/-- Classify an epistemic state by its attitude toward ψ: `Kψ` is
belief, `K¬ψ` disbelief, anything else no opinion. -/
def EpistemicState.beliefState (e : EpistemicState W) (ψ : W → Prop)
    [DecidablePred ψ] : BeliefState :=
  if knows e ψ then .belief
  else if hasSecondaryImplicature e ψ then .disbelief
  else .noOpinion

/-- Competence: the speaker knows whether ψ, `Bel_S(ψ) ∨ Bel_S(¬ψ)`. -/
def competent : BeliefState → Bool
  | .belief => true
  | .disbelief => true
  | .noOpinion => false

/-- Non-belief `¬Bel_S(ψ)` — the weak (primary) implicature. -/
def nonBelief : BeliefState → Bool
  | .belief => false
  | .disbelief => true
  | .noOpinion => true

/-- Strong (secondary) implicature `Bel_S(¬ψ)`. -/
def strongImpl : BeliefState → Bool
  | .belief => false
  | .disbelief => true
  | .noOpinion => false

/-- The classification is faithful: `disbelief` holds exactly when the
secondary implicature K¬ψ does. -/
theorem beliefState_disbelief_iff (e : EpistemicState W) (ψ : W → Prop)
    [DecidablePred ψ] (h : ¬ knows e ψ) :
    e.beliefState ψ = .disbelief ↔ hasSecondaryImplicature e ψ := by
  simp only [EpistemicState.beliefState, if_neg h]
  by_cases hs : hasSecondaryImplicature e ψ <;> simp [hs]

/-- Competence strengthening: `¬Bel_S(ψ) ∧ (Bel_S(ψ) ∨ Bel_S(¬ψ)) → Bel_S(¬ψ)`. -/
theorem competence_strengthening {b : BeliefState}
    (hweak : nonBelief b = true) (hcomp : competent b = true) :
    strongImpl b = true := by
  cases b <;> simp_all [nonBelief, competent, strongImpl]

/-- A weak implicature can hold without the strong one (incompetent speaker). -/
theorem weak_without_strong :
    ∃ b : BeliefState, nonBelief b = true ∧ strongImpl b = false :=
  ⟨.noOpinion, by decide⟩

/-- `Bel_S(¬ψ) → ¬Bel_S(ψ)`. -/
theorem strong_implies_weak {b : BeliefState} (h : strongImpl b = true) :
    nonBelief b = true := by
  cases b <;> simp_all [strongImpl, nonBelief]

/-- `Bel_S(¬ψ) → Bel_S(ψ) ∨ Bel_S(¬ψ)`. -/
theorem strong_implies_competent {b : BeliefState} (h : strongImpl b = true) :
    competent b = true := by
  cases b <;> simp_all [strongImpl, competent]

/-! ### Running the recipe

`processAlternative` applies the Standard Recipe to one alternative,
gated by whether the hearer assumes competence. The three `outcome_*`
theorems are [geurts-2010]'s outcome typology. -/

/-- Outcome of processing one alternative: the inferred belief state,
whether the weak implicature holds, whether competence was assumed
(and consistent), and whether the strong implicature was derived. -/
structure ImplicatureProcessing where
  /-- The belief state inferred -/
  beliefState : BeliefState
  /-- Whether weak implicature ¬Bel_S(ψ) holds -/
  weakHolds : Bool
  /-- Whether competence was assumed -/
  competenceAssumed : Bool
  /-- Whether strong implicature Bel_S(¬ψ) was derived -/
  strongDerived : Bool
  deriving Repr

/-- Run the Standard Recipe on one alternative under a competence
assumption. -/
def processAlternative (assumeCompetence : Bool) (b : BeliefState) :
    ImplicatureProcessing :=
  { beliefState := b
  , weakHolds := nonBelief b
  , competenceAssumed := assumeCompetence && competent b
  , strongDerived := assumeCompetence && strongImpl b
  }

/-- Outcome i (undecided): without the competence assumption, only the
weak implicature arises. -/
theorem outcome_i_undecided {b : BeliefState} (hne : b ≠ .belief) :
    (processAlternative false b).weakHolds = true ∧
    (processAlternative false b).strongDerived = false := by
  cases b <;> simp_all [processAlternative, nonBelief]

/-- Outcome ii (strong): competence assumed and consistent — the strong
implicature is derived. -/
theorem outcome_ii_strong :
    (processAlternative true .disbelief).weakHolds = true ∧
    (processAlternative true .disbelief).competenceAssumed = true ∧
    (processAlternative true .disbelief).strongDerived = true := by
  decide

/-- Outcome iii (incompetent): the speaker has no opinion, so the
competence assumption fails and only the weak implicature survives. -/
theorem outcome_iii_incompetent :
    (processAlternative true .noOpinion).weakHolds = true ∧
    (processAlternative true .noOpinion).competenceAssumed = false ∧
    (processAlternative true .noOpinion).strongDerived = false := by
  decide

end NeoGricean
