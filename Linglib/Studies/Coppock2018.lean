import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Hom.CompleteLattice
import Linglib.Core.Logic.Modal.Defs
import Linglib.Core.Logic.Truth3
import Linglib.Semantics.Presupposition.Basic

/-!
# Coppock 2018: outlook-based semantics
[coppock-2018]

[coppock-2018]'s relativism for statements of opinion: *outlooks* — refinements of worlds
that settle matters of opinion as well as fact — **replace** possible worlds as circumstances
of evaluation, rather than supplementing them with a judge as in world-judge relativism
([lasersohn-2005]). A proposition is a function from outlooks to three truth values
(`Prop3 Ω`, with [coppock-2018]'s Weak Kleene connectives available as `Truth3.meetWeak`/
`Truth3.joinWeak`/`Truth3.neg`); it is *objective* when its truth value never splits within
a world's refinement class, *discretionary* when it does, and *strongly discretionary* when
it splits within every world's class. Faultless disagreement ([kolbel-2003]) then falls out:
two agents can accept and reject the same strongly discretionary proposition at one outlook
(genuine disagreement) while neither violates the norm of accuracy (no world makes such a
proposition objectively false). The subjective attitude verb *tycka* 'think[opinion]'
presupposes strong discretionariness of its complement relative to the common ground; the
paper's ∂-operator rendering of that presupposition is played here by the project-canonical
`PartialProp`.

The formal fragment's syntax (types, translations `⤳`), the context-set parameter sequence,
and the §4 pragmatics (assertion-as-proposal, seeking a common outlook) are not modelled.
`Studies/Kubota2026.lean` borrows the outlook *term* for its two-layered outlook-marker
denotation; the apparatus here is the paper's own, where outlook-relativity is a property of
at-issue discretionary content. [kennedy-willer-2016]'s counterstance contingency appears
via the paper's translation: radically counterstance-contingent = strongly discretionary.

## Main definitions

* `Objective`, `objective_iff_fiberInvariant`, `objective_iff_preimage_image` —
  set-of-outlooks propositions (§3.1): objective = union of refinement classes =
  fiber-invariant = saturated under the refinement map. `objectiveSubalgebra` bundles the
  objective propositions as a `BooleanSubalgebra` of the powerset of `Ω`, and
  `objectiveOrderIso` realizes the paper's note that it is isomorphic to the powerset of
  the worlds. The classification predicates carry `Decidable` instances for finite models.
* `Objective3`, `Discretionary3`, `StronglyDiscretionary3` — the revised three-valued
  classification, plus the information-state-relativized `ObjectiveIn`/`DiscretionaryIn`/
  `StronglyDiscretionaryIn`.
* `Accepts`, `Rejects`, `DisagreeAt`, `Opinionated` — doxastic accessibility as a binary
  relation on outlooks (§5's `R_a`), acceptance as the Kripke box (`Core.Logic.Modal.box`).
* `AtFault` — the norm of accuracy: asserting what is objectively false at the context world.
* `think`, `tycka` — the attitude verbs as `PartialProp`s: same assertion (doxastic
  acceptance), differing only in *tycka*'s strong-discretionariness presupposition.

## Main results

* `stronglyDiscretionary3_never_atFault` — a strongly discretionary proposition never puts
  its asserter at fault: the faultlessness half of faultless disagreement.
* `chili_disagreement`, `tasty_never_atFault` — the chili dialogue in a four-outlook model:
  genuine disagreement about *tasty* with neither party at fault; contrast `opera_atFault`
  (objective propositions do incur fault) and the *sexy linguist* hybrid (discretionary but
  not strongly so, hence world-level falsity).
* `think_tycka_same_assertion`, `tycka_presup_survives_neg` — *tycka* differs from *think*
  only in its presupposition, and that presupposition projects through negation.
* `tycka_undefined_of_objectiveIn` — an objective complement yields presupposition failure
  (the *"#I think[opinion] it's Tuesday"* effect).
* `stronglyDiscretionaryIn_discretionaryIn` — strong discretionariness entails
  discretionariness on nonempty restricted classes: [coppock-2018]'s translation of
  [kennedy-willer-2016]'s *find* (radical) vs *consider* (mere counterstance contingency).

## References

[coppock-2018] [kolbel-2003] [lasersohn-2005] [kennedy-willer-2016] [kleene-1952]
[beaver-krahmer-2001]
-/

namespace Coppock2018

open Core.Duality (Truth3 Prop3)
open Core.Logic.Modal (AccessRel box)
open Semantics.Presupposition (PartialProp)

variable {W Ω : Type*}

/-! ### Refinement and objectivity (§3.1)

Outlooks refine worlds: each outlook settles all the facts its world settles, plus matters
of opinion. The refinement structure is a map `ρ : Ω → W`; the *refinement class* of `w` is
the fiber `ρ ⁻¹' {w}`, so classes are automatically mutually non-overlapping and in
one-to-one correspondence with (inhabited fibers of) worlds — [coppock-2018]'s `∝`. -/

variable (ρ : Ω → W)

/-- A set-of-outlooks proposition is **objective** when it corresponds to a set of possible
worlds: a union of refinement classes, i.e. a preimage of a set of worlds. -/
def Objective (O : Set Ω) : Prop := ∃ V : Set W, O = ρ ⁻¹' V

/-- A **discretionary** proposition doesn't "color within the lines": it is not objective. -/
def Discretionary (O : Set Ω) : Prop := ¬ Objective ρ O

/-- Objectivity is invariance across each refinement class: an outlook proposition is
objective iff membership depends only on the refined world. -/
theorem objective_iff_fiberInvariant (O : Set Ω) :
    Objective ρ O ↔ ∀ o o', ρ o = ρ o' → (o ∈ O ↔ o' ∈ O) := by
  constructor
  · rintro ⟨V, rfl⟩ o o' h
    simp [Set.mem_preimage, h]
  · intro h
    refine ⟨ρ '' O, Set.Subset.antisymm (λ o ho => ⟨o, ho, rfl⟩) ?_⟩
    rintro o ⟨o', ho', heq⟩
    exact (h o' o heq).mp ho'

/-- Objectivity is *saturation* under the refinement map: `O` already contains every outlook
that shares a world with one of its members. -/
theorem objective_iff_preimage_image (O : Set Ω) :
    Objective ρ O ↔ ρ ⁻¹' (ρ '' O) = O := by
  refine ⟨λ h => Set.Subset.antisymm ?_ (Set.subset_preimage_image ρ O), λ h => ⟨ρ '' O, h.symm⟩⟩
  rintro o ⟨o', ho', heq⟩
  exact ((objective_iff_fiberInvariant ρ O).mp h o' o heq).mp ho'

/-- Only the kernel of the refinement map matters: objectivity is constancy on the classes
of `Setoid.ker ρ`. (The worlds beyond the fibers are inert — `W` could be replaced by
`Quotient (Setoid.ker ρ)` without loss.) -/
theorem objective_iff_ker_invariant (O : Set Ω) :
    Objective ρ O ↔ ∀ o o', Setoid.ker ρ o o' → (o ∈ O ↔ o' ∈ O) :=
  objective_iff_fiberInvariant ρ O

/-- The objective propositions form a Boolean subalgebra of the powerset of `Ω`: the image
of the powerset of `W` under `Set.preimage ρ` bundled as a bounded-lattice homomorphism, so
closure under `⊔`/`⊓`/`ᶜ` is inherited wholesale rather than proved operation-by-operation. -/
def objectiveSubalgebra : BooleanSubalgebra (Set Ω) :=
  .map (CompleteLatticeHom.setPreimage ρ).toBoundedLatticeHom ⊤

@[simp] theorem mem_objectiveSubalgebra {O : Set Ω} :
    O ∈ objectiveSubalgebra ρ ↔ Objective ρ O := by
  simp [objectiveSubalgebra, Objective, eq_comm]

/-- When every world is refined by some outlook — [coppock-2018]'s `∝` pairs each world with
an *inhabited* refinement class — the objective subalgebra is order-isomorphic to the
powerset of the worlds (and an order iso between Boolean algebras preserves the whole
Boolean structure). -/
def objectiveOrderIso (hρ : Function.Surjective ρ) :
    Set W ≃o objectiveSubalgebra ρ where
  toFun V := ⟨ρ ⁻¹' V, (mem_objectiveSubalgebra ρ).mpr ⟨V, rfl⟩⟩
  invFun O := ρ '' O.1
  left_inv V := Set.image_preimage_eq V hρ
  right_inv O := Subtype.ext
    ((objective_iff_preimage_image ρ O.1).mp ((mem_objectiveSubalgebra ρ).mp O.2))
  map_rel_iff' {V₁ V₂} :=
    Set.preimage_subset_preimage_iff (by rw [hρ.range_eq]; exact Set.subset_univ V₁)

/-! ### The revised three-valued classification (§3.5)

To carry presupposition, propositions become total functions from outlooks to `{T, F, #}` —
`Prop3 Ω`. The classification now quantifies over truth-value splits within refinement
classes. -/

/-- `p` is **objectively true at** `w`: true at every refinement of `w`. -/
def ObjectivelyTrueAt (p : Prop3 Ω) (w : W) : Prop := ∀ o, ρ o = w → p o = .true

/-- `p` is **objectively false at** `w`: false at every refinement of `w`. -/
def ObjectivelyFalseAt (p : Prop3 Ω) (w : W) : Prop := ∀ o, ρ o = w → p o = .false

/-- **Objective** (revised): no world has refinements assigning `p` both `T` and `F`. -/
def Objective3 (p : Prop3 Ω) : Prop :=
    ∀ o o', ρ o = ρ o' → p o = .true → p o' ≠ .false

/-- **Discretionary** (revised): some world has refinements assigning `p` both `T` and `F`. -/
def Discretionary3 (p : Prop3 Ω) : Prop :=
    ∃ o o', ρ o = ρ o' ∧ p o = .true ∧ p o' = .false

/-- **Strongly discretionary** (revised): every world's refinements split `p` into `T` and
`F` — the proposition makes a cut across *all* the worlds. -/
def StronglyDiscretionary3 (p : Prop3 Ω) : Prop :=
    ∀ w, ∃ o o', ρ o = w ∧ ρ o' = w ∧ p o = .true ∧ p o' = .false

/-- Discretionary is exactly the failure of objective. -/
theorem discretionary3_iff_not_objective3 (p : Prop3 Ω) :
    Discretionary3 ρ p ↔ ¬ Objective3 ρ p := by
  unfold Discretionary3 Objective3
  push Not
  rfl

section Decidability

/-! The classification predicates are finitely checkable, so they carry `Decidable`
instances (delegating to the definitional quantifier forms) — model verifications below are
bare `decide`s. -/

variable [Fintype Ω] [DecidableEq W] (p : Prop3 Ω)

instance (w : W) : Decidable (ObjectivelyTrueAt ρ p w) :=
  inferInstanceAs (Decidable (∀ o, ρ o = w → p o = .true))

instance (w : W) : Decidable (ObjectivelyFalseAt ρ p w) :=
  inferInstanceAs (Decidable (∀ o, ρ o = w → p o = .false))

instance : Decidable (Objective3 ρ p) :=
  inferInstanceAs (Decidable (∀ o o', ρ o = ρ o' → p o = .true → p o' ≠ .false))

instance : Decidable (Discretionary3 ρ p) :=
  inferInstanceAs (Decidable (∃ o o', ρ o = ρ o' ∧ p o = .true ∧ p o' = .false))

instance [Fintype W] : Decidable (StronglyDiscretionary3 ρ p) :=
  inferInstanceAs
    (Decidable (∀ w, ∃ o o', ρ o = w ∧ ρ o' = w ∧ p o = .true ∧ p o' = .false))

end Decidability

/-- Strong discretionariness entails discretionariness whenever some world exists. -/
theorem StronglyDiscretionary3.discretionary3 {p : Prop3 Ω} [Nonempty W]
    (h : StronglyDiscretionary3 ρ p) : Discretionary3 ρ p :=
  let ⟨o, o', ho, ho', ht, hf⟩ := h (Classical.arbitrary W)
  ⟨o, o', ho.trans ho'.symm, ht, hf⟩

/-! ### Relativization to an information state (§3.5)

Discretionariness for *tycka* is evaluated against the common ground: an **information
state** is a set of outlooks `C`, and the classification quantifies over the `C`-restricted
refinement classes `ρ ⁻¹' {w} ∩ C`. -/

variable (C : Set Ω)

/-- **Objective relative to `C`**: no `C`-restricted refinement class splits `p`. -/
def ObjectiveIn (p : Prop3 Ω) : Prop :=
    ∀ o ∈ C, ∀ o' ∈ C, ρ o = ρ o' → p o = .true → p o' ≠ .false

/-- **Discretionary relative to `C`**: some `C`-restricted refinement class splits `p`. -/
def DiscretionaryIn (p : Prop3 Ω) : Prop :=
    ∃ o ∈ C, ∃ o' ∈ C, ρ o = ρ o' ∧ p o = .true ∧ p o' = .false

/-- **Strongly discretionary relative to `C`**: every nonempty `C`-restricted refinement
class splits `p` — the proposition makes a cut within every world the state leaves open. -/
def StronglyDiscretionaryIn (p : Prop3 Ω) : Prop :=
    ∀ w, (ρ ⁻¹' {w} ∩ C).Nonempty →
      ∃ o ∈ C, ∃ o' ∈ C, ρ o = w ∧ ρ o' = w ∧ p o = .true ∧ p o' = .false

/-- Strong discretionariness entails discretionariness on any state leaving a world open —
[coppock-2018]'s rendering of [kennedy-willer-2016]: *find* demands radical counterstance
contingency (strong discretionariness), *consider* mere counterstance contingency
(discretionariness), so whatever embeds under *find* embeds under *consider*. -/
theorem stronglyDiscretionaryIn_discretionaryIn {p : Prop3 Ω}
    (h : StronglyDiscretionaryIn ρ C p) {w : W} (hw : (ρ ⁻¹' {w} ∩ C).Nonempty) :
    DiscretionaryIn ρ C p :=
  let ⟨o, ho, o', ho', hwo, hwo', ht, hf⟩ := h w hw
  ⟨o, ho, o', ho', hwo.trans hwo'.symm, ht, hf⟩

/-! ### The norm of accuracy and faultlessness (§3.2)

Being *at fault* is relative to a world (the world of the context of utterance — contexts
determine worlds, not outlooks): one is at fault for expressing `φ` iff `φ` is objectively
false at that world. A strongly discretionary proposition is never objectively false at any
world, so no speaker of one is ever at fault — the faultlessness half of faultless
disagreement; genuine contradiction is supplied by the propositions being complements. -/

/-- The **norm of accuracy**: an asserter of `p` is at fault at `w` iff `p` is objectively
false at `w`. -/
def AtFault (p : Prop3 Ω) (w : W) : Prop := ObjectivelyFalseAt ρ p w

instance [Fintype Ω] [DecidableEq W] (p : Prop3 Ω) (w : W) : Decidable (AtFault ρ p w) :=
  inferInstanceAs (Decidable (ObjectivelyFalseAt ρ p w))

/-- A strongly discretionary proposition never puts its asserter at fault: every world has
a refinement where it is true. -/
theorem stronglyDiscretionary3_never_atFault {p : Prop3 Ω}
    (h : StronglyDiscretionary3 ρ p) (w : W) : ¬ AtFault ρ p w :=
  λ hfault =>
    let ⟨o, _, hwo, _, ht, _⟩ := h w
    by simp [hfault o hwo] at ht

/-! ### Doxastic states, acceptance, and disagreement (§3.3)

An agent's accessibility is a binary relation on outlooks ([coppock-2018] §5's `R_a`); the
doxastic state at `o` is the set of outlooks it reaches (states vary from outlook to
outlook, since whether an agent holds a belief is itself settled by outlooks). To *accept*
a proposition is for it to hold throughout one's accessible outlooks — the Kripke box
(`Core.Logic.Modal.box`) over outlooks with the proposition's truth as valuation. -/

/-- An agent with accessibility `R` **accepts** `p` at `o`: `p` holds at every accessible
outlook. -/
def Accepts (R : AccessRel Ω) (p : Prop3 Ω) : Ω → Prop := box R (p · = .true)

/-- An agent with accessibility `R` **rejects** `p` at `o`: `p` fails at every accessible
outlook. Rejection is stronger than non-acceptance. -/
def Rejects (R : AccessRel Ω) (p : Prop3 Ω) : Ω → Prop := box R (p · = .false)

/-- Two agents **disagree** about `p` at `o` when one accepts it and the other rejects it. -/
def DisagreeAt (R₁ R₂ : AccessRel Ω) (p : Prop3 Ω) (o : Ω) : Prop :=
    Accepts R₁ p o ∧ Rejects R₂ p o

/-- An agent is **opinionated** about `p` at `o` when they accept or reject it; lack of
opinionatedness — both live possibilities — is the state *tycka*-reports deny without
contradiction ([coppock-2018] (38)). -/
def Opinionated (R : AccessRel Ω) (p : Prop3 Ω) (o : Ω) : Prop :=
    Accepts R p o ∨ Rejects R p o

section Decidability

variable [Fintype Ω] (R : AccessRel Ω) [DecidableRel R] (p : Prop3 Ω) (o : Ω)

instance : Decidable (Accepts R p o) :=
  inferInstanceAs (Decidable (∀ o', R o o' → p o' = .true))

instance : Decidable (Rejects R p o) :=
  inferInstanceAs (Decidable (∀ o', R o o' → p o' = .false))

instance (R₂ : AccessRel Ω) [DecidableRel R₂] : Decidable (DisagreeAt R R₂ p o) :=
  inferInstanceAs (Decidable (Accepts R p o ∧ Rejects R₂ p o))

instance : Decidable (Opinionated R p o) :=
  inferInstanceAs (Decidable (Accepts R p o ∨ Rejects R p o))

end Decidability

/-! ### The chili dialogue: faultless disagreement in a four-outlook model

Four outlooks `(tasty?, opera?) : Bool × Bool` refine two worlds according to the objective
coordinate (whether the speaker is an opera singer); tastiness cuts across both refinement
classes. John accepts *the chili is tasty*, Mary rejects it: genuine disagreement, and by
`stronglyDiscretionary3_never_atFault` neither is at fault. The objective proposition
*I am an opera singer* contrasts on both counts, and the *sexy linguist* hybrid
([coppock-2018] (10)) is discretionary without being strongly so — false at every
refinement of a world where John is not a linguist, so assertable at fault. -/

/-- Chili-model outlooks: (chili is tasty?, speaker is an opera singer?). -/
abbrev ChiliOutlook := Bool × Bool

/-- The refinement map: outlooks refine worlds that settle only the objective coordinate. -/
def chiliWorld : ChiliOutlook → Bool := Prod.snd

/-- *The chili is tasty* — settled by the discretionary coordinate. -/
def tasty : Prop3 ChiliOutlook := λ o => .ofBool o.1

/-- *I am an opera singer* — settled by the objective coordinate. -/
def opera : Prop3 ChiliOutlook := λ o => .ofBool o.2

/-- *John is a sexy linguist* with world = linguisthood: true only where both coordinates
hold, reading the objective coordinate as *John is a linguist* ([coppock-2018] (10)). -/
def sexyLinguist : Prop3 ChiliOutlook := λ o => .ofBool (o.1 && o.2)

example : StronglyDiscretionary3 chiliWorld tasty := by decide
example : Objective3 chiliWorld opera := by decide

/-- The hybrid is discretionary (it cuts the linguist-world's refinements) … -/
example : Discretionary3 chiliWorld sexyLinguist := by decide

/-- … but not strongly discretionary: it is uniformly false among refinements of the
non-linguist world. -/
example : ¬ StronglyDiscretionary3 chiliWorld sexyLinguist := by decide

/-- John's doxastic state: only tasty-outlooks accessible. -/
abbrev johnR : AccessRel ChiliOutlook := λ _ o' => o'.1 = true

/-- Mary's doxastic state: only non-tasty-outlooks accessible. -/
abbrev maryR : AccessRel ChiliOutlook := λ _ o' => o'.1 = false

/-- An unopinionated agent: every outlook accessible (`Core.Logic.Modal.universalR`,
inlined for decidability). -/
abbrev openR : AccessRel ChiliOutlook := λ _ _ => True

/-- **The chili dialogue is a genuine disagreement**: at every outlook, John accepts *tasty*
and Mary rejects it. -/
theorem chili_disagreement : ∀ o, DisagreeAt johnR maryR tasty o := by decide

/-- **… and it is faultless**: no world makes *tasty* objectively false, so neither party
violates the norm of accuracy. -/
theorem tasty_never_atFault (w : Bool) : ¬ AtFault chiliWorld tasty w :=
  stronglyDiscretionary3_never_atFault chiliWorld (by decide) w

/-- **The doctor-dialogue contrast**: objective propositions do incur fault — asserting
*I am an opera singer* at the non-singer world violates the norm of accuracy. -/
example : AtFault chiliWorld opera false := by decide

/-- The hybrid incurs fault at the non-linguist world ([coppock-2018] on (10)). -/
example : AtFault chiliWorld sexyLinguist false := by decide

/-- Lack of opinionatedness is representable: the open-minded agent neither accepts nor
rejects *tasty* — the consistency of [coppock-2018] (38), which totally-opinionated-judge
frameworks wrongly rule out. -/
theorem open_agent_unopinionated : ∀ o, ¬ Opinionated openR tasty o := by decide

/-! ### Subjective attitude verbs (§3.5, §5)

English *think* and Swedish *tycka* 'think[opinion]' are both doxastic-acceptance operators;
the only difference is that *tycka* carries a presupposition that its complement is strongly
discretionary relative to the common ground — `∂(discretionary(φ)) ∧ □φ`. The ∂-operator's
role is played by `PartialProp`'s presupposition field (the project-canonical rendering of
partiality); the presupposition is outlook-independent because discretionariness is a global
property of `p` against `C`. -/

/-- *think*: bare doxastic acceptance, no presupposition. -/
def think (R : AccessRel Ω) (p : Prop3 Ω) : PartialProp Ω :=
  ⟨λ _ => True, Accepts R p⟩

/-- *tycka* 'think[opinion]': doxastic acceptance, presupposing that the complement is
strongly discretionary relative to the information state `C`. -/
def tycka (R : AccessRel Ω) (p : Prop3 Ω) : PartialProp Ω :=
  ⟨λ _ => StronglyDiscretionaryIn ρ C p, Accepts R p⟩

/-- *think* and *tycka* assert the same thing — the verbs differ only in *tycka*'s
discretionariness presupposition. -/
theorem think_tycka_same_assertion (R : AccessRel Ω) (p : Prop3 Ω) :
    (think R p).assertion = (tycka ρ C R p).assertion := rfl

/-- *tycka*'s subjectivity requirement projects through negation (via `PartialProp.neg`):
*"#I don't think[opinion] it's Tuesday"* is as bad as the unnegated version. -/
theorem tycka_presup_survives_neg (R : AccessRel Ω) (p : Prop3 Ω) :
    (PartialProp.neg (tycka ρ C R p)).presup = (tycka ρ C R p).presup := rfl

/-- An objective complement is presupposition failure for *tycka*, given that the state
leaves some world's refinements open in a way `p` actually cuts — the
*"#I think[opinion] it's Tuesday / that she's a doctor"* effect. -/
theorem tycka_undefined_of_objectiveIn {p : Prop3 Ω} (hobj : ObjectiveIn ρ C p)
    {w : W} (hw : (ρ ⁻¹' {w} ∩ C).Nonempty) (R : AccessRel Ω) (o : Ω) :
    ¬ (tycka ρ C R p).presup o :=
  λ h =>
    let ⟨o₁, ho₁, o₂, ho₂, hw₁, hw₂, ht, hf⟩ := h w hw
    hobj o₁ ho₁ o₂ ho₂ (hw₁.trans hw₂.symm) ht hf

end Coppock2018
