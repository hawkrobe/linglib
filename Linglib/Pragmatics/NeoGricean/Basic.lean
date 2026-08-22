import Mathlib.Data.Finset.Basic
import Linglib.Semantics.Alternatives.AsymStronger
import Linglib.Logic.Modal.Defs

/-!
# Neo-Gricean pragmatics: epistemic states and the Standard Recipe

This file defines a speaker's epistemic state as a nonempty finite set of worlds, the
knowledge and possibility operators K and P over it, the consistency-gated derivation of
secondary implicatures of [sauerland-2004], and the three-way belief-state classification
over which the Standard Recipe of [geurts-2010] runs. Asserting `φ` yields the primary
implicature `¬Kψ` for each stronger alternative `ψ`; the secondary implicature `K¬ψ` arises
only when it is consistent with the assertion and all primary implicatures, and the Standard
Recipe obtains it from `¬Kψ` under the competence assumption `Kψ ∨ K¬ψ`.

## Main definitions

* `EpistemicState`: a nonempty finite set of worlds, with `SetLike` membership.
* `EpistemicState.knows`, `EpistemicState.possible`: the K and P operators, `box`/`diamond`
  over the epistemic accessibility `EpistemicState.access`.
* `SatisfiesPrimaries`, `SecondaryLicensed`: the commitment set after an assertion and the
  consistency condition licensing a secondary implicature.
* `BeliefState`, `EpistemicState.beliefState`: belief, disbelief, or no opinion about an
  alternative, with the Standard Recipe's predicates `BeliefState.Competent`,
  `BeliefState.WeakImplicature`, `BeliefState.StrongImplicature`.

## Main results

* `secondaryLicensed_iff`: licensing decomposes over the alternatives, so a blocked secondary
  implicature is always blocked by a single primary; the disjunction case (K¬(A∧B) licensed,
  K¬A blocked) is `Studies/Sauerland2004.lean`.
* `secondaryLicensed_of_asymStrongerOn`: a lone asymmetrically stronger alternative always
  licenses its secondary implicature.
* `BeliefState.strongImplicature_iff`: the strong implicature is exactly the weak implicature
  plus competence.

## References

* [sauerland-2004] — primary vs secondary implicatures and the consistency condition
* [geurts-2010] — the Standard Recipe; textbook presentation
* [soames-1982], [horn-1989] — the epistemic modalization `¬Kψ`
* [vanrooij-schulz-2004], [spector-2006] — the competence step `Kψ ∨ K¬ψ`
-/

namespace NeoGricean

open ModalLogic (box diamond IsSerial)

variable {W : Type*}

/-! ### Epistemic states and the K/P operators -/

/-- A speaker's epistemic state: the nonempty finite set of worlds compatible with what the
speaker knows. Nonemptiness makes K serial (`EpistemicState.possible_of_knows`). -/
structure EpistemicState (W : Type*) where
  /-- The worlds compatible with the speaker's knowledge. -/
  carrier : Finset W
  nonempty : carrier.Nonempty

namespace EpistemicState

instance : SetLike (EpistemicState W) W where
  coe e := e.carrier
  coe_injective e₁ e₂ h := by cases e₁; cases e₂; congr; exact Finset.coe_injective h

@[simp] theorem mem_carrier {e : EpistemicState W} {w : W} : w ∈ e.carrier ↔ w ∈ e := Iff.rfl

@[simp] theorem mem_mk {s : Finset W} {h : s.Nonempty} {w : W} : w ∈ mk s h ↔ w ∈ s := Iff.rfl

@[ext] theorem ext {e₁ e₂ : EpistemicState W} (h : ∀ w, w ∈ e₁ ↔ w ∈ e₂) : e₁ = e₂ :=
  SetLike.ext h

/-- The K operator: the speaker knows `φ` iff `φ` holds throughout the epistemic state. -/
def knows (e : EpistemicState W) (φ : W → Prop) : Prop := ∀ w ∈ e, φ w

/-- The P operator: the speaker considers `φ` possible iff some world in the epistemic state
satisfies `φ`. -/
def possible (e : EpistemicState W) (φ : W → Prop) : Prop := ∃ w ∈ e, φ w

instance (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] : Decidable (e.knows φ) :=
  inferInstanceAs (Decidable (∀ w ∈ e.carrier, φ w))

instance (e : EpistemicState W) (φ : W → Prop) [DecidablePred φ] : Decidable (e.possible φ) :=
  inferInstanceAs (Decidable (∃ w ∈ e.carrier, φ w))

/-! ### K and P as restricted modality

`knows` and `possible` are `box` and `diamond` over the world-independent epistemic
accessibility `access`, serial because the state is nonempty; the duality and consistency
lemmas below are the corresponding instances of `ModalLogic.not_box`, `ModalLogic.not_diamond`,
and `ModalLogic.box_D`. -/

/-- Epistemic accessibility: from any world, the speaker's live possibilities. -/
def access (e : EpistemicState W) : W → W → Prop := fun _ w => w ∈ e

instance (e : EpistemicState W) : IsSerial e.access := ⟨fun _ => e.nonempty⟩

@[simp] theorem box_access (e : EpistemicState W) (φ : W → Prop) (w : W) :
    box e.access φ w ↔ e.knows φ := Iff.rfl

@[simp] theorem diamond_access (e : EpistemicState W) (φ : W → Prop) (w : W) :
    diamond e.access φ w ↔ e.possible φ := Iff.rfl

/-- K/P duality: `¬Kφ ↔ P¬φ`. -/
@[simp] theorem not_knows (e : EpistemicState W) (φ : W → Prop) :
    ¬ e.knows φ ↔ e.possible fun w => ¬ φ w :=
  e.nonempty.elim fun w _ => ModalLogic.not_box e.access φ w

/-- K/P duality: `¬Pφ ↔ K¬φ`. -/
@[simp] theorem not_possible (e : EpistemicState W) (φ : W → Prop) :
    ¬ e.possible φ ↔ e.knows fun w => ¬ φ w :=
  e.nonempty.elim fun w _ => ModalLogic.not_diamond e.access φ w

/-- Knowledge is consistent, `Kφ → Pφ` (the D axiom over a nonempty state). -/
theorem possible_of_knows {e : EpistemicState W} {φ : W → Prop} (h : e.knows φ) :
    e.possible φ :=
  e.nonempty.elim fun w _ => ModalLogic.box_D (R := e.access) (w := w) h

end EpistemicState

/-! ### The Sauerland derivation

Asserting `φ` against scalar alternatives `alts` commits the speaker to `Kφ` plus, for each
alternative, the primary implicature `¬Kψ` ([sauerland-2004] (42), verified p. 383). A
secondary implicature `K¬ψ` arises exactly when it is *consistent* with that commitment set
([sauerland-2004] (43)): when some epistemic state realizes the commitments together with
`K¬ψ`. -/

/-- The speaker commitment after asserting `φ` against `alts`: `Kφ` and the primary implicature
`¬Kψ` for each alternative. Per [sauerland-2004], the caller supplies only the asymmetrically
stronger alternatives (e.g. via `Entailment.asymStrongerOn`); the definition does not enforce
the filter. -/
def SatisfiesPrimaries (e : EpistemicState W) (φ : W → Prop) (alts : List (W → Prop)) : Prop :=
  e.knows φ ∧ ∀ ψ ∈ alts, ¬ e.knows ψ

/-- [sauerland-2004]'s consistency condition: the secondary implicature `K¬ψ` is licensed iff
some epistemic state realizes the assertion, all primary implicatures, and `K¬ψ` jointly. -/
def SecondaryLicensed (φ : W → Prop) (alts : List (W → Prop)) (ψ : W → Prop) : Prop :=
  ∃ e : EpistemicState W, SatisfiesPrimaries e φ alts ∧ e.knows fun w => ¬ ψ w

/-- Licensing decomposes over the alternatives: `K¬ψ` is consistent with the commitments iff
the strengthened meaning `φ ∧ ¬ψ` is realizable and, for each alternative `χ`, realizable at
a `¬χ`-world. A blocked secondary implicature is thus always blocked by a single primary. -/
theorem secondaryLicensed_iff {φ ψ : W → Prop} {alts : List (W → Prop)} :
    SecondaryLicensed φ alts ψ ↔
      (∃ w, φ w ∧ ¬ ψ w) ∧ ∀ χ ∈ alts, ∃ w, φ w ∧ ¬ ψ w ∧ ¬ χ w := by
  constructor
  · rintro ⟨e, ⟨hφ, hprim⟩, hψ⟩
    refine ⟨e.nonempty.imp fun w hw => ⟨hφ w hw, hψ w hw⟩, fun χ hχ => ?_⟩
    obtain ⟨w, hw, hχ⟩ := (e.not_knows χ).1 (hprim χ hχ)
    exact ⟨w, hφ w hw, hψ w hw, hχ⟩
  · classical
    rintro ⟨⟨w₀, hφ₀, hψ₀⟩, h⟩
    induction alts with
    | nil =>
      refine ⟨⟨{w₀}, Finset.singleton_nonempty w₀⟩, ⟨?_, by simp⟩, ?_⟩ <;>
        simpa [EpistemicState.knows]
    | cons χ alts ih =>
      obtain ⟨e, ⟨hφ, hprim⟩, hψ⟩ := ih fun χ' hχ' => h χ' (List.mem_cons_of_mem χ hχ')
      obtain ⟨w, hφw, hψw, hχw⟩ := h χ List.mem_cons_self
      refine ⟨⟨insert w e.carrier, Finset.insert_nonempty w _⟩,
        ⟨(Finset.forall_mem_insert ..).2 ⟨hφw, hφ⟩, List.forall_mem_cons.2 ⟨?_, ?_⟩⟩,
        (Finset.forall_mem_insert ..).2 ⟨hψw, hψ⟩⟩
      · exact fun hk => hχw (hk w (Finset.mem_insert_self w _))
      · exact fun χ' hχ' hk => hprim χ' hχ' fun v hv => hk v (Finset.mem_insert_of_mem hv)

/-- For a lone alternative `χ`, `K¬ψ` is licensed iff `φ ∧ ¬ψ ∧ ¬χ` is realizable. -/
theorem secondaryLicensed_singleton {φ ψ χ : W → Prop} :
    SecondaryLicensed φ [χ] ψ ↔ ∃ w, φ w ∧ ¬ ψ w ∧ ¬ χ w := by
  rw [secondaryLicensed_iff, List.forall_mem_singleton]
  exact and_iff_right_of_imp fun ⟨w, h⟩ => ⟨w, h.1, h.2.1⟩

/-- Against its own alternative alone, `K¬ψ` is licensed iff the strengthened meaning
`φ ∧ ¬ψ` is consistent. -/
theorem secondaryLicensed_singleton_self {φ ψ : W → Prop} :
    SecondaryLicensed φ [ψ] ψ ↔ ∃ w, φ w ∧ ¬ ψ w := by
  simp only [secondaryLicensed_singleton, and_self]

/-- A lone asymmetrically stronger alternative always yields its secondary implicature: the
*some ⇝ not all* case. -/
theorem secondaryLicensed_of_asymStrongerOn {s : Finset W} {φ ψ : W → Prop} [DecidablePred φ]
    [DecidablePred ψ] (h : Entailment.asymStrongerOn s ψ φ) : SecondaryLicensed φ [ψ] ψ :=
  secondaryLicensed_singleton_self.2 <| h.2.imp fun _ hw => hw.2

/-! ### The three-way belief-state classification

`BeliefState` is the decidable classification of a speaker's attitude toward one alternative
`ψ`; `EpistemicState.beliefState` grounds it in the K operator, so the Standard Recipe's
predicates are projections of K/P reasoning (`competent_beliefState_iff` and its siblings). -/

/-- A speaker's attitude toward an alternative `ψ`: belief `Bel_S(ψ)`, disbelief `Bel_S(¬ψ)`,
or no opinion. -/
inductive BeliefState where
  | belief
  | disbelief
  | noOpinion
  deriving DecidableEq, Repr

namespace BeliefState

/-- Competence: the speaker knows whether `ψ`, `Bel_S(ψ) ∨ Bel_S(¬ψ)`. -/
def Competent : BeliefState → Prop
  | .belief | .disbelief => True
  | .noOpinion => False

/-- The weak (primary) implicature `¬Bel_S(ψ)`. -/
def WeakImplicature : BeliefState → Prop
  | .belief => False
  | .disbelief | .noOpinion => True

/-- The strong (secondary) implicature `Bel_S(¬ψ)`. -/
def StrongImplicature : BeliefState → Prop
  | .disbelief => True
  | .belief | .noOpinion => False

instance : DecidablePred Competent
  | .belief | .disbelief => isTrue trivial
  | .noOpinion => isFalse id

instance : DecidablePred WeakImplicature
  | .belief => isFalse id
  | .disbelief | .noOpinion => isTrue trivial

instance : DecidablePred StrongImplicature
  | .disbelief => isTrue trivial
  | .belief | .noOpinion => isFalse id

/-- The Standard Recipe: the strong implicature is exactly the weak implicature plus
competence, `Bel_S(¬ψ) ↔ ¬Bel_S(ψ) ∧ (Bel_S(ψ) ∨ Bel_S(¬ψ))`. -/
theorem strongImplicature_iff {b : BeliefState} :
    b.StrongImplicature ↔ b.WeakImplicature ∧ b.Competent := by
  cases b <;> decide

end BeliefState

namespace EpistemicState

variable (e : EpistemicState W) (ψ : W → Prop) [DecidablePred ψ]

/-- Classify an epistemic state by its attitude toward `ψ`: `Kψ` is belief, `K¬ψ` disbelief,
anything else no opinion. -/
def beliefState : BeliefState :=
  if e.knows ψ then .belief else if e.knows (fun w => ¬ ψ w) then .disbelief else .noOpinion

/-- Competence is knowing whether `ψ`. -/
theorem competent_beliefState_iff :
    (e.beliefState ψ).Competent ↔ e.knows ψ ∨ e.knows fun w => ¬ ψ w := by
  unfold beliefState
  split_ifs with h₁ h₂ <;> simp [BeliefState.Competent, *]

/-- The weak implicature is `¬Kψ`. -/
theorem weakImplicature_beliefState_iff : (e.beliefState ψ).WeakImplicature ↔ ¬ e.knows ψ := by
  unfold beliefState
  split_ifs with h₁ h₂ <;> simp [BeliefState.WeakImplicature, h₁]

/-- The strong implicature is `K¬ψ`; the `Kψ` branch is excluded by consistency. -/
theorem strongImplicature_beliefState_iff :
    (e.beliefState ψ).StrongImplicature ↔ e.knows fun w => ¬ ψ w := by
  unfold beliefState
  split_ifs with h₁ h₂
  · exact iff_of_false id ((e.not_possible ψ).not.1 (not_not_intro (possible_of_knows h₁)))
  · exact iff_of_true trivial h₂
  · exact iff_of_false id h₂

end EpistemicState

end NeoGricean
