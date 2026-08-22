import Linglib.Pragmatics.NeoGricean.Basic
import Linglib.Studies.GoodmanStuhlmuller2013

/-!
# Bale, Noguchi, Rolland & Barner (2025): competence by default

[bale-etal-2025] test whether listeners assume by default that a speaker is competent about
unsaid alternatives — [geurts-2010]'s competence-by-default hypothesis — against contextual
licensing, on which competence must be contextually established ([soames-1982],
[horn-1989]). Farmer Brown looks into two or three of three boxes and says *Some of the boxes
have red cubes* (4); the listener generates the alternative *all* (5), the weak implicature
`¬K all` (6), and, if competence (7) `K all ∨ K¬all` is assumed, the strong implicature
`K¬all` (8). Half the participants are under cognitive load (a dot-array memory task). If
competence is a default that contextual integration must cancel, load should *raise* the
strong-implicature ("No") rate when the speaker is ignorant, which it does (10% → 23.3%,
P = .02), while the knowledgeable-speaker rate shows only the generalized load reduction of
earlier studies (65.6% → 56.7%, P = .22; Knowledge × Load interaction β = 2.62, χ²(1) = 11.3,
P < .001).

## Main definitions

* `speakerState`: Farmer Brown's epistemic state as a [goodman-stuhlmuller-2013] observation
  state — all three boxes seen, two with red cubes (full knowledge), or two boxes seen, both
  with red cubes (partial knowledge).
* `Competent`: (7), derived from `speakerState`.
* `AssumesCompetent`, `ContextuallyLicensed`: the two hearer models — competence as a default
  cancelled only by contextual integration, which load blocks, versus competence only when
  the context establishes it.

## Main results

* `fk_competent`, `pk_not_competent`: competence is derived from the observation states.
* `fk_strong`: the Standard Recipe runs (6) and (7) to (8) for the knowledgeable speaker.
* `agree_of_fullKnowledge_or_noLoad`, `diverge_pk_load`: the hearer models agree except for
  the ignorant speaker under load, where only competence by default predicts the strong
  implicature — the observed rise.
-/

namespace BaleEtAl2025

open GoodmanStuhlmuller2013 NeoGricean

/-- Whether Farmer Brown looked into the third box. -/
inductive SpeakerKnowledge where
  | fullKnowledge
  | partialKnowledge
  deriving DecidableEq, Repr

/-- The between-subjects cognitive-load manipulation (dot-array memorization). -/
inductive LoadCondition where
  | noLoad
  | load
  deriving DecidableEq, Repr

/-! ### Speaker knowledge as observation access -/

/-- The alternative (5): *all of the boxes have red cubes*. -/
def all : Set WorldState := {w | qMeaning .all w}

/-- Farmer Brown's epistemic state in the *some* trials: the worlds compatible with seeing
all three boxes, two with red cubes (full knowledge), or two boxes, both with red cubes
(partial knowledge). -/
def speakerState : SpeakerKnowledge → Set WorldState
  | .fullKnowledge    => {w | obsCompatible 3 2 w}
  | .partialKnowledge => {w | obsCompatible 2 2 w}

theorem speakerState_nonempty (k : SpeakerKnowledge) : (speakerState k).Nonempty := by
  cases k <;> exact ⟨.s2, by simp [speakerState]; decide⟩

/-- Competence (7): the speaker's state knows whether *all*. -/
def Competent (k : SpeakerKnowledge) : Prop := speakerState k ∈ competent all

/-- The weak implicature (6) holds for both speakers: neither knows *all*. -/
theorem not_speakerState_subset_all (k : SpeakerKnowledge) : ¬ speakerState k ⊆ all := by
  cases k <;> simp only [speakerState, all, Set.ofPred_subset_ofPred] <;> decide

/-- The knowledgeable speaker is competent: he knows *not all*. -/
theorem fk_competent : Competent .fullKnowledge :=
  Or.inr <| by
    simp only [speakerState, all, Set.mem_Iic, Set.compl_ofPred, Set.ofPred_subset_ofPred]; decide

/-- The ignorant speaker is not competent about *all*. -/
theorem pk_not_competent : ¬ Competent .partialKnowledge := by
  simp only [Competent, mem_competent, speakerState, all, Set.compl_ofPred,
    Set.ofPred_subset_ofPred]
  decide

/-- The strong implicature (8) for the knowledgeable speaker, by the Standard Recipe from
(6) and (7). -/
theorem fk_strong : speakerState .fullKnowledge ⊆ allᶜ :=
  (subset_compl_iff_not_subset (speakerState_nonempty _) fk_competent).2
    (not_speakerState_subset_all _)

/-- The ignorant speaker knows neither *all* nor *not all*. -/
theorem pk_ignorant : ¬ speakerState .partialKnowledge ⊆ allᶜ := by
  simp only [speakerState, all, Set.compl_ofPred, Set.ofPred_subset_ofPred]; decide

/-! ### The two hearer models -/

/-- Competence by default: (7) is assumed and cancelled only when contextual information
about the speaker is integrated, which load blocks. -/
def AssumesCompetent (k : SpeakerKnowledge) : LoadCondition → Prop
  | .load   => True
  | .noLoad => Competent k

/-- Contextual licensing: (7) is adopted only when the context establishes it. -/
def ContextuallyLicensed (k : SpeakerKnowledge) (_ : LoadCondition) : Prop := Competent k

/-- Outside the ignorant-speaker-under-load cell the two hearer models agree. -/
theorem agree_of_fullKnowledge_or_noLoad :
    ∀ k l, k = .fullKnowledge ∨ l = .noLoad → (AssumesCompetent k l ↔ ContextuallyLicensed k l)
  | .fullKnowledge, .load, _ => iff_of_true trivial fk_competent
  | .fullKnowledge, .noLoad, _ => Iff.rfl
  | .partialKnowledge, .noLoad, _ => Iff.rfl
  | .partialKnowledge, .load, h => absurd h (by decide)

/-- For the ignorant speaker under load, competence by default predicts the strong
implicature and contextual licensing does not: the observed 10% → 23.3% rise. -/
theorem diverge_pk_load :
    AssumesCompetent .partialKnowledge .load ∧ ¬ ContextuallyLicensed .partialKnowledge .load :=
  ⟨trivial, pk_not_competent⟩

end BaleEtAl2025
