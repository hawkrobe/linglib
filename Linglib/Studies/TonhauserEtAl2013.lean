import Linglib.Semantics.Presupposition.ProjectiveContent
import Linglib.Semantics.Presupposition.BeliefEmbedding

/-!
# Tonhauser, Beaver, Roberts & Simons (2013): a taxonomy of projective content

[tonhauser-beaver-roberts-simons-2013] sort projective contents by two diagnosable
properties. A trigger imposes a *strong contextual felicity constraint* with respect to its
content `m` if it is acceptable only in `m`-positive contexts (11), where a context is
`m`-positive if it entails `m` and `m`-neutral if it entails neither `m` nor `¬m` (10), so
acceptability in an `m`-neutral context refutes the constraint (12i). Under a belief
predicate, `m` has *local effect* when it is part of the attitude holder's belief state, and
*obligatory* local effect when it always does (§5), so acceptability with the holder ignorant
of `m` refutes it (41i). The two properties cross-classify the English and Guaraní triggers
of Table 2 into classes A–D (`Semantics/Presupposition/ProjectiveContent.lean`), cutting
across the traditional presuppositions: pronouns (A) and *stop* (C) are both classical
presuppositions (`stop_pronoun_classes_differ`).

§8 argues that a theory on which a presupposition is acceptable iff its local context entails
it ([karttunen-1974-presupposition], [heim-1983], [schlenker-2009]) predicts every trigger
to impose the constraint and to have obligatory local effect — to be class A. Against the
substrate's own rendering of that theory, `Context.presupSatisfied` at the matrix and
`BeliefEmbedding.presupAttributedToHolder` under belief, this is `scf_of_satisfaction` and
`ole_of_satisfaction`; Table 2's classes B–D are the counterexamples
(`exists_trigger_not_classA`).
-/

namespace TonhauserEtAl2013

open CommonGround Semantics.Presupposition Semantics.Presupposition.Context
  Semantics.Presupposition.BeliefEmbedding Semantics.Presupposition.ProjectiveContent

variable {W E : Type*} (m : Set W) (c : ContextSet W)

/-- (10): the context entails `m`. -/
def MPositive : Prop := ContextSet.entails c m

/-- (10): the context entails neither `m` nor `¬m`. -/
def MNeutral : Prop := ¬ ContextSet.entails c m ∧ ¬ ContextSet.entails c mᶜ

/-- (11): uttering the trigger's sentence, acceptable in the contexts `Acc`, is acceptable
only in `m`-positive contexts. -/
def StrongContextualFelicity (Acc : ContextSet W → Prop) : Prop := ∀ c, Acc c → MPositive m c

/-- (12i): acceptability in an `m`-neutral context refutes the constraint. -/
theorem not_scf_of_acceptable_neutral {Acc : ContextSet W → Prop} (h : Acc c)
    (hn : MNeutral m c) : ¬ StrongContextualFelicity m Acc :=
  fun hs => hn.1 (hs c h)

/-- §5: under `a believes S` at `w`, `m` has local effect when it is part of `a`'s belief
state. -/
def LocalEffect (Dox : E → W → W → Prop) (a : E) (w : W) : Prop :=
  ContextSet.entails (Dox a w) m

/-- Obligatory local effect: wherever the belief report is acceptable, `m` has local effect. -/
def ObligatoryLocalEffect (Dox : E → W → W → Prop) (a : E) (Acc : ContextSet W → Prop) :
    Prop :=
  ∀ c, Acc c → ∀ w ∈ c, LocalEffect m Dox a w

/-- (41i): acceptability of the report with the holder ignorant of `m` refutes obligatory
local effect. -/
theorem not_ole_of_acceptable_ignorant {Dox : E → W → W → Prop} {a : E}
    {Acc : ContextSet W → Prop} (h : Acc c) {w : W} (hw : w ∈ c) (hig : MNeutral m (Dox a w)) :
    ¬ ObligatoryLocalEffect m Dox a Acc :=
  fun ho => hig.1 (ho c h w hw)

/-! ### Against local satisfaction (§8) -/

variable (p : PartialProp W) (Dox : E → W → W → Prop) (a : E)

/-- A trigger acceptable exactly where its local context entails its presupposition imposes
the strong contextual felicity constraint. -/
theorem scf_of_satisfaction : StrongContextualFelicity p.presup (presupSatisfied · p) :=
  fun _ h => h

/-- Under belief, local satisfaction is satisfaction in the holder's belief state, so the
presupposition has obligatory local effect. -/
theorem ole_of_satisfaction :
    ObligatoryLocalEffect p.presup Dox a (presupAttributedToHolder ⟨·, Dox, a⟩ p) :=
  fun _ h w hw _ hx => h w hw ⟨hw, hx⟩

/-- Local satisfaction thus predicts class A for every trigger; Table 2 has triggers of every
other class. -/
theorem exists_trigger_not_classA :
    classFromProperties .requires .obligatory = .classA ∧
      ∃ t : ProjectiveTrigger, t.toClass ≠ .classA :=
  ⟨rfl, .expressive, by decide⟩

/-- The classes cut across the traditional presuppositions: pronouns and *stop* are both
classical presuppositions, in classes A and C. -/
theorem stop_pronoun_classes_differ :
    ProjectiveTrigger.stop_prestate.toClass ≠ ProjectiveTrigger.pronoun_existence.toClass := by
  decide

end TonhauserEtAl2013
