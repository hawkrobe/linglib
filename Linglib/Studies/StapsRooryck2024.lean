import Linglib.Semantics.ArgumentStructure.ArgumentIntroduction
import Linglib.Semantics.Presupposition.Defs
import Linglib.Fragments.Romance.French.Predicates

/-!
# Staps and Rooryck (2024): Formalizing Spatial-Causal Polysemy of Agent Prepositions

This file formalizes [staps-rooryck-2024]'s analysis of the French agent prepositions *par*
and *de*. Against accounts on which the agent preposition of a passive is a semantically
vacuous case marker, the paper gives each preposition one polymorphically typed denotation
in the sense of the principled polysemy of [tyler-evans-2003], instantiated by the syntactic
context: entities and situations in passives, situations or forces and situations in causal
adjuncts. The domain types are `SemDomain`, an instantiation type is `PrepType`, and `Rel`
types a relation at an instantiation. In causal adjuncts, in the force-theoretic frame of
[copley-harley-2015] and [copley-harley-2022], *de* names a causing situation and *par* a
force (`deCausal`, `parCausal`); a cause *de* names is, through its net force, a cause *par*
names (`parCausal_net_of_deCausal`). In passives the by-phrase is the external argument of
[angelopoulos-collins-terzi-2020], a predicate of events combined with the verb by Event
Identification and closed by passive Voice, and the closure is redundant
(`voicePass_eventIdentification`).

The agentive instantiations share the at-issue relation Initiator and differ only in
presupposition, high proto-agentivity for *par* and low for *de* (`parAgentive`,
`deAgentive`, `parAgentive_presup_iff`). The relevant proto-agentivity is relational, in the
terms of [dowty-1991] and [hopper-thompson-1980]: whether the agent brings about a change,
volitionality and telicity, a `Construal`, ordered with change primary
(`Construal.lt_of_change`, `Construal.le_iff_of_not_change`). *Par* presupposes a construal
at least as proto-agentive as any the verb makes available and *de* one without change at
most as proto-agentive as any (`ParSelects`, `DeSelects`); over the fragment's entries this
derives the paper's readings: the verbs of change exclude *de* (`change_verbs_exclude_de`),
the psych verbs allow both (`psych_verbs_allow_both`), *par* selects the volitional and *de*
the positional sense of *suivre* (`par_suivre`, `de_suivre`), and *par* the telic and *de*
the atelic sense of *abandonner* (`par_abandonner`, `de_abandonner`). The paper's remark that
in a causal model an effect depends on a distal cause only where it depends on the proximate
one, offered as a reason *de* marks low proto-agentivity, is
`dependsOnProximate_of_dependsOnDistal`.

## Implementation notes

The paper gives no threshold between high and low proto-agentivity and reports an informal
survey of twenty-one speakers on a six-point scale only to confirm its judgments; the means
it reports are not reproduced. Change on a contextually inferred scale, which lets the psych
verbs take *par* when the emotion has effects, is beyond the lexical construals and is not
formalized. The stative/dynamic contrast, which the paper finds never decisive on its own,
is not a coordinate of `Construal`. [straub-1974]'s generalization that non-stative verbs
take *par*, stative verbs with animate agents either preposition and stative verbs with
inanimate agents *de* is described in the paper as too coarse, since a stative verb with an
inanimate agent allows *par* when a change on an inferred scale is at stake.

## References

* [staps-rooryck-2024]
* [tyler-evans-2003]
* [croft-2012]
* [copley-harley-2015]
* [copley-harley-2022]
* [angelopoulos-collins-terzi-2020]
* [kratzer-1996]
* [dowty-1991]
* [hopper-thompson-1980]
* [straub-1974]
* [halpern-pearl-2005]
-/

namespace StapsRooryck2024

open ArgumentStructure Presupposition French.Predicates

/-! ### Polymorphic types -/

/-- The domain types of the paper's type system: entities, situations and forces. -/
inductive SemDomain
  | e
  | s
  | f
  deriving DecidableEq, Repr

/-- A preposition type `⟨η, ⟨θ, t⟩⟩`: the domain of the ground and the domain of the figure. -/
structure PrepType where
  ground : SemDomain
  figure : SemDomain
  deriving DecidableEq, Repr

universe u

/-- The interpretation of the domain types in the force-theoretic frame of
[copley-harley-2022]: a force is a function from situations to situations. -/
def Dom (Entity S : Type u) : SemDomain → Type u
  | .e => Entity
  | .s => S
  | .f => S → S

/-- A relation of type `⟨η, ⟨θ, t⟩⟩`, from ground to figure. -/
abbrev Rel (Entity S : Type u) (t : PrepType) : Type u :=
  Dom Entity S t.ground → Dom Entity S t.figure → Prop

/-! ### Causal adjuncts -/

section Causal

variable {Entity S : Type u} (net : S → S → S)

/-- *par* in a causal adjunct, at type `⟨f, ⟨s, t⟩⟩` (14b): the situation comes about through
the force, the net force of some situation the force maps to it. -/
def parCausal : Rel Entity S ⟨.f, .s⟩ := λ f s => ∃ s₀, net s₀ = f ∧ f s₀ = s

/-- *de* in a causal adjunct, at type `⟨s, ⟨s, t⟩⟩` (15b): the situation arises from the
causing situation, whose net force maps it to the situation. -/
def deCausal : Rel Entity S ⟨.s, .s⟩ := λ s s' => net s s = s'

/-- A cause *de* names as a situation is, through its net force, a cause *par* names as a
force: both prepositions describe the same causal event. -/
theorem parCausal_net_of_deCausal {s s' : S} (h : deCausal (Entity := Entity) net s s') :
    parCausal (Entity := Entity) net (net s) s' :=
  ⟨s, rfl, h⟩

end Causal

/-! ### By-phrases in passives -/

section Passive

variable {Entity T : Type*} [LinearOrder T]

/-- The by-phrase (10b): the agentive instantiation applied to its argument, a predicate of
events at type `⟨s, t⟩`. -/
def byPhrase (init : ThematicRel Entity T) (x : Entity) : Event T → Prop := init x

/-- Passive Voice (9b): existential closure of the external argument. -/
def voicePass (p : ThematicRel Entity T) : Event T → Prop := λ e => ∃ x, p x e

/-- (10): the by-phrase combines with the verb's denotation by Event Identification and the
closure passive Voice performs is redundant, since the by-phrase supplies the initiator. -/
theorem voicePass_eventIdentification (init : ThematicRel Entity T) (body : Event T → Prop)
    (j : Entity) (e : Event T) :
    voicePass (eventIdentification (λ x e => init x e ∧ body e) (byPhrase init j)) e ↔
      init j e ∧ body e :=
  ⟨λ ⟨_, ⟨_, hb⟩, hj⟩ => ⟨hj, hb⟩, λ ⟨hj, hb⟩ => ⟨j, ⟨hj, hb⟩, hj⟩⟩

/-- *par* in a passive (35a): the initiator relation, presupposing high proto-agentivity of
the agent in the event. The evaluation point of the partial proposition is the event. -/
def parAgentive (init : ThematicRel Entity T) (High : Entity → Event T → Prop) (x : Entity) :
    PartialProp (Event T) where
  presup := High x
  assertion := init x

/-- *de* in a passive (35b): the initiator relation, presupposing low proto-agentivity. -/
def deAgentive (init : ThematicRel Entity T) (High : Entity → Event T → Prop) (x : Entity) :
    PartialProp (Event T) where
  presup e := ¬ High x e
  assertion := init x

variable (init : ThematicRel Entity T) (High : Entity → Event T → Prop) (x : Entity)

/-- The two prepositions share their at-issue content. -/
theorem parAgentive_assertion :
    (parAgentive init High x).assertion = (deAgentive init High x).assertion := rfl

/-- Their presuppositions are complementary. -/
theorem parAgentive_presup_iff (e : Event T) :
    (parAgentive init High x).presup e ↔ ¬ (deAgentive init High x).presup e :=
  not_not.symm

end Passive

/-! ### Proto-agentivity -/

/-- A construal of the agent's relation to the event, by the relational proto-agentivity
properties the paper finds decisive: bringing about a change, volitionality and telicity. -/
structure Construal where
  change : Bool
  volition : Bool
  telic : Bool
  deriving DecidableEq, Repr, Fintype

namespace Construal

/-- The order of proto-agentivity (34): change is primary, and among construals agreeing on
change, more volitionality or telicity is more proto-agentive. -/
protected def LE (c d : Construal) : Prop :=
  (c.change = true → d.change = true) ∧
    (c.change = d.change →
      (c.volition = true → d.volition = true) ∧ (c.telic = true → d.telic = true))

instance : LE Construal := ⟨Construal.LE⟩

instance (c d : Construal) : Decidable (c ≤ d) := by
  change Decidable (Construal.LE c d); unfold Construal.LE; infer_instance

instance : PartialOrder Construal where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Construal := decidableLTOfDecidableLE

/-- (34a): a construal bringing about a change is more proto-agentive than any that does not,
whatever their volitionality and telicity. -/
theorem lt_of_change : ∀ c d : Construal, c.change = false → d.change = true → c < d := by
  decide

/-- (34b): among construals that bring about no change, proto-agentivity is volitionality and
telicity. -/
theorem le_iff_of_not_change :
    ∀ c d : Construal, c.change = false → d.change = false →
      (c ≤ d ↔ (c.volition = true → d.volition = true) ∧ (c.telic = true → d.telic = true)) := by
  decide

end Construal

/-- The construal a verb entry lexicalizes: change is the subject's causation entailment,
volitionality its volition entailment, and telicity that of the Vendler class. -/
def construal (v : FrenchVerbEntry) : Construal :=
  ⟨(v.subjectEntailments.getD {}).causation, (v.subjectEntailments.getD {}).volition,
    decide ((v.vendlerClass.map Aspect.VendlerClass.telicity).getD .atelic = .telic)⟩

/-- *Par* selects a sense whose construal is at least as proto-agentive as that of every
sense the verb makes available. -/
def ParSelects (senses : List FrenchVerbEntry) (v : FrenchVerbEntry) : Prop :=
  ∀ u ∈ senses, construal u ≤ construal v

/-- *De* selects a sense whose construal brings about no change and is at most as
proto-agentive as that of every sense the verb makes available. -/
def DeSelects (senses : List FrenchVerbEntry) (v : FrenchVerbEntry) : Prop :=
  (construal v).change = false ∧ ∀ u ∈ senses, construal v ≤ construal u

instance (senses : List FrenchVerbEntry) (v : FrenchVerbEntry) :
    Decidable (ParSelects senses v) := by
  unfold ParSelects; infer_instance

instance (senses : List FrenchVerbEntry) (v : FrenchVerbEntry) :
    Decidable (DeSelects senses v) := by
  unfold DeSelects; infer_instance

/-- The prototypically transitive verbs of Table 1 bring about a change and exclude *de*. -/
theorem change_verbs_exclude_de :
    ∀ v ∈ [laver, ecrire, construire, tuer], ParSelects [v] v ∧ ¬ DeSelects [v] v := by
  decide

/-- The psych verbs of Table 1 bring about no change and allow both prepositions. -/
theorem psych_verbs_allow_both :
    ∀ v ∈ [aimer, adorer, respecter], ParSelects [v] v ∧ DeSelects [v] v := by
  decide

/-- The two senses of *suivre*: goal-directed following and the positional relation. -/
def suivreSenses : List FrenchVerbEntry := [suivreDyn, suivreStat]

/-- *Par* selects the volitional sense of *suivre* (25b). -/
theorem par_suivre : ParSelects suivreSenses suivreDyn ∧ ¬ ParSelects suivreSenses suivreStat := by
  decide

/-- *De* selects the positional sense of *suivre* (26a). -/
theorem de_suivre : DeSelects suivreSenses suivreStat ∧ ¬ DeSelects suivreSenses suivreDyn := by
  decide

/-- The two senses of *abandonner*: the telic abandoning and the stative neglect. -/
def abandonnerSenses : List FrenchVerbEntry := [abandonner, abandonnerStat]

/-- *Par* selects the telic sense of *abandonner* (31a). -/
theorem par_abandonner :
    ParSelects abandonnerSenses abandonner ∧ ¬ ParSelects abandonnerSenses abandonnerStat := by
  decide

/-- *De* selects the atelic sense of *abandonner* (31b). -/
theorem de_abandonner :
    DeSelects abandonnerSenses abandonnerStat ∧ ¬ DeSelects abandonnerSenses abandonner := by
  decide

/-! ### Causal distance -/

section CausalModel

variable {P Q X Y Z : Type*} (g : P → X → Y) (h : Q → Y → Z)

/-- In the causal model (36), where `Y` depends on `X` and `Z` on `Y`, the effect depends on
the distal cause in a case when another value of the distal cause changes it. -/
def DependsOnDistal (p : P) (q : Q) (x : X) : Prop := ∃ x', h q (g p x') ≠ h q (g p x)

/-- The effect depends on the proximate cause in a case when another value of it changes the
effect. -/
def DependsOnProximate (p : P) (q : Q) (x : X) : Prop := ∃ y', h q y' ≠ h q (g p x)

/-- The cases in which the effect depends on the distal cause are among those in which it
depends on the proximate cause: greater causal distance means less dependency, which the
paper offers as a reason the ablative *de* marks low proto-agentivity. -/
theorem dependsOnProximate_of_dependsOnDistal {p : P} {q : Q} {x : X}
    (hd : DependsOnDistal g h p q x) : DependsOnProximate g h p q x :=
  let ⟨x', hx⟩ := hd; ⟨g p x', hx⟩

end CausalModel

end StapsRooryck2024
