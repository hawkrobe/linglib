module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Studies.Glass2025
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen

/-!
# Roberts and Özyıldız (2025): A causal explanation for the contrafactive gap

This file formalizes the paper's explanation of the absence of contrafactive predicates, verbs
that would presuppose the falsity of their complement while asserting belief in it. The
Predicate Lexicalization Constraint requires the presupposition of a predicate to be causally
upstream of its at-issue content in the normative model of belief formation, a causal chain
running from one variable to another when altering the first can alter the second,
`Upstream`. In the belief-formation model a fact generates indicators
for itself, experience of an indicator is acquaintance with it, acquaintance forms belief, and
a fact generates no indicator for its negation, `beliefModel`; the truth of a proposition
therefore manipulates belief in it, `know_plc`, whereas its falsity does not, `contra_plc`,
which is the gap. Predicates carrying the contrafactive inference are eventive: the Dutch
deception verb *wijsmaken* and *hallucinate* satisfy the constraint through an intervening
node of deception or distortion, `wijsmaken_plc`, and cutting that node returns the deficient
configuration. The postsuppositional Mandarin yǐwéi lies outside the constraint, so the
attestation table of [glass-2025] follows, `attested_iff`.

## Implementation notes

Models are deterministic Boolean causal models whose exogenous variables read the context. The
paper's first link makes the fact sufficient but not necessary for its indicators; in the
normative model, without forged evidence, the indicator copies the fact. The normative context
makes the experience conditions true and every other exogenous variable false, and the
manipulation test intervenes on the presupposed fact alone. The paper's causal chain is a template
over the choice of proposition and attitude holder, and the model is that template.

## References

* [T. Roberts, D. Özyıldız, *A causal explanation for the contrafactive gap*
  (2025)][roberts-ozyildiz-2025]
* [L. Glass, *Attested versus unattested contrafactive belief verbs* (2025)][glass-2025]
* [J. Pearl, *Causality: models, reasoning, and inference* (2009)][pearl-2000]
-/

@[expose] public section

namespace RobertsOzyildiz2025

open Glass2025 CausalModel Relation

/-- In the context `u`, the variable `c` is causally upstream of `e` when setting `c` true and
setting it false give `e` different values. -/
def Upstream {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    (u : U) (c e : V) : Prop :=
  M.solve (Function.update ⊥ c ↑true) u e ≠ M.solve (Function.update ⊥ c ↑false) u e

noncomputable instance {U V : Type*} [Fintype V] [DecidableEq V]
    (M : CausalModel U V fun _ ↦ Bool)
    [M.IsAcyclic] (u : U) (c e : V) : Decidable (Upstream M u c e) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- A variable with no directed path to another is not upstream of it. -/
theorem not_upstream_of_not_reflTransGen {U V : Type*} [DecidableEq V]
    {M : CausalModel U V fun _ ↦ Bool} [M.IsAcyclic] {c e : V}
    (h : ¬ ReflTransGen M.graph.Adj c e) (u : U) : ¬ Upstream M u c e := fun hu ↦
  hu (by rw [solve_update_of_not_reflTransGen h, solve_update_of_not_reflTransGen h])

/-! ### The belief-formation model -/

/-- The variables of belief formation for a proposition and for its negation: the fact, an
indicator for it, the agent's experience of the indicator, acquaintance with it, and the
resulting belief. -/
inductive V
  | p | indicP | expP | acqP | beliefP
  | notP | indicNotP | expNotP | acqNotP | beliefNotP
  deriving DecidableEq, Fintype, Repr

/-- The causal graph: a fact generates an indicator for itself, experience of the indicator
gives acquaintance with it, and acquaintance forms belief; the chains for a proposition and
for its negation do not cross. -/
abbrev graph : Digraph V := ⟨fun w v ↦ (w, v) ∈ ({
  (.p, .indicP), (.indicP, .acqP), (.expP, .acqP), (.acqP, .beliefP),
  (.notP, .indicNotP), (.indicNotP, .acqNotP), (.expNotP, .acqNotP), (.acqNotP, .beliefNotP)}
  : Finset (V × V))⟩

theorem graph_wellFounded : WellFounded graph.Adj :=
  Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The normative model of belief formation: an indicator exists when its fact holds,
acquaintance is the existence of the indicator together with experience of it, and belief
follows acquaintance. The context settles the facts and the experience conditions. -/
def beliefModel : CausalModel (V → Bool) V fun _ ↦ Bool where
  graph := graph
  eqn
    | .indicP => fun _ x ↦ x .p
    | .acqP => fun _ x ↦ x .indicP && x .expP
    | .beliefP => fun _ x ↦ x .acqP
    | .indicNotP => fun _ x ↦ x .notP
    | .acqNotP => fun _ x ↦ x .indicNotP && x .expNotP
    | .beliefNotP => fun _ x ↦ x .acqNotP
    | v => fun u _ ↦ u v

instance : beliefModel.IsAcyclic := graph_wellFounded

/-- In the normative context the agent experiences whatever indicators exist. -/
def normative : V → Bool
  | .expP | .expNotP => true
  | _ => false

/-! ### The Predicate Lexicalization Constraint -/

/-- *Know* satisfies the constraint: the truth of the complement manipulates belief in it,
through the indicator and acquaintance with it. -/
theorem know_plc : Upstream beliefModel normative .p .beliefP := by decide

/-- The hypothetical *contra* violates the constraint: the falsity of the complement does not
manipulate belief in it, because a fact generates indicators only for itself, so no path runs
from the falsity to the belief. -/
theorem contra_plc : ¬ Upstream beliefModel normative .notP .beliefP :=
  not_upstream_of_not_reflTransGen (by decide : ¬ ReflTransGen graph.Adj .notP .beliefP) _

/-- The template of the generalized constraint, oriented as the paper draws it: the fact does
not manipulate belief in its negation. -/
theorem contra_plc' : ¬ Upstream beliefModel normative .p .beliefNotP :=
  not_upstream_of_not_reflTransGen (by decide : ¬ ReflTransGen graph.Adj .p .beliefNotP) _

/-- The constraint's verdict on the profiles of [glass-2025]: for a factive and for the
hypothetical strong contrafactive, whether the presupposed fact manipulates belief in the
complement; a nonfactive presupposes nothing and yǐwéi's falsity inference is a
postsupposition on the output context, so the constraint does not apply. -/
def SatisfiesPLC : Profile → Prop
  | .factive => Upstream beliefModel normative .p .beliefP
  | .strongContrafactive => Upstream beliefModel normative .notP .beliefP
  | .nonfactive | .weakContrafactive => True

/-- The attestation table follows from the constraint: a profile is attested iff it
satisfies the constraint where the constraint applies. -/
theorem attested_iff : ∀ pr : Profile, pr.Attested ↔ SatisfiesPLC pr
  | .factive => ⟨fun _ ↦ know_plc, fun _ ↦ trivial⟩
  | .strongContrafactive => ⟨False.elim, fun h ↦ contra_plc h⟩
  | .nonfactive | .weakContrafactive => Iff.rfl

/-! ### Eventive predicates with the contrafactive inference -/

/-- The variables of *wijsmaken*: the complement's falsity, the object's prior lack of the
belief, the subject's fooling the object, and the object's resulting belief. -/
inductive W
  | notRich | notBeliefPrior | fool | beliefRich
  deriving DecidableEq, Fintype, Repr

/-- Falsity and prior lack of belief are jointly necessary for fooling, which is sufficient
for the belief. -/
abbrev wijsmakenGraph : Digraph W := ⟨fun w v ↦ (w, v) ∈
  ({(.notRich, .fool), (.notBeliefPrior, .fool), (.fool, .beliefRich)} : Finset (W × W))⟩

theorem wijsmakenGraph_wellFounded : WellFounded wijsmakenGraph.Adj :=
  Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The model of *wijsmaken*, and the model with the eventive node cut, on which the belief
no longer depends on anything. -/
def wijsmaken (eventive : Bool) : CausalModel (W → Bool) W fun _ ↦ Bool where
  graph := wijsmakenGraph
  eqn
    | .fool => fun _ x ↦ x .notRich && x .notBeliefPrior
    | .beliefRich => fun _ x ↦ eventive && x .fool
    | v => fun u _ ↦ u v

instance (eventive : Bool) : (wijsmaken eventive).IsAcyclic := wijsmakenGraph_wellFounded

/-- The context in which the object did not already hold the belief. -/
def noPriorBelief : W → Bool
  | .notBeliefPrior => true
  | _ => false

/-- *Wijsmaken* satisfies the constraint: the complement's falsity manipulates the object's
belief, through the act of fooling. -/
theorem wijsmaken_plc : Upstream (wijsmaken true) noPriorBelief .notRich .beliefRich := by
  decide

/-- With the eventive node cut, the falsity presupposition is no longer upstream of the
belief: the configuration of *contra*. -/
theorem wijsmaken_cut : ¬ Upstream (wijsmaken false) noPriorBelief .notRich .beliefRich := by
  decide

/-- The variables of *hallucinate*: the complement's falsity, the distortion of the input,
and the resulting belief. -/
inductive H
  | notLoves | distortion | beliefLoves
  deriving DecidableEq, Fintype, Repr

/-- Falsity is necessary for distortion, which is necessary for the belief. -/
abbrev hallucinateGraph : Digraph H := ⟨fun w v ↦ (w, v) ∈
  ({(.notLoves, .distortion), (.distortion, .beliefLoves)} : Finset (H × H))⟩

theorem hallucinateGraph_wellFounded : WellFounded hallucinateGraph.Adj :=
  Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The model of *hallucinate*, and the model with the distortion cut. -/
def hallucinate (eventive : Bool) : CausalModel (H → Bool) H fun _ ↦ Bool where
  graph := hallucinateGraph
  eqn
    | .distortion => fun _ x ↦ x .notLoves
    | .beliefLoves => fun _ x ↦ eventive && x .distortion
    | .notLoves => fun u _ ↦ u .notLoves

instance (eventive : Bool) : (hallucinate eventive).IsAcyclic := hallucinateGraph_wellFounded

/-- *Hallucinate* satisfies the constraint through the distortion. -/
theorem hallucinate_plc :
    Upstream (hallucinate true) (fun _ ↦ false) .notLoves .beliefLoves := by
  decide

/-- With the distortion cut, the falsity presupposition is no longer upstream of the
belief. -/
theorem hallucinate_cut :
    ¬ Upstream (hallucinate false) (fun _ ↦ false) .notLoves .beliefLoves := by
  decide

end RobertsOzyildiz2025
