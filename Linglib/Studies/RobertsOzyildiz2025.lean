module

public import Linglib.Studies.Glass2025
public import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Roberts and Özyıldız (2025): A causal explanation for the contrafactive gap

This file formalizes the paper's explanation of the absence of contrafactive predicates, verbs
that would presuppose the falsity of their complement while asserting belief in it. The
Predicate Lexicalization Constraint requires the presupposition of a predicate to be causally
upstream of its at-issue content in the normative model of belief formation, a causal chain
running from one variable to another when altering the first can alter the second, the
substrate's `BoolSEM.manipulates`. In the belief-formation model a fact generates indicators
for itself, experience of an indicator is acquaintance with it, acquaintance forms belief, and
a fact generates no indicator for its negation, `beliefModel`; the truth of a proposition
therefore manipulates belief in it, `know_plc`, whereas its falsity does not, `contra_plc`,
which is the gap. Predicates carrying the contrafactive inference are eventive: the Dutch
deception verb *wijsmaken* and *hallucinate* satisfy the constraint through an intervening
node of deception or distortion, `wijsmaken_plc`, and cutting that node returns the deficient
configuration. The postsuppositional Mandarin yǐwéi lies outside the constraint, so the
attestation table of [glass-2025] follows, `attested_iff`.

## Implementation notes

Models are the substrate's deterministic Boolean structural equation models. The paper's
first link makes the fact sufficient but not necessary for its indicators; in the normative
model, without forged evidence, the indicator copies the fact. Exogenous variables default to
false, and the normative background sets the experience conditions true, so that the
manipulation test varies only the presupposed fact. The paper's causal chain is a template
over the choice of proposition and attitude holder, and the model is that template.

## References

* [T. Roberts, D. Özyıldız, *A causal explanation for the contrafactive gap*
  (2025)][roberts-ozyildiz-2025]
* [L. Glass, *Attested versus unattested contrafactive belief verbs* (2025)][glass-2025]
* [J. Pearl, *Causality: models, reasoning, and inference* (2009)][pearl-2000]
-/

@[expose] public section

namespace RobertsOzyildiz2025

open Glass2025 Causation Causation.Mechanism Causation.SEM Causation.BoolSEM

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
def graph : CausalGraph V := ⟨λ
  | .indicP => {.p}
  | .acqP => {.indicP, .expP}
  | .beliefP => {.acqP}
  | .indicNotP => {.notP}
  | .acqNotP => {.indicNotP, .expNotP}
  | .beliefNotP => {.acqNotP}
  | _ => ∅⟩

instance : CausalGraph.IsDAG graph := .of_irrefl (by decide)

/-- The normative model of belief formation: an indicator exists when its fact holds,
acquaintance is the existence of the indicator together with experience of it, and belief
follows acquaintance. -/
def beliefModel : BoolSEM V where
  graph := graph
  mech
    | .indicP => fun ρ ↦ ρ ⟨.p, by simp [graph]⟩
    | .acqP => fun ρ ↦
        ρ ⟨.indicP, by simp [graph]⟩ && ρ ⟨.expP, by simp [graph]⟩
    | .beliefP => fun ρ ↦ ρ ⟨.acqP, by simp [graph]⟩
    | .indicNotP => fun ρ ↦ ρ ⟨.notP, by simp [graph]⟩
    | .acqNotP => fun ρ ↦
        ρ ⟨.indicNotP, by simp [graph]⟩ && ρ ⟨.expNotP, by simp [graph]⟩
    | .beliefNotP => fun ρ ↦ ρ ⟨.acqNotP, by simp [graph]⟩
    | _ => const (G := graph) false

instance : CausalGraph.IsDAG beliefModel.graph := inferInstanceAs (CausalGraph.IsDAG graph)

/-- The normative background: the agent experiences whatever indicators exist. -/
def normative : Valuation (λ _ : V => Bool) :=
  (Valuation.empty.extend .expP true).extend .expNotP true

/-! ### The Predicate Lexicalization Constraint -/

/-- *Know* satisfies the constraint: the truth of the complement manipulates belief in it,
through the indicator and acquaintance with it. -/
theorem know_plc : manipulates beliefModel normative .p .beliefP := by
  decide

/-- The hypothetical *contra* violates the constraint: the falsity of the complement does not
manipulate belief in it, because a fact generates indicators only for itself. -/
theorem contra_plc : ¬ manipulates beliefModel normative .notP .beliefP := by
  decide

/-- The template of the generalized constraint, oriented as the paper draws it: the fact does
not manipulate belief in its negation. -/
theorem contra_plc' : ¬ manipulates beliefModel normative .p .beliefNotP := by
  decide

/-- The constraint's verdict on the profiles of [glass-2025]: for a factive and for the
hypothetical strong contrafactive, whether the presupposed fact manipulates belief in the
complement; a nonfactive presupposes nothing and yǐwéi's falsity inference is a
postsupposition on the output context, so the constraint does not apply. -/
def SatisfiesPLC : Profile → Prop
  | .factive => manipulates beliefModel normative .p .beliefP
  | .strongContrafactive => manipulates beliefModel normative .notP .beliefP
  | .nonfactive | .weakContrafactive => True

/-- The attestation table follows from the constraint: a profile is attested iff it
satisfies the constraint where the constraint applies. -/
theorem attested_iff : ∀ pr : Profile, pr.Attested ↔ SatisfiesPLC pr
  | .factive => ⟨fun _ ↦ know_plc, fun _ ↦ trivial⟩
  | .strongContrafactive => ⟨False.elim, λ h => contra_plc h⟩
  | .nonfactive | .weakContrafactive => Iff.rfl

/-! ### Eventive predicates with the contrafactive inference -/

/-- The variables of *wijsmaken*: the complement's falsity, the object's prior lack of the
belief, the subject's fooling the object, and the object's resulting belief. -/
inductive W
  | notRich | notBeliefPrior | fool | beliefRich
  deriving DecidableEq, Fintype, Repr

/-- Falsity and prior lack of belief are jointly necessary for fooling, which is sufficient
for the belief. -/
def wijsmakenGraph : CausalGraph W := ⟨λ
  | .fool => {.notRich, .notBeliefPrior}
  | .beliefRich => {.fool}
  | _ => ∅⟩

instance : CausalGraph.IsDAG wijsmakenGraph := .of_irrefl (by decide)

/-- The model of *wijsmaken*, and the model with the eventive node cut, on which the belief
no longer depends on anything. -/
def wijsmaken (eventive : Bool) : BoolSEM W where
  graph := wijsmakenGraph
  mech
    | .fool => fun ρ ↦
        ρ ⟨.notRich, by simp [wijsmakenGraph]⟩ &&
          ρ ⟨.notBeliefPrior, by simp [wijsmakenGraph]⟩
    | .beliefRich => fun ρ ↦ eventive && ρ ⟨.fool, by simp [wijsmakenGraph]⟩
    | _ => const (G := wijsmakenGraph) false

instance (eventive : Bool) : CausalGraph.IsDAG (wijsmaken eventive).graph :=
  inferInstanceAs (CausalGraph.IsDAG wijsmakenGraph)

/-- The background in which the object did not already hold the belief. -/
def noPriorBelief : Valuation (λ _ : W => Bool) := Valuation.empty.extend .notBeliefPrior true

/-- *Wijsmaken* satisfies the constraint: the complement's falsity manipulates the object's
belief, through the act of fooling. -/
theorem wijsmaken_plc : manipulates (wijsmaken true) noPriorBelief .notRich .beliefRich := by
  decide

/-- With the eventive node cut, the falsity presupposition is no longer upstream of the
belief: the configuration of *contra*. -/
theorem wijsmaken_cut : ¬ manipulates (wijsmaken false) noPriorBelief .notRich .beliefRich := by
  decide

/-- The variables of *hallucinate*: the complement's falsity, the distortion of the input,
and the resulting belief. -/
inductive H
  | notLoves | distortion | beliefLoves
  deriving DecidableEq, Fintype, Repr

/-- Falsity is necessary for distortion, which is necessary for the belief. -/
def hallucinateGraph : CausalGraph H := ⟨λ
  | .distortion => {.notLoves}
  | .beliefLoves => {.distortion}
  | _ => ∅⟩

instance : CausalGraph.IsDAG hallucinateGraph := .of_irrefl (by decide)

/-- The model of *hallucinate*, and the model with the distortion cut. -/
def hallucinate (eventive : Bool) : BoolSEM H where
  graph := hallucinateGraph
  mech
    | .distortion => fun ρ ↦ ρ ⟨.notLoves, by simp [hallucinateGraph]⟩
    | .beliefLoves => fun ρ ↦
        eventive && ρ ⟨.distortion, by simp [hallucinateGraph]⟩
    | .notLoves => const (G := hallucinateGraph) false

instance (eventive : Bool) : CausalGraph.IsDAG (hallucinate eventive).graph :=
  inferInstanceAs (CausalGraph.IsDAG hallucinateGraph)

/-- *Hallucinate* satisfies the constraint through the distortion. -/
theorem hallucinate_plc :
    manipulates (hallucinate true) Valuation.empty .notLoves .beliefLoves := by
  decide

/-- With the distortion cut, the falsity presupposition is no longer upstream of the
belief. -/
theorem hallucinate_cut :
    ¬ manipulates (hallucinate false) Valuation.empty .notLoves .beliefLoves := by
  decide

end RobertsOzyildiz2025
