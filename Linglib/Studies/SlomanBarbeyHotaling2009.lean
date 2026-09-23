module

public import Linglib.Semantics.Causation.SEM.Entailment

/-!
# Sloman, Barbey and Hotaling (2009): A Causal Model Theory of Cause, Enable, and Prevent

This file formalizes the causal model theory of [sloman-barbey-hotaling-2009]: the verbs refer
to the causal model of a discourse, and in the deterministic binary case their meanings are the
structural equations (2) to (4). *A causes B* asserts a link from A to B, `B := A`; *A enables B*
asserts a link, an accessory variable also linked to B, and A necessary for B, `B := A ∧ X`; and
*A prevents B* asserts a link along which A reduces B, `B := ¬A` with no accessory and `B := ¬A ∧ X`
or `B := ¬(A ∧ X)` with one. Over the substrate's structural equation models the verbs are
predicates on a model (`Causes`, `Enables`, `Prevents`), and the equations are models
(`causes`, `enables`, `prevents`, `preventsAnd`, `preventsNand`) that satisfy them
(`causes_Causes`, `enables_Enables`, `prevents_Prevents`, `preventsAnd_Prevents`,
`preventsNand_Prevents`). The paper's experiments follow from the equations: an effect follows
from its cause without any accessory, but from its enabler only once the accessory is settled
(Experiments 1 to 3, `causes_entails`, `enables_not_entails`, `enables_entails_of_accessory`),
and a one-link model is labelled *cause* while a two-link model is labelled *enable*
(Experiment 4, `not_enables_of_parents_eq_singleton`, `causes_not_Enables`). Two-premise
arguments are composed by substituting causes for effects, and the compositions the paper
works out come out as the equations it names: *causes* then *causes* is `C := A`
(`causesCauses_causes`), *allows* then *prevents*, or *allows* then *not B causes C*, is
`C := ¬(A ∧ X)`, the accessory form of *prevents* (`allowsPrevents_prevents`), *prevents* then
*prevents* is `C := A` (`preventsPrevents_causes`), and the three-premise argument of section
4.2 composes to `D := A` (`threePremise_causes`).

## Implementation notes

* A structural equation is a deterministic Boolean mechanism at the effect over its parents;
  the accessory variable is an exogenous vertex of the model. Entailment is the substrate's
  strict causal entailment, on which an effect with an undetermined parent entails nothing:
  this is the paper's uncertainty when the accessory is unknown. Necessity is read eagerly, in
  every background leaving the effect open in which the cause is off, the model develops the
  effect off.
* The paper's experimental results stay in prose. In Experiments 1 to 3 confidence that the
  effect occurs was high only for a cause without an accessory and near the midpoint of the
  scale otherwise; in Experiment 4 one-link vignettes drew *cause* and two-link vignettes drew
  *enable*, *help* or *allow*. Of the sixteen two-premise argument forms of Goldvarg and
  Johnson-Laird's fourth experiment, the theory agrees with mental model theory on thirteen and
  predicts *A prevents C* for *allows* then *prevents* and for *allows* then *not B causes C*,
  and *A causes C* for *prevents* then *prevents*.

## References

* [sloman-barbey-hotaling-2009]
* [pearl-2000]
-/

@[expose] public section

namespace SlomanBarbeyHotaling2009

open Causation Causation.SEM Causation.Mechanism

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (M : BoolSEM V) [CausalGraph.IsDAG M.graph]

/-- *A causes B*: the discourse model has a link from A to B (section 3, Figure 3b). -/
def Causes (a b : V) : Prop := BoolSEM.hasDirectLaw M a b

instance (a b : V) : Decidable (Causes M a b) :=
  inferInstanceAs (Decidable (BoolSEM.hasDirectLaw M a b))

/-- A is necessary for B: in every background leaving B open in which A is off, B develops
off. -/
def Necessary (a b : V) : Prop :=
  ∀ bg : Valuation (λ _ : V => Bool),
    bg.get b = none → bg.hasValue a false → (M.developDet bg).hasValue b false

/-- *A enables B*: a link from A to B, an accessory variable also linked to B, and A necessary
for B (section 3, Figure 4). -/
def Enables (a b : V) : Prop :=
  BoolSEM.hasDirectLaw M a b ∧ (∃ x, x ≠ a ∧ BoolSEM.hasDirectLaw M x b) ∧ Necessary M a b

/-- *A prevents B* on a background in which the accessory, if any, is present: a link from A to
B along which turning A on entails B off. -/
def Prevents (bg : Valuation (λ _ : V => Bool)) (a b : V) : Prop :=
  BoolSEM.hasDirectLaw M a b ∧ causallyEntails M (bg.extend a true) b false

/-- The model realizes the equation `c := a` on `bg`: turning `a` on or off entails `c`
accordingly. -/
def EqCauses (bg : Valuation (λ _ : V => Bool)) (a c : V) : Prop :=
  ∀ v, causallyEntails M (bg.extend a v) c v

/-- The model realizes the equation `c := ¬a` on `bg`. -/
def EqPrevents (bg : Valuation (λ _ : V => Bool)) (a c : V) : Prop :=
  ∀ v, causallyEntails M (bg.extend a v) c (!v)

variable {M}

omit [Fintype V] [DecidableEq V] in
/-- Experiment 4: with A alone the source of B, the relation is not an enabling one. -/
theorem not_enables_of_parents_eq_singleton {a b : V} (h : M.graph.parents b = {a}) :
    ¬ Enables M a b := by
  rintro ⟨-, ⟨x, hx, hxb⟩, -⟩
  exact hx (by simpa [BoolSEM.hasDirectLaw, h] using hxb)

omit [Fintype V] in
/-- The equations `c := a` and `c := ¬a` exclude each other on a background. -/
theorem EqCauses.not_eqPrevents {bg : Valuation (λ _ : V => Bool)} {a c : V}
    (h : EqCauses M bg a c) : ¬ EqPrevents M bg a c :=
  λ h' => Bool.noConfusion (causallyEntails_unique (h true) (h' true))

end General

/-! ### The equations of section 3 -/

/-- The cause, the accessory variable and the effect. -/
inductive V
  | A | X | B
  deriving DecidableEq, Fintype

/-- The one-link model: B's only parent is A. -/
def oneLink : CausalGraph V := ⟨λ | .A => ∅ | .X => ∅ | .B => {.A}⟩

/-- The two-link model: B's parents are A and the accessory X. -/
def twoLink : CausalGraph V := ⟨λ | .A => ∅ | .X => ∅ | .B => {.A, .X}⟩

instance : CausalGraph.IsDAG oneLink := .of_irrefl (by decide)

instance : CausalGraph.IsDAG twoLink := .of_irrefl (by decide)

/-- A one-link model with the given equation at B. -/
def oneLinkModel (f : Bool → Bool) : BoolSEM V :=
  { graph := oneLink
    mech := fun
      | .A => const (G := oneLink) false
      | .X => const (G := oneLink) false
      | .B => fun ρ ↦ f (ρ ⟨.A, by decide⟩) }

/-- A two-link model with the given equation at B over A and X. -/
def twoLinkModel (f : Bool → Bool → Bool) : BoolSEM V :=
  { graph := twoLink
    mech := fun
      | .A => const (G := twoLink) false
      | .X => const (G := twoLink) false
      | .B => fun ρ ↦ f (ρ ⟨.A, by decide⟩) (ρ ⟨.X, by decide⟩) }

instance (f : Bool → Bool) : CausalGraph.IsDAG (oneLinkModel f).graph :=
  inferInstanceAs (CausalGraph.IsDAG oneLink)

instance (f : Bool → Bool → Bool) : CausalGraph.IsDAG (twoLinkModel f).graph :=
  inferInstanceAs (CausalGraph.IsDAG twoLink)

/-- (2) *A causes B*: `B := A`. -/
abbrev causes : BoolSEM V := oneLinkModel id

/-- (3) *A enables B*: `B := A ∧ X`. -/
abbrev enables : BoolSEM V := twoLinkModel (· && ·)

/-- (4a) *A prevents B* with no accessory: `B := ¬A`. -/
abbrev prevents : BoolSEM V := oneLinkModel (!·)

/-- (4b) *A prevents B* with an accessory: `B := ¬A ∧ X`. -/
abbrev preventsAnd : BoolSEM V := twoLinkModel (λ a x => !a && x)

/-- (4c) *A prevents B* with an accessory: `B := ¬(A ∧ X)`. -/
abbrev preventsNand : BoolSEM V := twoLinkModel (λ a x => !(a && x))

/-- The accessory present. -/
def accessory : Valuation (λ _ : V => Bool) := Valuation.empty.extend .X true

/-- *A causes B* holds of (2), and the model realizes `B := A`. -/
theorem causes_Causes : Causes causes .A .B ∧ EqCauses causes Valuation.empty .A .B :=
  ⟨by decide, fun v ↦ by cases v <;> decide⟩

/-- Experiments 2 and 3: from *A causes B* and A, B follows with no accessory settled. -/
theorem causes_entails : causallyEntails causes (Valuation.empty.extend .A true) .B true :=
  causes_Causes.2 true

/-- Experiment 4: the one-link model is not an enabling relation. -/
theorem causes_not_Enables : ¬ Enables causes .A .B :=
  not_enables_of_parents_eq_singleton rfl

/-- The effect of (3) develops as the conjunction of its developed cause and accessory. -/
theorem developDetVtx_enables_B {bg : Valuation (λ _ : V => Bool)} (h : bg.get .B = none) :
    developDetVtx enables bg .B = (developDetVtx enables bg .A && developDetVtx enables bg .X) := by
  rw [developDetVtx_undet _ _ _ h]
  rfl

/-- *A enables B* holds of (3): the link, the accessory, and the necessity of A. -/
theorem enables_Enables : Enables enables .A .B := by
  refine ⟨by decide, ⟨.X, by decide, by decide⟩, λ bg hb ha => ?_⟩
  rw [developDet_hasValue_iff, developDetVtx_enables_B hb, developDetVtx_extended _ _ _ _ ha]
  rfl

/-- Experiments 1 and 3: from *A enables B* and A alone, B does not follow, the accessory being
unknown. -/
theorem enables_not_entails : ¬ causallyEntails enables (Valuation.empty.extend .A true) .B true :=
  by decide

/-- With the accessory present, B follows from A. -/
theorem enables_entails_of_accessory :
    causallyEntails enables (accessory.extend .A true) .B true :=
  by decide

/-- (4a) prevents: turning A on entails B off. -/
theorem prevents_Prevents :
    Prevents prevents Valuation.empty .A .B ∧ EqPrevents prevents Valuation.empty .A .B :=
  ⟨⟨by decide, by decide⟩,
    fun v ↦ by cases v <;> decide⟩

/-- (4b) and (4c) prevent when the accessory is present, and (4b) does so as the equation
`B := ¬A` on that background. -/
theorem preventsAnd_Prevents :
    Prevents preventsAnd accessory .A .B ∧ EqPrevents preventsAnd accessory .A .B :=
  ⟨⟨by decide, by decide⟩,
    fun v ↦ by cases v <;> decide⟩

theorem preventsNand_Prevents :
    Prevents preventsNand accessory .A .B ∧ EqPrevents preventsNand accessory .A .B :=
  ⟨⟨by decide, by decide⟩,
    fun v ↦ by cases v <;> decide⟩

/-! ### Two-premise arguments, section 4.1

The premises *A relates to B* and *B relates to C* are structural equations, and the
conclusion is their composition, substituting the cause for the effect; the conclusion is the
equation the composed model realizes between A and C. -/

/-- The terms of a two-premise argument, with the first premise's accessory. -/
inductive W
  | A | X | B | C
  deriving DecidableEq, Fintype

/-- The graph of a two-premise argument whose first premise has no accessory. -/
def chainOne : CausalGraph W := ⟨λ | .A => ∅ | .X => ∅ | .B => {.A} | .C => {.B}⟩

/-- The graph of a two-premise argument whose first premise has an accessory. -/
def chainTwo : CausalGraph W := ⟨λ | .A => ∅ | .X => ∅ | .B => {.A, .X} | .C => {.B}⟩

instance : CausalGraph.IsDAG chainOne := .of_irrefl (by decide)

instance : CausalGraph.IsDAG chainTwo := .of_irrefl (by decide)

/-- The composition of a first premise `B := f A` with a second premise `C := g B`. -/
def composeOne (f g : Bool → Bool) : BoolSEM W :=
  { graph := chainOne
    mech := fun
      | .A => const (G := chainOne) false
      | .X => const (G := chainOne) false
      | .B => fun ρ ↦ f (ρ ⟨.A, by decide⟩)
      | .C => fun ρ ↦ g (ρ ⟨.B, by decide⟩) }

/-- The composition of a first premise `B := f A X` with a second premise `C := g B`. -/
def composeTwo (f : Bool → Bool → Bool) (g : Bool → Bool) : BoolSEM W :=
  { graph := chainTwo
    mech := fun
      | .A => const (G := chainTwo) false
      | .X => const (G := chainTwo) false
      | .B => fun ρ ↦ f (ρ ⟨.A, by decide⟩) (ρ ⟨.X, by decide⟩)
      | .C => fun ρ ↦ g (ρ ⟨.B, by decide⟩) }

instance (f g : Bool → Bool) : CausalGraph.IsDAG (composeOne f g).graph :=
  inferInstanceAs (CausalGraph.IsDAG chainOne)

instance (f : Bool → Bool → Bool) (g : Bool → Bool) : CausalGraph.IsDAG (composeTwo f g).graph :=
  inferInstanceAs (CausalGraph.IsDAG chainTwo)

/-- The first premise's accessory present. -/
def chainAccessory : Valuation (λ _ : W => Bool) := Valuation.empty.extend .X true

/-- (5) and (6): *A causes B*, *B causes C* compose to `C := A`, the conclusion *A causes C*. -/
theorem causesCauses_causes : EqCauses (composeOne id id) Valuation.empty .A .C :=
  fun v ↦ by cases v <;> decide

/-- *A allows B*, *B prevents C*, or equally *not B causes C*, compose to `C := ¬(A ∧ X)`, the
accessory form (4c) of *prevents*: with the accessory present, A prevents C. -/
theorem allowsPrevents_prevents : EqPrevents (composeTwo (· && ·) (!·)) chainAccessory .A .C :=
  fun v ↦ by cases v <;> decide

/-- *A prevents B*, *B prevents C* compose to `C := A`, the conclusion *A causes C*. -/
theorem preventsPrevents_causes : EqCauses (composeOne (!·) (!·)) Valuation.empty .A .C :=
  fun v ↦ by cases v <;> decide

/-! ### A three-premise argument, section 4.2 -/

/-- The terms of the three-premise argument. -/
inductive U
  | A | B | C | D
  deriving DecidableEq, Fintype

def line : CausalGraph U := ⟨λ | .A => ∅ | .B => {.A} | .C => {.B} | .D => {.C}⟩

instance : CausalGraph.IsDAG line := .of_irrefl (by decide)

/-- *A causes B*, *B causes not C*, *C causes not D*: `B := A`, `C := ¬B`, `D := ¬C`. -/
def threePremise : BoolSEM U :=
  { graph := line
    mech := fun
      | .A => const (G := line) false
      | .B => fun ρ ↦ ρ ⟨.A, by decide⟩
      | .C => fun ρ ↦ !ρ ⟨.B, by decide⟩
      | .D => fun ρ ↦ !ρ ⟨.C, by decide⟩ }

instance : CausalGraph.IsDAG threePremise.graph := inferInstanceAs (CausalGraph.IsDAG line)

/-- The three premises compose to `D := A`, the conclusion *A causes D*. -/
theorem threePremise_causes : EqCauses threePremise Valuation.empty .A .D :=
  fun v ↦ by cases v <;> decide

end SlomanBarbeyHotaling2009
