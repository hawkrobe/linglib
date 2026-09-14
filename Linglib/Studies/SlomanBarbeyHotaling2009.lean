import Linglib.Semantics.Causation.SEM.Counterfactual

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

namespace SlomanBarbeyHotaling2009

open Causation Causation.SEM Causation.Mechanism

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
  [SEM.IsDeterministic M]

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

def depth : V → ℕ := λ | .A => 0 | .X => 0 | .B => 1

private lemma oneLink_depth_lt : ∀ {u v : V}, u ∈ oneLink.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private lemma twoLink_depth_lt : ∀ {u v : V}, u ∈ twoLink.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def oneLinkRanking : CausalGraph.Ranking oneLink := ⟨depth, oneLink_depth_lt⟩

private def twoLinkRanking : CausalGraph.Ranking twoLink := ⟨depth, twoLink_depth_lt⟩

instance : CausalGraph.IsDAG oneLink := oneLinkRanking.isDAG

instance : CausalGraph.IsDAG twoLink := twoLinkRanking.isDAG

/-- A one-link model with the given equation at B. -/
noncomputable def oneLinkModel (f : Bool → Bool) : BoolSEM V :=
  { graph := oneLink
    mech := λ
      | .A => const (G := oneLink) false
      | .X => const (G := oneLink) false
      | .B => deterministic (λ ρ => f (ρ ⟨.A, by decide⟩)) }

/-- A two-link model with the given equation at B over A and X. -/
noncomputable def twoLinkModel (f : Bool → Bool → Bool) : BoolSEM V :=
  { graph := twoLink
    mech := λ
      | .A => const (G := twoLink) false
      | .X => const (G := twoLink) false
      | .B => deterministic (λ ρ => f (ρ ⟨.A, by decide⟩) (ρ ⟨.X, by decide⟩)) }

instance (f : Bool → Bool) : CausalGraph.IsDAG (oneLinkModel f).graph :=
  inferInstanceAs (CausalGraph.IsDAG oneLink)

instance (f : Bool → Bool → Bool) : CausalGraph.IsDAG (twoLinkModel f).graph :=
  inferInstanceAs (CausalGraph.IsDAG twoLink)

instance (f : Bool → Bool) : SEM.IsDeterministic (oneLinkModel f) where
  mech_det v := match v with
    | .A | .X => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .B => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

instance (f : Bool → Bool → Bool) : SEM.IsDeterministic (twoLinkModel f) where
  mech_det v := match v with
    | .A | .X => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .B => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- (2) *A causes B*: `B := A`. -/
noncomputable abbrev causes : BoolSEM V := oneLinkModel id

/-- (3) *A enables B*: `B := A ∧ X`. -/
noncomputable abbrev enables : BoolSEM V := twoLinkModel (· && ·)

/-- (4a) *A prevents B* with no accessory: `B := ¬A`. -/
noncomputable abbrev prevents : BoolSEM V := oneLinkModel (!·)

/-- (4b) *A prevents B* with an accessory: `B := ¬A ∧ X`. -/
noncomputable abbrev preventsAnd : BoolSEM V := twoLinkModel (λ a x => !a && x)

/-- (4c) *A prevents B* with an accessory: `B := ¬(A ∧ X)`. -/
noncomputable abbrev preventsNand : BoolSEM V := twoLinkModel (λ a x => !(a && x))

private lemma oneLink_entails_iff (f : Bool → Bool) {s : Valuation (λ _ : V => Bool)} {v : V}
    {x : Bool} : causallyEntails (oneLinkModel f) s v x ↔
      developDetVtxFuel (oneLinkModel f) s 2 v = some x :=
  causallyEntails_iff_fuel _ oneLinkRanking (by cases v <;> decide +revert) s x

private lemma twoLink_entails_iff (f : Bool → Bool → Bool) {s : Valuation (λ _ : V => Bool)}
    {v : V} {x : Bool} : causallyEntails (twoLinkModel f) s v x ↔
      developDetVtxFuel (twoLinkModel f) s 2 v = some x :=
  causallyEntails_iff_fuel _ twoLinkRanking (by cases v <;> decide +revert) s x

/-- The accessory present. -/
def accessory : Valuation (λ _ : V => Bool) := Valuation.empty.extend .X true

/-- *A causes B* holds of (2), and the model realizes `B := A`. -/
theorem causes_Causes : Causes causes .A .B ∧ EqCauses causes Valuation.empty .A .B :=
  ⟨by decide, λ v => (oneLink_entails_iff id).mpr (by cases v <;> decide)⟩

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
  (twoLink_entails_iff (· && ·)).not.mpr (by decide)

/-- With the accessory present, B follows from A. -/
theorem enables_entails_of_accessory :
    causallyEntails enables (accessory.extend .A true) .B true :=
  (twoLink_entails_iff (· && ·)).mpr (by decide)

/-- (4a) prevents: turning A on entails B off. -/
theorem prevents_Prevents :
    Prevents prevents Valuation.empty .A .B ∧ EqPrevents prevents Valuation.empty .A .B :=
  ⟨⟨by decide, (oneLink_entails_iff (!·)).mpr (by decide)⟩,
    λ v => (oneLink_entails_iff (!·)).mpr (by cases v <;> decide)⟩

/-- (4b) and (4c) prevent when the accessory is present, and (4b) does so as the equation
`B := ¬A` on that background. -/
theorem preventsAnd_Prevents :
    Prevents preventsAnd accessory .A .B ∧ EqPrevents preventsAnd accessory .A .B :=
  ⟨⟨by decide, (twoLink_entails_iff (λ a x => !a && x)).mpr (by decide)⟩,
    λ v => (twoLink_entails_iff (λ a x => !a && x)).mpr (by cases v <;> decide)⟩

theorem preventsNand_Prevents :
    Prevents preventsNand accessory .A .B ∧ EqPrevents preventsNand accessory .A .B :=
  ⟨⟨by decide, (twoLink_entails_iff (λ a x => !(a && x))).mpr (by decide)⟩,
    λ v => (twoLink_entails_iff (λ a x => !(a && x))).mpr (by cases v <;> decide)⟩

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

def chainDepth : W → ℕ := λ | .A => 0 | .X => 0 | .B => 1 | .C => 2

private lemma chainOne_depth_lt :
    ∀ {u v : W}, u ∈ chainOne.parents v → chainDepth u < chainDepth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private lemma chainTwo_depth_lt :
    ∀ {u v : W}, u ∈ chainTwo.parents v → chainDepth u < chainDepth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def chainOneRanking : CausalGraph.Ranking chainOne := ⟨chainDepth, chainOne_depth_lt⟩

private def chainTwoRanking : CausalGraph.Ranking chainTwo := ⟨chainDepth, chainTwo_depth_lt⟩

instance : CausalGraph.IsDAG chainOne := chainOneRanking.isDAG

instance : CausalGraph.IsDAG chainTwo := chainTwoRanking.isDAG

/-- The composition of a first premise `B := f A` with a second premise `C := g B`. -/
noncomputable def composeOne (f g : Bool → Bool) : BoolSEM W :=
  { graph := chainOne
    mech := λ
      | .A => const (G := chainOne) false
      | .X => const (G := chainOne) false
      | .B => deterministic (λ ρ => f (ρ ⟨.A, by decide⟩))
      | .C => deterministic (λ ρ => g (ρ ⟨.B, by decide⟩)) }

/-- The composition of a first premise `B := f A X` with a second premise `C := g B`. -/
noncomputable def composeTwo (f : Bool → Bool → Bool) (g : Bool → Bool) : BoolSEM W :=
  { graph := chainTwo
    mech := λ
      | .A => const (G := chainTwo) false
      | .X => const (G := chainTwo) false
      | .B => deterministic (λ ρ => f (ρ ⟨.A, by decide⟩) (ρ ⟨.X, by decide⟩))
      | .C => deterministic (λ ρ => g (ρ ⟨.B, by decide⟩)) }

instance (f g : Bool → Bool) : CausalGraph.IsDAG (composeOne f g).graph :=
  inferInstanceAs (CausalGraph.IsDAG chainOne)

instance (f : Bool → Bool → Bool) (g : Bool → Bool) : CausalGraph.IsDAG (composeTwo f g).graph :=
  inferInstanceAs (CausalGraph.IsDAG chainTwo)

instance (f g : Bool → Bool) : SEM.IsDeterministic (composeOne f g) where
  mech_det v := match v with
    | .A | .X => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .B | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

instance (f : Bool → Bool → Bool) (g : Bool → Bool) : SEM.IsDeterministic (composeTwo f g) where
  mech_det v := match v with
    | .A | .X => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .B | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

private lemma composeOne_entails_iff (f g : Bool → Bool) {s : Valuation (λ _ : W => Bool)}
    {v : W} {x : Bool} :
    causallyEntails (composeOne f g) s v x ↔ developDetVtxFuel (composeOne f g) s 3 v = some x :=
  causallyEntails_iff_fuel _ chainOneRanking (by cases v <;> decide +revert) s x

private lemma composeTwo_entails_iff (f : Bool → Bool → Bool) (g : Bool → Bool)
    {s : Valuation (λ _ : W => Bool)} {v : W} {x : Bool} :
    causallyEntails (composeTwo f g) s v x ↔ developDetVtxFuel (composeTwo f g) s 3 v = some x :=
  causallyEntails_iff_fuel _ chainTwoRanking (by cases v <;> decide +revert) s x

/-- The first premise's accessory present. -/
def chainAccessory : Valuation (λ _ : W => Bool) := Valuation.empty.extend .X true

/-- (5) and (6): *A causes B*, *B causes C* compose to `C := A`, the conclusion *A causes C*. -/
theorem causesCauses_causes : EqCauses (composeOne id id) Valuation.empty .A .C :=
  λ v => (composeOne_entails_iff id id).mpr (by cases v <;> decide)

/-- *A allows B*, *B prevents C*, or equally *not B causes C*, compose to `C := ¬(A ∧ X)`, the
accessory form (4c) of *prevents*: with the accessory present, A prevents C. -/
theorem allowsPrevents_prevents : EqPrevents (composeTwo (· && ·) (!·)) chainAccessory .A .C :=
  λ v => (composeTwo_entails_iff (· && ·) (!·)).mpr (by cases v <;> decide)

/-- *A prevents B*, *B prevents C* compose to `C := A`, the conclusion *A causes C*. -/
theorem preventsPrevents_causes : EqCauses (composeOne (!·) (!·)) Valuation.empty .A .C :=
  λ v => (composeOne_entails_iff (!·) (!·)).mpr (by cases v <;> decide)

/-! ### A three-premise argument, section 4.2 -/

/-- The terms of the three-premise argument. -/
inductive U
  | A | B | C | D
  deriving DecidableEq, Fintype

def line : CausalGraph U := ⟨λ | .A => ∅ | .B => {.A} | .C => {.B} | .D => {.C}⟩

def lineDepth : U → ℕ := λ | .A => 0 | .B => 1 | .C => 2 | .D => 3

private lemma line_depth_lt : ∀ {u v : U}, u ∈ line.parents v → lineDepth u < lineDepth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def lineRanking : CausalGraph.Ranking line := ⟨lineDepth, line_depth_lt⟩

instance : CausalGraph.IsDAG line := lineRanking.isDAG

/-- *A causes B*, *B causes not C*, *C causes not D*: `B := A`, `C := ¬B`, `D := ¬C`. -/
noncomputable def threePremise : BoolSEM U :=
  { graph := line
    mech := λ
      | .A => const (G := line) false
      | .B => deterministic (λ ρ => ρ ⟨.A, by decide⟩)
      | .C => deterministic (λ ρ => !ρ ⟨.B, by decide⟩)
      | .D => deterministic (λ ρ => !ρ ⟨.C, by decide⟩) }

instance : CausalGraph.IsDAG threePremise.graph := inferInstanceAs (CausalGraph.IsDAG line)

instance : SEM.IsDeterministic threePremise where
  mech_det v := match v with
    | .A => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .B | .C | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- The three premises compose to `D := A`, the conclusion *A causes D*. -/
theorem threePremise_causes : EqCauses threePremise Valuation.empty .A .D :=
  λ v => (causallyEntails_iff_fuel _ lineRanking (n := 4) (by decide +revert) _ _).mpr
    (by cases v <;> decide)

end SlomanBarbeyHotaling2009
