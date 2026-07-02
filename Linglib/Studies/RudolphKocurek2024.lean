import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Discourse.CommonGround
import Linglib.Core.Order.TotalPreorder
import Linglib.Core.Logic.FirstOrder.Comparative
import Linglib.Core.Order.ComparativeProbability.Systems
import Linglib.Semantics.Degree.Comparative
import Linglib.Semantics.Degree.Gradability.Delineation

/-!
# [rudolph-kocurek-2024]: Metalinguistic Gradability

Semantic expressivism for metalinguistic comparatives ("Ann is more a linguist
than a philosopher"), equatives, degree modifiers, and conditionals
[rudolph-kocurek-2024], with the revised semantics and degree-theoretic
formulation of its supplement [kocurek-2024-supplement]. Speakers express
interpretive as well as factual commitments: truth is evaluated at ⟨≤, i, w⟩
where ≤ is a total preorder over interpretations, and `A ≻ B` holds iff some
(A∧¬B)-interpretation ranked ≤ i dominates every (B∧¬A)-interpretation.

The formalization is model-theoretic throughout: an interpretation — the
paper's "function from expressions to intensions" — is a world-indexed family
of first-order structures, and the language with its basic semantics IS the
substrate's comparative-possibility logic
(`Core/Logic/FirstOrder/Comparative`): `L.CompFormula E` evaluated by
`CompFormula.Realize`, with ≻ the strict l-lifting. This file adds only what
is RK-specific: acceptance and the common ground, degree modifiers and the
conditional, the revised semantics, the delineation bridge, and the degree
theory.

## Main definitions

* `SemanticOrdering`, `Eval`, `EvalRevised` — the substrate's `CompFormula`
  language with the paper's basic (§4.2) and revised (supplement §B)
  semantics.
* `AssertoricContent`, `MetalinguisticCG` — acceptance and the common ground:
  the substrate's `ContextSet` at the ordering-world index, with assertion as
  `ContextSet.update` and the Stalnaker laws inherited.
* `DistanceFunction`, `EvalVery`, `EvalSorta`, `EvalMostly`, `EvalMCond` —
  degree modifiers (§6.1) and metalinguistic conditionals (§6.3).
* `degreeEquiv`, `strictlyBetter`, `MetaDegree` — the supplement's §C degree
  theory: metalinguistic degrees as a `Quotient` carrying `LinearOrder` and
  `BoundedOrder` instances.

## Main results

* `evalMuchMore_iff_strict_dominationLift`,
  `evalMostly_iff_strict_dominationLift` — ≫ and *mostly* are strict
  l-liftings ([holliday-icard-2013]), extending the substrate's grounding of
  ≻; the distance-function axioms are exactly totality of "not far below".
* `evalMCond_iff_entails` — for an MC-free consequent the conditional is
  Stalnakerian `ContextSet.entails` of the consequent by the antecedent-cone.
* `eval_mc_iff_delineation_of_noReversal` — under No Reversal (§7) the MC is
  [klein-1980]'s `Delineation.comparativeSem`.
* `mc_iff_degree_gt`, `me_iff_same_degree` — Facts 9–10: ≻ and ≈ are degree
  order and degree equality.
* `mc_iff_comparativeSem` — the paper's degree-theoretic claim, in substrate
  vocabulary: the revised MC is `Degree.comparativeSem` over the metalinguistic
  measure `formulaDeg`.
* Four finite models witness the §4.4 entailment patterns, nonclassical
  acceptance-preservation ([yalcin-2007]), and the supplement's ME-transitivity
  counterexample and its revised-semantics repair.
-/

namespace RudolphKocurek2024

open FirstOrder FirstOrder.Language in
/-! ### Interpretations and semantic orderings -/

open Core.Order (TotalPreorder)
open FirstOrder FirstOrder.Language
open ComparativeProbability

/-- The paper's ranking of interpretations by strength of interpretive
commitment (§4.2). -/
abbrev SemanticOrdering (I : Type*) := TotalPreorder I

/-! ### Semantics (§4.2 of the paper) -/

section Framework

variable {L : Language} {I W E : Type*} (interp : I → W → L.Structure E)

section Semantics

/-- Truth at an index ⟨≤, i, w⟩: `CompFormula.Realize` at the ordering's
`le`. -/
abbrev Eval (φ : L.CompFormula E) (ord : SemanticOrdering I) (i : I) (w : W) :
    Prop :=
  CompFormula.Realize interp φ ord.le i w

/-! ### Assertoric Content -/

/-- Assertoric content (§3.3): truth at all ≤-maximal interpretations —
`TotalPreorder.AcceptedAt`. Acceptance-preservation is nonclassical
(`mc_disj_not_accepted`). -/
def AssertoricContent [Fintype I] (φ : L.CompFormula E)
    (ord : SemanticOrdering I) (w : W) : Prop :=
  ord.AcceptedAt (fun i => Eval interp φ ord i w)

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (φ : L.CompFormula E) (ord : SemanticOrdering I) [DecidableRel ord.le] (w : W) :
    Decidable (AssertoricContent interp φ ord w) := by
  unfold AssertoricContent; infer_instance

end Semantics

/-! ### Distance Functions and Degree Modifiers (§6.1) -/

/-- A distance function (§6.1): which interpretations count as reasonably
close to each — the parameter behind *very*, *sorta*, *mostly*. -/
structure DistanceFunction (I : Type*) (ord : SemanticOrdering I) where
  /-- `close i i'` means i' is reasonably close to i. -/
  close : I → I → Prop
  /-- Centered: i ∈ d(i) -/
  centered : ∀ i, close i i
  /-- Top-bounded: if i' ∈ d(i), then i' ≤ i -/
  topBounded : ∀ i i', close i i' → ord.le i' i
  /-- Convex: if i' ∈ d(i) and i' ≤ i'' ≤ i, then i'' ∈ d(i) -/
  convex : ∀ i i' i'', close i i' → ord.le i' i'' → ord.le i'' i → close i i''
  /-- Noncontractive: if i' ∈ d(i) and i' ≤ j ≤ i, then i' ∈ d(j) -/
  noncontractive : ∀ i i' j, close i i' → ord.le i' j → ord.le j i → close j i'

/-- `i ≪ j`: i is below j and not even reasonably close to it. -/
def FarBelow {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i j : I) : Prop :=
  ord.le i j ∧ ¬ d.close j i

instance {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    [DecidableRel ord.le] [DecidableRel d.close] :
    DecidableRel (FarBelow ord d) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- ≪ is asymmetric: centeredness plus noncontractivity force mutually-≤
points to be close. -/
theorem FarBelow.asymm {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) {a b : I} (h : FarBelow ord d a b) :
    ¬ FarBelow ord d b a :=
  fun h' => h'.2 (d.noncontractive b b a (d.centered b) h'.1 h.1)

/-- "Not far below" is total — what lets the strict l-lifting characterize ≫. -/
theorem not_farBelow_total {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) (a b : I) :
    ¬ FarBelow ord d a b ∨ ¬ FarBelow ord d b a :=
  imp_iff_not_or.mp (FarBelow.asymm d)

section Modifiers

variable [Fintype I] (φ ψ : L.CompFormula E) (ord : SemanticOrdering I)
  (below : I → I → Prop) (d : DistanceFunction I ord) (i : I) (w : W)

/-- The paper's comparative template — the substrate's `coneStrictLift` at the
formulas' truth sets: ≻'s clause with an arbitrary dominance relation in
place of < (`eval_comp_iff_compWith`); ≫ is the instance at ≪. -/
abbrev EvalCompWith : Prop :=
  coneStrictLift ord.le below
    (fun j => Eval interp φ ord j w) (fun j => Eval interp ψ ord j w) i

omit [Fintype I] in
/-- ≻ is the template at <. -/
theorem eval_comp_iff_compWith :
    Eval interp (.comp φ ψ) ord i w ↔ EvalCompWith interp φ ψ ord ord.lt i w :=
  Iff.rfl

/-- Much more (A ≫ B): the template at ≪. -/
abbrev EvalMuchMore : Prop :=
  EvalCompWith interp φ ψ ord (FarBelow ord d) i w

/-- very A := A ≫ ¬A — every reasonably close interpretation makes A true. -/
abbrev EvalVery : Prop :=
  EvalMuchMore interp φ (.not φ) ord d i w

/-- sorta A := ¬ very ¬A — some reasonably close interpretation makes A true. -/
abbrev EvalSorta : Prop :=
  ¬ EvalVery interp (.not φ) ord d i w

/-- mostly A (eq. 97 of [rudolph-kocurek-2024]): some reasonably high level
strictly below the top makes A uniformly true, and every A-false level below
the current interpretation sits below it. Compatible with A and with ¬A
(unlike `very`); entails `sorta A`; `mostly A ∧ mostly ¬A` is contradictory. -/
def EvalMostly : Prop :=
  ∃ i', ord.lt i' i ∧ d.close i i' ∧
    (∀ j, ord.equiv j i' → Eval interp φ ord j w) ∧
    ∀ i'', ord.lt i'' i → (∀ j, ord.equiv j i'' → ¬ Eval interp φ ord j w) →
      ord.lt i'' i'

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] [DecidableRel d.close] :
    Decidable (EvalMostly interp φ ord d i w) := by
  unfold EvalMostly
  haveI h1 : DecidableRel ord.lt := inferInstance
  haveI h2 : DecidableRel ord.equiv := inferInstance
  haveI h3 : ∀ j, Decidable (Eval interp φ ord j w) := fun j => inferInstance
  infer_instance

end Modifiers

section ModifierGroundings

variable (φ ψ : L.CompFormula E) (ord : SemanticOrdering I)
  (d : DistanceFunction I ord) (i : I) (w : W)

/-- **Grounding**: ≫ is the strict l-lifting under the *coarser* total
preorder "not far below" — the distance-function axioms are exactly what
make that relation total, so [holliday-icard-2013]'s lift machinery applies
with ≪ in the role of <. -/
theorem evalMuchMore_iff_strict_dominationLift :
    EvalMuchMore interp φ ψ ord d i w ↔
    Strict
      (dominationLift (fun a b => ¬ FarBelow ord d a b))
      {x | ord.le x i ∧ Eval interp φ ord x w ∧ ¬ Eval interp ψ ord x w}
      {x | ord.le x i ∧ Eval interp ψ ord x w ∧ ¬ Eval interp φ ord x w} :=
  coneStrictLift_iff_strict_dominationLift
    (fun a b => not_farBelow_total d a b)
    (fun _ _ => ⟨fun h => ⟨FarBelow.asymm d h, not_not_intro h⟩,
      fun h => not_not.mp h.2⟩) _ _ i

/-- **Grounding**: *mostly* is the strict l-lifting comparing φ-uniform
*levels* (`ord.equiv`-classes, mathlib's `AntisymmRel.setoid`): some
reasonably-high all-φ level strictly below the index dominates every
all-¬φ level below it. -/
theorem evalMostly_iff_strict_dominationLift :
    EvalMostly interp φ ord d i w ↔
    Strict
      (dominationLift (fun a b => ord.le b a))
      {x | ord.lt x i ∧ d.close i x ∧ ∀ j, ord.equiv j x → Eval interp φ ord j w}
      {x | ord.lt x i ∧ ∀ j, ord.equiv j x → ¬ Eval interp φ ord j w} := by
  rw [strict_dominationLift_iff_below
    (fun a b => ord.le_total b a) (fun _ _ => Iff.rfl)]
  simp only [Set.mem_setOf_eq, and_imp, and_assoc]
  rfl

end ModifierGroundings

/-! ### No Reversal and the delineation bridge ([klein-1980], §7) -/

/-- No Reversal (van Benthem 1990; §7 of [rudolph-kocurek-2024]): below any
interpretation separating `a` from `b`, every extension admitting `b` admits
`a` — the order-restricted analogue of Klein's monotone delineation. -/
def NoReversal (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)
    (a b : E) : Prop :=
  ∀ i i', ord.le i' i →
    a ∈ (interp i w).ext₁ R → b ∉ (interp i w).ext₁ R →
    b ∈ (interp i' w).ext₁ R → a ∈ (interp i' w).ext₁ R

instance [Fintype I] [DecidableAtoms interp]
    (ord : SemanticOrdering I) [DecidableRel ord.le]
    (R : L.Relations 1) (w : W) (a b : E) :
    Decidable (NoReversal interp ord R w a b) := by
  unfold NoReversal; simp only [Structure.mem_ext₁]; infer_instance

section Delineation

variable (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)

/-- The delineation induced by a ranked interpretation family: admissible
comparison classes are the extensions of `R` in the ≤-cone; `x` is R-in-C iff
`x ∈ C`. Instantiates [klein-1980]'s comparison-class parameter. -/
def interpretationDelineation (i : I) :
    Semantics.Gradability.Delineation.ComparisonClass E → E → Prop :=
  fun C x =>
    (∃ i', ord.le i' i ∧ C = (interp i' w).ext₁ R) ∧ x ∈ C

/-- The delineation comparative over the induced delineation is the ∃-witness
clause of the MC: some cone extension separates `a` from `b`. -/
theorem delineation_comparativeSem_iff (i : I) (a b : E) :
    Semantics.Gradability.Delineation.comparativeSem
      (interpretationDelineation interp ord R w i) a b ↔
    ∃ i', ord.le i' i ∧ a ∈ (interp i' w).ext₁ R ∧ b ∉ (interp i' w).ext₁ R := by
  constructor
  · rintro ⟨C, ⟨⟨i', h_le, rfl⟩, h_aC⟩, h_nb⟩
    exact ⟨i', h_le, h_aC, fun hb => h_nb ⟨⟨i', h_le, rfl⟩, hb⟩⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    exact ⟨(interp i' w).ext₁ R, ⟨⟨i', h_le, rfl⟩, h_a⟩,
      fun h => h_b h.2⟩

/-- **The §7 bridge, in the substrate's vocabulary**: under No Reversal, the
metalinguistic comparative for a gradable predicate IS [klein-1980]'s
delineation comparative (`Delineation.comparativeSem`) over the
interpretation-induced delineation — the paper's eq. (128): NR makes the
domination clause of the MC semantics redundant. -/
theorem eval_mc_iff_delineation_of_noReversal (i : I) (a b : E)
    (hnr : NoReversal interp ord R w b a) :
    Eval interp (.comp (.matom R a) (.matom R b)) ord i w ↔
    Semantics.Gradability.Delineation.comparativeSem
      (interpretationDelineation interp ord R w i) a b := by
  rw [Eval, CompFormula.realize_comp_iff, delineation_comparativeSem_iff]
  simp only [CompFormula.realize_matom, ← Structure.mem_ext₁]
  constructor
  · rintro ⟨i', h_le, h_A, h_B, -⟩
    exact ⟨i', h_le, h_A, h_B⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    refine ⟨i', h_le, h_a, h_b, fun i'' h'' hB'' hA'' => ?_⟩
    have h_not : ¬ ord.le i' i'' :=
      fun hle' => h_b (hnr i'' i' hle' hB'' hA'' h_a)
    rcases ord.le_total i'' i' with h1 | h2
    · exact ⟨h1, h_not⟩
    · exact absurd h2 h_not

end Delineation

/-! ### Revised Semantics ([kocurek-2024-supplement] §B) -/

section Revised

/-- Truth under the revised MC semantics ([kocurek-2024-supplement] §B). The
basic semantics fails ME transitivity; the revision strengthens the MC: the
(A∧¬B)-witness must dominate either all B-interpretations or all
¬A-interpretations, blocking vacuous comparatives.

Properties ([kocurek-2024-supplement] §B): all basic entailment patterns
(Fact 3 a–n) are preserved (Fact 5); ME transitivity is validated (Fact 6);
interdefinable with the basic semantics (Fact 7). -/
def EvalRevised (φ : L.CompFormula E) (ord : SemanticOrdering I) (i : I) (w : W) : Prop :=
  match φ with
  | .ofFormula ψ => @Formula.Realize _ _ (interp i w) _ ψ id
  | .not A => ¬ EvalRevised A ord i w
  | .inf A B => EvalRevised A ord i w ∧ EvalRevised B ord i w
  | .sup A B => EvalRevised A ord i w ∨ EvalRevised B ord i w
  | .comp A B =>
      ∃ i', ord.le i' i ∧ EvalRevised A ord i' w ∧
        ¬ EvalRevised B ord i' w ∧
        ((∀ i'', ord.le i'' i → EvalRevised B ord i'' w → ord.lt i'' i') ∨
         (∀ i'', ord.le i'' i → ¬ EvalRevised A ord i'' w → ord.lt i'' i'))

instance EvalRevised.instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp]
    (φ : L.CompFormula E) (ord : SemanticOrdering I) [DecidableRel ord.le]
    (i : I) (w : W) :
    Decidable (EvalRevised interp φ ord i w) :=
  match φ with
  | .ofFormula ψ =>
      @Formula.decRealize L E (interp i w) _ _ (fun n r x => hA i w n r x) E ψ id
  | .not A =>
      haveI := EvalRevised.instDec A ord i w
      inferInstanceAs (Decidable (¬ EvalRevised interp A ord i w))
  | .inf A B =>
      haveI := EvalRevised.instDec A ord i w
      haveI := EvalRevised.instDec B ord i w
      inferInstanceAs (Decidable (EvalRevised interp A ord i w ∧
        EvalRevised interp B ord i w))
  | .sup A B =>
      haveI := EvalRevised.instDec A ord i w
      haveI := EvalRevised.instDec B ord i w
      inferInstanceAs (Decidable (EvalRevised interp A ord i w ∨
        EvalRevised interp B ord i w))
  | .comp A B =>
      haveI : ∀ j v, Decidable (EvalRevised interp A ord j v) :=
        (EvalRevised.instDec A ord · ·)
      haveI : ∀ j v, Decidable (EvalRevised interp B ord j v) :=
        (EvalRevised.instDec B ord · ·)
      inferInstanceAs (Decidable (∃ i', ord.le i' i ∧
        EvalRevised interp A ord i' w ∧ ¬ EvalRevised interp B ord i' w ∧
        ((∀ i'', ord.le i'' i → EvalRevised interp B ord i'' w → ord.lt i'' i') ∨
         (∀ i'', ord.le i'' i → ¬ EvalRevised interp A ord i'' w → ord.lt i'' i'))))

variable (A B : L.CompFormula E) (ord : SemanticOrdering I) (i : I) (w : W)

/-- Characterization of the revised MC case — definitional. -/
theorem evalRevised_mc_iff :
    EvalRevised interp (.comp A B) ord i w ↔
    ∃ i', ord.le i' i ∧ EvalRevised interp A ord i' w ∧
      ¬ EvalRevised interp B ord i' w ∧
      ((∀ i'', ord.le i'' i → EvalRevised interp B ord i'' w → ord.lt i'' i') ∨
       (∀ i'', ord.le i'' i → ¬ EvalRevised interp A ord i'' w → ord.lt i'' i')) :=
  Iff.rfl

end Revised

/-! ### Metalinguistic Conditional (§6.3) -/

section MCond

variable [Fintype I] (A B : L.CompFormula E)

/-- Restrict an ordering relation to A-interpretations (§6.3): drops non-A
interpretations, so the result satisfies reflexivity (at A-interpretations)
and transitivity but not totality — hence the consequent of a conditional is
evaluated via `EvalGen` rather than `Eval`. -/
def restrictLE (le : I → I → Prop) (w : W) : I → I → Prop :=
  fun i j => le i j ∧ CompFormula.Realize interp A le i w ∧ CompFormula.Realize interp A le j w

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (le : I → I → Prop) [DecidableRel le] (w : W) :
    DecidableRel (restrictLE interp A le w) := fun _ _ => by
  unfold restrictLE; infer_instance

variable (ord : SemanticOrdering I) (i : I) (w : W)

/-- Metalinguistic conditional (eq. 120 of [rudolph-kocurek-2024]): the
antecedent is evaluated with the full ordering, the consequent with the
A-restricted ordering ≤_A. For non-metagradable A and B this reduces to
interpretation-strict implication.

Key properties: C1 (conditionals entail weak comparatives), M1
(⊨ A → (A ≻ ¬A), see `mcond_m1`), failure of modus tollens for acceptance. -/
def EvalMCond : Prop :=
  ∀ i', ord.le i' i → CompFormula.Realize interp A ord.le i' w →
    CompFormula.Realize interp B (restrictLE interp A ord.le w) i' w

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] :
    Decidable (EvalMCond interp A B ord i w) := by
  unfold EvalMCond; infer_instance

omit [Fintype I] in
/-- **Grounding in the common-ground substrate**: for an MC-free consequent —
strictly weaker than the paper's reduction, which also assumes the antecedent
MC-free — the metalinguistic conditional is Stalnakerian entailment
(`ContextSet.entails`) of the consequent by the ranked antecedent-cone. The
antecedent may contain ≻ freely: it is always evaluated at the full ordering,
and an MC-free consequent never consults the restricted one. -/
theorem evalMCond_iff_entails (hB : B.CompFree) :
    EvalMCond interp A B ord i w ↔
    CommonGround.ContextSet.entails
      {x | ord.le x i ∧ CompFormula.Realize interp A ord.le x w}
      {x | CompFormula.Realize interp B ord.le x w} := by
  constructor
  · rintro h x ⟨hx1, hx2⟩
    exact (CompFormula.realize_congr_of_compFree interp B hB _ _ x w).mp (h x hx1 hx2)
  · intro h x hx hAx
    exact (CompFormula.realize_congr_of_compFree interp B hB _ _ x w).mpr (h ⟨hx, hAx⟩)

end MCond

end Framework

/-! ### Connection to Common Ground -/

open CommonGround (ContextSet HasContextSet)

/-- An ordering-world pair: the enriched index for the metalinguistic common
ground — a Stalnakerian world that fixes interpretive as well as factual
commitments. -/
structure OrderingWorldPair (I W : Type*) where
  ord : SemanticOrdering I
  world : W

/-- The metalinguistic common ground IS the substrate's `ContextSet`, taken at
the enriched index type: the Stalnaker generalization is "same object, richer worlds", so `ContextSet.update` and its laws apply unchanged. -/
abbrev MetalinguisticCG (I W : Type*) := ContextSet (OrderingWorldPair I W)

namespace MetalinguisticCG

variable {I W : Type*}

/-- Project to a classical context set: forget the ordering coordinate
(`Set.image` of the world projection). A world survives iff some ordering
paired with it does. -/
def toContextSet (cg : MetalinguisticCG I W) : ContextSet W :=
  OrderingWorldPair.world '' cg

variable {L : Language} {E : Type*} [Fintype I] [Fintype E] [DecidableEq E]
  (interp : I → W → L.Structure E) [DecidableAtoms interp]

/-- The proposition a formula expresses over the enriched index: the
ordering-world pairs at which its assertoric content holds. -/
def assertoricProp (φ : L.CompFormula E) : Set (OrderingWorldPair I W) :=
  {pair | AssertoricContent interp φ pair.ord pair.world}

/-- Assertion is the substrate's `ContextSet.update` with the assertoric
proposition — not a new operation. -/
def updateAssertoric (cg : MetalinguisticCG I W) (φ : L.CompFormula E) :
    MetalinguisticCG I W :=
  ContextSet.update cg (assertoricProp interp φ)

omit [Fintype E] [DecidableEq E] [DecidableAtoms interp] in
/-- Stalnaker's law at the enriched type: assertion restricts the common
ground (inherited from `ContextSet.update_restricts`). -/
theorem updateAssertoric_restricts (cg : MetalinguisticCG I W)
    (φ : L.CompFormula E) : updateAssertoric interp cg φ ⊆ cg :=
  ContextSet.update_restricts _ _

omit [Fintype E] [DecidableEq E] [DecidableAtoms interp] in
/-- Assertion order is irrelevant (inherited from `ContextSet.update_comm`). -/
theorem updateAssertoric_comm (cg : MetalinguisticCG I W)
    (φ ψ : L.CompFormula E) :
    updateAssertoric interp (updateAssertoric interp cg φ) ψ =
      updateAssertoric interp (updateAssertoric interp cg ψ) φ :=
  ContextSet.update_comm _ _ _

omit [Fintype E] [DecidableEq E] [DecidableAtoms interp] in
/-- Reassertion is idempotent (inherited from `ContextSet.update_idem`). -/
theorem updateAssertoric_idem (cg : MetalinguisticCG I W)
    (φ : L.CompFormula E) :
    updateAssertoric interp (updateAssertoric interp cg φ) φ =
      updateAssertoric interp cg φ :=
  ContextSet.update_idem _ _

omit [Fintype E] [DecidableEq E] [DecidableAtoms interp] in
/-- The projection is monotone, so assertion restricts the projected classical
context set too: the enriched update is Stalnaker-conservative. (That the
update does NOT factor through the projection — interpretive commitments do
real work — is the paper's expressivist thesis.) -/
theorem toContextSet_updateAssertoric_subset (cg : MetalinguisticCG I W)
    (φ : L.CompFormula E) :
    toContextSet (updateAssertoric interp cg φ) ⊆ toContextSet cg :=
  Set.image_mono (updateAssertoric_restricts interp cg φ)

end MetalinguisticCG

/-- MetalinguisticCG projects to a ContextSet via HasContextSet. -/
instance {I W : Type*} : HasContextSet (MetalinguisticCG I W) W where
  toContextSet := MetalinguisticCG.toContextSet

noncomputable section DegreeTheory

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

/-! ### Field and Denotation Sets -/

open Classical in
/-- The field I_i: the set of interpretations ranked at or below i.
Classical: the degree theory proves structure, it never computes. -/
def field : Finset I :=
  Finset.univ.filter (fun j => ord.le j i)

open Classical in
/-- The denotation of a formula: the set of interpretations in I_i
where the formula is true (under the revised semantics). -/
def denotation (φ : L.CompFormula E) (w : W) : Finset I :=
  (field ord i).filter (fun j => EvalRevised interp φ ord j w)

omit [DecidableEq I] in
open Classical in
theorem denotation_subset_field (φ : L.CompFormula E) (w : W) :
    denotation interp ord i φ w ⊆ field ord i :=
  Finset.filter_subset _ _

/-! ### The ∼ Equivalence Relation ([kocurek-2024-supplement] §C, p. 9) -/

variable (X Y Z : Finset I)

/-- ∼ condition (i): each element of `X \ Y` is matched by one of `Y \ X` at
least as high, and vice versa. -/
def equivCond1 : Prop :=
  (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'') ∧
  (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'')

/-- ∼ condition (ii): each element of the symmetric difference is dominated
both by an element of `X ∩ Y` and by one of the field outside `X ∪ Y`. -/
def equivCond2 : Prop :=
  ∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'') ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'')

/-- Metalinguistic degree equivalence `X ∼_i Y`: the revised ME truth
conditions applied to interpretation sets. -/
def degreeEquiv : Prop :=
  equivCond1 ord X Y ∨ equivCond2 ord i X Y

/-! ### Fact 8: ∼ is an Equivalence Relation -/

/-- Fact 8a: ∼ is reflexive. -/
theorem degreeEquiv_refl : degreeEquiv ord i X X := by
  left
  constructor <;> intro i' h <;> simp at h

/-- Fact 8b: ∼ is symmetric. -/
theorem degreeEquiv_symm : degreeEquiv ord i X Y → degreeEquiv ord i Y X := by
  rintro (h1 | h2)
  · exact Or.inl ⟨h1.2, h1.1⟩
  · refine Or.inr ?_
    unfold equivCond2 at h2 ⊢
    rwa [Finset.union_comm, Finset.inter_comm]

/-! ### The ⊐ Ordering on Sets ([kocurek-2024-supplement] §C, p. 10) -/

/-- `X ⊐ Y`: some witness in `X \ Y` inside the field dominates all of
`Y \ X` and, moreover, all of `X ∩ Y` or all of the field outside `X ∪ Y` —
the revised MC truth conditions applied to interpretation sets. -/
def strictlyBetter : Prop :=
  ∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i') ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i') ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i'))

omit [Fintype I] in
/-- If m dominates X ∩ Y and Y \ X, it dominates all of Y. -/
private lemma dom_all_of_inter_sdiff (m : I) (X Y : Finset I)
    (h_cap : ∀ c ∈ X ∩ Y, ord.lt c m)
    (h_sdiff : ∀ y ∈ Y \ X, ord.lt y m) :
    ∀ y ∈ Y, ord.lt y m := by
  intro y hy
  by_cases hyx : y ∈ X
  · exact h_cap y (Finset.mem_inter.mpr ⟨hyx, hy⟩)
  · exact h_sdiff y (Finset.mem_sdiff.mpr ⟨hy, hyx⟩)

/-- If m dominates Y \ X and field ord i \ (X ∪ Y), it dominates field ord i \ X. -/
private lemma dom_fX_of_sdiff_comp (m : I) (X Y : Finset I)
    (h_yx : ∀ y ∈ Y \ X, ord.lt y m)
    (h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m) :
    ∀ c ∈ field ord i \ X, ord.lt c m := by
  intro c hc
  by_cases hc_y : c ∈ Y
  · exact h_yx c (Finset.mem_sdiff.mpr ⟨hc_y, (Finset.mem_sdiff.mp hc).2⟩)
  · exact h_comp c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
      fun h => Finset.mem_union.mp h |>.elim (Finset.mem_sdiff.mp hc).2 hc_y⟩)

omit [Fintype I] in
/-- Both presentations of the symmetric difference `X ∆ Y`. -/
private lemma mem_symdiff_iff (X Y : Finset I) (s : I) :
    s ∈ (X ∪ Y) \ (X ∩ Y) ↔ s ∈ (X \ Y) ∪ (Y \ X) := by
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

omit [Fintype I] in
/-- The symmetric difference of distinct sets is nonempty. -/
private lemma symdiff_nonempty (X Y : Finset I) (h : X ≠ Y) :
    ((X \ Y) ∪ (Y \ X)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne, Finset.union_eq_empty,
    Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset]
  exact fun ⟨hXY, hYX⟩ => h (Finset.Subset.antisymm hXY hYX)

/-! ### Facts 11–12: ⊐ on Degrees -/

/-- Fact 12a: ⊐ is irreflexive. -/
theorem strictlyBetter_irrefl : ¬ strictlyBetter ord i X X := by
  intro ⟨i', hi', _, _, _⟩
  simp at hi'

/-- ∼ refutes ⊐: equivalent sets are incomparable. -/
theorem degreeEquiv_not_strictlyBetter :
    degreeEquiv ord i X Y → ¬ strictlyBetter ord i X Y := by
  intro h_eq ⟨i', h_sdiff, _, h_ymx, h_inner⟩
  rcases h_eq with ⟨h_match, _⟩ | h2
  · -- equivCond1: i' ∈ X\Y is matched by i'' ∈ Y\X with i' ≤ i''
    obtain ⟨i'', h_i''_sdiff, h_le⟩ := h_match i' h_sdiff
    exact (h_ymx i'' h_i''_sdiff).2 h_le
  · -- equivCond2: i' ∈ (X ∪ Y) \ (X ∩ Y), dominated by X∩Y and field\(X∪Y)
    have h_symdiff : i' ∈ (X ∪ Y) \ (X ∩ Y) :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp h_sdiff).1),
         fun h => (Finset.mem_sdiff.mp h_sdiff).2 (Finset.mem_inter.mp h).2⟩
    obtain ⟨⟨i₁, h_i₁_mem, h_le₁⟩, ⟨i₂, h_i₂_mem, h_le₂⟩⟩ := h2 i' h_symdiff
    rcases h_inner with h_cap | h_comp
    · exact (h_cap i₁ h_i₁_mem).2 h_le₁
    · exact (h_comp i₂ h_i₂_mem).2 h_le₂

/-- Fact 11: ⊐ respects ∼ on the right — `X ⊐ Y` and `Y ∼ Z` give `X ⊐ Z`. -/
theorem strictlyBetter_respects_right (_hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hyz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    -- z ∈ Z, z ∉ Y → lt z m (via Y∼Z matching + m_dom_Y)
    have z_ny_lt : ∀ z, z ∈ Z → z ∉ Y → ord.lt z m := by
      intro z hz hny
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · obtain ⟨y', hy', hle⟩ := hyz_b z (Finset.mem_sdiff.mpr ⟨hz, hny⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_Y y' (Finset.mem_sdiff.mp hy').1)
      · obtain ⟨⟨c, hc, hle⟩, _⟩ := hyz2 z
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hz),
            fun h => hny (Finset.mem_inter.mp h).1⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_Y c (Finset.mem_inter.mp hc).1)
    -- m ∉ Z forced
    have hm_nz : m ∉ Z :=
      fun hm_z => absurd (z_ny_lt m hm_z hm_ny) (ord.lt_irrefl m)
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_nz⟩, hm_f, ?_, Or.inl ?_⟩
    · intro z hz
      by_cases hz_y : z ∈ Y
      · exact hm_yx z (Finset.mem_sdiff.mpr ⟨hz_y, (Finset.mem_sdiff.mp hz).2⟩)
      · exact z_ny_lt z (Finset.mem_sdiff.mp hz).1 hz_y
    · intro c hc
      by_cases hc_y : c ∈ Y
      · exact m_dom_Y c hc_y
      · exact z_ny_lt c (Finset.mem_inter.mp hc).2 hc_y
  · -- RIGHT INNER: m dominates field ord i \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- Helper: w ∈ X forced when m_dom_fX w gives lt w m, contradicting le m w
    have forced_in_X (w : I) (hw_f : w ∈ field ord i) (hle : ord.le m w) :
        w ∈ X := by
      by_contra h
      exact (m_dom_fX w (Finset.mem_sdiff.mpr ⟨hw_f, h⟩)).2 hle
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z ∩ X: find alternative witness via Y∼Z
      -- Helper: once we have witness w ∈ X\Z with le m w, build the ⊐ proof
      suffices ∃ w, w ∈ X \ Z ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inr ?_⟩
        · intro z hz; exact ord.lt_of_lt_of_le
            (m_dom_fX z (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz).1,
              (Finset.mem_sdiff.mp hz).2⟩)) hle
        · intro c hc; exact ord.lt_of_lt_of_le
            (m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
              fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)) hle
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · -- cond1: m ∈ Z\Y → ∃ y₀ ∈ Y\Z, le m y₀; y₀ ∈ X forced
        obtain ⟨y₀, hy₀, hle⟩ := hyz_b m (Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩)
        exact ⟨y₀, Finset.mem_sdiff.mpr ⟨forced_in_X y₀ (hYf (Finset.mem_sdiff.mp hy₀).1) hle,
          (Finset.mem_sdiff.mp hy₀).2⟩, hYf (Finset.mem_sdiff.mp hy₀).1, hle⟩
      · -- cond2: ∃ c₂ ∈ field ord i\(Y∪Z), le m c₂; c₂ ∈ X forced
        obtain ⟨_, ⟨c₂, hc₂, hle⟩⟩ := hyz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hm_z),
            fun h => hm_ny (Finset.mem_inter.mp h).1⟩)
        exact ⟨c₂, Finset.mem_sdiff.mpr ⟨forced_in_X c₂ (Finset.mem_sdiff.mp hc₂).1 hle,
          fun h => (Finset.mem_sdiff.mp hc₂).2 (Finset.mem_union.mpr (Or.inr h))⟩,
          (Finset.mem_sdiff.mp hc₂).1, hle⟩
    · -- m ∉ Z: witness = m ∈ X\Z
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩, hm_f, ?_, Or.inr ?_⟩
      · intro z hz; exact m_dom_fX z (Finset.mem_sdiff.mpr
          ⟨hZf (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩)
      · intro c hc; exact m_dom_fX c (Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hc).1,
           fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)

/-- Fact 11: ⊐ respects ∼ on the left — `X ⊐ Y` and `X ∼ Z` give `Z ⊐ Y`. -/
theorem strictlyBetter_respects_left (hXf : X ⊆ field ord i) (_hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i X Z →
    strictlyBetter ord i Z Y := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hxz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z: witness m ∈ Z\Y
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inl ?_⟩
      · intro y hy; exact m_dom_Y y (Finset.mem_sdiff.mp hy).1
      · intro c hc; exact m_dom_Y c (Finset.mem_inter.mp hc).2
    · -- m ∉ Z: use X∼Z to find w ∈ Z with le m w, w ∉ Y forced
      -- Once we have w, the proof is uniform
      suffices ∃ w, w ∈ Z \ Y ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inl ?_⟩
        · intro y hy; exact ord.lt_of_lt_of_le
            (m_dom_Y y (Finset.mem_sdiff.mp hy).1) hle
        · intro c hc; exact ord.lt_of_lt_of_le
            (m_dom_Y c (Finset.mem_inter.mp hc).2) hle
      -- Helper: w ∉ Y when m_dom_Y w and le m w (lt w m contradicts le m w)
      have not_in_Y (w : I) (hle : ord.le m w) : w ∉ Y :=
        fun h => (m_dom_Y w h).2 hle
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z₀, hz₀, hle⟩ := hxz_a m (Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩)
        exact ⟨z₀, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz₀).1, not_in_Y z₀ hle⟩,
          hZf (Finset.mem_sdiff.mp hz₀).1, hle⟩
      · obtain ⟨⟨z₁, hz₁, hle⟩, _⟩ := hxz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hm_x),
            fun h => hm_z (Finset.mem_inter.mp h).2⟩)
        exact ⟨z₁, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz₁).2, not_in_Y z₁ hle⟩,
          hXf (Finset.mem_inter.mp hz₁).1, hle⟩
  · -- RIGHT INNER: m dominates field ord i \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- c ∈ X\Z → lt c m (via X∼Z matching to field\X, then m_dom_fX)
    have lt_via_xz : ∀ c, c ∈ X → c ∉ Z → ord.lt c m := by
      intro c hc_x hc_nz
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z', hz', hle⟩ := hxz_a c (Finset.mem_sdiff.mpr ⟨hc_x, hc_nz⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_fX z'
          (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz').1,
            (Finset.mem_sdiff.mp hz').2⟩))
      · obtain ⟨_, ⟨c', hc', hle⟩⟩ := hxz2 c
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hc_x),
            fun h => hc_nz (Finset.mem_inter.mp h).2⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_fX c'
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc').1,
            fun h => (Finset.mem_sdiff.mp hc').2 (Finset.mem_union.mpr (Or.inl h))⟩))
    -- m ∈ Z forced
    have hm_z : m ∈ Z := by
      by_contra hm_nz; exact absurd (lt_via_xz m hm_x hm_nz) (ord.lt_irrefl m)
    -- Witness m ∈ Z\Y
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inr ?_⟩
    · intro y hy
      by_cases hy_x : y ∈ X
      · exact lt_via_xz y hy_x (Finset.mem_sdiff.mp hy).2
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hy_x⟩)
    · intro c hc
      by_cases hc_x : c ∈ X
      · exact lt_via_xz c hc_x
          (fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h)))
      · exact m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1, hc_x⟩)

/-- Fact 12b: ⊐ is transitive. -/
theorem strictlyBetter_trans :
    strictlyBetter ord i X Y → strictlyBetter ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m₁, hm₁_sd, hm₁_f, hm₁_yx, hm₁_inner⟩
         ⟨m₂, hm₂_sd, hm₂_f, hm₂_zy, hm₂_inner⟩
  have hm₁_x := (Finset.mem_sdiff.mp hm₁_sd).1
  have hm₁_ny := (Finset.mem_sdiff.mp hm₁_sd).2
  have hm₂_y := (Finset.mem_sdiff.mp hm₂_sd).1
  have hm₂_nz := (Finset.mem_sdiff.mp hm₂_sd).2
  -- Key helper: z ∈ Z\X → lt z m₁ (when m₂ ≤ m₁)
  have zx_lt_m1 (hle : ord.le m₂ m₁) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₁ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)
    · exact ord.lt_of_lt_of_le (hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)) hle
  -- Key helper: z ∈ Z\X → lt z m₂ (when m₁ ≤ m₂)
  have zx_lt_m2 (hle : ord.le m₁ m₂) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₂ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact ord.lt_of_lt_of_le
        (hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)) hle
    · exact hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)
  rcases ord.le_total m₂ m₁ with hle | hle
  · -- Case: m₂ ≤ m₁. Witness = m₁.
    -- m₁ ∉ Z: lt m₁ m₂ ∧ le m₂ m₁ → lt m₁ m₁
    have hm₁_nz : m₁ ∉ Z := fun h =>
      absurd (ord.lt_of_lt_of_le
        (hm₂_zy m₁ (Finset.mem_sdiff.mpr ⟨h, hm₁_ny⟩)) hle) (ord.lt_irrefl m₁)
    refine ⟨m₁, Finset.mem_sdiff.mpr ⟨hm₁_x, hm₁_nz⟩, hm₁_f, zx_lt_m1 hle, ?_⟩
    -- Inner disjunct: follows from X⊐Y's inner
    rcases hm₁_inner with h_cap | h_comp
    · -- Left: ∀ X∩Y < m₁ → ∀ X∩Z < m₁
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_x, hc_y⟩)
      · exact ord.lt_of_lt_of_le
          (hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)) hle
    · -- Right: ∀ field\(X∪Y) < m₁ → ∀ field\(X∪Z) < m₁
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_nx hc_y⟩)
  · -- Case: m₁ ≤ m₂. Witness = m₂.
    -- m₂ ∈ X: lt m₂ m₁ ∧ le m₁ m₂ → lt m₂ m₂
    have hm₂_x : m₂ ∈ X := by
      by_contra h; exact absurd (ord.lt_of_lt_of_le
        (hm₁_yx m₂ (Finset.mem_sdiff.mpr ⟨hm₂_y, h⟩)) hle) (ord.lt_irrefl m₂)
    refine ⟨m₂, Finset.mem_sdiff.mpr ⟨hm₂_x, hm₂_nz⟩, hm₂_f, zx_lt_m2 hle, ?_⟩
    -- Inner disjunct: follows from Y⊐Z's inner
    rcases hm₂_inner with h_cap | h_comp
    · -- Left: ∀ Y∩Z < m₂ → ∀ X∩Z < m₂
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_y, hc_z⟩)
      · exact hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)
    · -- Right: ∀ field\(Y∪Z) < m₂ → ∀ field\(X∪Z) < m₂
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact ord.lt_of_lt_of_le
          (hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)) hle
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_y hc_nz⟩)

/-- Fact 12c: trichotomy — `X ∼ Y`, `X ⊐ Y`, or `Y ⊐ X`. -/
theorem strictlyBetter_total (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    degreeEquiv ord i X Y ∨ strictlyBetter ord i X Y ∨
    strictlyBetter ord i Y X := by
  by_cases h_eq : X = Y
  · exact Or.inl (h_eq ▸ degreeEquiv_refl ord i X)
  · obtain ⟨m, hm, hm_max⟩ := ord.exists_le_max _ (symdiff_nonempty X Y h_eq)
    -- Helper: any element of the symdiff ≤ m
    have hm_max' : ∀ s ∈ (X \ Y) ∪ (Y \ X), ord.le s m := hm_max
    rcases Finset.mem_union.mp hm with hm_xy | hm_yx
    · -- m ∈ X\Y: either equivCond1, or strictlyBetter X Y
      have hm_field : m ∈ field ord i := hX (Finset.mem_sdiff.mp hm_xy).1
      by_cases h_all_yx : ∀ y ∈ Y \ X, ord.lt y m
      · -- All Y\X < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ X ∩ Y, ord.lt c m
        · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m
          · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (fun s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, hc₁_mem, ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, hc₂_mem, ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ y₀ ∈ Y\X with ¬(lt y₀ m): equivCond1
        push Not at h_all_yx
        obtain ⟨y₀, hy₀_mem, hy₀_nlt⟩ := h_all_yx
        have hy₀_ge := ord.le_of_not_lt hy₀_nlt
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨y₀, hy₀_mem,
              ord.le_trans x m y₀
                (hm_max' x (Finset.mem_union.mpr (Or.inl hx))) hy₀_ge⟩,
           fun y hy => ⟨m, hm_xy,
              hm_max' y (Finset.mem_union.mpr (Or.inr hy))⟩⟩)
    · -- m ∈ Y\X: symmetric case — either equivCond1, or strictlyBetter Y X
      have hm_field : m ∈ field ord i := hY (Finset.mem_sdiff.mp hm_yx).1
      by_cases h_all_xy : ∀ x ∈ X \ Y, ord.lt x m
      · -- All X\Y < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ Y ∩ X, ord.lt c m
        · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (Y ∪ X), ord.lt c m
          · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (fun s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, by rw [Finset.inter_comm]; exact hc₁_mem,
                      ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, by rw [Finset.union_comm]; exact hc₂_mem,
                      ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ x₀ ∈ X\Y with ¬(lt x₀ m): equivCond1
        push Not at h_all_xy
        obtain ⟨x₀, hx₀_mem, hx₀_nlt⟩ := h_all_xy
        have hx₀_ge := ord.le_of_not_lt hx₀_nlt
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨m, hm_yx,
              hm_max' x (Finset.mem_union.mpr (Or.inl hx))⟩,
           fun y hy => ⟨x₀, hx₀_mem,
              ord.le_trans y m x₀
                (hm_max' y (Finset.mem_union.mpr (Or.inr hy))) hx₀_ge⟩⟩)

/-! ### Fact 8c: ∼ Transitivity (via Totality + Respects) -/

/-- Fact 8c: ∼ is transitive on field-subsets, via trichotomy and Fact 11. -/
theorem degreeEquiv_trans (hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y Z →
    degreeEquiv ord i X Z := by
  intro hxy hyz
  by_contra h_neq
  rcases strictlyBetter_total ord i X Z hXf hZf with h | h | h
  · exact h_neq h
  · -- X ⊐ Z, Z ∼ Y → X ⊐ Y, contradicts X ∼ Y
    exact degreeEquiv_not_strictlyBetter ord i X Y hxy
      (strictlyBetter_respects_right ord i X Z Y hXf hZf hYf h
        (degreeEquiv_symm ord i Y Z hyz))
  · -- Z ⊐ X, X ∼ Y → Z ⊐ Y, contradicts Y ∼ Z
    exact degreeEquiv_not_strictlyBetter ord i Z Y
      (degreeEquiv_symm ord i Y Z hyz)
      (strictlyBetter_respects_right ord i Z X Y hZf hXf hYf h hxy)

/-- ∼ as a `Setoid` on field-subsets (transitivity needs the field bound). -/
def metalinguisticSetoid :
    Setoid {X : Finset I // X ⊆ field ord i} where
  r X Y := degreeEquiv ord i X.1 Y.1
  iseqv := {
    refl := fun X => degreeEquiv_refl ord i X.1
    symm := fun {X Y} h => degreeEquiv_symm ord i X.1 Y.1 h
    trans := fun {X Y Z} hxy hyz =>
      degreeEquiv_trans ord i X.1 Y.1 Z.1 X.2 Y.2 Z.2 hxy hyz
  }

end DegreeTheory

/-! ### Metalinguistic Degree Type -/

/-- Metalinguistic degrees: ∼-classes of interpretation sets. The degree of
a sentence is `deg` of its denotation (`formulaDeg`). -/
def MetaDegree (I : Type*) [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :=
  Quotient (metalinguisticSetoid ord i)

/-- The metalinguistic degree of an interpretation set. -/
def deg {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X : Finset I) (hX : X ⊆ field ord i) :
    MetaDegree I ord i :=
  Quotient.mk (metalinguisticSetoid ord i) ⟨X, hX⟩

/-! ### Facts 9–10: Correspondence with Revised Semantics -/

/-- Membership in `field`: j ∈ I_i iff j ≤ i. -/
private theorem mem_field_iff {I : Type*} [Fintype I] [DecidableEq I]
    {ord : SemanticOrdering I} {i j : I} :
    j ∈ field ord i ↔ ord.le j i := by
  simp [field]

/-- Membership in `denotation`: j ∈ ⟦φ⟧_i iff j ≤ i and ⟦φ⟧^j = 1. -/
private theorem mem_denotation_iff {L : Language} {I W E : Type*}
    [Fintype I] [DecidableEq I]
    {interp : I → W → L.Structure E}
    {φ : L.CompFormula E}
    {ord : SemanticOrdering I} {i j : I} {w : W} :
    j ∈ denotation interp ord i φ w ↔
    ord.le j i ∧ EvalRevised interp φ ord j w := by
  simp [denotation, field]

noncomputable section DegreeBridges

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

/-- The metalinguistic degree of a formula's denotation. -/
def formulaDeg (φ : L.CompFormula E) (w : W) : MetaDegree I ord i :=
  deg ord i (denotation interp ord i φ w) (denotation_subset_field interp ord i φ w)

variable (A B : L.CompFormula E) (w : W)

/-- Fact 10: revised MC holds iff denotation of A ⊐ denotation of B. -/
theorem mc_iff_degree_gt :
    EvalRevised interp (.comp A B) ord i w ↔
    strictlyBetter ord i (denotation interp ord i A w)
      (denotation interp ord i B w) := by
  rw [evalRevised_mc_iff]
  constructor
  · rintro ⟨i', h_le, h_A, h_B, h_dom⟩
    refine ⟨i', Finset.mem_sdiff.mpr
        ⟨mem_denotation_iff.mpr ⟨h_le, h_A⟩,
         fun h => h_B (mem_denotation_iff.mp h).2⟩,
      mem_field_iff.mpr h_le, ?_, ?_⟩
    · intro i'' h_mem
      obtain ⟨h_inY, h_ninX⟩ := Finset.mem_sdiff.mp h_mem
      obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp h_inY
      rcases h_dom with h1 | h2
      · exact h1 i'' h_le'' h_B''
      · exact h2 i'' h_le'' fun h_A'' => h_ninX (mem_denotation_iff.mpr ⟨h_le'', h_A''⟩)
    · rcases h_dom with h1 | h2
      · exact Or.inl fun i'' h_mem =>
          h1 i'' (mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2).1
            (mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2).2
      · refine Or.inr fun i'' h_mem => ?_
        have h_sd := Finset.mem_sdiff.mp h_mem
        exact h2 i'' (mem_field_iff.mp h_sd.1) fun h_A'' =>
          h_sd.2 (Finset.mem_union.mpr
            (Or.inl (mem_denotation_iff.mpr ⟨mem_field_iff.mp h_sd.1, h_A''⟩)))
  · rintro ⟨i', h_sdiff, h_field, h_ymx, h_inner⟩
    obtain ⟨h_inX, h_ninY⟩ := Finset.mem_sdiff.mp h_sdiff
    obtain ⟨h_le, h_A⟩ := mem_denotation_iff.mp h_inX
    have h_B : ¬ EvalRevised interp B ord i' w :=
      fun h => h_ninY (mem_denotation_iff.mpr ⟨h_le, h⟩)
    refine ⟨i', h_le, h_A, h_B, ?_⟩
    rcases h_inner with h1 | h2
    · left; intro i'' h_le'' h_B''
      by_cases h_A'' : EvalRevised interp A ord i'' w
      · exact h1 i'' (Finset.mem_inter.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_A''⟩,
           mem_denotation_iff.mpr ⟨h_le'', h_B''⟩⟩)
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => h_A'' (mem_denotation_iff.mp h).2⟩)
    · right; intro i'' h_le'' h_A''
      by_cases h_B'' : EvalRevised interp B ord i'' w
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => h_A'' (mem_denotation_iff.mp h).2⟩)
      · exact h2 i'' (Finset.mem_sdiff.mpr
          ⟨mem_field_iff.mpr h_le'',
           fun h => (Finset.mem_union.mp h).elim
             (fun h => h_A'' (mem_denotation_iff.mp h).2)
             (fun h => h_B'' (mem_denotation_iff.mp h).2)⟩)

/-- Fact 9: ME holds iff denotations have the same degree — the Boolean-free
bridge from `EvalRevised` to the algebraic degree structure. Forward direction
uses `strictlyBetter_total`. -/
theorem me_iff_same_degree :
    EvalRevised interp (A.equi B) ord i w ↔
    degreeEquiv ord i (denotation interp ord i A w)
      (denotation interp ord i B w) := by
  have hX := denotation_subset_field interp ord i A w
  have hY := denotation_subset_field interp ord i B w
  constructor
  · intro h
    obtain ⟨h1, h2⟩ : ¬ EvalRevised interp (.comp A B) ord i w ∧
        ¬ EvalRevised interp (.comp B A) ord i w := h
    rcases strictlyBetter_total ord i _ _ hX hY with h | h | h
    · exact h
    · exact absurd ((mc_iff_degree_gt interp ord i A B w).mpr h) h1
    · exact absurd ((mc_iff_degree_gt interp ord i B A w).mpr h) h2
  · intro h_eq
    exact show ¬ EvalRevised interp (.comp A B) ord i w ∧
        ¬ EvalRevised interp (.comp B A) ord i w from
      ⟨fun h => degreeEquiv_not_strictlyBetter ord i _ _ h_eq
          ((mc_iff_degree_gt interp ord i A B w).mp h),
       fun h => degreeEquiv_not_strictlyBetter ord i _ _
          (degreeEquiv_symm ord i _ _ h_eq)
          ((mc_iff_degree_gt interp ord i B A w).mp h)⟩

end DegreeBridges

/-! ### The metalinguistic degree scale

Facts 11–13 make `MetaDegree` a bounded linear order — i.e., a *scale* in the
degree substrate's sense. The instances below package that, and
`mc_iff_comparativeSem` cashes it out: the revised MC is the degree
substrate's binary comparative over the measure function `formulaDeg`. -/

noncomputable section Scale

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (equivCond1 ord X Y) := by
  unfold equivCond1; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (equivCond2 ord i X Y) := by
  unfold equivCond2; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (degreeEquiv ord i X Y) := by
  unfold degreeEquiv; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (strictlyBetter ord i X Y) := by
  unfold strictlyBetter; infer_instance

/-- Fact 13a: nothing is strictly better than the full field `I_i`
(packaged as `OrderTop` below). -/
theorem not_strictlyBetter_field (X : Finset I) (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i X (field ord i) := by
  rintro ⟨i', hi', -⟩
  exact (Finset.mem_sdiff.mp hi').2 (hX (Finset.mem_sdiff.mp hi').1)

/-- Fact 13b: the empty set is strictly better than nothing
(packaged as `OrderBot` below). -/
theorem not_strictlyBetter_empty (X : Finset I) :
    ¬ strictlyBetter ord i (∅ : Finset I) X := by
  rintro ⟨i', hi', -⟩
  simp at hi'

/-- Fact 11 packaged as a congruence: ⊐ is invariant under ∼ on both sides. -/
theorem strictlyBetter_congr {X X' Y Y' : Finset I}
    (hXf : X ⊆ field ord i) (hX'f : X' ⊆ field ord i)
    (hYf : Y ⊆ field ord i) (hY'f : Y' ⊆ field ord i)
    (hX : degreeEquiv ord i X X') (hY : degreeEquiv ord i Y Y') :
    strictlyBetter ord i X Y ↔ strictlyBetter ord i X' Y' :=
  ⟨fun h => strictlyBetter_respects_right ord i X' Y Y' hX'f hYf hY'f
      (strictlyBetter_respects_left ord i X Y X' hXf hYf hX'f h hX) hY,
   fun h => strictlyBetter_respects_right ord i X Y' Y hXf hY'f hYf
      (strictlyBetter_respects_left ord i X' Y' X hX'f hY'f hXf h
        (degreeEquiv_symm ord i X X' hX)) (degreeEquiv_symm ord i Y Y' hY)⟩

instance [DecidableRel ord.le] : DecidableEq (MetaDegree I ord i) := fun d₁ d₂ =>
  Quotient.recOnSubsingleton₂ d₁ d₂ fun X Y =>
    decidable_of_iff (degreeEquiv ord i X.1 Y.1)
      ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- The scale order: `deg X ≤ deg Y` iff X is not strictly better than Y
(well-defined on ∼-classes by `strictlyBetter_congr`). -/
protected def MetaDegree.le (d₁ d₂ : MetaDegree I ord i) : Prop :=
  Quotient.lift₂ (fun X Y => ¬ strictlyBetter ord i X.1 Y.1)
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => propext (not_congr
      (strictlyBetter_congr ord i a₁.2 a₂.2 b₁.2 b₂.2 h₁ h₂))) d₁ d₂

/-- `MetaDegree` is a linear order: Fact 12, packaged. Irreflexivity,
transitivity, and totality of ⊐ become the order axioms on the quotient. -/
instance : LinearOrder (MetaDegree I ord i) where
  le := MetaDegree.le ord i
  le_refl d := Quotient.inductionOn d fun X => strictlyBetter_irrefl ord i X.1
  le_trans d₁ d₂ d₃ := Quotient.inductionOn₃ d₁ d₂ d₃ fun X Y Z h₁ h₂ hXZ => by
    rcases strictlyBetter_total ord i X.1 Y.1 X.2 Y.2 with heq | hXY | hYX
    · exact h₂ (strictlyBetter_respects_left ord i X.1 Z.1 Y.1 X.2 Z.2 Y.2 hXZ heq)
    · exact h₁ hXY
    · exact h₂ (strictlyBetter_trans ord i Y.1 X.1 Z.1 hYX hXZ)
  le_antisymm d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ fun X Y h₁ h₂ => by
    rcases strictlyBetter_total ord i X.1 Y.1 X.2 Y.2 with heq | hXY | hYX
    · exact Quotient.sound heq
    · exact absurd hXY h₁
    · exact absurd hYX h₂
  le_total d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ fun X Y => by
    by_cases h : strictlyBetter ord i X.1 Y.1
    · exact Or.inr fun hYX => strictlyBetter_irrefl ord i X.1
        (strictlyBetter_trans ord i X.1 Y.1 X.1 h hYX)
    · exact Or.inl h
  toDecidableLE := Classical.decRel _

/-- Fact 13, packaged: the tautology's degree is ⊤, the contradiction's ⊥. -/
instance : BoundedOrder (MetaDegree I ord i) where
  top := deg ord i (field ord i) (Finset.Subset.refl _)
  le_top d := Quotient.inductionOn d fun X => not_strictlyBetter_field ord i X.1 X.2
  bot := deg ord i ∅ (Finset.empty_subset _)
  bot_le d := Quotient.inductionOn d fun X => not_strictlyBetter_empty ord i X.1

@[simp] theorem deg_le_deg_iff {X Y : Finset I}
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    deg ord i X hX ≤ deg ord i Y hY ↔ ¬ strictlyBetter ord i X Y := Iff.rfl

/-- The strict order on metalinguistic degrees is exactly ⊐ (arguments
flipped): Y's degree lies below X's iff X is strictly better. -/
theorem deg_lt_deg_iff {X Y : Finset I}
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    deg ord i Y hY < deg ord i X hX ↔ strictlyBetter ord i X Y := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨-, h⟩
    exact not_not.mp h
  · intro h
    exact ⟨fun hYX => strictlyBetter_irrefl ord i Y
        (strictlyBetter_trans ord i Y X Y hYX h), not_not.mpr h⟩

/-- **The paper's (59), in the substrate's vocabulary**: the revised
metalinguistic comparative IS the degree substrate's binary comparative
(`Degree.comparativeSem`, positive direction) over the metalinguistic measure
function `formulaDeg`. Metagradability thereby instantiates the degree
substrate's central object — a measure `μ : E → D` into a bounded linear
scale — with `E` the formulas and `D` the `MetaDegree` scale. -/
theorem mc_iff_comparativeSem (A B : L.CompFormula E) (w : W) :
    EvalRevised interp (.comp A B) ord i w ↔
    Degree.comparativeSem (fun φ => formulaDeg interp ord i φ w) A B .positive := by
  rw [mc_iff_degree_gt]
  simp only [Degree.comparativeSem, gt_iff_lt]
  exact (deg_lt_deg_iff ord i (denotation_subset_field interp ord i A w)
    (denotation_subset_field interp ord i B w)).symm

end Scale

/-! ### Types (shared across models) -/

/-- One world. -/
inductive W | w0
  deriving DecidableEq, Repr, Fintype

/-- Two predicates: linguist and philosopher. -/
inductive Pred | linguist | philosopher
  deriving DecidableEq, Repr, Fintype

/-- One entity: Ann. -/
inductive Entity | ann
  deriving DecidableEq, Repr, Fintype

/-- The monadic language over `Pred`. -/
abbrev PredLang := Language.monadic Pred

/-- "Ann is a linguist" -/
abbrev La : PredLang.CompFormula Entity := .matom Pred.linguist .ann

/-- "Ann is a philosopher" -/
abbrev Pa : PredLang.CompFormula Entity := .matom Pred.philosopher .ann

/-- "Ann is more a linguist than a philosopher" -/
abbrev La_mc_Pa : PredLang.CompFormula Entity := .comp La Pa

/-! ### Model 1: Three interpretations (linear order) -/

/-- Three interpretations: i₀ < i₁ < i₂. -/
inductive I3 | i0 | i1 | i2
  deriving DecidableEq, Repr, Fintype

/-- Linear ordering: i0 ≤ i1 ≤ i2. -/
def ord₃ : SemanticOrdering I3 :=
  .ofBool
    (λ i j => match i, j with
      | .i0, _ => true
      | .i1, .i0 => false
      | .i1, _ => true
      | .i2, .i2 => true
      | .i2, _ => false)
    (by intro i; cases i <;> rfl)
    (by intro i j k hij hjk; cases i <;> cases j <;> cases k <;> simp_all)
    (by intro i j; cases i <;> cases j <;> simp)

/-- Interpretation family (a `monadic`-structure per interpretation):
- i₀: Ann is a philosopher, not a linguist
- i₁: Ann is a linguist, not a philosopher
- i₂: Ann is both -/
@[implicit_reducible] def interp₃ : I3 → W → PredLang.Structure Entity :=
  fun i _ => monadicStructure fun P _ =>
    (match i, P with
      | .i0, .philosopher => true
      | .i0, .linguist => false
      | .i1, .linguist => true
      | .i1, .philosopher => false
      | .i2, _ => true) = true

instance : DecidableAtoms interp₃ := fun _ _ => monadicStructure.decRelMap _

instance : DecidableRel ord₃.le := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-! ### Observations on Model 1 -/

/-- Observation 1a: MCs are consistent with truth of both constituents.
At i₂, Ann is both a linguist and a philosopher, yet "Ann is more a
linguist than a philosopher" is true — the (La∧¬Pa)-interpretation i₁
outranks the (Pa∧¬La)-interpretation i₀. -/
theorem obs1a_mc_consistent_with_both :
    Eval interp₃ La_mc_Pa ord₃ .i2 .w0 ∧
    Eval interp₃ La ord₃ .i2 .w0 ∧
    Eval interp₃ Pa ord₃ .i2 .w0 := by decide

/-- Observation 2: A ≻ B, B ⊨ A.
If the MC holds and Ann is a philosopher, she is a linguist. -/
theorem obs2_mc_B_entails_A :
    ∀ (i : I3),
      Eval interp₃ La_mc_Pa ord₃ i .w0 →
      Eval interp₃ Pa ord₃ i .w0 →
      Eval interp₃ La ord₃ i .w0 := by decide

/-! ### Model 2: Two interpretations (tied) for borderline cases -/

/-- Two interpretations for borderline / nonclassicality witnesses. -/
inductive I2 | j0 | j1
  deriving DecidableEq, Repr, Fintype

/-- Tied ordering: j0 ≡ j1 (both maximal). -/
def tiedOrd : SemanticOrdering I2 :=
  .ofBool
    (λ _ _ => true)
    (by intro i; cases i <;> rfl)
    (by intro i j k _ _; cases i <;> cases j <;> cases k <;> rfl)
    (by intro i j; left; cases i <;> cases j <;> rfl)

/-- j₀: La true, Pa false; j₁: La false, Pa true. -/
@[implicit_reducible] def interp₂ : I2 → W → PredLang.Structure Entity :=
  fun i _ => monadicStructure fun P _ =>
    (match i, P with
      | .j0, .linguist => true
      | .j0, .philosopher => false
      | .j1, .linguist => false
      | .j1, .philosopher => true) = true

instance : DecidableAtoms interp₂ := fun _ _ => monadicStructure.decRelMap _

instance : DecidableRel tiedOrd.le := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- Observation 5: A ≈ ¬A is satisfiable (not contradictory).
With tied interpretations where one makes La true and the other
makes La false, "Ann is (exactly) as much a linguist as not"
is coherent — it expresses a borderline case. -/
theorem obs5_me_neg_consistent :
    Eval interp₂ (La.equi (.not La)) tiedOrd .j0 .w0 := by decide

/-- ¬La -/
abbrev NLa : PredLang.CompFormula Entity := .not La

/-! ### Assertoric Content and Acceptance-Preservation -/

/- Observation 3 (acceptance-preservation): A ∧ ¬B ⊩ A ≻ B.
If assertoric content of (La ∧ ¬Pa) holds, then assertoric content of
La ≻ Pa holds. On ord₃, the premise fails (Pa is true at i₂), so
the implication holds vacuously. We verify the substantive case on a
model where the premise holds. -/

/-- For substantive Obs 3: i₂ is linguist only. -/
@[implicit_reducible] def interp₃' : I3 → W → PredLang.Structure Entity :=
  fun i _ => monadicStructure fun P _ =>
    (match i, P with
      | .i0, .philosopher => true
      | .i0, .linguist => false
      | .i1, _ => true
      | .i2, .linguist => true
      | .i2, .philosopher => false) = true

instance : DecidableAtoms interp₃' := fun _ _ => monadicStructure.decRelMap _

theorem obs3_acceptance :
    AssertoricContent interp₃' (.inf La (.not Pa)) ord₃ .w0 →
    AssertoricContent interp₃' La_mc_Pa ord₃ .w0 := by decide

/-- The tautology La ∨ ¬La has assertoric content 1 on the tied model. -/
theorem tautology_accepted :
    AssertoricContent interp₂ (.sup La (.not La)) tiedOrd .w0 := by
  decide

/-- Nonclassical acceptance-preservation: `(La ≻ ¬La) ∨ (¬La ≻ La)` is not
accepted on the tied model — the analogue of informational entailment for
epistemic modals ([yalcin-2007]). -/
theorem mc_disj_not_accepted :
    AssertoricContent interp₂ (.sup (.comp La (.not La)) (.comp (.not La) La))
      tiedOrd .w0 = false := by decide

/-! ### Degree Modifiers (§6.1) -/

/-- Distance function for ord₃: close(i) includes interpretations at the
same level or one level below.
- d(i₀) = {i₀}
- d(i₁) = {i₀, i₁}
- d(i₂) = {i₁, i₂} -/
def dist₃ : DistanceFunction I3 ord₃ where
  close i i' := (match i, i' with
    | .i0, .i0 => true
    | .i1, .i0 => true
    | .i1, .i1 => true
    | .i2, .i1 => true
    | .i2, .i2 => true
    | _, _ => false : Bool) = true
  centered := by decide
  topBounded := by decide
  convex := by decide
  noncontractive := by decide

instance : DecidableRel dist₃.close := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- very La is true at i₂: all interpretations reasonably close to i₂
(namely i₁ and i₂) make La true. -/
theorem very_la_at_top :
    EvalVery interp₃ La ord₃ dist₃ .i2 .w0 := by decide

/-- very La is false at i₁: i₀ is reasonably close to i₁ but
makes La false. -/
theorem very_la_false_at_mid :
    ¬ EvalVery interp₃ La ord₃ dist₃ .i1 .w0 := by decide

/-- sorta La holds at i₁: some close interpretation (i₁ itself) makes
La true, even though another close interpretation (i₀) does not. -/
theorem sorta_la_at_mid :
    EvalSorta interp₃ La ord₃ dist₃ .i1 .w0 := by decide

/-- sorta La is false at i₀: d(i₀) = {i₀}, and La is false at i₀. -/
theorem sorta_la_false_at_bot :
    ¬ EvalSorta interp₃ La ord₃ dist₃ .i0 .w0 := by decide

/-! ### Degree Modifier: mostly (§6.1) -/

/-- mostly La is true at i₂: there is a reasonably high level (i₁) where
La is uniformly true, and the only A-false level (i₀) is below it. -/
theorem mostly_la_at_top :
    EvalMostly interp₃ La ord₃ dist₃ .i2 .w0 := by decide

/-- mostly La is false at i₁: i₀ is the only candidate level below i₁ in
d(i₁), but La is false at i₀. -/
theorem mostly_la_false_at_mid :
    ¬ EvalMostly interp₃ La ord₃ dist₃ .i1 .w0 := by decide

/-! ### Bridge: No Reversal and Ordinary Comparison (§7) -/

/-! ### Two-Entity Model: No Reversal (§7) -/

/-- Two entities for gradable adjective models. -/
inductive Entity2 | ann | ben
  deriving DecidableEq, Repr, Fintype

/-- Single predicate: tall. -/
inductive Pred1 | tall
  deriving DecidableEq, Repr, Fintype

/-- NR model for "Ann is taller than Ben":
- i₀: neither Ann nor Ben is tall (empty extension)
- i₁: Ann is tall, Ben is not (Ann enters the extension first)
- i₂: both are tall

Satisfies No Reversal: extensions are monotonically nested
({} ⊆ {ann} ⊆ {ann, ben}). Uses the same 3-interpretation
linear order `ord₃` from Model 1. -/
@[implicit_reducible] def interpNR : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  fun i _ => monadicStructure fun _ e =>
    (match i, e with
      | .i0, _ => false
      | .i1, .ann => true
      | .i1, .ben => false
      | .i2, _ => true) = true

instance : DecidableAtoms interpNR := fun _ _ => monadicStructure.decRelMap _

/-- "Ann is tall" -/
abbrev Ta : (Language.monadic Pred1).CompFormula Entity2 := .matom Pred1.tall .ann

/-- "Ben is tall" -/
abbrev Tb : (Language.monadic Pred1).CompFormula Entity2 := .matom Pred1.tall .ben

/-- No Reversal holds for `tall`: the extensions are monotonically nested,
so Ben never outruns Ann. -/
theorem nr_tall_ann_ben :
    NoReversal interpNR ord₃ Pred1.tall .w0 .ann .ben := by decide

/-- Ann is taller than Ben: the MC `tall(ann) ≻ tall(ben)` is true
at i₁ and i₂. Witness: i₁ (Ann is tall, Ben is not). -/
theorem ann_taller_i1 :
    Eval interpNR (.comp Ta Tb) ord₃ .i1 .w0 := by decide

/-- The reverse MC — Ben taller than Ann — is false everywhere.
There is no interpretation where Ben is tall but Ann is not. -/
theorem ben_not_taller :
    ∀ (i : I3), ¬ Eval interpNR (.comp Tb Ta) ord₃ i .w0 := by decide

/-- NR also holds with the roles swapped (vacuously: Ben's extension never
outruns Ann's), which is the direction `eval_mc_iff_delineation_of_noReversal`
consumes. -/
theorem nr_tall_ben_ann :
    NoReversal interpNR ord₃ Pred1.tall .w0 .ben .ann := by decide

/-- The general §7 bridge, instantiated on the NR model: the MC *is* the
substrate's delineation comparative. -/
example (i : I3) :
    Eval interpNR (.comp Ta Tb) ord₃ i .w0 ↔
    Semantics.Gradability.Delineation.comparativeSem
      (interpretationDelineation interpNR ord₃ Pred1.tall .w0 i) .ann .ben :=
  eval_mc_iff_delineation_of_noReversal interpNR ord₃ .tall .w0 i .ann .ben
    nr_tall_ben_ann

/-- NR-violating model: Ann and Ben "swap" across interpretations.
- i₀: Ann tall, Ben not
- i₁: Ben tall, Ann not (reversal!)
- i₂: both tall -/
@[implicit_reducible] def interpNR_bad : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  fun i _ => monadicStructure fun _ e =>
    (match i, e with
      | .i0, .ann => true
      | .i0, .ben => false
      | .i1, .ann => false
      | .i1, .ben => true
      | .i2, _ => true) = true

instance : DecidableAtoms interpNR_bad := fun _ _ => monadicStructure.decRelMap _

/-- No Reversal fails on the violating model (for e₁=ben, e₂=ann):
Ben is tall at i₁ and Ann is not, but at i₀ ≤ i₁ where Ann is tall,
Ben is not — a reversal. -/
theorem nr_fails_bad :
    ¬ NoReversal interpNR_bad ord₃ Pred1.tall .w0 .ben .ann := by decide

/-- Without NR, MC and delineation diverge: the MC `Ta ≻ Tb` is
FALSE at i₂ (the (Tb∧¬Ta)-witness i₁ outranks the (Ta∧¬Tb)-witness
i₀, violating the domination clause), but the simple delineation
condition (∃ Fa∧¬Fb) is TRUE (i₀ is a witness). -/
theorem mc_delineation_diverge_without_nr :
    ¬ Eval interpNR_bad (.comp Ta Tb) ord₃ .i2 .w0 ∧
    Semantics.Gradability.Delineation.comparativeSem
      (interpretationDelineation interpNR_bad ord₃ Pred1.tall .w0 .i2) .ann .ben :=
  ⟨by decide,
   (delineation_comparativeSem_iff interpNR_bad ord₃ Pred1.tall .w0 .i2 .ann .ben).mpr
     ⟨.i0, by decide, by decide, by decide⟩⟩

/-! ### Metalinguistic Conditional (§6.3) -/

/-- `La → Pa` fails at i₂ even though both conjuncts are true there: the
conditional quantifies over all ranked La-interpretations, so it is not the
material conditional. -/
theorem mcond_la_pa_false :
    ¬ EvalMCond interp₃ La Pa ord₃ .i2 .w0 := by decide

/-- M1 (§6.3): ⊨ A → (A ≻ ¬A) — "if Pluto is a planet, it's more a planet
than not", the analogue of epistemic "if p then probably p"
([yalcin-2007]). -/
theorem mcond_m1 :
    ∀ (i : I3),
      EvalMCond interp₃ La (.comp La NLa) ord₃ i .w0 := by decide

/-! ### ME transitivity: basic vs revised semantics ([kocurek-2024-supplement] §B)

Model 4 is the minimal counterexample: `La ≻ Ca` holds vacuously in the basic
semantics (the (La∧¬Ca)-witness l faces no (Ca∧¬La)-witness), breaking
`A ≈ B, B ≈ C ⊨ A ≈ C`; the revised domination clause blocks the vacuous
witness and restores transitivity. -/

/-- Three predicates for the transitivity counterexample. -/
inductive Pred3 | linguist | philosopher | psychologist
  deriving DecidableEq, Repr, Fintype

/-- Four interpretations for the transitivity counterexample. -/
inductive I4 | i | j | k | l
  deriving DecidableEq, Repr, Fintype

/-- Ordering: l < j ≡ k < i (three levels).
j and k are tied at the middle level — this is essential for the
equatives La ≈ Pa and Pa ≈ Ca to hold (witnesses block each other). -/
def ord₄ : SemanticOrdering I4 :=
  .ofBool
    (λ x y => match x, y with
      | .l, _ => true
      | .j, .l => false
      | .j, _ => true
      | .k, .l => false
      | .k, _ => true
      | .i, .i => true
      | .i, _ => false)
    (by intro x; cases x <;> rfl)
    (by intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all)
    (by intro x y; cases x <;> cases y <;> simp)

/-- Counterexample interpretations: i all three; j linguist+psychologist;
k philosopher only; l linguist+philosopher. -/
@[implicit_reducible] def interp₄ : I4 → W → (Language.monadic Pred3).Structure Entity :=
  fun idx _ => monadicStructure fun P _ =>
    (match idx, P with
      | .i, _ => true
      | .j, .philosopher => false
      | .j, _ => true
      | .k, .philosopher => true
      | .k, _ => false
      | .l, .psychologist => false
      | .l, _ => true) = true

instance : DecidableAtoms interp₄ := fun _ _ => monadicStructure.decRelMap _

instance : DecidableRel ord₄.le := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- "Ann is a linguist" (3-predicate model) -/
abbrev La₄ : (Language.monadic Pred3).CompFormula Entity := .matom Pred3.linguist .ann

/-- "Ann is a philosopher" (3-predicate model) -/
abbrev Pa₄ : (Language.monadic Pred3).CompFormula Entity := .matom Pred3.philosopher .ann

/-- "Ann is a psychologist" -/
abbrev Ca₄ : (Language.monadic Pred3).CompFormula Entity := .matom Pred3.psychologist .ann

/-! #### Basic semantics: transitivity fails -/

/-- A ≈ B holds: Ann is as much a linguist as a philosopher.
The (La∧¬Pa)-witness j and (Pa∧¬La)-witness k are tied at the middle
level, blocking both MC directions. -/
theorem me_basic_la_pa :
    Eval interp₄ (La₄.equi Pa₄) ord₄ .i .w0 := by decide

/-- B ≈ C holds: Ann is as much a philosopher as a psychologist.
The (Pa∧¬Ca)-witnesses k, l and (Ca∧¬Pa)-witness j are balanced:
k is tied with j, blocking both MC directions. -/
theorem me_basic_pa_ca :
    Eval interp₄ (Pa₄.equi Ca₄) ord₄ .i .w0 := by decide

/-- A ≈ C FAILS: basic semantics predicts Ann is MORE a linguist
than a psychologist. ME transitivity is violated. -/
theorem me_basic_la_ca_fails :
    ¬ Eval interp₄ (La₄.equi Ca₄) ord₄ .i .w0 := by decide

/-- The failure mechanism: La ≻ Ca holds in the basic semantics.
The (La∧¬Ca)-witness l dominates all (Ca∧¬La)-interpretations
vacuously — there are none (Ca is true only at i and j, where La
is also true). -/
theorem mc_basic_la_gt_ca :
    Eval interp₄ (.comp La₄ Ca₄) ord₄ .i .w0 := by decide

/-! #### Revised semantics: transitivity restored -/

/-- Under the revised semantics, La ≻ Ca is blocked: the (La∧¬Ca)-
witness l cannot dominate all Ca-interpretations (i and j are above
it) or all ¬La-interpretations (k is above it). -/
theorem mc_revised_la_ca_blocked :
    ¬ EvalRevised interp₄ (.comp La₄ Ca₄) ord₄ .i .w0 := by decide

/-- ME transitivity is restored: A ≈ C holds under the revised
semantics, as required by transitivity from A ≈ B and B ≈ C. -/
theorem me_revised_la_ca :
    EvalRevised interp₄ (La₄.equi Ca₄) ord₄ .i .w0 := by decide

/-- The revised semantics preserves A ≈ B (no regression). -/
theorem me_revised_la_pa :
    EvalRevised interp₄ (La₄.equi Pa₄) ord₄ .i .w0 := by decide

/-- The revised semantics preserves B ≈ C (no regression). -/
theorem me_revised_pa_ca :
    EvalRevised interp₄ (Pa₄.equi Ca₄) ord₄ .i .w0 := by decide

/-! #### Agreement on Model 1 -/

/-- On Model 1 (linear ordering), the revised MC agrees with the basic
MC. The two diverge only when the revised semantics' stronger domination
clause matters — on a linear ordering with no ties at critical levels,
the basic witnesses satisfy the revised conditions too. -/
theorem revised_agrees_model1 :
    ∀ (x : I3),
      (Eval interp₃ La_mc_Pa ord₃ x .w0 ↔
       EvalRevised interp₃ La_mc_Pa ord₃ x .w0) := by decide

end RudolphKocurek2024
