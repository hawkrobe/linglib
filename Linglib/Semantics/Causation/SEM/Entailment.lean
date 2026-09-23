module

public import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Causal entailment and causal necessity

The strict development of [schulz-2011] and [nadathur-2023-implicatives] (`developDetVtx?`)
settles an inner vertex only once all its parents are settled and never settles an undetermined
exogenous vertex. The predicates of [nadathur-2023-implicatives] are stated over it.

- **`causallyEntails M s v x`**: Definition 5, the strict development of `s` assigns `x` to `v`.
- **`isConsistentSuper M base s'`**: Definition 9b, in its "not the opposite" form.
- **`causallyNecessary M s cause xC effect xE`**: Definition 10b, a preamble, achievability, and
  no-alternative, with supersituations quantified over exogenous settlements (see
  `IsExogenousSettlement` for why the literal quantification is unfaithful to the paper's own
  verdicts).

In a finite model each is decided through fuel `Fintype.card V` (`causallyEntails_iff_fuel`),
the supersituation quantifiers ranging over the finite valuation space.

## References

* [schulz-2011]
* [nadathur-2023-implicatives]
* [nadathur-lauer-2020]
-/

@[expose] public section

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}

/-- **Causal entailment** ([nadathur-2023-implicatives] Def 5): the strict
    T_D fixed point relative to `s` assigns `x` to `v` ("s ⊨_D ⟨v, x⟩").
    Stated over the partial `developDetVtx?` — an undetermined exogenous
    vertex entails nothing, and an inner vertex entails nothing while any
    parent is u-valued. Contrast the eager `causallySufficient`. -/
def causallyEntails [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) (x : α v) : Prop :=
  developDetVtx? M s v = some x

/-- In a finite model causal entailment is computed by fuel `Fintype.card V`. -/
theorem causallyEntails_iff_fuel [Fintype V] [DecidableEq V] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] (s : Valuation α) (v : V) (x : α v) :
    causallyEntails M s v x ↔ developDetVtxFuel M s (Fintype.card V) v = some x := by
  rw [causallyEntails, developDetVtxFuel_card]

instance [Fintype V] [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] (s : Valuation α) (v : V) (x : α v) :
    Decidable (causallyEntails M s v x) :=
  decidable_of_iff _ (causallyEntails_iff_fuel M s v x).symm

/-- Strict causal entailment of the extended background implies the bare
    eager-total sufficiency predicate (`causallySufficient`): the partial
    development refines the total one wherever it resolves. -/
theorem causallySufficient_of_causallyEntails [Fintype V] [DecidableEq V]
    [DecidableValuation α] {M : SEM V α} [CausalGraph.IsDAG M.graph]
    {s : Valuation α} {cause : V} {xC : α cause}
    {effect : V} {xE : α effect}
    (h : causallyEntails M (s.extend cause xC) effect xE) :
    causallySufficient M s cause xC effect xE :=
  (developDet_hasValue_iff M (s.extend cause xC) effect xE).mpr
    (developDetVtx_eq_of_developDetVtx?_eq_some M h)

/-- Causal entailment is functional: a vertex entails at most one value. -/
theorem causallyEntails_unique [DecidableEq V] {M : SEM V α}
    [CausalGraph.IsDAG M.graph] {s : Valuation α}
    {v : V} {x y : α v}
    (hx : causallyEntails M s v x) (hy : causallyEntails M s v y) : x = y :=
  Option.some.inj ((hx.symm.trans hy))

/-- **Consistent supersituation** ([nadathur-2023-implicatives] Def 9b),
    faithful "not the opposite" form: `s'` extends `base`, and for every
    vertex `s'` newly fixes, `base` does not causally entail a *different*
    value there. Def 9b restricts the condition to inner variables; that
    restriction is automatic here, since `developDetVtx?` is `none` at
    undetermined exogenous vertices. -/
def isConsistentSuper [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph]
    (base s' : Valuation α) : Prop :=
  base ≤ s' ∧
  ∀ (x : V) (xv : α x), base.get x = none → s'.get x = some xv →
    ∀ yv : α x, yv ≠ xv → ¬ causallyEntails M base x yv

instance [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] (base s' : Valuation α) :
    Decidable (isConsistentSuper M base s') := by
  unfold isConsistentSuper; infer_instance

/-- Every valuation is a consistent supersituation of itself. -/
theorem isConsistentSuper_self [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) : isConsistentSuper M s s :=
  ⟨le_rfl, fun _ _ hn hs => by simp [hn] at hs⟩

/-- **Determinations cannot be undone** ([nadathur-2023-implicatives]
    Def 2 prose): causal entailment is monotone under consistent
    supersituations — whatever `s` causally entails, any Def-9b-consistent
    extension of `s` still causally entails. -/
theorem causallyEntails_mono [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph]
    {s s' : Valuation α} (hcons : isConsistentSuper M s s')
    {v : V} {x : α v} (h : causallyEntails M s v x) :
    causallyEntails M s' v x := by
  induction v using (inferInstance : M.graph.IsDAG).induction with
  | _ v ih =>
    cases hs'v : s'.get v with
    | some z =>
        -- s' fixes v at z; show z = x, then v is determined.
        have hzx : z = x := by
          cases hsv : s.get v with
          | some w =>
              -- determined in s: w = x (from h) and s'.get v = some w (le).
              have hw : developDetVtx? M s v = some w :=
                developDetVtx?_determined M hsv
              have hxw : w = x := Option.some.inj (hw.symm.trans h)
              have := Valuation.le_def.1 hcons.1 v w hsv
              rw [Valuation.hasValue, hs'v] at this
              exact (Option.some.inj this).trans hxw
          | none =>
              -- newly fixed: consistency forbids s entailing any value ≠ z.
              by_contra hne
              exact hcons.2 v z hsv hs'v x (fun hxz => hne hxz.symm) h
        rw [causallyEntails, developDetVtx?_determined M hs'v, hzx]
    | none =>
        -- v undetermined in s' hence in s; h forces the inner case.
        have hsv : s.get v = none := by
          cases hsv : s.get v with
          | none => rfl
          | some w =>
              have := Valuation.le_def.1 hcons.1 v w hsv
              rw [Valuation.hasValue, hs'v] at this
              exact absurd this (by simp)
        rw [causallyEntails, developDetVtx?_unfold] at h
        simp only [hsv] at h
        by_cases hPar : M.graph.parents v = ∅
        · simp [hPar] at h
        · simp only [hPar, ite_false] at h
          by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
          · rw [dite_eq_left hAll] at h
            refine developDetVtx?_inner M hs'v hPar
              (fun u => (developDetVtx? M s u.val).get (hAll u)) (fun u => ?_) |>.trans ?_
            · exact ih u.val (Relation.TransGen.single u.property)
                (Option.some_get (hAll u)).symm
            · exact h
          · rw [dite_eq_right hAll] at h
            exact absurd h (by simp)

/-- **Exogenous settlement**: `s'` extends `base` by fixing only
    exogenous (parentless) vertices.

    Project-canonical restriction on Def 10b's supersituation
    quantifiers. Quantifying over *all* consistent supersituations (the
    literal Def 9b/10b reading) falsifies the paper's own §6.1.1
    verdicts: relative to the Dreyfus background, fixing the undetermined
    inner vertex MSG (plus LST, ¬BRK) is Def-9b-consistent and reaches
    COM without entailing NRV, contradicting the claim that ⟨NRV,1⟩ is
    causally necessary for ⟨COM,1⟩. The paper's worked example (21b)
    considers only background settlements ("the only such available");
    this definition makes that reading explicit. -/
def IsExogenousSettlement [DecidableValuation α] (M : SEM V α)
    (base s' : Valuation α) : Prop :=
  base ≤ s' ∧
  ∀ v : V, base.get v = none → (s'.get v).isSome → M.graph.parents v = ∅

instance [DecidableEq V] [Fintype V] [DecidableValuation α] (M : SEM V α)
    (base s' : Valuation α) : Decidable (IsExogenousSettlement M base s') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An exogenous settlement of an extension at a fresh exogenous vertex
    is an exogenous settlement of the base. -/
theorem IsExogenousSettlement.of_extend [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} {s s' : Valuation α} {p : V} {xP : α p}
    (hexo : M.graph.parents p = ∅) (hp : s.get p = none)
    (h : IsExogenousSettlement M (s.extend p xP) s') :
    IsExogenousSettlement M s s' := by
  refine ⟨(Valuation.le_extend xP hp).trans h.1, fun v hv hsv => ?_⟩
  by_cases hvp : v = p
  · subst hvp; exact hexo
  · exact h.2 v (by rw [Valuation.extend_get_ne hvp]; exact hv) hsv

/-- Exogenous settlements are automatically Def-9b-consistent: a newly
    fixed vertex is parentless and undetermined in `base`, so `base`
    causally entails nothing about it. -/
theorem IsExogenousSettlement.isConsistentSuper [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph]
    {base s' : Valuation α} (h : IsExogenousSettlement M base s') :
    isConsistentSuper M base s' := by
  refine ⟨h.1, fun x xv hn hs yv _ hent => ?_⟩
  have hExo : M.graph.parents x = ∅ := h.2 x hn (by rw [hs]; rfl)
  rw [causallyEntails, developDetVtx?_exogenous M hn hExo] at hent
  simp at hent

namespace causallyNecessary

/-- **Preamble of Definition 10** ([nadathur-2023-implicatives], with
    footnote 8's rationale): the background entails neither the cause
    fact nor the effect fact. Shared by Def 10a (sufficiency, see
    `Implicative.manageSem`) and Def 10b (necessity, below). -/
def precondition [DecidableEq V] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ¬ causallyEntails M s cause xC ∧ ¬ causallyEntails M s effect xE

instance [Fintype V] [DecidableEq V] [DecidableValuation α] (M : SEM V α)
    [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (precondition M s cause xC effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Achievability**, clause (i) of Def 10b: some consistent
    supersituation `s'` of `s + (cause = xC)` with `effect ∉ dom(s')`
    causally entails `effect = xE`. Quantified over exogenous settlements
    (see `IsExogenousSettlement`); Def 9b consistency is then automatic
    (`IsExogenousSettlement.isConsistentSuper`). -/
def achievable [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∃ s' : Valuation α, IsExogenousSettlement M (s.extend cause xC) s' ∧
    s'.get effect = none ∧ causallyEntails M s' effect xE

instance [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (achievable M s cause xC effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold achievable; infer_instance

/-- **No-alternative**, clause (ii) of Def 10b in positive-implication
    form: every consistent supersituation of `s` (exogenous settlement,
    `effect ∉ dom(s')`) that causally entails `effect = xE` also causally
    entails `cause = xC` — every consistent path to the effect goes
    through the cause. The paper's exclusion `s' ⊭ ⟨X,x⟩` is the
    *developed* entailment, not the syntactic `s'.get cause ≠ some xC`. -/
def noAlternative [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  ∀ s' : Valuation α, IsExogenousSettlement M s s' → s'.get effect = none →
    causallyEntails M s' effect xE → causallyEntails M s' cause xC

instance [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (noAlternative M s cause xC effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold noAlternative; infer_instance

end causallyNecessary

/-- **Causal Necessity** ([nadathur-2023-implicatives] Definition 10b)
    over the strict T_D development, polymorphic over value types:

    - **Preamble**: `s` entails neither `cause = xC` nor `effect = xE`.
    - **(i) Achievability**: some consistent supersituation of
      `s + (cause = xC)` not fixing the effect entails `effect = xE`.
    - **(ii) No-alternative**: every consistent supersituation of `s` not
      fixing the effect that entails `effect = xE` entails `cause = xC`.

    Supersituations are quantified over exogenous settlements — see
    `IsExogenousSettlement` for why the literal Def 9b/10b quantification
    is unfaithful to the paper's own verdicts. -/
def causallyNecessary [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  causallyNecessary.precondition M s cause xC effect xE ∧
  causallyNecessary.achievable M s cause xC effect xE ∧
  causallyNecessary.noAlternative M s cause xC effect xE

instance [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallyNecessary M s cause xC effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Causation.SEM

namespace Causation.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Causation (SEM Valuation BoolSEM)

/-- `BoolSEM`-flavored `causallyNecessary`: setting `cause = true` is
    necessary (Def 10b) for `effect = true`. -/
abbrev causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  SEM.causallyNecessary M s cause true effect true

instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) :=
  inferInstanceAs (Decidable (SEM.causallyNecessary M s cause true effect true))

end Causation.BoolSEM
