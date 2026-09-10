import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Studies.NadathurLauer2020

/-!
# Glass (2023): Using the Anna Karenina Principle to explain why *cause* favors negative-sentiment complements

This file formalizes [glass-2023b]'s account of why *cause* collocates with undesirable outcomes.
Over a deterministic causal model ([halpern-pearl-2005]), a value of a variable is locally
sufficient for a value of a downstream variable when some setting of the other variables
guarantees it, the sufficient sets of [mackie-1965], and globally sufficient when every setting
does; necessity is the mirror image, the absence of the cause being sufficient for the absence of
the effect (`GloballySufficient`, `LocallySufficient`, `GloballyNecessary`, `LocallyNecessary`,
`globallyNecessary_iff`). The global notions entail the local ones
(`LocallySufficient.of_globally`, `LocallyNecessary.of_globally`). *C causes E* asserted on a
state of knowledge requires that the effect develop in every settlement of what is unknown
(`Cause`), so knowing the cause alone it is assertable exactly when the cause is globally
sufficient (`cause_extend_empty_iff`): a globally sufficient cause licenses *cause* under
uncertainty, a merely necessary one only under full information, which is the asymmetry of the
paper's Table 2, worked out on its lightbulb (`Light`). Since the Anna Karenina Principle assigns
desired outcomes conjunctive models, in which each factor is necessary but insufficient, and
undesired ones disjunctive models, in which each factor suffices, *C causes E* is true in more
states of knowledge when E is bad. Glass's *cause* asserts only local sufficiency where
[nadathur-lauer-2020] make it assert necessity, so the two diverge on the latter's bus scenario
(`glass_nl_diverge_on_bus`).

## Implementation notes

* Backgrounds are the substrate's partial valuations developed by the eager deterministic
  dynamics, which settles an unspecified exogenous variable by its mechanism's default; "no matter
  what happens to any other variable" quantifies over all backgrounds leaving the effect open.
* The lightbulb of the paper's figures, on exactly when both switches are, is the conjunctive
  model for the light being on and the disjunctive model for its being off.
* The derivation of the Anna Karenina Principle from strategic model construction, the experiment
  supporting it (wanted outcomes drew "you had to do everything right" far more often than
  unwanted ones) and the corpus skew that motivates the paper stay in prose.

## References

* [glass-2023b]
* [nadathur-lauer-2020]
* [halpern-pearl-2005]
* [mackie-1965]
-/

namespace Glass2023

open Causation Causation.SEM Causation.Mechanism

section General

variable {V : Type*} (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]

/-! ### Local and global necessity and sufficiency -/

/-- `C = c` is globally sufficient for `E = e`: in every background leaving `E` open in which
`C = c`, the model develops `E = e`. -/
def GloballySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ bg : Valuation (λ _ : V => Bool),
    bg.get E = none → bg.hasValue C c → (M.developDet bg).hasValue E e

/-- `C = c` is locally sufficient for `E = e`: in some background leaving `E` open in which
`C = c`, the model develops `E = e`. -/
def LocallySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ bg : Valuation (λ _ : V => Bool),
    bg.get E = none ∧ bg.hasValue C c ∧ (M.developDet bg).hasValue E e

/-- `C = c` is globally necessary for `E = e`: without it, in every background leaving `E` open,
`E = e` fails. -/
def GloballyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ bg : Valuation (λ _ : V => Bool),
    bg.get E = none → bg.hasValue C (!c) → (M.developDet bg).hasValue E (!e)

/-- `C = c` is locally necessary for `E = e`: without it, in some background leaving `E` open,
`E = e` fails. -/
def LocallyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ bg : Valuation (λ _ : V => Bool),
    bg.get E = none ∧ bg.hasValue C (!c) ∧ (M.developDet bg).hasValue E (!e)

/-- *C causes E* asserted on the state of knowledge `k`: the cause is known, and the effect
develops in every background that settles the unknown variables, keeping what is known. -/
def Cause (k : Valuation (λ _ : V => Bool)) (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  k.hasValue C c ∧
    ∀ bg : Valuation (λ _ : V => Bool), (∀ v x, k.hasValue v x → bg.hasValue v x) →
      bg.get E = none → (M.developDet bg).hasValue E e

variable {M} {C E : V} {c e : Bool} {k : Valuation (λ _ : V => Bool)}

/-- Necessity is the mirror image of sufficiency: the absence of a necessary cause suffices for
the absence of the effect. -/
theorem globallyNecessary_iff :
    GloballyNecessary M C c E e ↔ GloballySufficient M C (!c) E (!e) := Iff.rfl

theorem locallyNecessary_iff :
    LocallyNecessary M C c E e ↔ LocallySufficient M C (!c) E (!e) := Iff.rfl

/-- A globally sufficient cause licenses *cause* whatever else is known or unknown. -/
theorem Cause.of_globallySufficient (h : GloballySufficient M C c E e) (hk : k.hasValue C c) :
    Cause M k C c E e :=
  ⟨hk, λ bg hkb hE => h bg hE (hkb C c hk)⟩

variable [DecidableEq V]

/-- Global sufficiency entails local sufficiency (22a). -/
theorem LocallySufficient.of_globally (hCE : C ≠ E) (h : GloballySufficient M C c E e) :
    LocallySufficient M C c E e :=
  ⟨Valuation.empty.extend C c, by rw [Valuation.extend_get_ne hCE.symm]; rfl,
    Valuation.extend_get_same _ _ _,
    h _ (by rw [Valuation.extend_get_ne hCE.symm]; rfl) (Valuation.extend_get_same _ _ _)⟩

/-- Global necessity entails local necessity (21a). -/
theorem LocallyNecessary.of_globally (hCE : C ≠ E) (h : GloballyNecessary M C c E e) :
    LocallyNecessary M C c E e :=
  LocallySufficient.of_globally hCE h

/-- Knowing the cause alone, *C causes E* is assertable exactly when the cause is globally
sufficient: the asymmetry of the paper's Table 2. -/
theorem cause_extend_empty_iff (hCE : C ≠ E) :
    Cause M (Valuation.empty.extend C c) C c E e ↔ GloballySufficient M C c E e := by
  constructor
  · rintro ⟨-, h⟩ bg hE hC
    refine h bg (λ v x hv => ?_) hE
    by_cases hvC : v = C
    · subst hvC
      unfold Valuation.hasValue at hv
      rw [Valuation.extend_get_same, Option.some.injEq] at hv
      subst hv
      exact hC
    · unfold Valuation.hasValue at hv
      rw [Valuation.extend_get_ne hvC] at hv
      exact absurd hv (by simp)
  · exact λ h => Cause.of_globallySufficient h (Valuation.extend_get_same _ _ _)

end General

/-! ### The lightbulb (Figure 2, Tables 1 and 2)

Two switches and a light that is on exactly when both are: each switch being on is necessary but
insufficient for the light to be on, and each being off suffices for it to be off. -/

namespace Light

/-- The two switches and the light. -/
inductive V
  | S1
  | S2
  | L
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨λ | .S1 => ∅ | .S2 => ∅ | .L => {.S1, .S2}⟩

def depth : V → ℕ := λ | .S1 => 0 | .S2 => 0 | .L => 1

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h
  revert h
  cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- The light is on exactly when both switches are. -/
noncomputable def light : BoolSEM V :=
  { graph := graph
    mech := λ
      | .S1 => const (G := graph) false
      | .S2 => const (G := graph) false
      | .L => deterministic (λ ρ => ρ ⟨.S1, by simp [graph]⟩ && ρ ⟨.S2, by simp [graph]⟩) }

instance : CausalGraph.IsDAG light.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic light where
  mech_det v := match v with
    | .S1 | .S2 => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .L => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- The light develops as the conjunction of the developed switches. -/
theorem developDetVtx_L {bg : Valuation (λ _ : V => Bool)} (h : bg.get .L = none) :
    developDetVtx light bg .L = (developDetVtx light bg .S1 && developDetVtx light bg .S2) := by
  rw [developDetVtx_undet _ _ _ h]
  rfl

/-- Switch 1 being off is globally sufficient for the light to be off. -/
theorem s1_off_globallySufficient : GloballySufficient light .S1 false .L false := by
  intro bg hL hS1
  rw [developDet_hasValue_iff, developDetVtx_L hL, developDetVtx_extended _ _ _ _ hS1]
  rfl

/-- Switch 1 being on is globally necessary for the light to be on: the mirror image. -/
theorem s1_on_globallyNecessary : GloballyNecessary light .S1 true .L true :=
  s1_off_globallySufficient

/-- The background with switch 1 on and switch 2 off. -/
noncomputable def s1OnS2Off : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .S1 true |>.extend .S2 false

/-- Switch 1 being on is not globally sufficient for the light to be on. -/
theorem s1_on_not_globallySufficient : ¬ GloballySufficient light .S1 true .L true := by
  intro h
  have hL : s1OnS2Off.get .L = none := by
    rw [s1OnS2Off, Valuation.extend_get_ne (show (V.L : V) ≠ .S2 by decide),
      Valuation.extend_get_ne (show (V.L : V) ≠ .S1 by decide)]
    rfl
  have hS1 : s1OnS2Off.hasValue .S1 true := by
    unfold Valuation.hasValue
    rw [s1OnS2Off, Valuation.extend_get_ne (show (V.S1 : V) ≠ .S2 by decide),
      Valuation.extend_get_same]
  have hS2 : s1OnS2Off.get .S2 = some false := by
    rw [s1OnS2Off, Valuation.extend_get_same]
  have := h s1OnS2Off hL hS1
  rw [developDet_hasValue_iff, developDetVtx_L hL, developDetVtx_extended _ _ _ _ hS2] at this
  simp at this

/-- Bottom right of Table 2: knowing only that switch 1 is off, it caused the light to be off. -/
theorem s1_off_causes_off_uncertain :
    Cause light (Valuation.empty.extend .S1 false) .S1 false .L false :=
  (cause_extend_empty_iff (by decide)).2 s1_off_globallySufficient

/-- Bottom left of Table 2: knowing only that switch 1 is on, one cannot say it caused the light
to be on. -/
theorem not_s1_on_causes_on_uncertain :
    ¬ Cause light (Valuation.empty.extend .S1 true) .S1 true .L true :=
  λ h => s1_on_not_globallySufficient ((cause_extend_empty_iff (by decide)).1 h)

/-- The background with both switches on. -/
noncomputable def bothOn : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .S1 true |>.extend .S2 true

theorem bothOn_S1 : bothOn.hasValue .S1 true := by
  unfold Valuation.hasValue
  rw [bothOn, Valuation.extend_get_ne (show (V.S1 : V) ≠ .S2 by decide),
    Valuation.extend_get_same]

theorem bothOn_S2 : bothOn.hasValue .S2 true := by
  unfold Valuation.hasValue
  rw [bothOn, Valuation.extend_get_same]

/-- Top left of Table 2: with both switches known to be on, switch 1 caused the light to be on. -/
theorem s1_on_causes_on_certain : Cause light bothOn .S1 true .L true := by
  refine ⟨bothOn_S1, λ bg hle hL => ?_⟩
  rw [developDet_hasValue_iff, developDetVtx_L hL,
    developDetVtx_extended _ _ _ _ (hle _ _ bothOn_S1),
    developDetVtx_extended _ _ _ _ (hle _ _ bothOn_S2)]
  rfl

end Light

/-! ### Against necessity-based *cause* -/

namespace Bus

open NadathurLauer2020.Bus

/-- Lia takes the bus when it rains or her bike is gone. -/
theorem developDetVtx_Bs {bg : Valuation (λ _ : V => Bool)} (h : bg.get .Bs = none) :
    developDetVtx busSEM bg .Bs =
      (developDetVtx busSEM bg .Rn || developDetVtx busSEM bg .Bk) := by
  rw [developDetVtx_undet _ _ _ h]
  rfl

theorem s_b_Rn : (s_b.extend .Tr true).hasValue .Rn true := by
  unfold Valuation.hasValue
  rw [Valuation.extend_get_ne (show (V.Rn : V) ≠ .Tr by decide), s_b, Valuation.extend_get_same]

/-- In the bus scenario, with Ava's visit and the rain forecast known, Ava's training is a
locally sufficient cause of Lia's taking the bus, so Glass's *cause* accepts "Ava's training
caused Lia to take the bus", which [nadathur-lauer-2020]'s necessity-based *cause* rejects: the
same verb, the same scenario, opposite verdicts. -/
theorem glass_nl_diverge_on_bus :
    Cause busSEM (s_b.extend .Tr true) .Tr true .Bs true ∧
      ¬ Necessity.causeSem busSEM s_b .Tr true .Bs true := by
  refine ⟨⟨Valuation.extend_get_same _ _ _, λ bg hle hBs => ?_⟩, cause_infelicitous_for_bus⟩
  rw [developDet_hasValue_iff, developDetVtx_Bs hBs,
    developDetVtx_extended _ _ _ _ (hle _ _ s_b_Rn)]
  rfl

end Bus

end Glass2023
