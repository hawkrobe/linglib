module

public import Linglib.Studies.NadathurLauer2020

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
sufficient (`cause_update_bot_iff`): a globally sufficient cause licenses *cause* under
uncertainty, a merely necessary one only under full information, which is the asymmetry of the
paper's Table 2, worked out on its lightbulb (`Light`). Since the Anna Karenina Principle assigns
desired outcomes conjunctive models, in which each factor is necessary but insufficient, and
undesired ones disjunctive models, in which each factor suffices, *C causes E* is true in more
states of knowledge when E is bad. Glass's *cause* asserts only local sufficiency where
[nadathur-lauer-2020] make it assert necessity, so the two diverge on the latter's bus scenario
(`glass_nl_diverge_on_bus`).

## Implementation notes

* A background is a setting of some variables, imposed on a causal model in a context; "no
  matter what happens to any other variable" quantifies over every context and every setting
  leaving the effect open.
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

@[expose] public section

namespace Glass2023

open CausalModel

section General

variable {U V : Type*} (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]

/-! ### Local and global necessity and sufficiency -/

/-- `C = c` is globally sufficient for `E = e` when, in every context and under every background
leaving `E` open in which `C = c`, `E = e`. -/
def GloballySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ u (I : V → Flat Bool), I E = ⊥ → I C = ↑c → M.solve I u E = e

/-- `C = c` is locally sufficient for `E = e` when, in some context and under some background
leaving `E` open in which `C = c`, `E = e`. -/
def LocallySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ u, ∃ I : V → Flat Bool, I E = ⊥ ∧ I C = ↑c ∧ M.solve I u E = e

/-- `C = c` is globally necessary for `E = e` when, without it, `E = e` fails in every context and
under every background leaving `E` open. -/
def GloballyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ u (I : V → Flat Bool), I E = ⊥ → I C = ↑(!c) → M.solve I u E = !e

/-- `C = c` is locally necessary for `E = e` when, without it, `E = e` fails in some context and
under some background leaving `E` open. -/
def LocallyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ u, ∃ I : V → Flat Bool, I E = ⊥ ∧ I C = ↑(!c) ∧ M.solve I u E = !e

/-- *C causes E* is assertable on the state of knowledge `k` when the cause is known and the effect
holds in every context under every background that keeps what is known and leaves it open. -/
def Cause (k : V → Flat Bool) (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  k C = ↑c ∧ ∀ u (I : V → Flat Bool), k ≤ I → I E = ⊥ → M.solve I u E = e

variable {M} {C E : V} {c e : Bool} {k : V → Flat Bool}

/-- Necessity is the mirror image of sufficiency: the absence of a necessary cause suffices for
the absence of the effect. -/
theorem globallyNecessary_iff :
    GloballyNecessary M C c E e ↔ GloballySufficient M C (!c) E (!e) := Iff.rfl

theorem locallyNecessary_iff :
    LocallyNecessary M C c E e ↔ LocallySufficient M C (!c) E (!e) := Iff.rfl

/-- A globally sufficient cause licenses *cause* whatever else is known or unknown. -/
theorem Cause.of_globallySufficient (h : GloballySufficient M C c E e) (hk : k C = ↑c) :
    Cause M k C c E e :=
  ⟨hk, fun u I hkI hE ↦ h u I hE (Flat.coe_le_iff.1 (hk ▸ hkI C))⟩

variable [DecidableEq V]

/-- Global sufficiency entails local sufficiency (22a). -/
theorem LocallySufficient.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballySufficient M C c E e) : LocallySufficient M C c E e :=
  ⟨default, [C ← c], by rw [Function.update_of_ne hCE.symm]; rfl,
    Function.update_self .., h _ _ (by rw [Function.update_of_ne hCE.symm]; rfl)
      (Function.update_self ..)⟩

/-- Global necessity entails local necessity (21a). -/
theorem LocallyNecessary.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballyNecessary M C c E e) : LocallyNecessary M C c E e :=
  LocallySufficient.of_globally hCE h

/-- Knowing the cause alone, *C causes E* is assertable exactly when the cause is globally
sufficient: the asymmetry of the paper's Table 2. -/
theorem cause_update_bot_iff :
    Cause M [C ← c] C c E e ↔ GloballySufficient M C c E e := by
  refine ⟨fun h u I hE hC ↦ h.2 u I (fun v ↦ ?_) hE,
    fun h ↦ Cause.of_globallySufficient h (Function.update_self ..)⟩
  by_cases hvC : v = C
  · subst hvC; rw [Function.update_self, hC]
  · rw [Function.update_of_ne hvC]; exact bot_le

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

/-- The light reads the two switches. -/
def edges : Finset (V × V) := {(.S1, .L), (.S2, .L)}

/-- The context settles the two switches. -/
structure Context where
  S1 : Bool
  S2 : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The light is on exactly when both switches are. -/
def light : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .S1 => fun u _ ↦ u.S1 | .S2 => fun u _ ↦ u.S2 | .L => fun _ x ↦ x .S1 && x .S2

instance : DecidableRel light.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : light.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The light's equation, under a background that leaves it open. -/
theorem solve_L {I : V → Flat Bool} (h : I .L = ⊥) (u : Context) :
    light.solve I u .L = (light.solve I u .S1 && light.solve I u .S2) :=
  solve_of_eq_bot h u

/-- Switch 1 being off is globally sufficient for the light to be off. -/
theorem s1_off_globallySufficient : GloballySufficient light .S1 false .L false :=
  fun u _ hL hS1 ↦ by rw [solve_L hL, solve_of_eq_coe hS1, Bool.false_and]

/-- Switch 1 being on is globally necessary for the light to be on. -/
theorem s1_on_globallyNecessary : GloballyNecessary light .S1 true .L true :=
  s1_off_globallySufficient

/-- Switch 1 being on is not globally sufficient for the light to be on, since with switch 2 off
the light stays off. -/
theorem s1_on_not_globallySufficient : ¬ GloballySufficient light .S1 true .L true :=
  fun h ↦ absurd (h ⟨true, false⟩ [.S1 ← true] (by decide) (by decide))
    (by decide)

/-- Bottom right of Table 2: knowing only that switch 1 is off, it caused the light to be off. -/
theorem s1_off_causes_off_uncertain :
    Cause light [.S1 ← false] .S1 false .L false :=
  cause_update_bot_iff.2 s1_off_globallySufficient

/-- Bottom left of Table 2: knowing only that switch 1 is on, one cannot say it caused the light
to be on. -/
theorem not_s1_on_causes_on_uncertain :
    ¬ Cause light [.S1 ← true] .S1 true .L true :=
  fun h ↦ s1_on_not_globallySufficient (cause_update_bot_iff.1 h)

/-- The background with both switches on. -/
def bothOn : V → Flat Bool := [.S1 ← true, .S2 ← true]

/-- Top left of Table 2: with both switches known to be on, switch 1 caused the light to be on. -/
theorem s1_on_causes_on_certain : Cause light bothOn .S1 true .L true := by
  refine ⟨by decide, fun u I hk hL ↦ ?_⟩
  have h1 : I .S1 = ↑true := Flat.coe_le_iff.1 ((by decide : bothOn .S1 = ↑true) ▸ hk .S1)
  have h2 : I .S2 = ↑true := Flat.coe_le_iff.1 ((by decide : bothOn .S2 = ↑true) ▸ hk .S2)
  rw [solve_L hL, solve_of_eq_coe h1, solve_of_eq_coe h2]
  rfl

end Light

/-! ### Against necessity-based *cause* -/

namespace Bus

open NadathurLauer2020.Bus

/-- In the bus scenario, with Ava's visit and the rain forecast known, Ava's training is a
sufficient cause of Lia's taking the bus in every settlement of the rest, rain alone sufficing,
so Glass's *cause* accepts "Ava's training caused Lia to take the bus", which
[nadathur-lauer-2020]'s necessity-based *cause* rejects: the same verb, the same scenario,
opposite verdicts. -/
theorem glass_nl_diverge_on_bus :
    Cause busModel (Function.update s_b .Tr ↑true) .Tr true .Bs true ∧
      ¬ NadathurLauer2020.denotation busModel .cause s_b .Tr true .Bs true := by
  refine ⟨⟨by decide, fun u I hk hBs ↦ ?_⟩, cause_infelicitous_for_bus⟩
  have hRn : I .Rn = ↑true :=
    Flat.coe_le_iff.1 ((by decide : Function.update s_b .Tr ↑true .Rn = ↑true) ▸ hk .Rn)
  rw [solve_of_eq_bot hBs]
  show (busModel.solve I u .Rn || busModel.solve I u .Bk) = true
  rw [solve_of_eq_coe hRn]
  rfl

end Bus

end Glass2023
