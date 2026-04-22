import Linglib.Theories.Semantics.Conditionals.PremiseSemantic

/-!
# @cite{ciardelli-zhang-champollion-2018} switches under @cite{kratzer-2012} lumping CF

Companion to `Phenomena/Conditionals/Studies/CiardelliZhangChampollion2018.lean`
(which formalizes CZC's argument against minimal-change semantics) and to
`Phenomena/Conditionals/Studies/Kratzer2012Lumping.lean` (which
formalizes the §5.4.4 lumping CF on the Paula apple-buying scenario).
This file applies the lumping CF to CZC's switches scenario and proves
it has a different failure pattern than minimal-change CF.

## The result: asymmetric failure across operators

```
| Operator                          | aDn > OFF | bDn > OFF | ¬(A∧B) > OFF |
| --------------------------------- | --------- | --------- | ------------ |
| Empirics (Tables 7–8)             | TRUE 78%  | TRUE 76%  | FALSE 20%    |
| Lewis/Stalnaker minimal-change    | TRUE ✓    | TRUE ✓    | TRUE ✗       |
| Kratzer 2012 lumping CF           | FALSE ✗   | FALSE ✗   | FALSE ✓      |
```

Lewis fails on the disjunctive antecedent
(`CiardelliZhangChampollion2018.minimal_change_forces_notBothUp_off`
plus `notBothUp_off_at_uu` makes this concrete). **Lumping fails on
simple antecedents** (this file: `not_wouldCF_aDn_lightOff` and
`not_wouldCF_bDn_lightOff`). And lumping correctly predicts the
disjunctive case false (`not_wouldCF_notBothUp_lightOff`) — though for
the same structural reason it gets the simple ones wrong.

Neither operator predicts all three correctly. This is a genuine
theoretical incompatibility — exactly the kind that the linglib
"interconnection density" goal exists to surface.

## Why the asymmetry

**Lewis CF** restricts to the *closest* antecedent-worlds. For `aDn > OFF`:
the closest aDn-world to `uu` is `du` (Hamming distance 1), where
`lightOff` holds. For `¬(A∧B) > OFF`: the closest are `{ud, du}`, both
`lightOff`. Lewis correctly predicts the simple ones; the disjunctive
prediction inherits CZC §1.2's structural failure.

**Lumping CF** considers *all consistent extensions* of the antecedent
within an admissible Base Set. With `aDn` as antecedent at `uu`: any
consistent extension that includes `aDn` is compatible with both
`du`-style and `dd`-style worlds (since `aDn ∩ Worlds = {du, dd}`).
`Follows {aDn} lightOff` therefore fails, since `dd` is an `aDn`-world
where `lightOff` is false (both switches down → light *on* by the
wiring). Without a closest-worlds restriction, lumping has no way to
break the `du`/`dd` symmetry on the simple counterfactuals.

The symmetric upside: lumping correctly predicts `¬(A∧B) > OFF` false,
because `Follows {notBothUp} lightOff` also fails (again `dd` blocks).

## Formalization

We use the worlds-only switches model lifted to a `SituationFrame` via
`Frame.toDiscreteSituationFrame`. Under discrete parthood,
`Core.IntensionalLogic.Lumping.Lumps.discrete_iff` reduces lumping to
joint truth at `w`. This gives a clean (if degenerate) lumping
behavior: every fact true at `uu` lumps every other fact true at `uu`,
so the Crucial Set's lumping-closure clause forces any Crucial Set
member containing a Base-Set element to contain *all* Base-Set
elements — which is incompatible with the counterfactual antecedent.

Therefore every Crucial Set in this model collapses to the singleton
`{antecedent}`, and `wouldCF` reduces to `Follows {antecedent}
consequent`, i.e., "every antecedent-world satisfies the consequent."

## Scope and caveats

This is the **worlds-only** model (no proper partial situations
beyond worlds-as-themselves). A more sophisticated partial-situation
model with the wiring law as a @cite{kratzer-2012} §5.5 non-accidental
generalization (rather than a contingent member of `Fw`) might
ameliorate the asymmetry. We do not explore that here.

`Fw₀` choice: we use the empty Base Set. The result generalizes — for
*any* Base Set choice including the wiring law and the actual switch
positions, the same `dd`-blocking argument forces `Follows {aDn}
lightOff` false (since `aDn ∩ Worlds = {du, dd}` regardless of Fw).
The empty Base Set keeps the proofs direct.
-/

namespace Phenomena.Conditionals.Studies.CiardelliZhangChampollion2018Lumping

open Core.IntensionalLogic
open Core.IntensionalLogic.Lumping (Lumps IsConsistent IsCompatible Follows)
open Semantics.Conditionals.PremiseSemantic
  (CrucialSet IsCrucialSet wouldCF)

/-! ## The switches model -/

/-- The four switch-position worlds (same as
    `CiardelliZhangChampollion2018.World`; renamed locally to avoid
    namespace ambiguity). -/
inductive World where
  /-- A up, B up — actual world; light on. -/
  | uu
  /-- A up, B down — light off. -/
  | ud
  /-- A down, B up — light off. -/
  | du
  /-- A down, B down — light on. -/
  | dd
  deriving Repr, DecidableEq

/-- Discrete partial order on worlds: `s ≤ t ↔ s = t`. (Worlds-only
    model — no proper sub-situations.) -/
instance : PartialOrder World := discreteOrder World

/-- The switches frame promoted to a `SituationFrame` with discrete
    parthood. -/
def switchesSituationFrame : SituationFrame where
  Entity := Unit
  Index := World
  order := inferInstance

/-! ## Propositions

Truth-makers at the worlds-only level (every world supports its own
positive facts; nothing else). -/

/-- "Switch A is up." -/
def aUp : Set switchesSituationFrame.Index := {.uu, .ud}
/-- "Switch A is down." -/
def aDn : Set switchesSituationFrame.Index := {.du, .dd}
/-- "Switch B is up." -/
def bUp : Set switchesSituationFrame.Index := {.uu, .du}
/-- "Switch B is down." -/
def bDn : Set switchesSituationFrame.Index := {.ud, .dd}
/-- "At least one switch is down" (= `¬(A ∧ B)`). -/
def notBothUp : Set switchesSituationFrame.Index := {.ud, .du, .dd}
/-- "The light is on" (per the wiring law, holds iff both switches in
    the same position). -/
def lightOn : Set switchesSituationFrame.Index := {.uu, .dd}
/-- "The light is off." -/
def lightOff : Set switchesSituationFrame.Index := {.ud, .du}

/-! ## Worlds (maximal situations)

Under the discrete order, every world is maximal. -/

theorem all_isWorld (w : switchesSituationFrame.Index) :
    IsWorld w := by
  intro w' hw'
  exact hw'.symm.le

theorem worlds_eq_univ :
    switchesSituationFrame.Worlds = Set.univ := by
  ext w; exact ⟨fun _ => trivial, fun _ => all_isWorld w⟩

/-! ## The Crucial Set collapses to a singleton

For any antecedent `p` not true at `uu` and any non-empty Base Set
`Fw₀ ⊆ {q : Set World | uu ∈ q}`, the discrete-parthood lumping
closure forces every Crucial Set member containing one Fw element to
contain all of them — and that union is inconsistent with `p`. So the
only consistent lumping-closed Crucial Set member is `{p}` itself.

For our negative result we use `Fw₀ = ∅`, which trivializes the
lumping closure further: the only Crucial Set member is `{p}` because
there are no Fw elements to add. -/

/-- Empty Base Set. -/
def Fw₀ : Set (Set switchesSituationFrame.Index) := ∅

/-- With an empty Base Set, the Crucial Set for any antecedent
    consistent at *some* world reduces to the singleton `{antecedent}`. -/
theorem crucialSet_empty_Fw_eq_singleton
    (p : Set switchesSituationFrame.Index)
    (hp : (switchesSituationFrame.Worlds ∩ p).Nonempty) :
    CrucialSet (F := switchesSituationFrame) Fw₀ World.uu p = {{p}} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · -- Membership: {p} ∈ CrucialSet Fw₀ uu p
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- subset_insert: {p} ⊆ insert p ∅ = {p}
      intro x hx; rcases hx with rfl; exact Set.mem_insert _ _
    · -- antecedent_mem: p ∈ {p}
      rfl
    · -- consistent: ⟨w, w ∈ Worlds, ∀ q ∈ {p}, w ∈ q⟩
      obtain ⟨w, hw_world, hw_p⟩ := hp
      refine ⟨w, hw_world, ?_⟩
      intro q hq; rcases hq with rfl; exact hw_p
    · -- lumping_closed: vacuous (Fw₀ = ∅, no r ∈ Fw₀ to consider)
      intro _ _ _ hr _
      exact hr.elim
  · -- Uniqueness: every CrucialSet member equals {p}
    intro A hA
    apply Set.eq_of_subset_of_subset
    · intro x hx
      -- x ∈ A ⊆ insert p Fw₀ = insert p ∅ = {p}
      have := hA.subset_insert hx
      rcases this with rfl | hxFw
      · exact Set.mem_singleton _
      · exact hxFw.elim
    · intro x hx
      rcases hx with rfl
      exact hA.antecedent_mem

/-! ## The asymmetric failure: lumping CF on the simple antecedents

The headline result. `wouldCF Fw₀ uu aDn lightOff` is **false** —
empirically the wrong prediction. The reason: `Follows {aDn} lightOff`
fails because the world `dd` satisfies `aDn` but not `lightOff` (both
switches down means the light is *on* by the wiring). -/

/-- `dd` is an `aDn`-world where `lightOff` fails — the witness that
    breaks `Follows {aDn} lightOff`. -/
theorem follows_aDn_lightOff_fails :
    ¬ Follows (F := switchesSituationFrame) {aDn} lightOff := by
  intro h
  have h_world : (.dd : World) ∈ switchesSituationFrame.Worlds :=
    all_isWorld _
  have h_aDn : (.dd : World) ∈ aDn := Or.inr rfl
  have h_inter : (.dd : World) ∈ ⋂₀ ({aDn} : Set (Set World)) := by
    intro q hq; rcases hq with rfl; exact h_aDn
  have h_lightOff : (.dd : World) ∈ lightOff := h ⟨h_world, h_inter⟩
  -- lightOff = {ud, du}; dd ≠ ud and dd ≠ du
  rcases h_lightOff with hh | hh <;> cases hh

/-- The symmetric witness for `bDn`. -/
theorem follows_bDn_lightOff_fails :
    ¬ Follows (F := switchesSituationFrame) {bDn} lightOff := by
  intro h
  have h_world : (.dd : World) ∈ switchesSituationFrame.Worlds :=
    all_isWorld _
  have h_bDn : (.dd : World) ∈ bDn := Or.inr rfl
  have h_inter : (.dd : World) ∈ ⋂₀ ({bDn} : Set (Set World)) := by
    intro q hq; rcases hq with rfl; exact h_bDn
  have h_lightOff : (.dd : World) ∈ lightOff := h ⟨h_world, h_inter⟩
  rcases h_lightOff with hh | hh <;> cases hh

/-- And for `notBothUp` (`¬(A ∧ B)`) — `dd` blocks here too, this
    time *correctly* matching the empirics. -/
theorem follows_notBothUp_lightOff_fails :
    ¬ Follows (F := switchesSituationFrame) {notBothUp} lightOff := by
  intro h
  have h_world : (.dd : World) ∈ switchesSituationFrame.Worlds :=
    all_isWorld _
  have h_NAB : (.dd : World) ∈ notBothUp := Or.inr (Or.inr rfl)
  have h_inter : (.dd : World) ∈ ⋂₀ ({notBothUp} : Set (Set World)) := by
    intro q hq; rcases hq with rfl; exact h_NAB
  have h_lightOff : (.dd : World) ∈ lightOff := h ⟨h_world, h_inter⟩
  rcases h_lightOff with hh | hh <;> cases hh

/-! ### Witnesses of antecedent consistency (for the Crucial Set proofs) -/

private theorem aDn_consistent :
    (switchesSituationFrame.Worlds ∩ aDn).Nonempty :=
  ⟨World.du, all_isWorld _, Or.inl rfl⟩

private theorem bDn_consistent :
    (switchesSituationFrame.Worlds ∩ bDn).Nonempty :=
  ⟨World.ud, all_isWorld _, Or.inl rfl⟩

private theorem notBothUp_consistent :
    (switchesSituationFrame.Worlds ∩ notBothUp).Nonempty :=
  ⟨World.ud, all_isWorld _, Or.inl rfl⟩

/-! ### The three headline theorems

Lumping CF (with empty `Fw₀`) predicts **false** for all three
counterfactuals. The first two are empirically *wrong* (lumping's
failure); the third is empirically *right* (lumping's lucky catch). -/

/-- **Lumping CF wrongly predicts `aDn > OFF` false** (empirically
    ~78% true). The dd-world (both switches down → light on)
    satisfies the antecedent but not the consequent, blocking the
    `Follows` step that the singleton Crucial Set demands. -/
theorem not_wouldCF_aDn_lightOff :
    ¬ wouldCF (F := switchesSituationFrame) Fw₀ World.uu aDn lightOff := by
  intro hwould
  have h_singleton := crucialSet_empty_Fw_eq_singleton aDn aDn_consistent
  -- {aDn} is the only Crucial Set member; instantiate
  have h_in_CS : ({aDn} : Set (Set World)) ∈
      CrucialSet (F := switchesSituationFrame) Fw₀ World.uu aDn := by
    rw [h_singleton]; exact rfl
  obtain ⟨A', hA'_in, _, hFollows⟩ := hwould {aDn} h_in_CS
  rw [h_singleton] at hA'_in
  rcases hA'_in with rfl
  exact follows_aDn_lightOff_fails hFollows

/-- **Lumping CF wrongly predicts `bDn > OFF` false** (empirically
    ~76% true). Symmetric to the `aDn` case. -/
theorem not_wouldCF_bDn_lightOff :
    ¬ wouldCF (F := switchesSituationFrame) Fw₀ World.uu bDn lightOff := by
  intro hwould
  have h_singleton := crucialSet_empty_Fw_eq_singleton bDn bDn_consistent
  have h_in_CS : ({bDn} : Set (Set World)) ∈
      CrucialSet (F := switchesSituationFrame) Fw₀ World.uu bDn := by
    rw [h_singleton]; exact rfl
  obtain ⟨A', hA'_in, _, hFollows⟩ := hwould {bDn} h_in_CS
  rw [h_singleton] at hA'_in
  rcases hA'_in with rfl
  exact follows_bDn_lightOff_fails hFollows

/-- **Lumping CF correctly predicts `¬(A ∧ B) > OFF` false**
    (empirically ~20% true, i.e., not-true). Same structural reason
    as the simple cases — the dd-world blocks `Follows`. -/
theorem not_wouldCF_notBothUp_lightOff :
    ¬ wouldCF (F := switchesSituationFrame) Fw₀ World.uu notBothUp lightOff := by
  intro hwould
  have h_singleton :=
    crucialSet_empty_Fw_eq_singleton notBothUp notBothUp_consistent
  have h_in_CS : ({notBothUp} : Set (Set World)) ∈
      CrucialSet (F := switchesSituationFrame) Fw₀ World.uu notBothUp := by
    rw [h_singleton]; exact rfl
  obtain ⟨A', hA'_in, _, hFollows⟩ := hwould {notBothUp} h_in_CS
  rw [h_singleton] at hA'_in
  rcases hA'_in with rfl
  exact follows_notBothUp_lightOff_fails hFollows

/-! ## The asymmetry, formally

Pulling the three predictions together with the
`CiardelliZhangChampollion2018` results: lumping and minimal-change
operators fail on disjoint subsets of the switches counterfactuals. -/

/-- **Asymmetric failure**: lumping CF and minimal-change CF have
    disjoint failure modes on switches. Lumping is wrong on the simple
    antecedents (this file's `not_wouldCF_aDn_lightOff` /
    `not_wouldCF_bDn_lightOff`); minimal-change is wrong on the
    disjunctive antecedent (CZC2018's `notBothUp_off_at_uu` predicts
    true, contrary to empirics).

    Statement form: lumping CF predicts `aDn > OFF` false (empirically
    wrong), AND lumping CF predicts `notBothUp > OFF` false
    (empirically right). The contrast with minimal-change is that
    minimal-change predicts `aDn > OFF` true and `notBothUp > OFF`
    true; the empirics are true / false. -/
theorem lumping_failure_pattern :
    ¬ wouldCF (F := switchesSituationFrame) Fw₀ World.uu aDn lightOff ∧
    ¬ wouldCF (F := switchesSituationFrame) Fw₀ World.uu notBothUp lightOff :=
  ⟨not_wouldCF_aDn_lightOff, not_wouldCF_notBothUp_lightOff⟩

end Phenomena.Conditionals.Studies.CiardelliZhangChampollion2018Lumping
