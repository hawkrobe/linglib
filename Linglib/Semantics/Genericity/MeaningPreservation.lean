module

public import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Meaning Preservation

This file defines Meaning Preservation, the ranking of covert type shifts that decides which of
the shifts available to a bare nominal it takes. [chierchia-1998] restricts covert type shifting
in two ways: the Blocking Principle bars a shift that a determiner of the language lexicalizes,
and Meaning Preservation ranks the shifts, so that a bare nominal takes the highest-ranked of
those available to it. Both rankings in the literature have two tiers, and a two-tier ranking is
the predicate of its upper tier, `Prop` ordered by implication. A shift applies when it is
`MaximalFor` the ranking among the available shifts, that is, when it is available and in the
upper tier unless no available shift is.

Chierchia ranks ∩ alone above ι and ∃ (`MeaningPreservation.chierchia`), (39b) in
[dayal-2004]'s rendering. [dayal-2004] revises the ranking to {∩, ι} > ∃
(`MeaningPreservation.dayal`), (39c), on Chierchia's own rationale that ∩ is preferred because it
changes the type without introducing quantificational force, which holds of ι as well. The two
rankings choose alike wherever no definite shift is available, as in a language whose definite
article blocks ι and ι^x (`maximalFor_chierchia_iff_dayal`), and part ways where ι is available:
under Dayal's ranking ι applies whenever it is unblocked (`maximalFor_dayal_iota`), under
Chierchia's only where ∩ is undefined (`maximalFor_chierchia_iota`).

## Main definitions

* `Available` — the covert shifts available to a bare nominal: defined for it
  and not blocked
* `MeaningPreservation.chierchia`, `MeaningPreservation.dayal` — the two rankings

## Main results

* `maximalFor_chierchia_iff`, `maximalFor_dayal_iff` — which available shifts each ranking selects
* `maximalFor_dayal_down`, `maximalFor_dayal_iota`, `maximalFor_dayal_exists` — under Dayal's
  ranking ∩ and ι apply wherever available and ∃ only as a last resort
* `maximalFor_chierchia_down`, `maximalFor_chierchia_iota`, `maximalFor_chierchia_exists` — under
  Chierchia's ranking ι and ∃ apply only where ∩ is undefined
* `maximalFor_chierchia_iff_dayal` — the rankings agree where no definite shift is available

## Implementation notes

ι^x, the anaphoric definite of [jenks-2018], postdates both rankings, and [moroney-2021] is the
first to make it a covert shift. It introduces no quantificational force, so `dayal` ranks it
with ∩ and ι, and `chierchia` ranks it with ι.

## References

* [chierchia-1998]
* [dayal-2004]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

open Genericity

namespace Determiner.Inventory

/-- A covert shift is available to a bare nominal in a language with the determiners `ds` when it
is defined for the nominal, ∩ only where `down` holds, and no determiner blocks it. ∩ is defined
for a plural or a mass noun (`DownDefined`), but not for a singular count noun, nor for a
property anchored to particular entities such as *parts of this machine* ([dayal-2004]'s
fn. 1). -/
def Available (ds : Inventory) (down : Prop) (τ : CovertShift) : Prop :=
  (τ = .down → down) ∧ ¬ ds.Blocks τ

instance (ds : Inventory) (down : Prop) [Decidable down] : DecidablePred (ds.Available down) :=
  fun _ ↦ by unfold Available; infer_instance

end Determiner.Inventory

namespace Genericity.MeaningPreservation

/-- An index is maximal for a predicate `T`, ordered by implication, among those satisfying `P`
exactly when it satisfies `T` or none of them does. -/
private theorem maximalFor_prop_iff {ι : Type*} {P T : ι → Prop} {i : ι} :
    MaximalFor P T i ↔ P i ∧ (T i ∨ ∀ j, P j → ¬ T j) :=
  ⟨fun ⟨hi, h⟩ ↦ ⟨hi, or_iff_not_imp_left.2 fun hT _ hj hTj ↦ hT (h hj (fun _ ↦ hTj) hTj)⟩,
    fun ⟨hi, h⟩ ↦ ⟨hi, fun j hj _ hTj ↦ h.resolve_right fun h' ↦ h' j hj hTj⟩⟩

/-- [chierchia-1998]'s Meaning Preservation, ∩ > {ι, ∃}, puts kind formation alone in the upper
tier. -/
def chierchia (τ : CovertShift) : Prop := τ = .down

/-- [dayal-2004]'s Revised Meaning Preservation, {∩, ι} > ∃, puts every shift in the upper tier
but ∃, the one that introduces quantificational force. -/
def dayal (τ : CovertShift) : Prop := τ ≠ .exists

variable {A : CovertShift → Prop} {τ : CovertShift}

/-- Under Chierchia's ranking an available shift applies when it is ∩ or ∩ is unavailable. -/
theorem maximalFor_chierchia_iff :
    MaximalFor A chierchia τ ↔ A τ ∧ (τ = .down ∨ ¬ A .down) := by
  rw [maximalFor_prop_iff]
  exact and_congr_right fun _ ↦ or_congr_right
    ⟨fun h hd ↦ h _ hd rfl, fun h _ hj hd ↦ h (hd ▸ hj)⟩

/-- Under Dayal's ranking an available shift applies when it is not ∃ or only ∃ is available. -/
theorem maximalFor_dayal_iff :
    MaximalFor A dayal τ ↔ A τ ∧ (τ ≠ .exists ∨ ∀ σ, A σ → σ = .exists) := by
  simp [maximalFor_prop_iff, dayal]

instance [DecidablePred A] : DecidablePred (MaximalFor A chierchia) := fun _ ↦
  decidable_of_iff _ maximalFor_chierchia_iff.symm

instance [DecidablePred A] : DecidablePred (MaximalFor A dayal) := fun _ ↦
  decidable_of_iff _ maximalFor_dayal_iff.symm

open Determiner.Inventory

variable {ds : Determiner.Inventory} {down : Prop}

/-- Under Dayal's ranking ∩ applies wherever it is defined, since no determiner blocks it. -/
@[simp] theorem maximalFor_dayal_down : MaximalFor (ds.Available down) dayal .down ↔ down := by
  simp [maximalFor_dayal_iff, Available, not_blocks_down]

/-- Under Dayal's ranking ι applies wherever it is unblocked, whether or not ∩ is defined. -/
@[simp] theorem maximalFor_dayal_iota :
    MaximalFor (ds.Available down) dayal .iota ↔ ¬ ds.Blocks .iota := by
  simp [maximalFor_dayal_iff, Available]

/-- Under Dayal's ranking ∃ is a last resort, applying only where ∩ is undefined and ι and ι^x
are blocked. -/
@[simp] theorem maximalFor_dayal_exists :
    MaximalFor (ds.Available down) dayal .exists ↔
      ¬ ds.Blocks .exists ∧ ¬ down ∧ ds.Blocks .iota ∧ ds.Blocks .iotaAnaphoric := by
  simp only [maximalFor_dayal_iff, Available, ne_eq, not_true_eq_false, false_or]
  refine ⟨fun ⟨⟨_, h⟩, h'⟩ ↦ ⟨h, fun hd ↦ ?_, not_not.1 fun hι ↦ ?_, not_not.1 fun hx ↦ ?_⟩,
    fun ⟨h, hd, hι, hx⟩ ↦ ⟨⟨nofun, h⟩, fun σ ⟨hσ, hb⟩ ↦ ?_⟩⟩
  · exact absurd (h' .down ⟨fun _ ↦ hd, ds.not_blocks_down⟩) nofun
  · exact absurd (h' .iota ⟨nofun, hι⟩) nofun
  · exact absurd (h' .iotaAnaphoric ⟨nofun, hx⟩) nofun
  · cases σ <;> simp_all

/-- Under Chierchia's ranking, too, ∩ applies wherever it is defined. -/
@[simp] theorem maximalFor_chierchia_down :
    MaximalFor (ds.Available down) chierchia .down ↔ down := by
  simp [maximalFor_chierchia_iff, Available,
    not_blocks_down]

/-- Under Chierchia's ranking ι applies only where it is unblocked and ∩ undefined, so kind
formation pre-empts the definite. -/
@[simp] theorem maximalFor_chierchia_iota :
    MaximalFor (ds.Available down) chierchia .iota ↔ ¬ ds.Blocks .iota ∧ ¬ down := by
  simp [maximalFor_chierchia_iff, Available,
    not_blocks_down]

/-- Under Chierchia's ranking ∃ applies wherever it is unblocked and ∩ undefined, whether or not
ι is available. -/
@[simp] theorem maximalFor_chierchia_exists :
    MaximalFor (ds.Available down) chierchia .exists ↔ ¬ ds.Blocks .exists ∧ ¬ down := by
  simp [maximalFor_chierchia_iff, Available,
    not_blocks_down]

/-- Where the determiners block ι and ι^x, as a definite article used anaphorically does, the two
rankings select the same shifts. -/
theorem maximalFor_chierchia_iff_dayal (hι : ds.Blocks .iota) (hx : ds.Blocks .iotaAnaphoric) :
    MaximalFor (ds.Available down) chierchia τ ↔ MaximalFor (ds.Available down) dayal τ := by
  cases τ
  case iotaAnaphoric =>
    simp [maximalFor_chierchia_iff, maximalFor_dayal_iff, Available, hx]
  all_goals simp [hι, hx]

end Genericity.MeaningPreservation
