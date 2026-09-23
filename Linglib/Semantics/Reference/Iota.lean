module

public import Mathlib.Data.Set.Subsingleton
public import Linglib.Semantics.Quantification.Basic

/-!
# The Russellian iota

The unique satisfier of a predicate, as a partial individual: `russellIota P` is `some e` when
`e` is the only `P`, and `none` when `P` has no satisfier or several ([russell-1905]). Definedness
is unique existence (`russellIota_isSome_iff`), which factors into existence and uniqueness of
the extension (`existsUnique_iff_nonempty_subsingleton`), the two components
[coppock-beaver-2015] separate into an assertion and a presupposition.

[partee-1987]'s partial type shifts are Russellian iotas: `THE`, the Montague lift of the unique
member of a property, and `lower`, the entity whose lift a principal ultrafilter is; each inverts
its total shift (`THE_ident`, `lower_individual`). The determiner `Quantifier.GQ.the_sem` is the
same object at the third type: it asserts its scope of the Russellian referent, and it is `THE`
applied to the scope (`the_sem_iff_russellIota`, `the_sem_iff_THE`).

## Main definitions

* `Reference.russellIota`: the unique satisfier of a predicate, or `none`.
* `Reference.THE`, `Reference.lower`: Partee's partial shifts.

## Main results

* `russellIota_eq_some_iff`, `russellIota_isSome_iff`, `russellIota_eq_none_iff`.
* `existsUnique_iff_nonempty_subsingleton`: `∃!` is nonemptiness with subsingletonness.
* `the_sem_iff_russellIota`, `the_sem_iff_THE`: the determiner, entity and quantifier meanings
  of the definite article agree.

## References

* [russell-1905]
* [coppock-beaver-2015]
* [partee-1987]
-/

@[expose] public section

variable {α : Type*} {p : α → Prop}

/-- Unique existence is nonemptiness together with subsingletonness of the extension. -/
theorem existsUnique_iff_nonempty_subsingleton :
    (∃! x, p x) ↔ {x | p x}.Nonempty ∧ {x | p x}.Subsingleton :=
  (exists_congr fun _ ↦ Set.eq_singleton_iff_unique_mem.symm).trans
    Set.exists_eq_singleton_iff_nonempty_subsingleton

namespace Reference

variable {E : Type*} (P : E → Prop) {e : E}

/-- The unique satisfier of `P`, or `none` when `P` has no satisfier or several. -/
noncomputable def russellIota : Option E :=
  letI := Classical.dec (∃! x, P x)
  if h : ∃! x, P x then some h.choose else none

theorem russellIota_eq_some_iff : russellIota P = some e ↔ P e ∧ ∀ x, P x → x = e := by
  classical
  unfold russellIota
  split_ifs with h
  · rw [Option.some_inj, h.choose_eq_iff]
    exact ⟨fun he ↦ ⟨he, fun _ hx ↦ h.unique hx he⟩, And.left⟩
  · exact ⟨(nomatch ·), fun he ↦ (h ⟨e, he⟩).elim⟩

theorem russellIota_isSome_iff : (russellIota P).isSome ↔ ∃! x, P x := by
  classical
  unfold russellIota
  split_ifs with h <;> simp [h]

theorem russellIota_eq_none_iff : russellIota P = none ↔ ¬ ∃! x, P x := by
  rw [← Option.not_isSome_iff_eq_none, russellIota_isSome_iff]

/-! ### Partee's partial shifts -/

section Partee

open Quantifier Quantifier.GQ Quantifier.NP

variable (j : E)

/-- The presuppositional definite article, the Montague lift of the unique `P`. -/
noncomputable def THE : Option (NP E) := (russellIota P).map individual

/-- The entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
noncomputable def lower (Q : NP E) : Option E := russellIota fun j ↦ Q = individual j

theorem russellIota_ident : russellIota (ident j) = some j :=
  (russellIota_eq_some_iff _).2 ⟨rfl, fun _ h ↦ h⟩

theorem lower_individual : lower (individual j) = some j :=
  (russellIota_eq_some_iff _).2 ⟨rfl, fun _ h ↦ (individual_injective h).symm⟩

theorem THE_ident : THE (ident j) = some (individual j) := by
  rw [THE, russellIota_ident]; rfl

/-! ### The three types of the definite article -/

variable (S : E → Prop)

/-- The determiner *the* asserts its scope of the Russellian referent. -/
theorem the_sem_iff_russellIota : the_sem P S ↔ ∃ x ∈ russellIota P, S x :=
  exists_congr fun x ↦ and_congr_left' <|
    (⟨fun h ↦ ⟨(h x).2 rfl, fun y ↦ (h y).1⟩, fun ⟨hx, hu⟩ y ↦ ⟨hu y, fun e ↦ e ▸ hx⟩⟩ :
      (∀ y, P y ↔ y = x) ↔ P x ∧ ∀ y, P y → y = x).trans (russellIota_eq_some_iff P).symm

/-- The determiner *the* is the quantifier `THE` applied to its scope. -/
theorem the_sem_iff_THE : the_sem P S ↔ ∃ Q ∈ THE P, Q S :=
  (the_sem_iff_russellIota P S).trans
    ⟨fun ⟨x, hx, hS⟩ ↦ ⟨individual x, Option.map_eq_some_iff.2 ⟨x, hx, rfl⟩, hS⟩,
      fun ⟨_, hQ, hS⟩ ↦
        let ⟨x, hx, hxQ⟩ := Option.map_eq_some_iff.1 hQ; ⟨x, hx, (hxQ ▸ hS : individual x S)⟩⟩

end Partee

end Reference
