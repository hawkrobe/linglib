import Linglib.Semantics.Quantification.Basic

/-!
# The definite article

The Russellian description operator `russellIota P`, the unique member of `P` when there is
one, and its two other types: `THE P`, the Montague lift of that member to a quantifier, and the
determiner `Quantification.the_sem`, which asserts its scope of it. The three are one object,
`the_sem_iff_russellIota` and `the_sem_iff_THE`, so a study may state the truth conditions of a
definite at whichever type its analysis composes. `lower` is the partial inverse of the Montague
lift, the iota over the entities a quantifier is the lift of. [coppock-beaver-2015] factor the
iota's presupposition into `Existence` and `Uniqueness`, which
`existsUnique_iff_existence_and_uniqueness` relates to `∃!`.

## Main definitions

* `russellIota P`: the unique `P`, `none` unless `P` has exactly one member.
* `THE P`, `lower Q`: the Montague lift of the unique `P`, and the entity whose lift is `Q`.
* `Existence P`, `Uniqueness P`: the two components of the Russellian presupposition, the
  nonemptiness and the subsingletonhood of the extension of `P`.

## Main results

* `russellIota_eq_some_iff`, `russellIota_isSome_iff_exists_unique`: when the iota refers.
* `the_sem_iff_russellIota`, `the_sem_iff_THE`: the determiner, entity and quantifier meanings
  of the definite article agree.
* `russellIota_ident`, `lower_individual`, `THE_ident`: each partial shift of [partee-1987]
  inverts its total one.

## Implementation notes

The iota is `Option`-valued and classical: a description without a unique referent denotes
`none`, and `Presupposition.PartialProp.presupOfReferent` turns definedness into a
presupposition. A contextual domain `C` is a conjunct of the restrictor, `russellIota (· ∈ C ∧
P ·)`. The maximal member of a plural restrictor, [sharvy-1980]'s definite, is `IsGreatest` of
its extension and needs no operator of its own.

## References

* [russell-1905]
* [partee-1987]
* [coppock-beaver-2015]
* [sharvy-1980]
-/

namespace Definiteness

open Quantification

variable {E : Type*}

/-! ### The Russellian iota -/

/-- The unique member of `P`, when `P` has exactly one; `none` otherwise. -/
noncomputable def russellIota (P : E → Prop) : Option E :=
  open scoped Classical in if h : ∃! x, P x then some h.choose else none

theorem russellIota_eq_some_iff (P : E → Prop) (e : E) :
    russellIota P = some e ↔ P e ∧ ∀ x, P x → x = e := by
  classical
  unfold russellIota
  split_ifs with h
  · refine Option.some_inj.trans ⟨fun he => ?_, fun ⟨_, hu⟩ => hu _ h.choose_spec.1⟩
    subst he
    exact ⟨h.choose_spec.1, fun x hx => h.unique hx h.choose_spec.1⟩
  · exact iff_of_false (fun h => nomatch h) fun ⟨he, hu⟩ => h ⟨e, he, hu⟩

theorem russellIota_isSome_iff_exists_unique (P : E → Prop) :
    (russellIota P).isSome ↔ ∃! x, P x := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun e => russellIota_eq_some_iff P e

/-! ### The Coppock–Beaver factorization -/

/-- `P` has a member, the asserted component of the Russellian presupposition. -/
def Existence (P : E → Prop) : Prop := ∃ x, P x

/-- `P` has at most one member, the presupposed component. -/
def Uniqueness (P : E → Prop) : Prop := ∀ x y, P x → P y → x = y

/-- `∃!` is existence with uniqueness. -/
theorem existsUnique_iff_existence_and_uniqueness (P : E → Prop) :
    (∃! x, P x) ↔ Existence P ∧ Uniqueness P :=
  ⟨fun ⟨x, hx, hu⟩ => ⟨⟨x, hx⟩, fun a b ha hb => (hu a ha).trans (hu b hb).symm⟩,
    fun ⟨⟨x, hx⟩, hu⟩ => ⟨x, hx, fun y hy => hu y x hy hx⟩⟩

/-! ### Partee's partial shifts -/

/-- The presuppositional definite article, the Montague lift of the unique `P`. -/
noncomputable def THE (P : E → Prop) : Option (Quantifier E) := (russellIota P).map individual

/-- The entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
noncomputable def lower (Q : Quantifier E) : Option E := russellIota fun j => Q = individual j

theorem russellIota_ident (j : E) : russellIota (ident j) = some j :=
  (russellIota_eq_some_iff _ _).2 ⟨rfl, fun _ h => h⟩

theorem lower_individual (j : E) : lower (individual j) = some j :=
  (russellIota_eq_some_iff _ _).2 ⟨rfl, fun _ h => (individual_injective h).symm⟩

theorem THE_ident (j : E) : THE (ident j) = some (individual j) := by
  rw [THE, russellIota_ident]; rfl

/-! ### The three types of the definite article -/

/-- The determiner *the* asserts its scope of the Russellian referent. -/
theorem the_sem_iff_russellIota (R S : E → Prop) : the_sem R S ↔ ∃ x ∈ russellIota R, S x :=
  exists_congr fun x => and_congr_left' <|
    (⟨fun h => ⟨(h x).2 rfl, fun y => (h y).1⟩, fun ⟨hx, hu⟩ y => ⟨hu y, fun e => e ▸ hx⟩⟩ :
      (∀ y, R y ↔ y = x) ↔ R x ∧ ∀ y, R y → y = x).trans (russellIota_eq_some_iff R x).symm

/-- The determiner *the* is the quantifier `THE` applied to its scope. -/
theorem the_sem_iff_THE (R S : E → Prop) : the_sem R S ↔ ∃ Q ∈ THE R, Q S :=
  (the_sem_iff_russellIota R S).trans
    ⟨fun ⟨x, hx, hS⟩ => ⟨individual x, Option.map_eq_some_iff.2 ⟨x, hx, rfl⟩, hS⟩,
      fun ⟨_, hQ, hS⟩ =>
        let ⟨x, hx, hxQ⟩ := Option.map_eq_some_iff.1 hQ; ⟨x, hx, (hxQ ▸ hS : individual x S)⟩⟩

end Definiteness
