module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Antichain
public import Linglib.Semantics.Quantification.Basic

/-!
# Iota

The iota operator takes a predicate to the individual it describes, when there is one. On a
domain without parts, `russellIota P` is the unique satisfier of `P` and is `none` when `P` has
no satisfier or several. Its definedness is unique existence, which splits into existence and
uniqueness of the extension, the two components that Coppock and Beaver separate into an
assertion and a presupposition. Partee's partial type shifts `THE` and `lower` are Russellian
iotas, and each inverts its total shift.

Sharvy generalizes ι to individuals ordered by part-of, and Chierchia adopts the generalization:
`iota X` is the largest member of `X`. No atom is larger than another, so on a set of atoms it is
defined only when there is exactly one, and it agrees with Russell's ι. Its partial inverse sends
an individual to its parts, `Set.Iic d`.

## Main definitions

* `Reference.russellIota`: the unique satisfier of a predicate, or `none`.
* `Reference.THE`, `Reference.lower`: Partee's partial shifts.
* `Reference.iota`: the largest member of a set, or `none`.

## Main results

* `russellIota_eq_some_iff`, `russellIota_isSome_iff`, `russellIota_eq_none_iff`.
* `existsUnique_iff_nonempty_subsingleton`: `∃!` is nonemptiness with subsingletonness.
* `the_sem_iff_russellIota`, `the_sem_iff_THE`: the determiner, entity and quantifier meanings
  of the definite article agree.
* `iota_eq_russellIota`: on an antichain the two iotas agree, Chierchia's (11c).
* `iota_elim_Iic`, `elim_Iic_iota`: ι and its inverse undo each other, Chierchia's (17a) and
  (17b) at a single situation.

## Implementation notes

A partial individual is an `Option`. A kind in Chierchia's sense is a function `S → Option E`
from situations to partial individuals: his ∩ is `fun s ↦ iota (P s)` and his ∪ is
`fun s ↦ (k s).elim ∅ Set.Iic`, the pair ι and Id of his (25) applied at each situation
(pp. 359–360). Krifka, following Link, writes σ for `iota`. Chierchia's (25e) prints
Id(x) = λx[x ≤ y]; his footnote 14 shows that λy[y ≤ x] is meant.

## References

* [russell-1905]
* [coppock-beaver-2015]
* [partee-1987]
* [sharvy-1980]
* [chierchia-1998]
* [link-1983]
* [krifka-2026]
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

/-- `russellIota P` is the unique satisfier of `P`, or `none` when `P` has no satisfier or
several. -/
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

/-- `THE P` is the presuppositional definite article, the Montague lift of the unique `P`. -/
noncomputable def THE : Option (NP E) := (russellIota P).map individual

/-- `lower Q` is the entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
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
theorem the_sem_iff_russellIota : the P S ↔ ∃ x ∈ russellIota P, S x :=
  exists_congr fun x ↦ and_congr_left' <|
    (⟨fun h ↦ ⟨(h x).2 rfl, fun y ↦ (h y).1⟩, fun ⟨hx, hu⟩ y ↦ ⟨hu y, fun e ↦ e ▸ hx⟩⟩ :
      (∀ y, P y ↔ y = x) ↔ P x ∧ ∀ y, P y → y = x).trans (russellIota_eq_some_iff P).symm

/-- The determiner *the* is the quantifier `THE` applied to its scope. -/
theorem the_sem_iff_THE : the P S ↔ ∃ Q ∈ THE P, Q S :=
  (the_sem_iff_russellIota P S).trans
    ⟨fun ⟨x, hx, hS⟩ ↦ ⟨individual x, Option.map_eq_some_iff.2 ⟨x, hx, rfl⟩, hS⟩,
      fun ⟨_, hQ, hS⟩ ↦
        let ⟨x, hx, hxQ⟩ := Option.map_eq_some_iff.1 hQ; ⟨x, hx, (hxQ ▸ hS : individual x S)⟩⟩

end Partee

/-! ### The iota of a partial order -/

section Order

variable [PartialOrder E] {X : Set E} {d : E}

/-- `iota X` is the largest member of `X`, or `none` when `X` has no largest member. -/
noncomputable def iota (X : Set E) : Option E :=
  letI := Classical.dec (∃ d, IsGreatest X d)
  if h : ∃ d, IsGreatest X d then some h.choose else none

theorem iota_eq_some_iff : iota X = some d ↔ IsGreatest X d := by
  classical
  unfold iota
  split_ifs with h
  · exact ⟨fun e ↦ Option.some_inj.1 e ▸ h.choose_spec,
      fun hd ↦ congrArg some (h.choose_spec.unique hd)⟩
  · exact ⟨(nomatch ·), fun hd ↦ (h ⟨d, hd⟩).elim⟩

theorem iota_isSome_iff : (iota X).isSome ↔ ∃ d, IsGreatest X d := by
  classical
  unfold iota
  split_ifs with h <;> simp [h]

theorem iota_eq_none_iff : iota X = none ↔ ¬ ∃ d, IsGreatest X d := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

theorem iota_Iic : iota (Set.Iic d) = some d :=
  iota_eq_some_iff.2 isGreatest_Iic

theorem iota_empty : iota (∅ : Set E) = none :=
  iota_eq_none_iff.2 fun ⟨_, h, _⟩ ↦ h

/-- The largest part of a partial individual is that individual. -/
theorem iota_elim_Iic (o : Option E) : iota (o.elim ∅ Set.Iic) = o := by
  cases o
  exacts [iota_empty, iota_Iic]

/-- If `X` is closed downward and has a largest member wherever it is nonempty, then `X` is the
set of parts of its largest member. -/
theorem elim_Iic_iota (hX : IsLowerSet X) (hd : X.Nonempty → ∃ d, IsGreatest X d) :
    (iota X).elim ∅ Set.Iic = X := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · rw [iota_empty]
    rfl
  · obtain ⟨d, hd⟩ := hd hne
    rw [iota_eq_some_iff.2 hd]
    exact Set.Subset.antisymm (fun _ hx ↦ hX hx hd.1) fun _ hx ↦ hd.2 hx

/-- On an antichain, such as a set of atoms, the largest member is the unique member. -/
theorem iota_eq_russellIota {Q : E → Prop} (h : IsAntichain (· ≤ ·) {x | Q x}) :
    iota {x | Q x} = russellIota Q :=
  Option.ext fun e ↦ by
    rw [iota_eq_some_iff, russellIota_eq_some_iff]
    exact ⟨fun he ↦ ⟨he.1, fun x hx ↦ h.eq hx he.1 (he.2 hx)⟩,
      fun he ↦ ⟨he.1, fun x hx ↦ (he.2 x hx).le⟩⟩

end Order

end Reference
