module

public import Linglib.Logic.Truthmaker.Bilateral

/-!
# Exclusion

This file defines exclusion between states and what it determines in unilateral truthmaker
semantics. Given an exclusion relation, two states conflict when a part of one excludes a part of
the other, and a state is possible when it does not conflict with itself. Plebani, Rosella and
Saitta, and independently Champollion and Bernard, derive possibility in this way, while Fine
takes the possible states as given. Fine constrains exclusion by three conditions and negates a
proposition `P` by fusing states that together exclude its verifiers. This gives the exclusive
negation `−P`, and its regular closure, the exclusionary negation `∼P`.

## Main definitions

* `Truthmaker.Conflict excl s t`: some part of `s` excludes some part of `t`.
* `Truthmaker.possible excl`: the states that do not conflict with themselves.
* `Truthmaker.PossibleFusion excl`: two possible states that do not conflict have a possible
  fusion.
* `Truthmaker.UpwardExclusion`, `Truthmaker.DownwardExclusion`, `Truthmaker.NullExclusion`:
  Fine's conditions on exclusion.
* `Truthmaker.Excludes excl Q P`: every verifier of `Q` excludes a verifier of `P`, and every
  verifier of `P` is excluded by a verifier of `Q`.
* `Truthmaker.exclusiveNeg`, `Truthmaker.exclusionaryNeg`: Fine's negations `−P` and `∼P`.
* `Truthmaker.ClassicalExclusion excl P`: Fine's classical exclusion over the possible states `P`.

## Main results

* `Truthmaker.isConjunctivePart_iff_excludes`: containment is exclusion with parthood in place of
  exclusion.
* `Truthmaker.mem_possible_iff_forall`: a state is possible exactly when no two of its parts
  conflict.
* `Truthmaker.exclusionaryNeg_singleton`: the negation of a single state is the regular closure of
  its excluders.
* `Truthmaker.exclusionaryNeg_sups_singleton`: under Upward and Downward Exclusion, the negation
  of a conjunction of single states is the disjunction of their negations.
* `Truthmaker.ClassicalExclusion.exclusive`, `Truthmaker.ClassicalExclusion.exhaustive`: under
  classical exclusion a single state paired with its negation is exclusive and exhaustive.
* `Truthmaker.Canonical.possible_excl`: in the canonical space, where a literal excludes its mirror
  image, the derived possibility is Fine's consistency.
* `Truthmaker.RedBlueGreen.exclusionaryNeg_exclusionaryNeg_ne`: double negation can fail.

## Implementation notes

Fine's published Downward Exclusion condition omits the regular closure of the excluders, which
Champollion and Bernard report as a typo. It is stated here with the closure.

## TODO

Fine's de Morgan laws for the exclusionary negation of regular propositions, and his reduction of
double negation to single states. The latter needs conjunctions of arbitrary families.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [M. Plebani, G. Rosella and V. Saitta, *Truthmakers, Incompatibility, and Modality*
  (2022)][plebani-rosella-saitta-2022]
* [L. Champollion and T. Bernard, *Negation and modality in unilateral truthmaker semantics*
  (2024)][champollion-bernard-2024]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

variable {S : Type*}

/-- A proposition `Q` excludes `P` when every verifier of `Q` excludes a verifier of `P` and every
verifier of `P` is excluded by a verifier of `Q`. -/
def Excludes (excl : S → S → Prop) (Q P : Set S) : Prop :=
  Q ⊆ {q | ∃ p ∈ P, excl q p} ∧ P ⊆ {p | ∃ q ∈ Q, excl q p}

/-! ### Conflict and possibility -/

section Preorder

variable [Preorder S] {excl : S → S → Prop} {s t : S}

/-- A proposition `s` contains `t` exactly when `s` excludes `t` in the sense of `Excludes`, with
containment of states in place of exclusion. -/
theorem isConjunctivePart_iff_excludes {s t : Set S} :
    IsConjunctivePart t s ↔ Excludes (· ≥ ·) s t :=
  Iff.rfl

variable (excl) in
/-- Two states conflict when some part of the first excludes some part of the second. -/
def Conflict (s t : S) : Prop :=
  ∃ s' ≤ s, ∃ t' ≤ t, excl s' t'

theorem Conflict.of_excl (h : excl s t) : Conflict excl s t :=
  ⟨s, le_rfl, t, le_rfl, h⟩

theorem Conflict.mono {s' t' : S} (h : Conflict excl s t) (hs : s ≤ s') (ht : t ≤ t') :
    Conflict excl s' t' :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨a, ha.trans hs, b, hb.trans ht, hx⟩

theorem Conflict.symm [Std.Symm excl] (h : Conflict excl s t) : Conflict excl t s :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨b, hb, a, ha, Std.Symm.symm _ _ hx⟩

variable (excl) in
/-- A state is possible when it does not conflict with itself, and every part of a possible state
is possible. -/
def possible : LowerSet S where
  carrier := {s | ¬ Conflict excl s s}
  lower' := by
    intro s t hts hs hc
    exact hs (hc.mono hts hts)

theorem mem_possible : s ∈ possible excl ↔ ¬ Conflict excl s s :=
  Iff.rfl

/-- A state is possible exactly when no two of its parts conflict. -/
theorem mem_possible_iff_forall : s ∈ possible excl ↔ ∀ t ≤ s, ∀ u ≤ s, ¬ Conflict excl t u :=
  ⟨fun hs _ ht _ hu hc ↦ hs (hc.mono ht hu), fun h ↦ h s le_rfl s le_rfl⟩

variable (excl) in
/-- Upward Exclusion holds when a state that excludes `p` excludes every state containing `p`. -/
def UpwardExclusion : Prop :=
  ∀ ⦃q p p' : S⦄, excl q p → p ≤ p' → excl q p'

/-- Under Upward Exclusion, a state conflicts with `t` exactly when some part of it excludes
`t`. -/
theorem UpwardExclusion.conflict_iff (hU : UpwardExclusion excl) :
    Conflict excl s t ↔ ∃ s' ≤ s, excl s' t :=
  ⟨fun ⟨a, ha, _, hb, hx⟩ ↦ ⟨a, ha, hU hx hb⟩, fun ⟨a, ha, hx⟩ ↦ ⟨a, ha, t, le_rfl, hx⟩⟩

end Preorder

section SemilatticeSup

variable [SemilatticeSup S] {excl : S → S → Prop} {s t : S}

/-- Two states one of which excludes the other have an impossible fusion. -/
theorem sup_not_mem_possible (h : excl s t) : s ⊔ t ∉ possible excl :=
  fun hp ↦ hp ((Conflict.of_excl h).mono le_sup_left le_sup_right)

/-- Two states with a possible fusion do not conflict. -/
theorem not_conflict_of_sup_mem_possible (h : s ⊔ t ∈ possible excl) : ¬ Conflict excl s t :=
  fun hc ↦ h (hc.mono le_sup_left le_sup_right)

variable (excl) in
/-- Possible Fusion holds when two possible states that do not conflict have a possible
fusion. -/
def PossibleFusion : Prop :=
  ∀ ⦃s : S⦄, s ∈ possible excl → ∀ ⦃t : S⦄, t ∈ possible excl → ¬ Conflict excl s t →
    s ⊔ t ∈ possible excl

/-- Possible Fusion holds exactly when two possible states have a possible fusion just when they
do not conflict. -/
theorem possibleFusion_iff : PossibleFusion excl ↔
    ∀ s ∈ possible excl, ∀ t ∈ possible excl, (s ⊔ t ∈ possible excl ↔ ¬ Conflict excl s t) :=
  ⟨fun h _ hs _ ht ↦ ⟨not_conflict_of_sup_mem_possible, fun hc ↦ h hs ht hc⟩,
    fun h _ hs _ ht ↦ (h _ hs _ ht).2⟩

end SemilatticeSup

/-! ### Fine's exclusion conditions and negations -/

section CompleteLattice

variable [CompleteLattice S] {excl : S → S → Prop} {P : Set S}

variable (excl) in
/-- Downward Exclusion holds when every state that excludes the fusion of `P` lies in the regular
closure of the excluders of members of `P`. -/
def DownwardExclusion : Prop :=
  ∀ ⦃P : Set S⦄ ⦃q : S⦄, excl q (sSup P) → q ∈ regularClosure {r | ∃ p ∈ P, excl r p}

variable (excl) in
/-- Null Exclusion holds when the null state neither excludes nor is excluded, and every other
state excludes some state and is excluded by some state. -/
def NullExclusion : Prop :=
  (∀ s : S, ¬ excl ⊥ s ∧ ¬ excl s ⊥) ∧ ∀ s : S, s ≠ ⊥ → (∃ t, excl s t) ∧ ∃ t, excl t s

variable (excl) in
/-- The exclusive negation of `P` is verified by the fusions of propositions that exclude `P`. -/
def exclusiveNeg (P : Set S) : Set S :=
  {q | ∃ Q, Excludes excl Q P ∧ sSup Q = q}

variable (excl) in
/-- The exclusionary negation of `P` is the regular closure of its exclusive negation. -/
def exclusionaryNeg (P : Set S) : Set S :=
  regularClosure (exclusiveNeg excl P)

/-- The exclusionary negation of a single state is the regular closure of its excluders. -/
theorem exclusionaryNeg_singleton (p : S) :
    exclusionaryNeg excl {p} = regularClosure {q | excl q p} := by
  refine le_antisymm (regularClosure.le_closure_iff.1 ?_) (regularClosure.monotone ?_)
  · rintro _ ⟨Q, ⟨hQ, hpQ⟩, rfl⟩
    obtain ⟨q, hq, hqp⟩ := hpQ (Set.mem_singleton p)
    have hQE : Q ⊆ {q | excl q p} := fun r hr ↦ by
      obtain ⟨_, hp', h⟩ := hQ hr
      rwa [Set.mem_singleton_iff.1 hp'] at h
    exact ⟨mem_upperClosure.2 ⟨q, hqp, le_sSup hq⟩, sSup_le_sSup hQE⟩
  · intro q hq
    refine ⟨{q}, ⟨fun r hr ↦ ⟨p, rfl, Set.mem_singleton_iff.1 hr ▸ hq⟩, fun p' hp' ↦
      ⟨q, rfl, Set.mem_singleton_iff.1 hp' ▸ hq⟩⟩, sSup_singleton⟩

/-- Under Upward and Downward Exclusion, the exclusionary negation of the conjunction of two single
states is the disjunction of their exclusionary negations. -/
theorem exclusionaryNeg_sups_singleton (hU : UpwardExclusion excl) (hD : DownwardExclusion excl)
    (p q : S) : exclusionaryNeg excl ({p} ⊻ {q}) =
      regularClosure (exclusionaryNeg excl {p} ∪ exclusionaryNeg excl {q}) := by
  rw [Set.singleton_sups_singleton, exclusionaryNeg_singleton, exclusionaryNeg_singleton,
    exclusionaryNeg_singleton]
  refine le_antisymm (regularClosure.le_closure_iff.1 fun r hr ↦ ?_)
    (regularClosure.le_closure_iff.1 (Set.union_subset
      (regularClosure.monotone fun _ h ↦ hU h le_sup_left)
      (regularClosure.monotone fun _ h ↦ hU h le_sup_right)))
  have hr' := hD (P := {p, q}) (q := r) (by rwa [sSup_pair])
  refine regularClosure.monotone ?_ hr'
  rintro x ⟨_, rfl | rfl, hx⟩
  · exact .inl (regularClosure.le_closure _ hx)
  · exact .inr (regularClosure.le_closure _ hx)

/-- Under Null Exclusion, a proposition that the null state does not verify has a negation with a
verifier. -/
theorem exclusionaryNeg_nonempty (hN : NullExclusion excl) (hP : ⊥ ∉ P) :
    (exclusionaryNeg excl P).Nonempty := by
  have : ∀ p ∈ P, ∃ q, excl q p := fun p hp ↦ (hN.2 p (ne_of_mem_of_not_mem hp hP)).2
  choose! f hf using this
  refine ⟨sSup (f '' P), regularClosure.le_closure _ ⟨f '' P, ⟨?_, fun p hp ↦
    ⟨f p, Set.mem_image_of_mem f hp, hf p hp⟩⟩, rfl⟩⟩
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hp, hf p hp⟩

/-- Under Null Exclusion, the null state does not verify the negation of a proposition with a
verifier. -/
theorem bot_not_mem_exclusionaryNeg (hN : NullExclusion excl) (hP : P.Nonempty) :
    ⊥ ∉ exclusionaryNeg excl P := by
  rintro ⟨h₁, -⟩
  obtain ⟨_, ⟨Q, ⟨-, hPQ⟩, rfl⟩, hle⟩ := mem_upperClosure.1 h₁
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq, hqp⟩ := hPQ hp
  obtain rfl : q = ⊥ := le_bot_iff.1 ((le_sSup hq).trans hle)
  exact (hN.1 p).1 hqp

/-! ### Classical exclusion -/

variable (excl) in
/-- An exclusion relation is classical over the possible states `P` when a state is incompatible
with the states it excludes, two incompatible possible states have a part of the first that
excludes the second, and every possible state is compatible with an excluder of each impossible
state. -/
structure ClassicalExclusion (P : LowerSet S) : Prop where
  /-- A state and a state it excludes have an impossible fusion. -/
  sup_not_mem : ∀ ⦃s t : S⦄, excl s t → s ⊔ t ∉ P
  /-- Two possible states with an impossible fusion have a part of the first that excludes the
  second. -/
  exists_le_excl : ∀ ⦃s t : S⦄, s ∈ P → t ∈ P → s ⊔ t ∉ P → ∃ s' ≤ s, excl s' t
  /-- Every possible state has a possible fusion with some excluder of each impossible state. -/
  exists_excl : ∀ ⦃t : S⦄, t ∉ P → ∀ s ∈ P, ∃ t', excl t' t ∧ s ⊔ t' ∈ P

variable {P : LowerSet S}

/-- Under classical exclusion, a single state paired with its exclusionary negation is
exclusive. -/
theorem ClassicalExclusion.exclusive (h : ClassicalExclusion excl P) (p : S) :
    (BilProp.mk {p} (exclusionaryNeg excl {p})).Exclusive P := by
  intro s hs t ht hpt
  rw [Set.mem_singleton_iff.1 hs] at hpt
  replace ht : t ∈ exclusionaryNeg excl {p} := ht
  rw [exclusionaryNeg_singleton] at ht
  obtain ⟨e, he, het⟩ := mem_upperClosure.1 ht.1
  exact h.sup_not_mem he (P.lower ((sup_le_sup_right het p).trans (sup_comm t p).le) hpt)

/-- Under classical exclusion, a single state paired with its exclusionary negation is
exhaustive. -/
theorem ClassicalExclusion.exhaustive (h : ClassicalExclusion excl P) (p : S) :
    (BilProp.mk {p} (exclusionaryNeg excl {p})).Exhaustive P := by
  intro s hs
  by_cases hsp : s ⊔ p ∈ P
  · exact .inl ⟨p, rfl, hsp⟩
  refine .inr ?_
  change ∃ t ∈ exclusionaryNeg excl {p}, s ⊔ t ∈ P
  rw [exclusionaryNeg_singleton]
  by_cases hp : p ∈ P
  · obtain ⟨s', hs's, hx⟩ := h.exists_le_excl hs hp hsp
    exact ⟨s', regularClosure.le_closure _ hx, by rwa [sup_eq_left.2 hs's]⟩
  · obtain ⟨t', hx, hst'⟩ := h.exists_excl hp s hs
    exact ⟨t', regularClosure.le_closure _ hx, hst'⟩

end CompleteLattice

/-! ### The canonical space -/

namespace Canonical

variable {α : Type*}

/-- In the canonical space a literal excludes its mirror image and nothing else holds. -/
def excl (s t : Set (α × Bool)) : Prop :=
  ∃ x, s = {x} ∧ t = {mirror x}

instance : Std.Symm (excl (α := α)) :=
  ⟨fun _ _ ⟨x, hs, ht⟩ ↦ ⟨mirror x, ht, by rw [hs, mirror_mirror]⟩⟩

theorem conflict_excl_iff {s t : Set (α × Bool)} :
    Conflict excl s t ↔ ∃ x ∈ s, mirror x ∈ t := by
  constructor
  · rintro ⟨_, h₁, _, h₂, x, rfl, rfl⟩
    exact ⟨x, h₁ rfl, h₂ rfl⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨{x}, Set.singleton_subset_iff.2 hx₁, _, Set.singleton_subset_iff.2 hx₂, x, rfl, rfl⟩

/-- The states possible under canonical exclusion are the consistent sets of literals. -/
theorem possible_excl : Truthmaker.possible (excl (α := α)) = possible :=
  SetLike.ext fun _ ↦ by
    simp [Truthmaker.mem_possible, conflict_excl_iff, Canonical.mem_possible]

theorem possibleFusion_excl : PossibleFusion (excl (α := α)) := by
  intro s hs t ht hc
  rw [possible_excl] at hs ht ⊢
  rw [conflict_excl_iff] at hc
  rintro x (hx | hx) (hx' | hx')
  · exact hs x hx hx'
  · exact hc ⟨x, hx, hx'⟩
  · exact hc ⟨mirror x, hx', by rwa [mirror_mirror]⟩
  · exact ht x hx hx'

end Canonical

/-! ### Red, blue and green -/

namespace RedBlueGreen

/-- In Fine's example of three colours, red `0`, blue `1` and green `2`, a single colour excludes
every state containing another colour. -/
def excl (s t : Set (Fin 3)) : Prop :=
  ∃ i, s = {i} ∧ ∃ j ∈ t, j ≠ i

/-- The exclusionary negation of the exclusionary negation of red is not red. -/
theorem exclusionaryNeg_exclusionaryNeg_ne :
    exclusionaryNeg excl (exclusionaryNeg excl {{0}}) ≠ {{0}} := by
  have hblue : ({1} : Set (Fin 3)) ∈ exclusionaryNeg excl {{0}} := by
    rw [exclusionaryNeg_singleton]
    exact regularClosure.le_closure _ ⟨1, rfl, 0, rfl, by decide⟩
  have hmem : sSup ({{0}, {2}} : Set (Set (Fin 3))) ∈
      exclusionaryNeg excl (exclusionaryNeg excl {{0}}) := by
    refine regularClosure.le_closure _ ⟨_, ⟨?_, fun x hx ↦ ?_⟩, rfl⟩
    · rintro _ (rfl | rfl)
      · exact ⟨{1}, hblue, 0, rfl, 1, rfl, by decide⟩
      · exact ⟨{1}, hblue, 2, rfl, 1, rfl, by decide⟩
    · rw [exclusionaryNeg_singleton] at hx
      obtain ⟨_, ⟨i, rfl, j, hj, hji⟩, hix⟩ := mem_upperClosure.1 hx.1
      obtain rfl : j = 0 := hj
      exact ⟨{0}, .inl rfl, 0, rfl, i, hix rfl, fun h ↦ hji h.symm⟩
  intro h
  rw [h, Set.mem_singleton_iff, sSup_pair] at hmem
  have : (2 : Fin 3) ∈ ({0} ⊔ {2} : Set (Fin 3)) := Or.inr rfl
  rw [hmem] at this
  exact absurd this (by decide)

end RedBlueGreen

end Truthmaker
