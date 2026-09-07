import Mathlib.Data.Sigma.Order
import Linglib.Semantics.Degree.Hom
import Linglib.Semantics.Conditionals.SelectionFunction
import Linglib.Data.Examples.Cresswell1976

/-!
# The semantics of degree

Cresswell's degrees of comparison are pairs of a point and the ordering of the scale it lies
on, and the comparative *er than* relates two properties of degrees: it holds when both are
instantiated and every degree of the first exceeds every degree of the second on their common
scale. Degrees on distinct scales never stand in the ordering, so a comparative whose terms
measure on different scales, *taller man than … clever man*, *taller than … beautiful*, or
*longer* of a meeting and a road, is semantically anomalous without any syntactic feature, and
since a degree carries its ordering, *six feet*, which names a degree on the upward scale, lies
outside the domain of *short*, which takes degrees read downward. A disjoined standard is
compared universally, so *taller than Arabella or Clarissa* means taller than both, and the
equative *as as* is the weak comparison that *exactly* strengthens to identity.

Mass nouns and plurals carry degrees of the same kind. The totality operator picks the greatest
degree among the parts satisfying a predicate, so *more water ebbs than mud flows* compares two
volumes, and pluralization turns a count noun into a predicate of sets carrying their
cardinality, so *more men walk than birds fly* compares two numbers and *all men walk* comes
out synonymous with *every man walks* although *all* applies to the pluralized noun, as it
does to a mass noun, and *every* to the count noun. Degrees need no units: any comparison
relation yields a scale by quotienting its field by indistinguishability, and since the things
compared are things at worlds, the counterfactual *if Bill had been a smoker he would be
shorter than he is* compares his height at the nearest world where he smokes with his actual
height.

We take the degrees on a family of scales to be mathlib's disjoint sum of the scales' orders
and prove from it the same-scale restriction and the anomaly of the paper's starred
comparatives, the universal reading of disjoined standards, the reduction of the totality
comparatives to comparisons of volumes and of cardinalities, the synonymy of *all* and *every*
given that the noun is instantiated, the comparative on constructed degrees, and the reading
of the counterfactual through a Stalnaker selection function, on which it is false whenever
Bill is in fact a smoker.

## Implementation notes

* A degree property is a set of degrees, and the comparative, the equative and the totality
  operator are stated on sets over any ordered type; the scale-tagged degrees of (2.1) are the
  case of a sigma type with mathlib's fiberwise order, where the same-scale requirement of
  (2.3) is that the order never relates distinct fibers. The downward reading of *short*
  ((39), (72)) is the order dual of the spatial scale, on which the comparative is the
  substrate's negative-polarity comparative. The paper places the bare degree *six feet* as
  the second term of *er than* ((35), (36)); here that term is the singleton of the degree.
  The uniqueness of a totality's degree uses antisymmetry of the scale, which the paper
  declines to require of the ordering of a degree (§2).
* The plural (3.6) is read as in (49): a nonempty set of things satisfying the noun together
  with its cardinality, a positive integer as the paper has the scale. As printed, (3.6) fixes
  the set to all of them, on which (54) would require the set of all men to walk; the (49)
  reading gives (55). Predicates of sets are taken distributive where the paper compares
  numbers. Since the plural's degrees are positive, *all* carries existential import, and the
  synonymy of (56) and (57) holds given that there are men.
* The positive form (2.5), *much* and *deg* (3.3), the syntax of §5, and the differential and
  factor comparatives through a natural metric (the end of §4, §6) are not formalized.

## TODO

* (50), *Arabella is more beautiful than Tom is clever*, is listed without an asterisk as an
  instance of *more* with an adjective, although it compares distinct scales like the starred
  (65); the paper's as-if order-preserving mapping between scales ((66)) is not formalized.

## References

* [M. J. Cresswell, *The semantics of degree* (1976)][cresswell-1976]
* [R. C. Stalnaker, *A theory of conditionals* (1968)][stalnaker-1968]
-/

namespace Cresswell1976

open Degree OrderDual

/-! ### Comparison of degree properties (2.3), (2.7) -/

section Comparative

variable {D : Type*} [LT D] {ω ω' ω₁ ω₂ : Set D} {a b : D}

/-- *er than* on two properties of degrees: both are instantiated and every degree of the
first exceeds every degree of the second (2.3). -/
def ErThan (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', b < a

/-- *as as*: every degree of the first exceeds or equals every degree of the second (2.7). -/
def AsAs (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', b < a ∨ b = a

/-- *exactly as as*: the degrees coincide (2.7). -/
def Exactly (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', a = b

theorem ErThan.asAs (h : ErThan ω ω') : AsAs ω ω' :=
  ⟨h.1, h.2.1, λ a ha b hb => .inl (h.2.2 a ha b hb)⟩

theorem Exactly.asAs (h : Exactly ω ω') : AsAs ω ω' :=
  ⟨h.1, h.2.1, λ a ha b hb => .inr (h.2.2 a ha b hb).symm⟩

/-- A phrasal comparative compares its two degrees ((13), (18)). -/
@[simp] theorem erThan_singleton : ErThan {a} {b} ↔ b < a := by simp [ErThan]

theorem erThan_singleton_toDual : ErThan {toDual a} {toDual b} ↔ a < b :=
  erThan_singleton.trans toDual_lt_toDual

@[simp] theorem asAs_singleton : AsAs {a} {b} ↔ b < a ∨ b = a := by simp [AsAs]

omit [LT D] in
@[simp] theorem exactly_singleton : Exactly {a} {b} ↔ a = b := by simp [Exactly]

/-- A disjoined standard is compared universally: *taller than Arabella or Clarissa* is taller
than both (footnote 10). -/
theorem erThan_union (h₁ : ω₁.Nonempty) (h₂ : ω₂.Nonempty) :
    ErThan ω (ω₁ ∪ ω₂) ↔ ErThan ω ω₁ ∧ ErThan ω ω₂ :=
  ⟨λ ⟨h, _, hlt⟩ => ⟨⟨h, h₁, λ a ha b hb => hlt a ha b (.inl hb)⟩,
    ⟨h, h₂, λ a ha b hb => hlt a ha b (.inr hb)⟩⟩,
   λ ⟨⟨h, _, hlt₁⟩, ⟨_, _, hlt₂⟩⟩ =>
    ⟨h, h₁.inl, λ a ha b hb => hb.elim (hlt₁ a ha b) (hlt₂ a ha b)⟩⟩

/-- Reading a scale downward reverses the comparison: *shorter than* is *taller than* with the
terms exchanged ((39), (72)). -/
theorem erThan_image_toDual : ErThan (toDual '' ω) (toDual '' ω') ↔ ErThan ω' ω := by
  simp only [ErThan, Set.image_nonempty, Set.forall_mem_image, toDual_lt_toDual, and_left_comm]
  exact and_congr_right λ _ => and_congr_right λ _ => forall₂_comm

end Comparative

section Substrate

variable {E α : Type*} {μ : E → α} {x y : E}

/-- On one scale the phrasal comparative is the substrate's comparative. -/
theorem erThan_singleton_iff_comparativeSem [Preorder α] :
    ErThan {μ x} {μ y} ↔ comparativeSem μ x y .positive :=
  erThan_singleton

/-- On a scale read downward it is the substrate's negative-polarity comparative. -/
theorem erThan_singleton_toDual_iff_comparativeSem [Preorder α] :
    ErThan {toDual (μ x)} {toDual (μ y)} ↔ comparativeSem μ x y .negative :=
  erThan_singleton_toDual

/-- The equative is the substrate's weak equative (2.7). -/
theorem asAs_singleton_iff_equativeSem [PartialOrder α] :
    AsAs {μ x} {μ y} ↔ equativeSem μ x y .positive :=
  asAs_singleton.trans le_iff_lt_or_eq.symm

/-- *Exactly* is the substrate's strengthened equative (2.7). -/
theorem exactly_singleton_iff_equativeStrengthened [Preorder α] :
    Exactly {μ x} {μ y} ↔ equativeStrengthened μ x y :=
  exactly_singleton

end Substrate

/-! ### Degrees on a family of scales (2.1) -/

section Scales

variable {ι : Type*} {P : ι → Type*} [∀ i, LT (P i)] {ω ω' : Set (Σ i, P i)}

/-- Compared degrees lie on one scale (2.3). -/
theorem ErThan.fst_eq (h : ErThan ω ω') {a b : Σ i, P i} (ha : a ∈ ω) (hb : b ∈ ω') :
    a.1 = b.1 :=
  (Sigma.lt_def.1 (h.2.2 a ha b hb)).1.symm

/-- Degree properties on distinct scales are never compared: the anomaly of (23), (65) and
(69). -/
theorem not_erThan_of_fst_ne (h : ∀ a ∈ ω, ∀ b ∈ ω', a.1 ≠ b.1) : ¬ ErThan ω ω' :=
  λ he => let ⟨a, ha⟩ := he.1; let ⟨b, hb⟩ := he.2.1; h a ha b hb (he.fst_eq ha hb)

/-- On one scale the comparative is the scale's. -/
theorem erThan_image_sigmaMk {i : ι} {ω ω' : Set (P i)} :
    ErThan (Sigma.mk i '' ω) (Sigma.mk i '' ω') ↔ ErThan ω ω' := by
  simp only [ErThan, Set.image_nonempty, Set.forall_mem_image, Sigma.mk_lt_mk_iff]

end Scales

/-! ### The scales of the paper's comparatives -/

/-- The scales the examples compare on: spatial and temporal distances, volumes, the numbers
of (3.6), and the unit-free scales of §4. -/
inductive Scale where
  | distance
  | time
  | volume
  | number
  | cleverness
  | beauty
  deriving DecidableEq

/-- A scale read upward or, for *short*, downward: the relation of a degree (2.1). -/
abbrev DirectedScale := Scale × ScalePolarity

/-- The scale a `paperFeatures` label names. -/
def DirectedScale.ofLabel : String → Option DirectedScale
  | "distance" => some (.distance, .positive)
  | "distanceDownward" => some (.distance, .negative)
  | "time" => some (.time, .positive)
  | "volume" => some (.volume, .positive)
  | "number" => some (.number, .positive)
  | "cleverness" => some (.cleverness, .positive)
  | "beauty" => some (.beauty, .positive)
  | _ => none

/-- The scales of an example's two terms and its judgment. -/
def datum (e : Data.Examples.LinguisticExample) :
    Option (DirectedScale × DirectedScale × Features.Judgment) := do
  let l ← DirectedScale.ofLabel (← e.feature? "leftScale")
  let r ← DirectedScale.ofLabel (← e.feature? "rightScale")
  pure (l, r, e.judgment)

/-- The comparatives whose scales the paper records. -/
def data : List (DirectedScale × DirectedScale × Features.Judgment) :=
  Examples.all.filterMap datum

/-- The starred comparatives compare distinct scales. -/
theorem scale_ne_of_unacceptable : ∀ d ∈ data, d.2.2 = .unacceptable → d.1 ≠ d.2.1 := by
  decide

/-- Every starred comparative is unsatisfiable, whatever the points of its scales. -/
theorem not_erThan_of_unacceptable {P : DirectedScale → Type*} [∀ s, LT (P s)] {d}
    (hd : d ∈ data) (hj : d.2.2 = .unacceptable) {ω ω' : Set (Σ s, P s)}
    (hω : ∀ a ∈ ω, a.1 = d.1) (hω' : ∀ b ∈ ω', b.1 = d.2.1) : ¬ ErThan ω ω' :=
  not_erThan_of_fst_ne λ a ha b hb => by
    rw [hω a ha, hω' b hb]; exact scale_ne_of_unacceptable d hd hj

/-! ### Superlatives, mass nouns and plurals ((2.6), §3) -/

section Totality

variable {E D : Type*} [LE D] (ω : E → D → Prop) (ω' : E → Prop)

/-- *tot*: the degree of the greatest part of whatever satisfies both predicates (3.2). -/
def tot : Set D := {u | IsGreatest {d | ∃ c, ω' c ∧ ω c d} u}

/-- *est*: `a` bears a unique degree at or above every degree of anything (2.6). -/
def Est (a : E) : Prop := ∃! b, ω a b ∧ b ∈ upperBounds {d | ∃ c, ω c d}

/-- The superlative of a measure holds of a greatest value, ties allowed as in (2.6): *tallest
spy* (27). -/
theorem est_iff (μ : E → D) (a : E) : Est (λ c d => μ c = d) a ↔ ∀ c, μ c ≤ μ a := by
  simp [Est, upperBounds, ExistsUnique]

end Totality

section TotalityOrder

variable {E D : Type*} [PartialOrder D] {ω : E → D → Prop} {ω' : E → Prop}

theorem tot_eq_singleton {u : D} (h : IsGreatest {d | ∃ c, ω' c ∧ ω c d} u) : tot ω ω' = {u} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h, λ _ h' => h'.unique h⟩

/-- The comparative of two totalities compares their greatest degrees: *more water ebbs than
mud flows* compares two volumes ((42), (44)). -/
theorem erThan_tot_tot {E' : Type*} {ω₁ : E' → D → Prop} {ω₁' : E' → Prop} {u u₁ : D}
    (h : IsGreatest {d | ∃ c, ω' c ∧ ω c d} u) (h₁ : IsGreatest {d | ∃ c, ω₁' c ∧ ω₁ c d} u₁) :
    ErThan (tot ω ω') (tot ω₁ ω₁') ↔ u₁ < u := by
  rw [tot_eq_singleton h, tot_eq_singleton h₁, erThan_singleton]

end TotalityOrder

section Plural

variable {E : Type*} (noun : Finset E) (pred : E → Prop)

/-- *pl*: a nonempty set of things satisfying the noun, with its cardinality, a positive
integer, as degree ((3.6), (49)). -/
def Pl (a : Finset E) (n : ℕ) : Prop := a ⊆ noun ∧ a.Nonempty ∧ a.card = n

/-- *all*: something satisfies the plural, and everything that does satisfies the predicate
(3.7). -/
def All {A B : Type*} (ω : A → B → Prop) (ω' : A → Prop) : Prop :=
  (∃ a b, ω a b) ∧ ∀ a, (∃ b, ω a b) → ω' a

/-- The totality of the sets satisfying a distributive predicate is the number of things
satisfying it: *more men walk* counts the walking men ((54), (55)). -/
theorem tot_pl [DecidablePred pred] (h : (noun.filter pred).Nonempty) :
    tot (Pl noun) (λ a => ∀ x ∈ a, pred x) = {(noun.filter pred).card} := by
  refine tot_eq_singleton ⟨⟨noun.filter pred, λ _ hx => (Finset.mem_filter.1 hx).2,
    Finset.filter_subset _ _, h, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, hsub, -, rfl⟩
  exact Finset.card_le_card λ x hx => Finset.mem_filter.2 ⟨hsub hx, ha x hx⟩

/-- *More men walk than birds fly*: the walking men outnumber the flying birds ((52), (55)). -/
theorem erThan_tot_pl (man bird : Finset E) (walk fly : E → Prop) [DecidablePred walk]
    [DecidablePred fly] (hw : (man.filter walk).Nonempty) (hf : (bird.filter fly).Nonempty) :
    ErThan (tot (Pl man) (λ a => ∀ x ∈ a, walk x)) (tot (Pl bird) (λ a => ∀ x ∈ a, fly x)) ↔
      (bird.filter fly).card < (man.filter walk).card := by
  rw [tot_pl _ _ hw, tot_pl _ _ hf, erThan_singleton]

/-- *All men walk* and *every man walks* are synonymous given that there are men, although
*all* takes the plural and *every* (3.8) the count noun ((56), (57)). -/
theorem all_pl_iff_forall :
    All (Pl noun) (λ a => ∀ x ∈ a, pred x) ↔ noun.Nonempty ∧ ∀ x ∈ noun, pred x :=
  ⟨λ ⟨⟨_, _, hsub, hne, _⟩, h⟩ =>
    ⟨hne.mono hsub, λ x hx => h noun ⟨_, Finset.Subset.refl _, hne.mono hsub, rfl⟩ x hx⟩,
   λ ⟨hne, h⟩ => ⟨⟨noun, _, Finset.Subset.refl _, hne, rfl⟩,
    λ _ ⟨_, hsub, _, _⟩ x hx => h x (hsub hx)⟩⟩

end Plural

/-! ### Degrees from comparisons (§4) -/

/-- On the degrees a comparison relation constructs, the comparative is the relation itself:
*Arabella is more beautiful than Clarissa* ((62), (4.2)). -/
theorem erThan_singleton_mk {E : Type*} (φ : E → E → Prop) (a b : E) :
    ErThan ({⟦a⟧} : Set (CresswellDegree φ)) {⟦b⟧} ↔ φ a b :=
  erThan_singleton.trans CresswellDegree.mk_lt_mk

/-! ### Comparison across worlds ((70)–(73)) -/

section Counterfactual

variable {W D : Type*} [Preorder D] (s : Conditionals.SelectionFunction W) (height : W → D)
  (smokes : Set W) (w : W)

/-- *If Bill had been a smoker he would be shorter than he is*: his height at the nearest world
where he smokes is below his actual height ((71)). -/
theorem erThan_sel :
    ErThan {toDual (height (s.sel w smokes))} {toDual (height w)} ↔
      height (s.sel w smokes) < height w :=
  erThan_singleton_toDual

/-- A smoker would not be shorter than he is: the nearest world where he smokes is the actual
one. -/
theorem not_erThan_sel_of_mem (hw : w ∈ smokes) :
    ¬ ErThan {toDual (height (s.sel w smokes))} {toDual (height w)} := by
  rw [erThan_sel, s.centering w smokes hw]
  exact lt_irrefl _

end Counterfactual

end Cresswell1976
