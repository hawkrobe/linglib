module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.NormNum
public import Linglib.Semantics.Degree.Hom
public import Linglib.Data.Examples.Bale2008

/-!
# Bale (2008): A universal scale of comparison

A gradable adjective orders a comparison class by a quasi-order, such as *has as much beauty as*.
Its classes of equivalent members form the primary scale, and each member is sent to the
universal degree of its class: one plus the number of classes below it, over the number of
classes. The comparative compares universal degrees whatever the two scales, so one
interpretation serves indirect comparisons (*Betty is more beautiful than Heather is
intelligent*) and direct ones (*Seymour is taller than he is wide*). A comparison is direct when
the comparison class contains the measurements in inches up to a bound and everyone is as tall,
or as wide, as exactly one of them: both primary scales are then the measurement system, and
universal degrees compare as measurements do. A for-clause restricts the comparison class to
men and drops the measurements, so Seymour, short and very wide, is taller than he is wide but
not taller for a man than he is wide for a man.

## Main statements

* `universalDegree_congr`, `universalDegree_eq_iff`: a universal degree depends only on the
  quasi-order the adjective induces on the comparison class, and two members share one exactly
  when they are equivalent in Cresswell's sense.
* `direct_comparison`: with the measurements up to a common bound in the comparison class,
  comparing universal degrees is comparing measurements.
* `for_a_man`: under the same quasi-orders, Seymour is taller than he is wide but not taller for
  a man than he is wide for a man.
* `rows_truth`: the sentences the paper evaluates take the truth values it reports.

## Implementation notes

* An adjective's quasi-order is given by a measure `μ : E → D` into a linear order, and a
  comparison class by a finite set `C`, which restricts the quasi-order as Klein's comparison
  classes do. The primary scale, the quotient of the restricted quasi-order, is order-isomorphic
  to the values `C.image μ`, where the universal degree is computed.
* The comparative is Kennedy's, as in the paper: MORE applied to the greatest degree the
  than-clause reaches is `Degree.maxComparative` over the two measures (`more_iff`), stated as
  the point comparison `Comparison.gt.over`.
* Universal degrees are rationals: the paper's universal scale is the rationals from zero to one.
* Measurements are individuals `.inr n` of `n` inches, bounded by the comparison class; heights
  and widths are in inches as printed, and the committee's rankings count from the bottom.

## References

* [bale-2008]
* [cresswell-1976]
* [kennedy-1999]
* [klein-1980]
-/

@[expose] public section

namespace Bale2008

open Finset Degree

/-! ### The universal homomorphism -/

section Rank

variable {D : Type*} [LinearOrder D]

/-- The universal degree of `d` in a finite scale `S` is the share of `S` at or below it: one
plus the number of values below `d`, over the number of values. -/
def relativeRank (S : Finset D) (d : D) : ℚ := #(S.filter (· ≤ d)) / #S

/-- The universal homomorphism preserves and reflects the order of the scale. -/
theorem relativeRank_strictMonoOn (S : Finset D) : StrictMonoOn (relativeRank S) S := by
  intro a ha b hb hab
  have hS : (0 : ℚ) < #S := by exact_mod_cast card_pos.2 ⟨a, ha⟩
  rw [relativeRank, relativeRank, div_lt_div_iff_of_pos_right hS, Nat.cast_lt]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right S fun x _ (hx : x ≤ a) ↦ hx.trans hab.le)).2 ⟨b, ?_, ?_⟩)
  · exact mem_filter.2 ⟨hb, le_rfl⟩
  · exact fun h ↦ (mem_filter.1 h).2.not_gt hab

/-- The top of a scale has universal degree one. -/
theorem relativeRank_of_forall_le {S : Finset D} {d : D} (hd : d ∈ S) (h : ∀ x ∈ S, x ≤ d) :
    relativeRank S d = 1 := by
  rw [relativeRank, filter_true_of_mem h, div_self]
  exact_mod_cast (card_pos.2 ⟨d, hd⟩).ne'

/-- The bottom of a scale has universal degree one over the size of the scale. -/
theorem relativeRank_of_forall_ge {S : Finset D} {d : D} (hd : d ∈ S) (h : ∀ x ∈ S, d ≤ x) :
    relativeRank S d = 1 / #S := by
  rw [relativeRank, show S.filter (· ≤ d) = {d} by ext x; grind, card_singleton, Nat.cast_one]

/-- On the scale of the numbers from one to `N`, the universal degree of `n` is `n / N`. -/
theorem relativeRank_Icc {N n : ℕ} (hn : n ∈ Icc 1 N) : relativeRank (Icc 1 N) n = n / N := by
  rw [relativeRank, show (Icc 1 N).filter (· ≤ n) = Icc 1 n by ext k; grind]
  simp

end Rank

/-! ### Universal degrees -/

section Universal

variable {D E F : Type*} [LinearOrder D] [DecidableEq D]

/-- The universal degree of `x` under an adjective whose quasi-order `μ` gives, restricted to the
comparison class `C`, is the universal homomorphism applied to the class of `x` in the primary
scale of `C`. -/
def universalDegree (μ : E → D) (C : Finset E) (x : E) : ℚ := relativeRank (C.image μ) (μ x)

variable {μ : E → D} {C C' : Finset E} {x y : E}

/-- Within one comparison class, universal degrees compare as the adjective's quasi-order
does. -/
theorem universalDegree_lt_iff (hx : x ∈ C) (hy : y ∈ C) :
    universalDegree μ C x < universalDegree μ C y ↔ μ x < μ y :=
  (relativeRank_strictMonoOn (C.image μ)).lt_iff_lt (mem_image_of_mem μ hx) (mem_image_of_mem μ hy)

/-- Two members of a comparison class share a universal degree exactly when they are
equivalent in [cresswell-1976]'s sense under the restricted quasi-order. -/
theorem universalDegree_eq_iff (hx : x ∈ C) (hy : y ∈ C) :
    universalDegree μ C x = universalDegree μ C y ↔
      (cresswellSetoid fun a b : C ↦ μ b ≤ μ a).r ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [universalDegree, universalDegree,
    (relativeRank_strictMonoOn _).injOn.eq_iff (mem_image_of_mem μ hx) (mem_image_of_mem μ hy)]
  refine ⟨fun h ↦ ⟨fun _ ↦ by simp only [h], fun _ ↦ by simp only [h]⟩, fun ⟨h, _⟩ ↦ ?_⟩
  exact le_antisymm ((h ⟨x, hx⟩).1 le_rfl) ((h ⟨y, hy⟩).2 le_rfl)

/-- Two primary scales with the same classes compare across as the measures do. -/
theorem universalDegree_lt_iff_of_image_eq {ν : F → D} {C' : Finset F} {y : F}
    (h : C.image μ = C'.image ν) (hx : x ∈ C) (hy : y ∈ C') :
    universalDegree μ C x < universalDegree ν C' y ↔ μ x < ν y := by
  rw [universalDegree, universalDegree, h]
  exact (relativeRank_strictMonoOn _).lt_iff_lt (h ▸ mem_image_of_mem μ hx)
    (mem_image_of_mem ν hy)

/-- Members added to a comparison class, each as ADJ as one already there, change no universal
degree: the classes, not the members, are counted. -/
theorem universalDegree_eq_of_image_eq (h : C.image μ = C'.image μ) :
    universalDegree μ C = universalDegree μ C' :=
  funext fun _ ↦ by rw [universalDegree, universalDegree, h]

/-- A map identifying at least the members another identifies takes no more values. -/
private theorem card_image_le_of_eq_imp {D₁ D₂ : Type*} [DecidableEq D₁] [DecidableEq D₂]
    [Nonempty E] {T : Finset E} (f : E → D₁) (g : E → D₂)
    (h : ∀ a ∈ T, ∀ b ∈ T, g a = g b → f a = f b) : #(T.image f) ≤ #(T.image g) := by
  refine card_le_card_of_injOn (fun d ↦ g (Function.invFunOn f T d)) ?_ ?_
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hd
    exact mem_image_of_mem g (Function.invFunOn_mem ⟨a, ha, rfl⟩)
  · intro d hd d' hd' hdd
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hd
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hd'
    rw [← Function.invFunOn_eq (f := f) ⟨a, ha, rfl⟩, ← Function.invFunOn_eq (f := f) ⟨b, hb, rfl⟩]
    exact h _ (Function.invFunOn_mem ⟨a, ha, rfl⟩) _ (Function.invFunOn_mem ⟨b, hb, rfl⟩) hdd

/-- A universal degree depends only on the quasi-order the adjective induces on the comparison
class, not on the measure that presents it. -/
theorem universalDegree_congr {D' : Type*} [LinearOrder D'] [DecidableEq D'] {ν : E → D'}
    (h : ∀ a ∈ C, ∀ b ∈ C, μ a ≤ μ b ↔ ν a ≤ ν b) (hx : x ∈ C) :
    universalDegree μ C x = universalDegree ν C x := by
  have : Nonempty E := ⟨x⟩
  have card_image : ∀ T ⊆ C, #(T.image μ) = #(T.image ν) := fun T hT ↦
    have heq : ∀ a ∈ T, ∀ b ∈ T, μ a = μ b ↔ ν a = ν b := fun a ha b hb ↦ by grind
    (card_image_le_of_eq_imp μ ν fun a ha b hb ↦ (heq a ha b hb).2).antisymm
      (card_image_le_of_eq_imp ν μ fun a ha b hb ↦ (heq a ha b hb).1)
  rw [universalDegree, universalDegree, relativeRank, relativeRank, filter_image, filter_image,
    card_image _ (filter_subset _ _), card_image C subset_rfl,
    filter_congr fun a ha ↦ h a ha x hx]

/-- A member at least as ADJ as every other has universal degree one. -/
theorem universalDegree_of_forall_le (hx : x ∈ C) (h : ∀ y ∈ C, μ y ≤ μ x) :
    universalDegree μ C x = 1 :=
  relativeRank_of_forall_le (mem_image_of_mem μ hx) fun _ hd ↦ by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hd; exact h y hy

/-- A member at most as ADJ as every other has universal degree one over the number of
classes. -/
theorem universalDegree_of_forall_ge (hx : x ∈ C) (h : ∀ y ∈ C, μ x ≤ μ y) :
    universalDegree μ C x = 1 / #(C.image μ) :=
  relativeRank_of_forall_ge (mem_image_of_mem μ hx) fun _ hd ↦ by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hd; exact h y hy

/-- When the classes of a comparison class are the numbers from one to `N`, a universal degree
is the measure over `N`. -/
theorem universalDegree_of_image_eq_Icc {μ : E → ℕ} {N : ℕ} (h : C.image μ = Icc 1 N)
    (hx : x ∈ C) : universalDegree μ C x = μ x / N := by
  rw [universalDegree, h, relativeRank_Icc (h ▸ mem_image_of_mem μ hx)]

end Universal

/-! ### The comparative -/

/-- MORE applied to the greatest degree to which `y` is ADJ₂, the meaning of *x is more ADJ₁ than
y is ADJ₂*, holds of `x` exactly when the degree of `x` exceeds that of `y`. -/
theorem more_iff {E F : Type*} (μ₁ : E → ℚ) (μ₂ : F → ℚ) (x : E) (y : F) :
    maxComparative (· = .inl x) (· = .inr y) (Sum.elim μ₁ μ₂) ↔
      x ∈ Comparison.gt.over μ₁ (μ₂ y) :=
  maxComparative_eq_iff _ _ _

/-- A member lowest on one scale is not more ADJ₁ than a member highest on another is ADJ₂: its
degree is at most one over the number of classes and the standard's is one. -/
theorem not_more_of_least_of_greatest {D D' E F : Type*} [LinearOrder D] [DecidableEq D]
    [LinearOrder D'] [DecidableEq D'] {μ : E → D} {ν : F → D'} {C : Finset E} {C' : Finset F}
    {x : E} {y : F} (hx : x ∈ C) (hy : y ∈ C') (hmin : ∀ z ∈ C, μ x ≤ μ z)
    (hmax : ∀ z ∈ C', ν z ≤ ν y) :
    x ∉ Comparison.gt.over (universalDegree μ C) (universalDegree ν C' y) := by
  simp only [Comparison.over, Comparison.interval_gt, Set.mem_preimage, Set.mem_Ioi, not_lt,
    universalDegree_of_forall_le hy hmax, universalDegree_of_forall_ge hx hmin]
  exact div_le_one_of_le₀ (by exact_mod_cast card_pos.2 ⟨μ x, mem_image_of_mem μ hx⟩)
    (Nat.cast_nonneg _)

/-! ### The committee -/

/-- The committee has ten original members `a`–`j`, among them Betty (`b`), Evelin (`e`) and
Heather (`h`), and the expanded committee adds five members `a'`–`e'`. -/
inductive Member
  | a | b | c | d | e | f | g | h | i | j | a' | b' | c' | d' | e'
  deriving DecidableEq, Fintype, Repr

/-- The original ten members. -/
def original : Finset Member := {.a, .b, .c, .d, .e, .f, .g, .h, .i, .j}

/-- A member's beauty is their position counted from the least beautiful, the original ten
ranking a, b, c, …, j from the most beautiful down; `a'` and `b'` are as beautiful as Betty, `c'`
as `c`, `d'` as `d` and `e'` as Evelin. -/
def beauty : Member → ℕ
  | .a => 10 | .b | .a' | .b' => 9 | .c | .c' => 8 | .d | .d' => 7 | .e | .e' => 6
  | .f => 5 | .g => 4 | .h => 3 | .i => 2 | .j => 1

/-- A member's intelligence is their position counted from the least intelligent, the original
ten ranking i, f, j, g, h, a, d, b, e, c from the most intelligent down; `a'` is as intelligent as
Heather, `b'` and `c'` as Betty, `d'` as `f` and `e'` as Evelin. -/
def intelligence : Member → ℕ
  | .i => 10 | .f | .d' => 9 | .j => 8 | .g => 7 | .h | .a' => 6 | .a => 5 | .d => 4
  | .b | .b' | .c' => 3 | .e | .e' => 2 | .c => 1

/-- Betty, second most beautiful, is more beautiful for a committee member than Heather, fifth
most intelligent, is intelligent; Betty, third least intelligent, is not more intelligent than
Evelin, fifth most beautiful, is beautiful. -/
theorem indirect_comparison :
    .b ∈ Comparison.gt.over (universalDegree beauty original)
      (universalDegree intelligence original .h) ∧
    .b ∉ Comparison.gt.over (universalDegree intelligence original)
      (universalDegree beauty original .e) := by
  have hb : original.image beauty = Icc 1 10 := by decide
  have hi : original.image intelligence = Icc 1 10 := by decide
  simp only [Comparison.over, Comparison.interval_gt, Set.mem_preimage, Set.mem_Ioi,
    universalDegree_of_image_eq_Icc hb (by decide : Member.b ∈ original),
    universalDegree_of_image_eq_Icc hb (by decide : Member.e ∈ original),
    universalDegree_of_image_eq_Icc hi (by decide : Member.b ∈ original),
    universalDegree_of_image_eq_Icc hi (by decide : Member.h ∈ original)]
  norm_num [beauty, intelligence]

/-- The expanded committee assigns every member the universal degrees the original committee
does: each newcomer joins an existing class. -/
theorem expanded :
    universalDegree beauty univ = universalDegree beauty original ∧
    universalDegree intelligence univ = universalDegree intelligence original :=
  ⟨universalDegree_eq_of_image_eq (by decide), universalDegree_eq_of_image_eq (by decide)⟩

/-! ### Measurements -/

section Measured

variable {E : Type*} {μ ν : E ⊕ ℕ → ℕ} {P : Finset E} {N : ℕ}

/-- The comparison class of the people in `P` and the measurements from one to `N` inches. -/
def withMeasurements (P : Finset E) (N : ℕ) : Finset (E ⊕ ℕ) := P.disjSum (Icc 1 N)

/-- When each measurement measures itself and every person measures one of the measurements up
to `N`, the classes are the measurements. -/
theorem image_withMeasurements (hμ : ∀ n, μ (.inr n) = n) (hP : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) :
    (withMeasurements P N).image μ = Icc 1 N := by
  refine Subset.antisymm (fun _ h ↦ ?_) fun n hn ↦ mem_image.2 ⟨.inr n, ?_, hμ n⟩
  · obtain ⟨y | n, hy, rfl⟩ := mem_image.1 h <;> simp_all [withMeasurements]
  · simp_all [withMeasurements]

/-- With the measurements up to `N` in the comparison class, a person's universal degree is
their measurement over `N`. -/
theorem universalDegree_withMeasurements (hμ : ∀ n, μ (.inr n) = n)
    (hP : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) {x : E} (hx : x ∈ P) :
    universalDegree μ (withMeasurements P N) (.inl x) = μ (.inl x) / N :=
  universalDegree_of_image_eq_Icc (image_withMeasurements hμ hP) (by simp [withMeasurements, hx])

/-- When the comparison class keeps the measurements up to a common bound, each measuring itself
on both scales, and everyone measures within the bound, comparing universal degrees is
comparing measurements: a direct comparison. -/
theorem direct_comparison (hμ : ∀ n, μ (.inr n) = n) (hν : ∀ n, ν (.inr n) = n)
    (hPμ : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) (hPν : ∀ x ∈ P, ν (.inl x) ∈ Icc 1 N)
    {z w : E ⊕ ℕ} (hz : z ∈ withMeasurements P N) (hw : w ∈ withMeasurements P N) :
    z ∈ Comparison.gt.over (universalDegree μ (withMeasurements P N))
      (universalDegree ν (withMeasurements P N) w) ↔ ν w < μ z :=
  universalDegree_lt_iff_of_image_eq
    ((image_withMeasurements hν hPν).trans (image_withMeasurements hμ hPμ).symm) hw hz

end Measured

/-- The seven people of the height and width situation; `s` is Seymour. -/
inductive Person
  | a | b | c | d | e | f | s
  deriving DecidableEq, Fintype, Repr

/-- Heights are in inches: a is six foot three, b six foot two, c six foot, d, e and f five foot
ten and Seymour five foot two, and a measurement is as tall as itself. -/
def height : Person ⊕ ℕ → ℕ
  | .inl .a => 75 | .inl .b => 74 | .inl .c => 72 | .inl .d | .inl .e | .inl .f => 70
  | .inl .s => 62 | .inr n => n

/-- Widths are in inches: Seymour is three feet wide, f two foot five, b two foot two and the
rest two foot one, and a measurement is as wide as itself. -/
def width : Person ⊕ ℕ → ℕ
  | .inl .s => 36 | .inl .f => 29 | .inl .b => 26
  | .inl .a | .inl .c | .inl .d | .inl .e => 25 | .inr n => n

/-- The comparison class of the height and width situation holds the seven people and the
measurements up to eighty inches. -/
def measured : Finset (Person ⊕ ℕ) := withMeasurements univ 80

/-- Seymour's universal degrees are his measurements over eighty, so he is taller than he is
wide and not wider than he is tall. -/
theorem taller_than_wide :
    universalDegree height measured (.inl .s) = 62 / 80 ∧
    universalDegree width measured (.inl .s) = 36 / 80 ∧
    .inl .s ∈ Comparison.gt.over (universalDegree height measured)
      (universalDegree width measured (.inl .s)) ∧
    .inl .s ∉ Comparison.gt.over (universalDegree width measured)
      (universalDegree height measured (.inl .s)) := by
  have hs : (.inl .s : Person ⊕ ℕ) ∈ measured := by simp [measured, withMeasurements]
  have hh : ∀ x ∈ (univ : Finset Person), height (.inl x) ∈ Icc 1 80 := by decide
  have hw : ∀ x ∈ (univ : Finset Person), width (.inl x) ∈ Icc 1 80 := by decide
  refine ⟨?_, ?_, (direct_comparison (fun _ ↦ rfl) (fun _ ↦ rfl) hh hw hs hs).2 (by decide),
    fun h ↦ absurd ((direct_comparison (fun _ ↦ rfl) (fun _ ↦ rfl) hw hh hs hs).1 h) (by decide)⟩
  · rw [measured, universalDegree_withMeasurements (fun _ ↦ rfl) hh (mem_univ _)]; norm_num [height]
  · rw [measured, universalDegree_withMeasurements (fun _ ↦ rfl) hw (mem_univ _)]; norm_num [width]

/-! ### For a man -/

/-- The nineteen men; `s` is Seymour. -/
inductive Man
  | a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s
  deriving DecidableEq, Fintype, Repr

/-- A man's height class counts from the shortest: Seymour is alone at the bottom, followed by
o and p; k, l, m and n; q and c; f, g, h and i; d and e; j and r; and a and b. -/
def heightClass : Man → ℕ
  | .s => 1 | .o | .p => 2 | .k | .l | .m | .n => 3 | .q | .c => 4
  | .f | .g | .h | .i => 5 | .d | .e => 6 | .j | .r => 7 | .a | .b => 8

/-- A man's width class counts from the narrowest: q, r and a are at the bottom, followed by p;
n and o; j, k, l and m; f, g and h; b, c, d and e; and Seymour and i at the top. -/
def widthClass : Man → ℕ
  | .q | .r | .a => 1 | .p => 2 | .n | .o => 3 | .j | .k | .l | .m => 4
  | .f | .g | .h => 5 | .b | .c | .d | .e => 6 | .i | .s => 7

/-- The comparison class that *for a man* fixes holds the men and no measurements. -/
def men : Finset (Man ⊕ ℕ) := univ.map .inl

/-- Seymour, five feet tall and three feet wide, among men ordered as above and measurements up
to eighty inches: he is taller than he is wide, but restricted to men his height degree is one
eighth and his width degree one, so he is not taller for a man than he is wide for a man. -/
theorem for_a_man {τ ω : Man ⊕ ℕ → ℕ}
    (hτ : ∀ x y, τ (.inl x) ≤ τ (.inl y) ↔ heightClass x ≤ heightClass y)
    (hω : ∀ x y, ω (.inl x) ≤ ω (.inl y) ↔ widthClass x ≤ widthClass y)
    (hτn : ∀ n, τ (.inr n) = n) (hωn : ∀ n, ω (.inr n) = n)
    (hs : τ (.inl .s) = 60 ∧ ω (.inl .s) = 36)
    (hb : ∀ x, τ (.inl x) ∈ Icc 1 80 ∧ ω (.inl x) ∈ Icc 1 80) :
    .inl .s ∈ Comparison.gt.over (universalDegree τ (withMeasurements univ 80))
      (universalDegree ω (withMeasurements univ 80) (.inl .s)) ∧
    universalDegree τ men (.inl .s) = 1 / 8 ∧ universalDegree ω men (.inl .s) = 1 ∧
    .inl .s ∉ Comparison.gt.over (universalDegree τ men) (universalDegree ω men (.inl .s)) := by
  have hs' : (.inl .s : Man ⊕ ℕ) ∈ men := by simp [men]
  have hτC : universalDegree τ men (.inl .s) = 1 / 8 := by
    rw [universalDegree_congr (ν := Sum.elim heightClass fun _ ↦ 0) ?_ hs']
    · decide +kernel
    · simp only [men, mem_map, mem_univ, true_and]
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact hτ x y
  have hωC : universalDegree ω men (.inl .s) = 1 := by
    rw [universalDegree_congr (ν := Sum.elim widthClass fun _ ↦ 0) ?_ hs']
    · decide +kernel
    · simp only [men, mem_map, mem_univ, true_and]
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact hω x y
  refine ⟨(direct_comparison hτn hωn (fun x _ ↦ (hb x).1) (fun x _ ↦ (hb x).2)
    (by simp [withMeasurements]) (by simp [withMeasurements])).2 (by omega), hτC, hωC, ?_⟩
  simp only [Comparison.over, Comparison.interval_gt, Set.mem_preimage, Set.mem_Ioi, hτC, hωC]
  norm_num

/-- The hypotheses of `for_a_man` are consistent: some heights and widths in inches induce the
two orders of the men. -/
example : ∃ τ ω : Man ⊕ ℕ → ℕ,
    (∀ x y, τ (.inl x) ≤ τ (.inl y) ↔ heightClass x ≤ heightClass y) ∧
    (∀ x y, ω (.inl x) ≤ ω (.inl y) ↔ widthClass x ≤ widthClass y) ∧
    (∀ n, τ (.inr n) = n) ∧ (∀ n, ω (.inr n) = n) ∧ τ (.inl .s) = 60 ∧ ω (.inl .s) = 36 ∧
    ∀ x, τ (.inl x) ∈ Icc 1 80 ∧ ω (.inl x) ∈ Icc 1 80 :=
  ⟨Sum.elim (heightClass · + 59) id, Sum.elim (widthClass · + 29) id, by simp, by simp,
    fun _ ↦ rfl, fun _ ↦ rfl, rfl, rfl, by decide⟩

/-! ### The rows -/

/-- A committee member by name. -/
def Member.parse? : String → Option Member
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "g" => some .g | "h" => some .h | "i" => some .i | "j" => some .j
  | _ => none

/-- A person of the height and width situation by name. -/
def Person.parse? : String → Option Person
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "s" => some .s | _ => none

/-- A man by name. -/
def Man.parse? : String → Option Man
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "g" => some .g | "h" => some .h | "i" => some .i | "j" => some .j
  | "k" => some .k | "l" => some .l | "m" => some .m | "n" => some .n | "o" => some .o
  | "p" => some .p | "q" => some .q | "r" => some .r | "s" => some .s | _ => none

/-- The universal degree a row assigns one of its participants on one of its scales, in the
comparison class of its situation: the original committee, the people with the measurements up
to eighty inches, or the men. -/
def degree? (r : Datum) (who scale : String) : Option ℚ := do
  let n ← r.feature? who
  match r.feature? "model", r.feature? scale with
  | some "committee", some "beauty" => (Member.parse? n).map (universalDegree beauty original)
  | some "committee", some "intelligence" =>
    (Member.parse? n).map (universalDegree intelligence original)
  | some "measured", some "height" =>
    (Person.parse? n).map fun p ↦ universalDegree height measured (.inl p)
  | some "measured", some "width" =>
    (Person.parse? n).map fun p ↦ universalDegree width measured (.inl p)
  | some "men", some "height" => (Man.parse? n).map (universalDegree heightClass univ)
  | some "men", some "width" => (Man.parse? n).map (universalDegree widthClass univ)
  | _, _ => none

/-- The truth value a row reports. -/
def truth? (r : Datum) : Option Bool :=
  match r.feature? "truth" with
  | some "true" => some true
  | some "false" => some false
  | _ => none

/-- Every sentence the paper evaluates in one of its situations has the truth value it reports:
the subject's universal degree exceeds the standard's exactly when the paper says the sentence
is true. -/
theorem rows_truth : ∀ r ∈ Examples.all, (r.feature? "model").isSome →
    ∃ t ∈ truth? r, ∃ d₁ ∈ degree? r "subject" "subjectScale",
      ∃ d₂ ∈ degree? r "standard" "standardScale", (d₂ < d₁ ↔ t = true) := by
  decide +kernel

end Bale2008
