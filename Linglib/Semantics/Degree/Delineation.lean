module

public import Linglib.Semantics.Supervaluation

/-!
# Delineation semantics

In delineation semantics a gradable adjective has no degree argument. A delineation decides, for
each comparison class (a set of entities the adjective is evaluated against), which entities the
adjective holds of, and *a is taller than b* holds when some comparison class puts `a` in the
extension and leaves `b` out. Klein develops this analysis from Kamp's account of the comparative.
A measure function induces a delineation whose ordering is degree comparison, so the threshold
analysis embeds in this one; `Degree/Hom.lean` relates the two further.

## Main definitions

* `comparativeSem`: Klein's comparative.
* `IsMonotoneDelineation`: no comparison class reverses a ranking another class makes.
* `ordering`, `nondistinct`: comparison and indistinguishability within a comparison class.
* `IsLinearDelineation`, `IsNonlinearDelineation`: single-criterion adjectives such as *tall*
  and multi-criteria adjectives such as *clever*.
* `measureDelineation`: the delineation a measure function induces.

## Main statements

* `ordering_asymm`, `ordering_trans`, `ordering_neg_trans`: under monotonicity the ordering is a
  strict weak order.
* `ordering_iff_degree`: under a measure-induced delineation the ordering is degree comparison.
* `IsMonotoneDelineation.not_isNonlinearDelineation`: a monotone delineation is never nonlinear,
  so no measure function induces a nonlinear one.

## References

* [klein-1980]
* [kamp-1975]
* [fine-1975]
* [bochnak-2015]
* [burnett-2017]
* [cobreros-etal-2012]
* [kennedy-2011]
* [van-rooij-2011a]
-/

@[expose] public section

namespace Degree.Delineation

open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff)

/-- A comparison class is the set of entities a gradable predicate is evaluated against, the only
contextual parameter of a delineation. -/
abbrev ComparisonClass (Entity : Type*) := Set Entity

variable {Entity : Type*}

/-! ### The comparative -/

section Comparative

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Klein's comparative holds of `a` and `b` when some comparison class puts `a` in the extension
and leaves `b` out. -/
def comparativeSem (a b : Entity) : Prop :=
  ∃ C, delineation C a ∧ ¬ delineation C b

/-- A delineation is monotone on a set of comparison classes when no class in the set puts `b` in
the extension and leaves `a` out once another class has put `a` in and left `b` out. -/
def IsMonotoneDelineation (allClasses : Set (ComparisonClass Entity)) : Prop :=
  ∀ C₁ C₂ : ComparisonClass Entity,
    C₁ ∈ allClasses → C₂ ∈ allClasses →
    ∀ a b : Entity,
      delineation C₁ a → ¬ delineation C₁ b →
      delineation C₂ b → delineation C₂ a

end Comparative

/-! ### The Fine duality

Comparison classes are specification points: Klein's comparative is the
existential dual of [fine-1975]'s supervaluation. -/

section Supervaluation

variable (delineation : ComparisonClass Entity → Entity → Prop)
  [∀ C (x : Entity), Decidable (delineation C x)]
  (a b : Entity) (S : SpecSpace (ComparisonClass Entity))

/-- Under a monotone delineation, if some admissible class ranks `a` above `b` and `b` is in the
extension of every admissible class, then so is `a`. -/
theorem monotone_comparative_superTrue
    (hmono : ∀ C₁ ∈ S.admissible, ∀ C₂ ∈ S.admissible,
      ∀ x y : Entity, delineation C₁ x → ¬ delineation C₁ y →
      delineation C₂ y → delineation C₂ x)
    (hdisc : ∃ C ∈ S.admissible, delineation C a ∧ ¬ delineation C b)
    (hb : superTrue (fun C => decide (delineation C b)) S = .true) :
    superTrue (fun C => decide (delineation C a)) S = .true := by
  rw [superTrue_true_iff] at hb ⊢
  intro C hC
  obtain ⟨C₀, hC₀, haC₀, hnotbC₀⟩ := hdisc
  simp only [decide_eq_true_eq] at hb ⊢
  exact hmono C₀ hC₀ C hC a b haC₀ hnotbC₀ (hb C hC)

/-- A discriminating class in the space falsifies `b`'s super-truth. -/
theorem comparative_prevents_superTrue
    (hdisc : ∃ C ∈ S.admissible, delineation C a ∧ ¬ delineation C b) :
    superTrue (fun C => decide (delineation C b)) S ≠ .true := by
  intro h
  obtain ⟨C₀, hC₀, _, hnotb⟩ := hdisc
  have := (superTrue_true_iff _ S).mp h C₀ hC₀
  simp only [decide_eq_true_eq] at this
  exact hnotb this

end Supervaluation

/-! ### The ordering within a comparison class -/

section Ordering

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Within the comparison class `cc`, `u` is ordered above `u'` when some subclass of `cc` puts `u`
in the extension and leaves `u'` out. -/
def ordering (cc : ComparisonClass Entity) (u u' : Entity) : Prop :=
  ∃ X, X ⊆ cc ∧ delineation X u ∧ ¬ delineation X u'

/-- `comparativeSem` is the ordering over the universal class. -/
theorem comparativeSem_eq_ordering_univ (a b : Entity) :
    comparativeSem delineation a b ↔ ordering delineation Set.univ a b :=
  ⟨fun ⟨C, h1, h2⟩ => ⟨C, Set.subset_univ C, h1, h2⟩,
   fun ⟨C, _, h1, h2⟩ => ⟨C, h1, h2⟩⟩

variable {cc : ComparisonClass Entity} {u v w : Entity}

/-- Under monotonicity the ordering is asymmetric. -/
theorem ordering_asymm
    (hmono : IsMonotoneDelineation delineation Set.univ) :
    ordering delineation cc u v → ¬ ordering delineation cc v u := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, _, hv₂, hnu₂⟩
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂)

/-- Under monotonicity the ordering is transitive. -/
theorem ordering_trans
    (hmono : IsMonotoneDelineation delineation Set.univ) :
    ordering delineation cc u v → ordering delineation cc v w →
    ordering delineation cc u w := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, hX₂, hv₂, hnw₂⟩
  exact ⟨X₂, hX₂, hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂, hnw₂⟩

/-- The ordering is negatively transitive for every delineation, so together with asymmetry it is
a strict weak order. -/
theorem ordering_neg_trans :
    ordering delineation cc u w →
    ordering delineation cc u v ∨ ordering delineation cc v w := by
  intro ⟨X, hX, hu, hnw⟩
  by_cases hdel : delineation X v
  · exact Or.inr ⟨X, hX, hdel, hnw⟩
  · exact Or.inl ⟨X, hX, hu, hdel⟩

/-- Two entities are nondistinct in `cc` when no subclass of `cc` containing both puts one in the
extension and leaves the other out. The relation is reflexive and symmetric, and transitive
only for linear adjectives. -/
def nondistinct (cc : ComparisonClass Entity) (u u' : Entity) : Prop :=
  ∀ X, X ⊆ cc → u ∈ X → u' ∈ X →
    (delineation X u ↔ delineation X u')

variable {delineation}

theorem nondistinct_refl : nondistinct delineation cc u u :=
  fun _ _ _ _ => Iff.rfl

theorem nondistinct_symm (h : nondistinct delineation cc u v) :
    nondistinct delineation cc v u :=
  fun X hX hu hv => (h X hX hv hu).symm

/-- Incomparable entities are nondistinct. The converse holds under
    Klein's domain restriction (witness classes contain both entities). -/
theorem nondistinct_of_incomparable
    (hno1 : ¬ ordering delineation cc u v)
    (hno2 : ¬ ordering delineation cc v u) :
    nondistinct delineation cc u v := by
  intro X hX _ _
  constructor
  · intro hdu; exact by_contra fun hdnu' => hno1 ⟨X, hX, hdu, hdnu'⟩
  · intro hdu'; exact by_contra fun hdnu => hno2 ⟨X, hX, hdu', hdnu⟩

end Ordering

/-! ### Linear and nonlinear adjectives -/

section Linearity

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- A delineation is linear when any two members of a comparison class are ordered one way or the
other or nondistinct, as for single-criterion adjectives such as *tall* and *heavy*. -/
def IsLinearDelineation : Prop :=
  ∀ cc : ComparisonClass Entity, ∀ u u' : Entity,
    u ∈ cc → u' ∈ cc → u ≠ u' →
    ordering delineation cc u u' ∨
    ordering delineation cc u' u ∨
    nondistinct delineation cc u u'

/-- A delineation is nonlinear when its ordering ranks two entities each above the other, as when
different subclasses apply different criteria for *clever* or *nice*. -/
def IsNonlinearDelineation : Prop :=
  ∃ cc : ComparisonClass Entity, ∃ u u' : Entity,
    ordering delineation cc u u' ∧ ordering delineation cc u' u

variable {delineation} in
/-- A monotone delineation is never nonlinear, since monotonicity makes its ordering asymmetric. -/
theorem IsMonotoneDelineation.not_isNonlinearDelineation
    (hmono : IsMonotoneDelineation delineation Set.univ) :
    ¬ IsNonlinearDelineation delineation :=
  fun ⟨_, _, _, h, h'⟩ ↦ ordering_asymm delineation hmono h h'

end Linearity

/-! ### The delineation of a measure

`measureDelineation` maps threshold semantics into delineation semantics, and
`ordering_iff_degree` says the map is faithful. -/

section Measure

variable {E D : Type*} [LinearOrder D] (μ : E → D)

/-- The delineation a measure induces puts `x` in the extension relative to `C` when `x` measures
strictly more than some member of `C`. -/
def measureDelineation : ComparisonClass E → E → Prop :=
  fun C x => ∃ y ∈ C, μ y < μ x

/-- Measure-induced delineations are monotone. -/
theorem measureDelineation_monotone :
    IsMonotoneDelineation (measureDelineation μ) Set.univ := by
  intro C₁ C₂ _ _ a b ha hnotb hb
  obtain ⟨y₁, hy₁, hlt_a⟩ := ha
  obtain ⟨y₂, hy₂, hlt_b⟩ := hb
  have hle : μ b ≤ μ y₁ := not_lt.mp fun h => hnotb ⟨y₁, hy₁, h⟩
  exact ⟨y₂, hy₂, lt_trans hlt_b (lt_of_le_of_lt hle hlt_a)⟩

/-- Under a measure-induced delineation, membership of a fixed `x` is monotone in the comparison
class, since a larger class only adds witnesses. -/
theorem measureDelineation_mono_in_class (x : E) :
    Monotone (fun C => measureDelineation μ C x) :=
  fun _ _ hle ⟨y, hy, hlt⟩ => ⟨y, hle hy, hlt⟩

/-- Klein's ordering entails degree comparison. -/
theorem ordering_implies_degree (cc : ComparisonClass E) (a b : E) :
    ordering (measureDelineation μ) cc a b → μ b < μ a := by
  intro ⟨_, _, hpos, hneg⟩
  obtain ⟨y, hy, hlt⟩ := hpos
  have hle : μ b ≤ μ y := not_lt.mp fun h => hneg ⟨y, hy, h⟩
  exact lt_of_le_of_lt hle hlt

/-- Degree comparison entails Klein's ordering for class-mates, with
    the two-element class `{a, b}` as witness. -/
theorem degree_implies_ordering (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    μ b < μ a → ordering (measureDelineation μ) cc a b := by
  intro hlt
  refine ⟨{a, b}, ?_, ⟨b, Set.mem_insert_of_mem _ rfl, hlt⟩, ?_⟩
  · intro x hx; rcases hx with rfl | rfl <;> assumption
  · intro ⟨y, hy, hlt_y⟩
    rcases hy with rfl | rfl
    · exact absurd hlt_y (not_lt.mpr (le_of_lt hlt))
    · exact absurd hlt_y (lt_irrefl _)

/-- Under a measure-induced delineation, the ordering of two members of a comparison class is
degree comparison. -/
theorem ordering_iff_degree (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    ordering (measureDelineation μ) cc a b ↔ μ b < μ a :=
  ⟨ordering_implies_degree μ cc a b, degree_implies_ordering μ cc a b ha hb⟩

/-- Measure-induced delineations are linear. -/
theorem measureDelineation_is_linear :
    IsLinearDelineation (measureDelineation μ) := by
  intro cc u u' hu hu' _
  rcases lt_trichotomy (μ u) (μ u') with hlt | heq | hgt
  · right; left; exact degree_implies_ordering μ cc u' u hu' hu hlt
  · right; right; intro X _ _ _
    simp only [measureDelineation, heq]
  · left; exact degree_implies_ordering μ cc u u' hu hu' hgt

end Measure

/-! ### Degree modifiers as narrowings of the comparison class -/

section Modifiers

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Klein's *very A* holds of `x` relative to `C` when *A* holds of `x` relative to the members of
`C` that *A* holds of. -/
def veryDelineation (C : ComparisonClass Entity) (x : Entity) : Prop :=
  delineation {u | delineation C u} x

/-- Klein's *fairly A* holds of `x` relative to `C` when *A* holds of `x` relative to the members of
`C` that *very A* does not hold of. -/
def fairlyDelineation (C : ComparisonClass Entity) (x : Entity) : Prop :=
  let veryPos : ComparisonClass Entity := {u | delineation {v | delineation C v} u}
  delineation {u | u ∈ C ∧ u ∉ veryPos} x

variable {delineation} {C : ComparisonClass Entity} {x : Entity}

/-- *very A* entails *A* when the delineation classifies only members of the comparison class. -/
theorem very_entails_base (hcc : ∀ C x, delineation C x → x ∈ C)
    (hv : veryDelineation delineation C x) :
    delineation C x :=
  hcc _ x hv

/-- *fairly A* excludes *very A*. -/
theorem fairly_excludes_very (hcc : ∀ C x, delineation C x → x ∈ C)
    (hf : fairlyDelineation delineation C x) :
    ¬ veryDelineation delineation C x :=
  (hcc _ x hf).2

end Modifiers

/-! ### The equative -/

/-- In the equative preorder `u ≤ v` holds when every comparison class whose extension contains `v`
also contains `u`, so `u ≤ v` says that *u is as A as v*. -/
@[reducible] def kleinPreorder
    (delineation : ComparisonClass Entity → Entity → Prop) :
    Preorder Entity where
  le u v := ∀ C, delineation C v → delineation C u
  le_refl _ := fun _ h => h
  le_trans _ _ _ hab hbc := fun C hc => hab C (hbc C hc)

/-! ### Faithfulness to a scalar relation

A delineation is sound for a scalar relation `R` when separation by a comparison class entails
`R`, which is Bochnak's second consistency constraint; it is complete when every pair related by
`R` is separated by some class, closer to Burnett's axioms. Both are classical: under the
tolerant semantics of Cobreros and colleagues, similar pairs would defeat strict separation. -/

section Faithfulness

variable {del : ComparisonClass Entity → Entity → Prop}
  {R : Entity → Entity → Prop}

/-- A delineation is sound for a scalar relation `R` when every class that puts `x` in the
extension and leaves `y` out witnesses `R x y`. -/
class IsSoundDelineation
    (del : ComparisonClass Entity → Entity → Prop)
    (R : Entity → Entity → Prop) : Prop where
  /-- Per-context separation implies the scalar relation. -/
  sound : ∀ C x y, del C x → ¬ del C y → R x y

/-- A delineation is complete for a scalar relation `R` when every pair related by `R` is
separated by some comparison class. -/
class IsCompleteDelineation
    (del : ComparisonClass Entity → Entity → Prop)
    (R : Entity → Entity → Prop) : Prop where
  /-- `R`-distinguished pairs admit a discriminating context. -/
  complete : ∀ x y, R x y → ∃ C, del C x ∧ ¬ del C y

/-- Klein's comparative coincides with any scalar relation the delineation is sound and complete
for. -/
theorem comparativeSem_iff_of_sound_and_complete
    [hSound : IsSoundDelineation del R]
    [hComplete : IsCompleteDelineation del R]
    {x y : Entity} : comparativeSem del x y ↔ R x y :=
  ⟨fun ⟨C, hpos, hneg⟩ => hSound.sound C x y hpos hneg,
   hComplete.complete x y⟩

end Faithfulness

instance instSoundMeasureDelineation {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsSoundDelineation (measureDelineation μ) (fun a b => μ b < μ a) where
  sound C x y hpos hneg :=
    ordering_implies_degree μ Set.univ x y
      ⟨C, Set.subset_univ _, hpos, hneg⟩

instance instCompleteMeasureDelineation {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsCompleteDelineation (measureDelineation μ) (fun a b => μ b < μ a) where
  complete x y hR := by
    obtain ⟨C, _, hpos, hneg⟩ :=
      degree_implies_ordering μ Set.univ x y
        (Set.mem_univ _) (Set.mem_univ _) hR
    exact ⟨C, hpos, hneg⟩

end Degree.Delineation
