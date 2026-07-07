import Linglib.Semantics.Degree.Discrete
import Linglib.Semantics.Supervaluation.Basic

/-!
# Klein's delineation semantics
[klein-1980] [kamp-1975] [kennedy-2007]

Degree-free gradability: a gradable adjective is a predicate whose
extension varies with a contextually supplied **comparison class**, and
the comparative holds when some class discriminates the two entities
([klein-1980], formalizing [kamp-1975]'s definition (12)). The rival
threshold analysis is `Degree/Basic.lean`; the representation maps
between them and the strict-separation theorem are in `Degree/Hom.lean`.

## Main definitions

* `comparativeSem` — Klein's comparative: `∃ C, tall(a, C) ∧ ¬tall(b, C)`.
* `IsMonotoneDelineation` — [bochnak-2015]'s Consistency Constraint a.
* `PartialDelineation` — extension gaps (Klein §2.3, eqs 12–13).
* `ordering`, `nondistinct` — the context-relative comparison and
  indistinguishability relations (§3.3, eqs 29–30).
* `IsLinearDelineation`, `IsNonlinearDelineation` — single- vs
  multi-criteria adjectives (§2.2 eq 9; *tall* vs *clever*).
* `measureDelineation` — the delineation a measure function induces.
* `veryDelineation`, `fairlyDelineation` — degree modifiers as
  comparison-class narrowers (§4.1, eqs 42–43).
* `kleinPreorder` — *as A as* (§5.3, eq 89b; Kamp's definition 12).
* `IsSoundDelineation`, `IsCompleteDelineation` — faithfulness to an
  abstract scalar relation ([bochnak-2015] eq (28b) and its converse).

## Main results

* `ordering_asymm`, `ordering_trans`, `ordering_neg_trans` — under
  monotonicity the ordering is a strict weak order (§3.3, p. 23).
* `ordering_iff_degree` — measure-induced delineations are faithful:
  Klein's ordering is exactly degree comparison (§4.2).
* `comparativeSem_iff_of_sound_and_complete` — the comparative
  coincides with any scalar relation the delineation is sound and
  complete for.
* `monotone_comparative_superTrue`, `comparative_prevents_superTrue` —
  the [fine-1975] duality: comparison classes are specification points.
-/

namespace Degree.Delineation

open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff)

/-- A comparison class: the set of entities a gradable predicate is
    evaluated against — Klein's only contextual parameter. -/
abbrev ComparisonClass (Entity : Type*) := Set Entity

variable {Entity : Type*}

/-! ### The comparative -/

section Comparative

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Klein's comparative: some comparison class discriminates `a` from `b`. -/
def comparativeSem (a b : Entity) : Prop :=
  ∃ C, delineation C a ∧ ¬ delineation C b

/-- Monotone delineation ([bochnak-2015] eq (28a), Consistency
    Constraint a): a class that ranks `a` above `b` is never
    contradicted by another class. Forces asymmetry of the comparative. -/
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

/-- Under monotone delineation, a discriminating class carries
    super-truth upward: if `b` is tall in every admissible class, so is
    the `a` that outranks it. -/
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

/-! ### Partial extensions (Klein §2.3, eqs 12–13) -/

/-- Klein's partial extension function: each entity lands in the
    positive extension (`some true`), negative extension (`some false`),
    or the gap (`none`). The total `delineation` elsewhere in this file
    is the gap-free special case. -/
def PartialDelineation (Entity : Type*) :=
  ComparisonClass Entity → Entity → Option Bool

namespace PartialDelineation

variable (d : PartialDelineation Entity) (C : ComparisonClass Entity)

/-- Positive extension (eq 13i). -/
def posExt : Set Entity := {x | d C x = some true}

/-- Negative extension (eq 13ii). -/
def negExt : Set Entity := {x | d C x = some false}

/-- The extension gap: borderline cases. -/
def extGap : Set Entity := {x | x ∈ C ∧ d C x = none}

/-- Gap-free members fall in the positive or negative extension. -/
theorem trichotomy {x : Entity} (_hx : x ∈ C) (hdom : d C x ≠ none) :
    x ∈ d.posExt C ∨ x ∈ d.negExt C := by
  unfold posExt negExt
  match hv : d C x with
  | some true => exact Or.inl hv
  | some false => exact Or.inr hv
  | none => exact absurd hv hdom

end PartialDelineation

/-! ### The context-relative ordering (Klein §3.3, eqs 29–30) -/

section Ordering

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Klein's ordering at a context (eq 29): some subclass of `cc` puts
    `u` in the positive and `u'` in the negative extension. -/
def ordering (cc : ComparisonClass Entity) (u u' : Entity) : Prop :=
  ∃ X, X ⊆ cc ∧ delineation X u ∧ ¬ delineation X u'

/-- `comparativeSem` is the ordering over the universal class. -/
theorem comparativeSem_eq_ordering_univ (a b : Entity) :
    comparativeSem delineation a b ↔ ordering delineation Set.univ a b :=
  ⟨fun ⟨C, h1, h2⟩ => ⟨C, Set.subset_univ C, h1, h2⟩,
   fun ⟨C, _, h1, h2⟩ => ⟨C, h1, h2⟩⟩

variable {cc : ComparisonClass Entity} {u v w : Entity}

/-- Under monotonicity the ordering is asymmetric (§3.3, p. 23). -/
theorem ordering_asymm
    (hmono : IsMonotoneDelineation delineation Set.univ) :
    ordering delineation cc u v → ¬ ordering delineation cc v u := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, _, hv₂, hnu₂⟩
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂)

/-- Under monotonicity the ordering is transitive (§3.3, p. 23). -/
theorem ordering_trans
    (hmono : IsMonotoneDelineation delineation Set.univ) :
    ordering delineation cc u v → ordering delineation cc v w →
    ordering delineation cc u w := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, hX₂, hv₂, hnw₂⟩
  exact ⟨X₂, hX₂, hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂, hnw₂⟩

/-- Negative transitivity, with no side conditions: together with
    asymmetry this makes the ordering a strict weak order. -/
theorem ordering_neg_trans :
    ordering delineation cc u w →
    ordering delineation cc u v ∨ ordering delineation cc v w := by
  intro ⟨X, hX, hu, hnw⟩
  by_cases hdel : delineation X v
  · exact Or.inr ⟨X, hX, hdel, hnw⟩
  · exact Or.inl ⟨X, hX, hu, hdel⟩

/-- Nondistinctness (eq 30): no subclass containing both can
    distinguish them. Reflexive and symmetric; transitive only for
    linear adjectives (eq 40). -/
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

/-! ### Linear and nonlinear adjectives (Klein §2.2 eq 9, §3.3) -/

section Linearity

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Linear (eq 9): any two class-mates are ordered or nondistinct —
    single-criterion adjectives (*tall*, *heavy*). Orthogonal to
    Kennedy's relative/absolute axis. -/
def IsLinearDelineation : Prop :=
  ∀ cc : ComparisonClass Entity, ∀ u u' : Entity,
    u ∈ cc → u' ∈ cc → u ≠ u' →
    ordering delineation cc u u' ∨
    ordering delineation cc u' u ∨
    nondistinct delineation cc u u'

/-- Nonlinear: the ordering cycles — different subclasses apply
    different criteria (*clever*, *nice*). No measure function induces
    such a delineation (`Degree/Hom.lean`, `delineation_strictly_more_general`). -/
def IsNonlinearDelineation : Prop :=
  ∃ cc : ComparisonClass Entity, ∃ u u' : Entity,
    ordering delineation cc u u' ∧ ordering delineation cc u' u

end Linearity

/-! ### Morphisms

`measureDelineation` maps threshold-degree semantics into delineation
semantics; `ordering_iff_degree` is its faithfulness. Strictness — some
delineations come from no measure — and the composite from typed
measurement live in `Degree/Hom.lean`. -/

section Measure

variable {E D : Type*} [LinearOrder D] (μ : E → D)

/-- The delineation a measure induces: `x` qualifies in `C` iff it
    strictly exceeds some member of `C`. -/
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

/-- For fixed `x`, membership is `Monotone` in the class: larger
    classes only add witnesses. General delineations are not — that is
    the point of nonlinear adjectives. -/
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

/-- Faithfulness: Klein's ordering under the induced delineation is
    exactly degree comparison — degrees are dispensable (§4.2). -/
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

/-! ### Degree modifiers as class narrowers (Klein §4.1, eqs 42–43) -/

section Modifiers

variable (delineation : ComparisonClass Entity → Entity → Prop)

/-- Klein's *very* (eq 42): tall relative to the tall people — the
    class narrows to the positive extension. -/
def veryDelineation (C : ComparisonClass Entity) (x : Entity) : Prop :=
  delineation {u | delineation C u} x

/-- Klein's *fairly* (eq 43): tall among those not very tall. -/
def fairlyDelineation (C : ComparisonClass Entity) (x : Entity) : Prop :=
  let veryPos : ComparisonClass Entity := {u | delineation {v | delineation C v} u}
  delineation {u | u ∈ C ∧ u ∉ veryPos} x

variable {delineation} {C : ComparisonClass Entity} {x : Entity}

/-- *very A* entails *A*, given Klein's domain restriction (eq 12:
    only class members are classified). For measure-induced
    delineations see `Klein1980.measureDelineation_very_entails_base`. -/
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

/-! ### The Kamp preorder (Klein §5.3, eq 89b) -/

/-- *as A as* : `u ≤ v` iff every class where `v` qualifies also
    qualifies `u` ([kamp-1975] definition 12). Under monotone
    delineation its strict part is `comparativeSem`. -/
@[reducible] def kleinPreorder
    (delineation : ComparisonClass Entity → Entity → Prop) :
    Preorder Entity where
  le u v := ∀ C, delineation C v → delineation C u
  le_refl _ := fun _ h => h
  le_trans _ _ _ hab hbc := fun C hc => hab C (hbc C hc)

/-! ### Faithfulness to a scalar relation

Soundness is [bochnak-2015] eq (28b) (Consistency Constraint b, cf.
[klein-1980] [kennedy-2011] [van-rooij-2011a]); completeness is its
converse (closer to [burnett-2017]'s Plenitude/Granularity axioms —
[bochnak-2015]'s footnote 11 notes the one-directional character).
CC-b is strict-classical: under [cobreros-etal-2012]'s tolerant
semantics, similar pairs would defeat strict separation. -/

section Faithfulness

variable {del : ComparisonClass Entity → Entity → Prop}
  {R : Entity → Entity → Prop}

/-- Sound w.r.t. a scalar relation `R`: per-class separation entails `R`. -/
class IsSoundDelineation
    (del : ComparisonClass Entity → Entity → Prop)
    (R : Entity → Entity → Prop) : Prop where
  /-- Per-context separation implies the scalar relation. -/
  sound : ∀ C x y, del C x → ¬ del C y → R x y

/-- Complete w.r.t. `R`: every `R`-distinguished pair admits a
    discriminating class. -/
class IsCompleteDelineation
    (del : ComparisonClass Entity → Entity → Prop)
    (R : Entity → Entity → Prop) : Prop where
  /-- `R`-distinguished pairs admit a discriminating context. -/
  complete : ∀ x y, R x y → ∃ C, del C x ∧ ¬ del C y

/-- `comparativeSem` coincides with any scalar relation the delineation
    is sound and complete for — the comparison entailment without a
    measure function in the lexical entry. -/
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
