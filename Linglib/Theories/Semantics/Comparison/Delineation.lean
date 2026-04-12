import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Supervaluation.Basic

/-!
# Klein's Delineation Approach
@cite{klein-1980} @cite{kennedy-2007}
@cite{kamp-1975}

@cite{klein-1980} "A Semantics for Positive and Comparative Adjectives":
a degree-free analysis where gradable adjectives are simple predicates
(type `⟨e,t⟩`) whose extension is determined relative to a **comparison
class** — a contextually supplied set of entities.

## Lineage from Kamp (1975)

Klein's comparative — `∃ C. tall(a,C) ∧ ¬tall(b,C)` — is a direct
formalization of @cite{kamp-1975}'s definition (12): u₁ is at least as A
as u₂ iff in every completion where u₂ is in the extension, u₁ is too.
Kamp's "completions" become Klein's "comparison classes"; both derive
the comparative from existential quantification over ways of making a
vague predicate precise.

## Key Ideas

1. **No degrees**: "tall" does not denote a relation between entities and
   degrees. It is simply a predicate whose extension varies with context.

2. **Comparison class**: The positive form "Kim is tall" is true iff Kim
   is tall relative to the contextually relevant comparison class C
   (e.g., basketball players, children, people in general).

3. **Comparative via supervaluation**: "Kim is taller than Lee" is true
   iff there exists a comparison class C where Kim is tall and Lee is
   not. This uses a **supervaluation** over comparison classes rather
   than degree comparison.

## Comparison with Kennedy

| Feature           | @cite{kennedy-2007}           | @cite{klein-1980}             |
|-------------------|--------------------------|--------------------------|
| Ontology          | Degrees exist            | No degrees               |
| ⟦tall⟧           | λd.λx. height(x) ≥ d    | λx. tall(x) in C        |
| Comparative       | max > max                | ∃C. tall(x) ∧ ¬tall(y) |
| Vagueness         | Threshold variability    | Comparison class var.    |
| Comparison class  | Not a semantic argument  | Semantic argument of pos |
| Measure phrases   | Direct (3 inches of d)   | Via ≈-classes (§4.2)     |

@cite{kennedy-2007} argues (§2.2–2.3) that the comparison class is NOT
a semantic argument of *pos* (contra Klein). Instead, the standard is
determined by a context-sensitive function **s** (eq 27) that may draw on
domain information descriptively called a "comparison class" but which
"does not correspond to a constituent of the logical form" (p. 16).

Klein handles degree modifiers via comparison-class narrowing (§4.1,
eqs 42–43) and measure phrases via equivalence classes on a measurement
scale (§4.2), though the degree-based treatment is arguably more direct.

For the formal subsumption hierarchy (Klein ← Kennedy ← Measurement),
see `Theories/Semantics/Comparison/Hierarchy.lean`.
-/

namespace Semantics.Comparison.Delineation


-- ════════════════════════════════════════════════════
-- § 1. Comparison Class
-- ════════════════════════════════════════════════════

/-- A comparison class: a set of entities relevant for evaluating
    a gradable predicate. In Klein's framework, this is the only
    contextual parameter — there are no degrees or thresholds. -/
abbrev ComparisonClass (Entity : Type*) := Set Entity

-- ════════════════════════════════════════════════════
-- § 2. Positive Form
-- ════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 3. Comparative via Supervaluation
-- ════════════════════════════════════════════════════

/-- Klein's comparative: "Kim is taller than Lee" is true iff there
    EXISTS a comparison class C such that Kim is tall-in-C but Lee is
    not tall-in-C.

    This is a supervaluation over comparison classes: the comparative
    holds when the predicate can discriminate the two entities. -/
def comparativeSem {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (a b : Entity) : Prop :=
  ∃ C, delineation C a ∧ ¬ delineation C b

-- ════════════════════════════════════════════════════
-- § 4. Properties
-- ════════════════════════════════════════════════════

/-- Klein's comparative is asymmetric: if a is taller than b, then
    b is not taller than a.

    This requires the **monotonicity constraint** on delineations:
    if a is tall-in-C and b is not, then for any C' where b is tall,
    a is also tall. Without this constraint, the comparative can fail
    to be asymmetric. -/
def IsMonotoneDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (allClasses : Set (ComparisonClass Entity)) : Prop :=
  ∀ C₁ C₂ : ComparisonClass Entity,
    C₁ ∈ allClasses → C₂ ∈ allClasses →
    ∀ a b : Entity,
      delineation C₁ a → ¬ delineation C₁ b →
      delineation C₂ b → delineation C₂ a

-- ════════════════════════════════════════════════════
-- § 5. Bridge: Klein ↔ Fine (Supervaluation)
-- ════════════════════════════════════════════════════

/-! @cite{klein-1980}'s comparative is the **existential dual** of
    @cite{fine-1975}'s supervaluation. Where supervaluation asks "true at
    ALL specifications?", Klein asks "true at SOME specification where the
    other is false?" Both quantify over the same space — comparison classes
    (Klein) = specification points (Fine). The positive form "a is tall"
    maps to `superTrue (delineation · a)`, and Klein's comparative
    `∃ C. tall(a,C) ∧ ¬tall(b,C)` captures the asymmetry between a's
    and b's supervaluation status.

    Under monotone delineation, Klein's comparative entails Fine's
    comparative entailment: if b is super-true (tall in every comparison
    class), then a — who is at least as tall — must also be super-true. -/

open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff)

/-- Under monotone delineation, Klein's comparative entails Fine's
    comparative entailment: if b is super-true, a is super-true.

    The proof extracts the discriminating comparison class C₀ (where
    a is tall but b isn't), then uses monotonicity: in any class C₂
    where b is tall, a must also be tall. -/
theorem monotone_comparative_superTrue {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    [∀ C (x : Entity), Decidable (delineation C x)]
    (a b : Entity) (S : SpecSpace (ComparisonClass Entity))
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

/-- Klein's comparative witnesses supervaluation indefiniteness for b:
    if a is taller than b (∃ discriminating class IN the space), then b
    is not super-true — the discriminating class falsifies b. -/
theorem comparative_prevents_superTrue {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    [∀ C (x : Entity), Decidable (delineation C x)]
    (a b : Entity) (S : SpecSpace (ComparisonClass Entity))
    (hdisc : ∃ C ∈ S.admissible, delineation C a ∧ ¬ delineation C b) :
    superTrue (fun C => decide (delineation C b)) S ≠ .true := by
  intro h
  obtain ⟨C₀, hC₀, _, hnotb⟩ := hdisc
  have := (superTrue_true_iff _ S).mp h C₀ hC₀
  simp only [decide_eq_true_eq] at this
  exact hnotb this

-- ════════════════════════════════════════════════════
-- § 6. Partial Extensions (Klein §2.3, eqs 12–13)
-- ════════════════════════════════════════════════════

/-- Klein's partial extension function (§2.3, eq 12). For a vague
    predicate ζ at context c, `F_ζ(c)` assigns each entity in the
    comparison class to the positive extension (`some true`), negative
    extension (`some false`), or the extension gap (`none`).

    The total `delineation` in §§1–5 is the special case where every
    entity receives a definite value (no gap). -/
def PartialDelineation (Entity : Type*) :=
  ComparisonClass Entity → Entity → Option Bool

/-- Positive extension: `pos_ζ(c) = {u ∈ U : F_ζ(c)(u) = 1}` (eq 13i). -/
def PartialDelineation.posExt {Entity : Type*}
    (d : PartialDelineation Entity) (C : ComparisonClass Entity) : Set Entity :=
  {x | d C x = some true}

/-- Negative extension: `neg_ζ(c) = {u ∈ U : F_ζ(c)(u) = 0}` (eq 13ii). -/
def PartialDelineation.negExt {Entity : Type*}
    (d : PartialDelineation Entity) (C : ComparisonClass Entity) : Set Entity :=
  {x | d C x = some false}

/-- Extension gap: entities in the comparison class whose truth value
    is undefined — the borderline cases. -/
def PartialDelineation.extGap {Entity : Type*}
    (d : PartialDelineation Entity) (C : ComparisonClass Entity) : Set Entity :=
  {x | x ∈ C ∧ d C x = none}

/-- The three zones partition the comparison class: every member is in
    exactly one of posExt, negExt, or extGap. -/
theorem PartialDelineation.trichotomy {Entity : Type*}
    (d : PartialDelineation Entity) (C : ComparisonClass Entity) (x : Entity)
    (_hx : x ∈ C) (hdom : d C x ≠ none) :
    x ∈ d.posExt C ∨ x ∈ d.negExt C := by
  unfold posExt negExt; simp only [Set.mem_setOf_eq]
  match hv : d C x with
  | some true => exact Or.inl rfl
  | some false => exact Or.inr rfl
  | none => exact absurd hv hdom

-- ════════════════════════════════════════════════════
-- § 7. Context-Relative Ordering (Klein §3.3, eq 29)
-- ════════════════════════════════════════════════════

/-- Klein's ordering at context c (eq 29): `u >_{c,ζ} u'` iff there
    exists a comparison class X ⊆ 𝒰(c) that puts u in the positive
    extension and u' in the negative extension. The existing
    `comparativeSem` is the unrestricted case (𝒰(c) = U). -/
def ordering {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (cc : ComparisonClass Entity) (u u' : Entity) : Prop :=
  ∃ X, X ⊆ cc ∧ delineation X u ∧ ¬ delineation X u'

/-- The unrestricted comparative is the ordering over all of U. -/
theorem comparativeSem_eq_ordering_univ {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) (a b : Entity) :
    comparativeSem delineation a b ↔ ordering delineation Set.univ a b :=
  ⟨fun ⟨C, h1, h2⟩ => ⟨C, Set.subset_univ C, h1, h2⟩,
   fun ⟨C, _, h1, h2⟩ => ⟨C, h1, h2⟩⟩

/-- Klein's ordering is **asymmetric** under monotone delineation
    (§3.3, p. 23): if u >_{c,ζ} u', then u' ≯_{c,ζ} u. -/
theorem ordering_asymm {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (cc : ComparisonClass Entity) (u v : Entity) :
    ordering delineation cc u v → ¬ordering delineation cc v u := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, _, hv₂, hnu₂⟩
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂)

/-- Klein's ordering is **transitive** under monotone delineation
    (§3.3, p. 23): if u >_{c,ζ} v and v >_{c,ζ} w, then u >_{c,ζ} w.

    Proof: take X₂ (the class separating v from w). By monotonicity
    with X₁ separating u from v, u must also be positive in X₂.
    Since w is negative in X₂, X₂ separates u from w. -/
theorem ordering_trans {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (cc : ComparisonClass Entity) (u v w : Entity) :
    ordering delineation cc u v → ordering delineation cc v w →
    ordering delineation cc u w := by
  intro ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, hX₂, hv₂, hnw₂⟩
  exact ⟨X₂, hX₂, hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u v hu₁ hnv₁ hv₂, hnw₂⟩

/-- **Negative transitivity** of the ordering: if u >_{c,ζ} w then
    for any v, either u >_{c,ζ} v or v >_{c,ζ} w. No conditions
    required — follows from excluded middle on `delineation X v`.

    This is the key structural property that, combined with asymmetry
    (from monotonicity), makes the ordering a strict weak order. -/
theorem ordering_neg_trans {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (cc : ComparisonClass Entity) (u v w : Entity) :
    ordering delineation cc u w →
    ordering delineation cc u v ∨ ordering delineation cc v w := by
  intro ⟨X, hX, hu, hnw⟩
  by_cases hdel : delineation X v
  · exact Or.inr ⟨X, hX, hdel, hnw⟩
  · exact Or.inl ⟨X, hX, hu, hdel⟩

-- ════════════════════════════════════════════════════
-- § 8. Nondistinctness (Klein §3.3, eq 30)
-- ════════════════════════════════════════════════════

/-- Two entities are NONDISTINCT w.r.t. ζ at c (eq 30) iff no
    comparison class containing both can distinguish them.

    Nondistinctness is reflexive and symmetric but NOT transitive
    in general. For linear adjectives, nondistinctness collapses to
    equivalence (eq 40); for nonlinear adjectives it does not —
    this is what makes clever-type adjectives special. -/
def nondistinct {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (cc : ComparisonClass Entity) (u u' : Entity) : Prop :=
  ∀ X, X ⊆ cc → u ∈ X → u' ∈ X →
    (delineation X u ↔ delineation X u')

theorem nondistinct_refl {Entity : Type*}
    {delineation : ComparisonClass Entity → Entity → Prop}
    {cc : ComparisonClass Entity} {u : Entity} :
    nondistinct delineation cc u u :=
  fun _ _ _ _ => Iff.rfl

theorem nondistinct_symm {Entity : Type*}
    {delineation : ComparisonClass Entity → Entity → Prop}
    {cc : ComparisonClass Entity} {u u' : Entity}
    (h : nondistinct delineation cc u u') :
    nondistinct delineation cc u' u :=
  fun X hX hu' hu => (h X hX hu hu').symm

/-- Incomparability implies nondistinctness: if neither u > u' nor
    u' > u in the ordering, then u and u' are nondistinct. No
    conditions required — follows from excluded middle on `delineation`.

    The converse (nondistinct → incomparable) holds under Klein's
    domain restriction where the ordering additionally requires both
    entities to be members of the witness class X. -/
theorem nondistinct_of_incomparable {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (cc : ComparisonClass Entity) (u u' : Entity)
    (hno1 : ¬ ordering delineation cc u u')
    (hno2 : ¬ ordering delineation cc u' u) :
    nondistinct delineation cc u u' := by
  intro X hX _ _
  constructor
  · intro hdu; exact by_contra fun hdnu' => hno1 ⟨X, hX, hdu, hdnu'⟩
  · intro hdu'; exact by_contra fun hdnu => hno2 ⟨X, hX, hdu', hdnu⟩

-- ════════════════════════════════════════════════════
-- § 9. Linear vs. Nonlinear (Klein §2.2, eq 9; §3.3)
-- ════════════════════════════════════════════════════

/-- A delineation is LINEAR (eq 9) iff the ordering it induces is
    connected: for any two distinct members of a comparison class,
    either one is ranked above the other or they are nondistinct.

    Examples: tall, heavy, expensive — single-criterion adjectives
    that induce total orderings.

    This is orthogonal to Kennedy's open/closed (RGA/AGA) axis:
    tall is both linear AND relative-gradable. -/
def IsLinearDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) : Prop :=
  ∀ cc : ComparisonClass Entity, ∀ u u' : Entity,
    u ∈ cc → u' ∈ cc → u ≠ u' →
    ordering delineation cc u u' ∨
    ordering delineation cc u' u ∨
    nondistinct delineation cc u u'

/-- A delineation is NONLINEAR iff its ordering can go both ways:
    there exist u, u' and a comparison class cc such that both
    `u >_{cc} u'` and `u' >_{cc} u`. This happens when different
    subsets of cc apply different criteria (e.g., math vs. social
    skills for "clever"), so the delineation is not monotone.

    For linear adjectives (tall, heavy), monotonicity ensures the
    ordering is asymmetric; for nonlinear ones (clever, nice), the
    ordering can cycle. This is orthogonal to Kennedy's open/closed
    (RGA/AGA) distinction. -/
def IsNonlinearDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) : Prop :=
  ∃ cc : ComparisonClass Entity, ∃ u u' : Entity,
    ordering delineation cc u u' ∧ ordering delineation cc u' u

-- ════════════════════════════════════════════════════
-- § 10. Measure-Induced Delineation (Degree ↔ Delineation Bridge)
-- ════════════════════════════════════════════════════

/-! A measure function μ : E → D naturally induces a Klein delineation:
    entity x is "tall in C" iff x is strictly taller than some member
    of C. This bridges the degree world (Kennedy) and the degreeless
    world (Klein): the delineation is determined by the measure, but
    the semantics never mentions degrees directly. -/

/-- Delineation induced by a measure function: x is "A-in-C" iff
    there exists a member of C that x strictly exceeds on μ. -/
def measureDelineation {E D : Type*} [LinearOrder D]
    (μ : E → D) : ComparisonClass E → E → Prop :=
  fun C x => ∃ y ∈ C, μ y < μ x

/-- A measure-induced delineation is monotone: if a is tall-in-C₁
    and b is not, and b is tall-in-C₂, then a is tall-in-C₂. -/
theorem measureDelineation_monotone {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsMonotoneDelineation (measureDelineation μ) Set.univ := by
  intro C₁ C₂ _ _ a b ha hnotb hb
  obtain ⟨y₁, hy₁, hlt_a⟩ := ha
  obtain ⟨y₂, hy₂, hlt_b⟩ := hb
  have hle : μ b ≤ μ y₁ := by
    by_contra h; push_neg at h; exact hnotb ⟨y₁, hy₁, h⟩
  exact ⟨y₂, hy₂, lt_trans hlt_b (lt_of_le_of_lt hle hlt_a)⟩

/-- For a fixed entity x, `measureDelineation μ · x` is `Monotone` in
    the comparison class under `⊆`: enlarging C adds potential witnesses
    y ∈ C with μ y < μ x, so if x is "tall in C" then x is "tall in C'"
    for any C' ⊇ C.

    This connects Klein's parameter space to Mathlib's `Monotone`
    infrastructure. Note that general (non-measure-induced) delineations
    are NOT uniformly monotone — that's the whole point of nonlinear
    adjectives like "clever". -/
theorem measureDelineation_mono_in_class {E D : Type*} [LinearOrder D]
    (μ : E → D) (x : E) :
    Monotone (λ C => measureDelineation μ C x) :=
  λ _ _ hle ⟨y, hy, hlt⟩ => ⟨y, hle hy, hlt⟩

/-- **Forward**: Klein's ordering entails degree ordering. -/
theorem ordering_implies_degree {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E) :
    ordering (measureDelineation μ) cc a b → μ b < μ a := by
  intro ⟨_, _, hpos, hneg⟩
  obtain ⟨y, hy, hlt⟩ := hpos
  have hle : μ b ≤ μ y := by
    by_contra h; push_neg at h; exact hneg ⟨y, hy, h⟩
  exact lt_of_le_of_lt hle hlt

/-- **Backward**: degree ordering entails Klein's ordering
    (provided both entities are in the comparison class). -/
theorem degree_implies_ordering {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    μ b < μ a → ordering (measureDelineation μ) cc a b := by
  intro hlt
  refine ⟨{a, b}, ?_, ⟨b, Set.mem_insert_of_mem _ rfl, hlt⟩, ?_⟩
  · intro x hx; rcases hx with rfl | rfl <;> assumption
  · intro ⟨y, hy, hlt_y⟩
    rcases hy with rfl | rfl
    · exact absurd hlt_y (not_lt.mpr (le_of_lt hlt))
    · exact absurd hlt_y (lt_irrefl _)

/-- **Equivalence**: Klein's ordering ↔ degree comparison. Justifies
    Klein's claim that degrees are dispensable (§4.2). -/
theorem ordering_iff_degree {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    ordering (measureDelineation μ) cc a b ↔ μ b < μ a :=
  ⟨ordering_implies_degree μ cc a b, degree_implies_ordering μ cc a b ha hb⟩

/-- A measure-induced delineation is linear: for any two entities in a
    comparison class, either one ranks above the other or they are
    nondistinct (equal measure). This connects Klein's typology (§2.2):
    single-criterion adjectives like "tall" are always linear. -/
theorem measureDelineation_is_linear {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsLinearDelineation (measureDelineation μ) := by
  intro cc u u' hu hu' _
  rcases lt_trichotomy (μ u) (μ u') with hlt | heq | hgt
  · right; left; exact degree_implies_ordering μ cc u' u hu' hu hlt
  · right; right; intro X _ _ _
    simp only [measureDelineation, heq]
  · left; exact degree_implies_ordering μ cc u u' hu hu' hgt

-- ════════════════════════════════════════════════════
-- § 11. Degree Modifiers as CC Narrowers (Klein §4.1, eqs 42–43)
-- ════════════════════════════════════════════════════

/-! Klein handles degree modifiers WITHOUT degrees: `very` and `fairly`
    are comparison-class narrowers. Under the correspondence with degree
    semantics, narrowing the CC is equivalent to shifting the threshold. -/

/-- Klein's `very` (§4.1, eq 42): narrows the comparison class to the
    positive extension. "Very tall" = tall relative to the tall people.

    Under the degree correspondence, this is equivalent to raising the
    threshold from θ to a higher θ' — the threshold for being tall
    among tall people. -/
def veryDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (C : ComparisonClass Entity) (x : Entity) : Prop :=
  delineation {u | delineation C u} x

/-- Klein's `fairly` (§4.1, eq 43): narrows the comparison class to
    exclude the very-A entities. "Fairly tall" = tall among those who
    aren't very tall. -/
def fairlyDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (C : ComparisonClass Entity) (x : Entity) : Prop :=
  let veryPos : ComparisonClass Entity := {u | delineation {v | delineation C v} u}
  delineation {u | u ∈ C ∧ u ∉ veryPos} x

/-- `very` entails the base predicate: if x is very-tall-in-C then
    x is tall-in-C. (The positive extension of `very A` is a subset
    of the positive extension of A.)

    This requires Klein's **domain restriction**: the delineation only
    classifies entities that are members of the comparison class. Klein
    §2.3 eq (12) specifies that F_ζ(c) is a partial function on 𝒰(c),
    so `delineation C x` implies `x ∈ C`. Given this, the proof is
    immediate: if x is tall among the tall people, then x must be
    one of the tall people, hence tall in C.

    For measure-induced delineations (which don't satisfy this domain
    restriction), `very → base` holds by a different argument — see
    `Klein1980.measureDelineation_very_entails_base`. -/
theorem very_entails_base {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hcc : ∀ C x, delineation C x → x ∈ C)
    (C : ComparisonClass Entity) (x : Entity)
    (hv : veryDelineation delineation C x) :
    delineation C x :=
  hcc _ x hv

/-- `fairly` excludes `very`: if x is fairly-A-in-C then x is NOT
    very-A-in-C. Under domain restriction, being in the fairly-CC
    requires being outside the very-positive extension. -/
theorem fairly_excludes_very {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hcc : ∀ C x, delineation C x → x ∈ C)
    (C : ComparisonClass Entity) (x : Entity)
    (hf : fairlyDelineation delineation C x) :
    ¬ veryDelineation delineation C x :=
  (hcc _ x hf).2

-- ════════════════════════════════════════════════════
-- § 12. Preorder on Entities (Klein §5.3, eq 89b)
-- ════════════════════════════════════════════════════

/-- Klein's delineation induces a `Preorder` on entities:
    `u ≤ v` iff every comparison class where `v` qualifies also
    qualifies `u`. This is Klein's "as A as" (§5.3, eq 89b)
    and Kamp's at-least-as (definition 12).

    The strict part `u < v` is `u ≤ v ∧ ¬ v ≤ u`.
    Under monotone delineation, this coincides with `comparativeSem`. -/
@[reducible] def kleinPreorder {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) :
    Preorder Entity where
  le u v := ∀ C, delineation C v → delineation C u
  le_refl _ := fun _ h => h
  le_trans _ _ _ hab hbc := fun C hc => hab C (hbc C hc)

end Semantics.Comparison.Delineation
