import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Supervaluation.Basic

/-!
# Klein's Delineation Approach
@cite{burnett-2014} @cite{klein-1980} @cite{van-rooij-2011} @cite{kennedy-2007}
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
| Measure phrases   | Direct (3 inches of d)   | Requires extension       |

Klein's approach has difficulty with measure phrases ("3 inches taller")
and degree modifiers ("very tall"), which are natural in degree-based
frameworks.

-/

namespace Semantics.Degree.Frameworks.Klein

-- ════════════════════════════════════════════════════
-- § 1. Comparison Class
-- ════════════════════════════════════════════════════

/-- A comparison class: a set of entities relevant for evaluating
    a gradable predicate. In Klein's framework, this is the only
    contextual parameter — there are no degrees or thresholds. -/
def ComparisonClass (Entity : Type*) := Set Entity

-- ════════════════════════════════════════════════════
-- § 2. Positive Form
-- ════════════════════════════════════════════════════

/-- Klein's positive form: "Kim is tall" is true iff Kim is in the
    positive extension of "tall" relative to comparison class C.

    The delineation function partitions entities in C into those that
    satisfy the predicate and those that don't. The partition can be
    indeterminate (vagueness = gap between positive and negative extension). -/
def positiveSem {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (C : ComparisonClass Entity) (x : Entity) : Prop :=
  delineation C x

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
  ∃ C : ComparisonClass Entity, delineation C a ∧ ¬ delineation C b

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

end Semantics.Degree.Frameworks.Klein
