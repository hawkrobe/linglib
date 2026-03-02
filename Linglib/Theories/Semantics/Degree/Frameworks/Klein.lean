import Linglib.Theories.Semantics.Degree.Core

/-!
# Klein's Delineation Approach
@cite{burnett-2014} @cite{klein-1980} @cite{van-rooij-2011} @cite{kennedy-2007}

@cite{klein-1980} "A Semantics for Positive and Comparative Adjectives":
a degree-free analysis where gradable adjectives are simple predicates
(type `⟨e,t⟩`) whose extension is determined relative to a **comparison
class** — a contextually supplied set of entities.

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

end Semantics.Degree.Frameworks.Klein
