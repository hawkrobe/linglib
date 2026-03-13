import Linglib.Theories.Semantics.Dynamic.Core.KindAnaphora

/-!
# Anaphora for Concepts, Kinds, and Parts
@cite{krifka-2026}

Empirical data and verification theorems for @cite{krifka-2026}'s theory
of concept discourse referents. Three types of anaphora are distinguished:

| Type | Pronoun | Picks up | Example |
|------|---------|----------|---------|
| Entity | *he/she/it* | individual dref | *A dog₃ came in. It₃ barked.* |
| Concept | *one*, empty NP | concept dref | *John has a big dog₂. Mary has a small one₂.* |
| Kind | *it*[MASS], *they*[COUNT] | concept dref → kind | *John owns a dog₂. They₂ are loyal.* |

## Key empirical claims

1. **Concept drefs project past anaphoric islands** — negation, modals,
   conditionals cannot trap concept drefs (unlike entity drefs)
2. **Mass/count feature determines kind pronoun** — *it* for [MASS],
   *they* for [COUNT], independent of ontology
3. **Kind anaphora ≠ concept anaphora** — kind anaphors derive kind
   individuals via ∩ (and ⊔ for count), concept anaphors reuse the property

## End-to-End Example

Section 3 constructs a concrete model of examples (44)–(45):

```
John₁ doesn't own [DP a₃ [NP dog]₂].
  → concept dref x₂ ('dog'[COUNT]) persists in output
  → entity dref x₃ (the dog) is trapped under ¬∃
He₁ is afraid of them₂,₄.
  → kind anaphor picks up concept x₂ (accessible!)
  → derives kind individual via ∩(⊔⟦dog⟧)
```
-/

namespace Phenomena.Reference.Studies.Krifka2026

open Semantics.Dynamic.Core (ConceptDRef DRefVal)
open Semantics.Dynamic.Core.KindAnaphora

-- ════════════════════════════════════════════════════
-- § 1. Kind Pronoun Selection
-- ════════════════════════════════════════════════════

/-- Kind-anaphoric pronouns, selected by the [MASS]/[COUNT] feature. -/
inductive KindPronoun where
  | it    -- singular, selects [MASS] concepts
  | they  -- plural, selects [COUNT] concepts
  deriving DecidableEq, Repr

/-- Select kind-anaphoric pronoun from the count feature.

    @cite{krifka-2026} (17a,b):
    - ⟦it⟧  = λP[MASS]  λi.∩P(i)
    - ⟦they⟧ = λP[COUNT] λi.∩⊔P(i) -/
def selectPronoun : MassCount → KindPronoun
  | .mass => .it
  | .count => .they

/-- Example (7a): count noun antecedent → plural kind anaphor *them*.
    *John noticed a spider in the bathroom. He has a phobia against them / \*it.* -/
theorem ex7a_count_them : selectPronoun .count = .they := rfl

/-- Example (7b): mass noun antecedent → singular kind anaphor *it*.
    *John noticed mold in the bathroom. He is allergic against it / \*them.* -/
theorem ex7b_mass_it : selectPronoun .mass = .it := rfl

/-- Examples (8a,b): the same individuals (*pollen*[MASS] vs *pollen grains*[COUNT])
    select different pronouns based purely on the morphosyntactic feature.
    (8a) *There is a lot of pollen in the air. I am allergic against it / \*them.*
    (8b) *There are a lot of pollen grains in the air. I am allergic against them / ??it.* -/
theorem ex8_feature_determines_pronoun :
    selectPronoun .mass ≠ selectPronoun .count := by decide


-- ════════════════════════════════════════════════════
-- § 2. Concept DRef Projection: Island Escaping
-- ════════════════════════════════════════════════════

section IslandEscaping

variable {W E : Type*}

/-- Examples (5a,c), (25), (44–45): Concept drefs project past negation.

    (5a) *John doesn't own a dog. He is afraid of them. But Mary owns one.*
    (5c) *John doesn't own a dog. \*It is friendly.*

    In the DRT representation (25) and dynamic semantics (44–45), the concept
    dref x₂ for 'dog' is in the main box / presupposed in the input. After
    negation, x₂ persists (licensing *them₂*, *one₂*), but the entity dref
    x₃ is trapped under ¬∃ (blocking *\*it₃*). -/
theorem dog_concept_survives_negation
    {dogConcept : ConceptDRef W E}
    {φ : DSent W E}
    {g h : HAssign W E}
    (hDog : g 2 = .concept dogConcept)
    (hNovel : g 3 = .undef)
    (hNeg : dNeg φ g h) :
    h 2 = .concept dogConcept ∧ h 3 = .undef :=
  concept_entity_asymmetry hDog hNovel hNeg

end IslandEscaping


-- ════════════════════════════════════════════════════
-- § 3. End-to-End: "John doesn't own a dog" (44–45)
-- ════════════════════════════════════════════════════

section EndToEnd

/-- Concrete entity type for the worked example. -/
inductive Ent where | john | mary
  deriving DecidableEq, Repr

/-- Concrete world type. A world where John doesn't own a dog. -/
inductive Wld where | w₀
  deriving DecidableEq, Repr

/-- The concept 'dog' as a concept dref with [COUNT] feature.
    In this model, no entity satisfies the dog predicate (John doesn't own one). -/
def dogConcept : ConceptDRef Wld Ent where
  property := λ _ _ => false   -- no dogs in this model
  feature := .count

/-- Initial assignment for (44e): g₁=F(John), g₂=F(dog), F(C)(g₂).
    Following @cite{krifka-2026} (40g)/(44e): John's name presupposes
    dref 1 is anchored to John; the head noun *dog*₂ presupposes dref 2
    is anchored to the 'dog' concept with [COUNT] feature. -/
def g₀ : HAssign Wld Ent := λ n =>
  match n with
  | 1 => .entity .john
  | 2 => .concept dogConcept
  | _ => .undef

/-- Sentence meaning for "own [DP a₃ [NP dog]₂]": introduces entity dref
    at index 3, constrained to satisfy the concept property at index 2. -/
def ownADog : DSent Wld Ent := entityIntro 3 (λ g h =>
  g = h ∧ (g 2).liftConceptPred (λ c => c.property .w₀ (match g 3 with
    | .entity e => e | _ => .john)) = true)

/-- "John₁ doesn't own [DP a₃ [NP dog]₂]" as the negation of ownADog. -/
def doesntOwnADog : DSent Wld Ent := dNeg ownADog

/-- The negation is satisfiable in this model (no dogs exist).
    Output: g₀ = h (test), confirming no entity dref was introduced. -/
theorem negation_satisfiable :
    doesntOwnADog g₀ g₀ := by
  refine ⟨rfl, ?_⟩
  intro ⟨k, e, hBody⟩
  simp only [g₀, dogConcept, DRefVal.liftConceptPred] at hBody
  obtain ⟨hEq, hProp⟩ := hBody
  -- After update, g(2) = g₀(2) = .concept dogConcept, g(3) = .entity e
  -- The concept property returns false for all entities
  simp at hProp

/-- **Main result**: after "John doesn't own a dog", the concept dref
    for 'dog' at index 2 is accessible while the entity dref at index 3
    remains undefined. This is the concrete instantiation of the asymmetry
    predicted by @cite{krifka-2026} §4. -/
theorem concrete_concept_entity_asymmetry :
    ∀ h : HAssign Wld Ent,
      doesntOwnADog g₀ h →
      h 2 = .concept dogConcept ∧ h 3 = .undef :=
  λ _ hNeg => concept_entity_asymmetry rfl rfl hNeg

/-- The kind anaphor *them* selects [COUNT] for dogs, as expected. -/
theorem dog_kind_pronoun : selectPronoun dogConcept.feature = .they := rfl

end EndToEnd


-- ════════════════════════════════════════════════════
-- § 4. Concept vs Kind Anaphora (19a,b)
-- ════════════════════════════════════════════════════

/-- Anaphoric constructions that pick up concept drefs.

    @cite{krifka-2026} §3 distinguishes concept anaphors (which reuse the
    property directly) from kind anaphors (which derive kind individuals
    via ∩). Both pick up concept drefs, but they do different things.

    The distinction is testable via examples like (19a,b):
    (19a) *John didn't get a dog from the animal shelter downtown.
           He is afraid of them.* — kind anaphora (OK: dogs-as-kind)
    (19b) *John didn't get a dog from the animal shelter downtown.
           But Mary got one.* — concept anaphora (OK: a dog-from-the-shelter) -/
inductive AnaphoricConstruction where
  | emptyNP   -- *one*, empty NP: picks up concept property directly
  | emptyPP   -- partitive *of them*: picks up concept for part-whole
  | kindPron  -- *it*[MASS], *they*[COUNT]: derives kind via ∩(⊔)P
  deriving DecidableEq, Repr

/-- Whether a construction derives a kind individual or reuses the property. -/
def derivesKind : AnaphoricConstruction → Bool
  | .kindPron => true
  | .emptyNP  => false
  | .emptyPP  => false

/-- Kind pronouns derive kinds; concept anaphors (*one*, empty NP/PP) don't.
    This distinction explains (19a) vs (19b): "dogs from the animal shelter"
    doesn't name a kind (cf. @cite{carlson-1977}), so kind anaphora yields the
    general dog-kind, while concept anaphora preserves the full NP property. -/
theorem kind_vs_concept_distinction :
    derivesKind .kindPron = true ∧
    derivesKind .emptyNP = false ∧
    derivesKind .emptyPP = false :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.Reference.Studies.Krifka2026
