import Linglib.Semantics.Kinds.NominalMappingParameter
import Linglib.Semantics.Dynamic.DiscourseRef
import Linglib.Semantics.Dynamic.Update
import Linglib.Core.Logic.Assignment
import Linglib.Features.MassCount

/-!
# Anaphora for Concepts, Kinds, and Parts
[krifka-2026]

Head nouns introduce presupposed **concept discourse referents** — properties
tagged [MASS]/[COUNT] — which project past anaphoric islands (in Krifka's
extended sense: negation, modals, conditionals), while entity drefs introduced
by indefinites under negation are trapped. Kind anaphors pick up concept drefs
and derive kind individuals via [chierchia-1998]'s ∩ from
`Semantics/Kinds/NominalMappingParameter`: ⟦it⟧ = λP[MASS] λi.∩P(i),
⟦they⟧ = λP[COUNT] λi.∩⊔P(i) (17a,b). The dynamic layer instantiates the
substrate `Update`/`test`/`dneg` algebra of `Semantics/Dynamic/Connectives`
at heterogeneous assignments over `DRefVal`.

Negation here is the paper's VP negation ⟦doesn't⟧ (44b), `test (∼φ)`; the
sentential ⟦NEG⟧ (34) additionally restricts the negated existential to
extensions g≤k, and both carry a world-time index — differences orthogonal to
projection, which needs only that negation is a test. The paper derives the
concept dref's input-presupposition compositionally from the head noun's
partial (strong-Kleene) lexical entry (40d); that pipeline is not formalized,
so the projection theorems take the input conditions as hypotheses. Cf.
[hofmann-2025] (`Studies/Hofmann2025.lean`) for the neighboring account of
entity-dref accessibility under negation via nonveridical continuations.

## Main declarations

- `selectPronoun`, `selectKindAnaphor`, `selectKindAnaphor_count_eq_mass`:
  [MASS]/[COUNT]-driven pronoun and kind-operator selection, with absorption
- `HAssign`, `entityIntro`: heterogeneous assignments and indefinite update
- `concept_survives_test`, `entity_trapped_by_test`,
  `concept_entity_asymmetry`: projection past island operators
- an end-to-end model of *John₁ doesn't own [DP a₃ [NP dog]₂]* (44–45)
-/

namespace Krifka2026

open Semantics.Kinds.NMP (Property Kind IsMass
  kindAnaphorMass kindAnaphorCount kindAnaphorCount_mass)
open Semantics.Dynamic.Core.DynProp (Update Condition test dneg eq_of_test)
open scoped Semantics.Dynamic.Core.DynProp

/-! ### Concept drefs and heterogeneous dref values ([krifka-2026] §4)

Paper-specific substrate: concept discourse referents (property + count
feature), the heterogeneous `DRefVal` universe, and concept-variable
indices. -/
-- ════════════════════════════════════════════════════
-- Concept Discourse Referents
-- ════════════════════════════════════════════════════

-- Mass/Count Feature: uses `MassCount` from `Features.MassCount`.

/--
A concept discourse referent value: a property annotated with a
morphosyntactic count feature.

Introduced by the NP of an antecedent DP. For example, *dog* in
*John owns a dog* introduces a concept dref anchored to the property
`λi.λx[dog(i)(x)]` with feature [COUNT].

Kind anaphors pick up concept drefs and derive kind individuals
via Chierchia's ∩ (down) operator:
- ⟦it⟧   = λP[MASS].  λi. ∩P(i)
- ⟦they⟧ = λP[COUNT]. λi. ∩(⊔P)(i)

The ⊔-closure for count nouns introduces pluralization, allowing for
the number mismatch between *a spider* (singular) and *they* (plural).
For mass nouns, ⊔-closure is vacuous (mass predicates are already
cumulative), so the singular *it* is used.
-/
structure ConceptDRef (W E : Type*) where
  /-- The property this concept is anchored to: λi.λx[P(i)(x)] -/
  property : W → E → Bool
  /-- Morphosyntactic count feature -/
  feature : MassCount

/--
Values that discourse referent indices can map to.

Standard dynamic semantics restricts assignments to map indices to
entities. [krifka-2026] §4 extends this: assignments are partial
functions from ℕ to a heterogeneous universe including entities,
concepts (properties with count features), and world-time indices.

- `.entity e`: an individual referent (standard entity dref)
- `.concept c`: a concept dref — the NP property with [MASS]/[COUNT]
- `.index w`: a world-time index dref
- `.undef`: index not in the domain (models assignment partiality)

Key property: concept drefs project past operators like negation,
disjunction, and modals — they are introduced in the global
assignment, not in local sub-assignments. This is what licenses
kind anaphora out of anaphoric islands:

  *John doesn't own a dog. He is afraid of them.*

The entity dref for *a dog* is trapped under negation, but the
concept dref for 'dog' projects to the global context.
-/
inductive DRefVal (W E : Type*) where
  | entity : E → DRefVal W E
  | concept : ConceptDRef W E → DRefVal W E
  | index : W → DRefVal W E
  | undef : DRefVal W E

namespace DRefVal

variable {W E : Type*}

/-- Extract entity value, if present. -/
def getEntity : DRefVal W E → Option E
  | .entity e => some e
  | _ => none

/-- Extract concept dref, if present. -/
def getConcept : DRefVal W E → Option (ConceptDRef W E)
  | .concept c => some c
  | _ => none

/-- Extract world-time index, if present. -/
def getIndex : DRefVal W E → Option W
  | .index w => some w
  | _ => none

/-- Is this index in the domain of the assignment? -/
def isDefined : DRefVal W E → Prop
  | .undef => False
  | _ => True

instance : DecidablePred (@isDefined W E) :=
  fun d => by unfold isDefined; cases d <;> infer_instance

/-- Lift a predicate on entities to DRefVal (false for non-entities). -/
def liftEntityPred (p : E → Bool) : DRefVal W E → Bool
  | .entity e => p e
  | _ => false

/-- Lift a predicate on concepts to DRefVal (false for non-concepts). -/
def liftConceptPred (p : ConceptDRef W E → Bool) : DRefVal W E → Bool
  | .concept c => p c
  | _ => false

end DRefVal

/--
A concept variable (names a concept dref).

Concept variables are indices into the assignment that map to
`ConceptDRef` values — properties annotated with [MASS]/[COUNT].
-/
structure CVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/-! ### Kind pronoun and kind-operator selection -/

/-- Kind-anaphoric pronouns, selected by the [MASS]/[COUNT] feature. -/
inductive KindPronoun where
  | it    -- singular, selects [MASS] concepts
  | they  -- plural, selects [COUNT] concepts
  deriving DecidableEq, Repr

/-- Select kind-anaphoric pronoun from the count feature.

    [krifka-2026] (17a,b):
    - ⟦it⟧  = λP[MASS]  λi.∩P(i)
    - ⟦they⟧ = λP[COUNT] λi.∩⊔P(i) -/
def selectPronoun : MassCount → KindPronoun
  | .mass => .it
  | .count => .they

/-- The semantic side of (17a,b): *it* applies ∩ directly, *they* applies
    plural closure ⊔ before ∩. -/
def selectKindAnaphor {World Atom : Type} (feature : MassCount)
    (P : Property World Atom) : Kind World Atom :=
  match feature with
  | .mass => kindAnaphorMass World Atom P
  | .count => kindAnaphorCount World Atom P

/-- For mass properties both anaphor paths yield the same kind, by
    [krifka-2026]'s absorption rule ⊔⊔S = ⊔S: plural closure is a no-op on
    cumulative properties, so for mass concepts the [MASS]/[COUNT] feature's
    only role is selecting pronoun morphology. -/
theorem selectKindAnaphor_count_eq_mass {World Atom : Type}
    (P : Property World Atom) (hMass : IsMass World Atom P) :
    selectKindAnaphor .count P = selectKindAnaphor .mass P :=
  kindAnaphorCount_mass World Atom P hMass

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

/-! ### Concept dref projection past anaphoric islands -/

section IslandEscaping

variable {W E : Type*}

/-- Heterogeneous assignment: drefs valued in entities, concepts, or indices
    ([krifka-2026] §4). Partiality is modeled by `DRefVal.undef`, so this is
    `Core.Assignment (DRefVal W E)` rather than `Core.PartialAssign`. -/
abbrev HAssign (W E : Type*) := Core.Assignment (DRefVal W E)

/-- Existential introduction of an entity dref at index `n`, as by the indexed
    determiner *a₃* in (40c) — minus the falls-under-the-concept condition,
    which is delegated to `body`, and with novelty (`g n = .undef`) as an
    external hypothesis rather than built into the extension relation g<₃k. -/
def entityIntro (n : Nat) (body : Update (HAssign W E)) : Update (HAssign W E) :=
  λ g h => ∃ e : E, body (Function.update g n (.entity e)) h

/-- Island operators are tests, and tests preserve every dref of the input
    assignment. Negation, implication, and disjunction all return a
    `Condition` re-entering the update algebra via `test`, so this single
    fact covers [krifka-2026]'s whole island list at once. -/
theorem test_apply_eq {C : Condition (HAssign W E)} {g h : HAssign W E}
    (hTest : test C g h) (n : Nat) : h n = g n :=
  congrFun (eq_of_test hTest).symm n

/-- **Concept drefs survive islands** ((5a), (25), (44–45)): a concept dref
    presupposed in the input is still anchored in the output of any test.
    The presupposition is a hypothesis here; the paper derives it from the
    head noun's partial lexical entry (40d). -/
theorem concept_survives_test {n : Nat} {c : ConceptDRef W E}
    {C : Condition (HAssign W E)} {g h : HAssign W E}
    (hPresup : g n = .concept c) (hTest : test C g h) :
    h n = .concept c :=
  (test_apply_eq hTest n).trans hPresup

/-- **Entity drefs are trapped by islands** ((5c)): a dref novel in the input
    (introduced only inside the island's ¬∃k) is still undefined in the
    output. -/
theorem entity_trapped_by_test {n : Nat}
    {C : Condition (HAssign W E)} {g h : HAssign W E}
    (hNovel : g n = .undef) (hTest : test C g h) :
    h n = .undef :=
  (test_apply_eq hTest n).trans hNovel

/-- The concept/entity asymmetry under negation `test (∼φ)` ((44e)): the
    concept dref persists, the entity dref does not. Both conjuncts are
    instances of `test_apply_eq` — the asymmetry is carried entirely by where
    the hypotheses place the two conditions (input presupposition vs input
    novelty), which is [krifka-2026]'s point. -/
theorem concept_entity_asymmetry {nC nE : Nat} {c : ConceptDRef W E}
    {φ : Update (HAssign W E)} {g h : HAssign W E}
    (hPresup : g nC = .concept c) (hNovel : g nE = .undef)
    (hNeg : test (∼φ) g h) :
    h nC = .concept c ∧ h nE = .undef :=
  ⟨concept_survives_test hPresup hNeg, entity_trapped_by_test hNovel hNeg⟩

/-- Examples (5a,c), (25), (44–45): concept drefs project past negation.

    (5a) *John doesn't own a dog. He is afraid of them. But Mary owns one.*
    (5c) *John doesn't own a dog. \*It is friendly.*

    In the DRT representation (25) and dynamic semantics (44–45), the concept
    dref x₂ for 'dog' is in the main box / presupposed in the input. After
    negation, x₂ persists (licensing *them₂*, *one₂*), but the entity dref
    x₃ is trapped under ¬∃ (blocking *\*it₃*). -/
theorem dog_concept_survives_negation
    {dogConcept : ConceptDRef W E}
    {φ : Update (HAssign W E)}
    {g h : HAssign W E}
    (hDog : g 2 = .concept dogConcept)
    (hNovel : g 3 = .undef)
    (hNeg : test (∼φ) g h) :
    h 2 = .concept dogConcept ∧ h 3 = .undef :=
  concept_entity_asymmetry hDog hNovel hNeg

end IslandEscaping

/-! ### End-to-end: *John doesn't own a dog* (44–45) -/

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
    Following [krifka-2026] (40g)/(44e): John's name presupposes
    dref 1 is anchored to John; the head noun *dog*₂ presupposes dref 2
    is anchored to the 'dog' concept with [COUNT] feature. -/
def g₀ : HAssign Wld Ent := λ n =>
  match n with
  | 1 => .entity .john
  | 2 => .concept dogConcept
  | _ => .undef

/-- Sentence meaning for "own [DP a₃ [NP dog]₂]": introduces entity dref
    at index 3, constrained to satisfy the concept property at index 2. -/
def ownADog : Update (HAssign Wld Ent) := entityIntro 3 (λ g h =>
  g = h ∧ (g 2).liftConceptPred (λ c => c.property .w₀ (match g 3 with
    | .entity e => e | _ => .john)) = true)

/-- "John₁ doesn't own [DP a₃ [NP dog]₂]": the paper's VP negation
    ⟦doesn't⟧ (44b) is the substrate test of dynamic negation. -/
def doesntOwnADog : Update (HAssign Wld Ent) := test (∼ownADog)

/-- The negation is satisfiable in this model (no dogs exist).
    Output: g₀ = h (test), confirming no entity dref was introduced. -/
theorem negation_satisfiable : doesntOwnADog g₀ g₀ := by
  refine ⟨rfl, ?_⟩
  rintro ⟨k, e, -, hProp⟩
  rw [Function.update_of_ne (by decide : (2 : Nat) ≠ 3),
      show g₀ 2 = .concept dogConcept from rfl] at hProp
  exact Bool.noConfusion hProp

/-- **Main result**: after "John doesn't own a dog", the concept dref
    for 'dog' at index 2 is accessible while the entity dref at index 3
    remains undefined. This is the concrete instantiation of the asymmetry
    predicted by [krifka-2026] §4. -/
theorem concrete_concept_entity_asymmetry :
    ∀ h : HAssign Wld Ent,
      doesntOwnADog g₀ h →
      h 2 = .concept dogConcept ∧ h 3 = .undef :=
  λ _ hNeg => concept_entity_asymmetry rfl rfl hNeg

/-- The kind anaphor *them* selects [COUNT] for dogs, as expected. -/
theorem dog_kind_pronoun : selectPronoun dogConcept.feature = .they := rfl

end EndToEnd

/-! ### Concept vs kind anaphora (19a,b) -/

/-- Anaphoric constructions that pick up concept drefs.

    [krifka-2026] §3 distinguishes concept anaphors (which reuse the
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
    doesn't name a kind (cf. [carlson-1977]), so kind anaphora yields the
    general dog-kind, while concept anaphora preserves the full NP property. -/
theorem kind_vs_concept_distinction :
    derivesKind .kindPron = true ∧
    derivesKind .emptyNP = false ∧
    derivesKind .emptyPP = false :=
  ⟨rfl, rfl, rfl⟩

end Krifka2026
