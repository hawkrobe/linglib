import Linglib.Phenomena.Morphology.CategoryChanging
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Properties

/-!
# Categorial Features ↔ Category-Changing Morphology

@cite{panagiotidis-2015} @cite{marantz-1997}Connects the theory-side predictions of @cite{panagiotidis-2015} — substantive
categorial features [N] and [V] hosted on categorizer heads — to the empirical
data on category-changing morphology in English.

## What this bridge proves

1. **Categorizer–LexCat correspondence**: Each theory-side categorizer (v, n, a)
   maps to exactly one empirical lexical category (verb, noun, adjective).

2. **Feature predictions**: The categorial features [N]/[V] on each categorizer
   correctly predict the interpretive perspective of the resulting category —
   nouns have sortal perspective ([N]), verbs have temporal perspective ([V]),
   adjectives have both ([N, V]).

3. **EP well-formedness**: Each categorizer extends its lexical anchor into a
   well-formed EP (A→a, N→n, V→v).

4. **Categorizer parallelism**: All three categorizers sit at the same F-level
   (F1 in Grimshaw's system), formalizing Panagiotidis's claim that
   categorization is a uniform operation across category families.

## Derivational chain

```
ExtendedProjection/Basic.lean (CategorialFeatures, isCategorizer, categorialFeatures)
    ↓
THIS BRIDGE FILE
    ↓
Phenomena/Morphology/CategoryChanging.lean (RootFamily, LexCat)
```

-/

namespace Phenomena.Morphology.Studies.Panagiotidis2015

open Minimalism
open Phenomena.Morphology.CategoryChanging

-- ════════════════════════════════════════════════════════════════
-- § 1: Categorizer ↔ LexCat Correspondence
-- ════════════════════════════════════════════════════════════════

/-- Map a Minimalist categorizer to the empirical lexical category
    of the word it produces. This is the core link between the theory
    (Cat.v, Cat.n, Cat.a) and the data (LexCat). -/
def categorizerToLexCat : Cat → Option LexCat
  | .v => some .verb
  | .n => some .noun
  | .a => some .adjective
  | _  => none

/-- Map an empirical lexical category to its theory-side categorizer. -/
def lexCatToCategorizer : LexCat → Cat
  | .verb      => .v
  | .noun      => .n
  | .adjective => .a

/-- The mapping is a partial bijection: lexCat → categorizer → lexCat roundtrips. -/
theorem roundtrip (c : LexCat) :
    categorizerToLexCat (lexCatToCategorizer c) = some c := by
  cases c <;> rfl

/-- Every categorizer maps to some LexCat. -/
theorem categorizers_have_lexcat :
    categorizerToLexCat .v = some .verb ∧
    categorizerToLexCat .n = some .noun ∧
    categorizerToLexCat .a = some .adjective := ⟨rfl, rfl, rfl⟩

/-- Non-categorizers don't map to any LexCat. -/
theorem non_categorizers_no_lexcat :
    categorizerToLexCat .V = none ∧
    categorizerToLexCat .N = none ∧
    categorizerToLexCat .A = none ∧
    categorizerToLexCat .T = none ∧
    categorizerToLexCat .D = none := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Feature Predictions
-- ════════════════════════════════════════════════════════════════

/-- Does a categorizer produce a category with sortal perspective?
    Panagiotidis §4.3: [N] = sortal perspective / referentiality. Items bearing [N] have the capacity to introduce
    discourse referents (nouns, adjectives) — items lacking [N] do not
    (verbs). -/
def producesReferential (c : Cat) : Bool :=
  (categorialFeatures c).hasN

/-- Does a categorizer produce a category with temporal perspective?
    Panagiotidis §4.3: [V] = temporal perspective / eventivity. Items
    bearing [V] can anchor to time/events (verbs, adjectives) — items
    lacking [V] do not have temporal anchoring (nouns). -/
def producesPredicative (c : Cat) : Bool :=
  (categorialFeatures c).hasV

/-- Nouns have sortal but not temporal perspective: n bears [N] only. -/
theorem noun_referential_not_predicative :
    producesReferential .n = true ∧ producesPredicative .n = false := by decide

/-- Verbs have temporal but not sortal perspective: v bears [V] only. -/
theorem verb_predicative_not_referential :
    producesPredicative .v = true ∧ producesReferential .v = false := by decide

/-- Adjectives have both sortal and temporal perspective: a bears [N, V]. -/
theorem adjective_both :
    producesReferential .a = true ∧ producesPredicative .a = true := by decide

/-- The noun–verb asymmetry: nouns have sortal but not temporal perspective;
    verbs have temporal but not sortal perspective. Adjectives have both.
    This follows from the [N]/[V] feature distribution on categorizers. -/
theorem referential_predicative_asymmetry :
    -- Nouns: [N], not [V]
    (categorialFeatures .n).hasN = true ∧ (categorialFeatures .n).hasV = false ∧
    -- Verbs: [V], not [N]
    (categorialFeatures .v).hasV = true ∧ (categorialFeatures .v).hasN = false ∧
    -- Adjectives: [N] and [V]
    (categorialFeatures .a).hasN = true ∧ (categorialFeatures .a).hasV = true := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 3: EP Well-Formedness
-- ════════════════════════════════════════════════════════════════

/-- Each categorizer forms a well-formed EP with its lexical anchor:
    V→v, N→n, A→a are all category-consistent and F-monotone. -/
theorem all_categorizer_eps_wellformed :
    (allCategoryConsistent [Cat.V, Cat.v] = true ∧ allFMonotone [Cat.V, Cat.v] = true) ∧
    (allCategoryConsistent [Cat.N, Cat.n] = true ∧ allFMonotone [Cat.N, Cat.n] = true) ∧
    (allCategoryConsistent [Cat.A, Cat.a] = true ∧ allFMonotone [Cat.A, Cat.a] = true) := by
  decide

/-- The F-level jump from lexical head to categorizer is exactly 1 in all cases.
    The uniformity of categorization is Panagiotidis's prediction (§4.4–§4.5);
    the F-value encoding is @cite{grimshaw-2005}'s EP architecture. -/
theorem categorization_uniform_fstep :
    fValue .v - fValue .V = 1 ∧
    fValue .n - fValue .N = 1 ∧
    fValue .a - fValue .A = 1 := by decide

-- ════════════════════════════════════════════════════════════════
-- § 4: Categorizer Parallelism
-- ════════════════════════════════════════════════════════════════

/-- All categorizers sit at exactly F1 (in Grimshaw's system), parallel
    across families. Panagiotidis's core claim: v, n, a are structurally
    parallel — they differ only in which interpretable features they bear. -/
theorem categorizers_parallel_at_f1 :
    fValue .v = 1 ∧ fValue .n = 1 ∧ fValue .a = 1 := by decide

/-- The categorizers are in their respective families. -/
theorem categorizers_in_own_families :
    catFamily .v = .verbal ∧ catFamily .n = .nominal ∧ catFamily .a = .adjectival := by
  decide

/-- Category-changing morphology = changing the categorizer.
    The same root under different categorizers yields items in
    different EP families — this is what it means to "change category." -/
theorem different_categorizers_different_families :
    catFamily .v ≠ catFamily .n ∧
    catFamily .n ≠ catFamily .a ∧
    catFamily .v ≠ catFamily .a := by decide

-- ════════════════════════════════════════════════════════════════
-- § 5: Data–Theory Connection
-- ════════════════════════════════════════════════════════════════

/-- A root family is predicted to be tricategorial iff categorization by
    each of v, n, a is possible. Since all three categorizers are available
    in English, any root can in principle surface in all three categories. -/
theorem three_categorizers_predict_tricategoriality :
    isCategorizer .v ∧ isCategorizer .n ∧ isCategorizer .a := by decide

/-- The √DESTROY family's three categories correspond to three categorizers. -/
theorem destroy_matches_categorizers :
    destroy.hasCategory .verb = true ∧
    destroy.hasCategory .noun = true ∧
    destroy.hasCategory .adjective = true := by native_decide

/-- Every root family in the sample has a form for each categorizer's category. -/
theorem all_families_match_all_categorizers :
    allFamilies.all (fun rf =>
      rf.hasCategory .verb && rf.hasCategory .noun && rf.hasCategory .adjective) = true := by
  native_decide

end Phenomena.Morphology.Studies.Panagiotidis2015
