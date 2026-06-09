/-
# CCG Analysis of Non-Constituent Coordination
[pickering-barry-1991] [steedman-2000]

## The Phenomenon

In "John likes and Mary hates beans", the strings "John likes" and
"Mary hates" are coordinated. But in traditional phrase structure:

    [S [NP John] [VP likes ___]] and [S [NP Mary] [VP hates ___]] beans

"John likes" is NOT a constituent - it's NP + part of VP.
Yet native speakers accept this sentence as grammatical.

## Qualitative Empirical Facts

1. Non-constituent coordination is GRAMMATICAL
2. Non-constituent coordination is HARDER TO PROCESS than standard coordination

## CCG's Solution

CCG shows that "John likes" IS a constituent with category S/NP:
- John: NP type-raises to S/(S\NP)
- likes: (S\NP)/NP
- John likes: S/(S\NP) ∘ (S\NP)/NP = S/NP (forward composition)

Both conjuncts have category S/NP, so they can coordinate normally.

-/

import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.Interface
import Linglib.Fragments.English.Toy

namespace Steedman2000

open CCG
open Semantics.Montague

/-- Theory-neutral data: a non-constituent coordination sentence
paired with its semantically equivalent fully-spelled-out version.
Both are grammatical; native speakers judge them to have the same
truth conditions. (Originally in `Coordination/Data.lean`; inlined
0.230.270 per the provenance-tracking policy.) -/
structure SemanticEquivalence where
  /-- The non-constituent coordination sentence -/
  sentence : List String
  /-- The semantically equivalent spelled-out version -/
  equivalentTo : List String
  /-- Both are grammatical -/
  bothGrammatical : Bool := true
  deriving Repr

/-- "John likes and Mary hates beans" ≡
"John likes beans and Mary hates beans" — the canonical
non-constituent coordination test pair ([steedman-2000]). -/
def johnLikesAndMaryHatesBeans : SemanticEquivalence :=
  { sentence := ["John", "likes", "and", "Mary", "hates", "beans"]
  , equivalentTo := ["John", "likes", "beans", "and", "Mary", "hates", "beans"] }

-- Empirical Fact 1: Non-constituent coordination is GRAMMATICAL

-- CCG derives "John likes and Mary hates beans" with category S
theorem nonConstituentCoord_is_grammatical :
    john_likes_and_mary_hates_beans.cat = some S := rfl

-- CCG also derives standard coordination
theorem standardCoord_is_grammatical :
    john_sleeps.cat = some S := rfl

-- Empirical Fact 2: Non-constituent coordination is HARDER TO PROCESS

/-
Processing difficulty correlates with the number of combinatory operations.
Non-constituent coordination requires MORE operations than standard sentences.
-/

def john_sleeps_and_mary_sleeps : DerivStep :=
  .coord
    (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
    (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩))

#guard john_sleeps.opCount == 1
#guard john_sleeps_and_mary_sleeps.opCount == 3
#guard john_likes_and_mary_hates_beans.opCount == 8

-- THEOREM: CCG predicts non-constituent coordination is harder to process
theorem nonConstituentCoord_harder_than_standard :
    john_sleeps_and_mary_sleeps.opCount < john_likes_and_mary_hates_beans.opCount := by
  native_decide

-- THEOREM: Standard coordination is harder than simple sentences
theorem standardCoord_harder_than_simple :
    john_sleeps.opCount < john_sleeps_and_mary_sleeps.opCount := by
  native_decide

-- Why This Matters

/-
CCG makes two correct qualitative predictions:

1. GRAMMATICALITY: Non-constituent coordination is derivable
   - Other theories need special mechanisms (ATB movement, ellipsis, etc.)
   - CCG handles it with the same rules used everywhere else

2. PROCESSING DIFFICULTY: More operations = harder to process
   - This connects to surprisal-based and memory-based processing models
   - The extra type-raising and composition operations have a cost

The theorems above show that CCG's predictions MATCH the empirical facts.
This is the syntax-to-processing linking function in action.
-/

-- Empirical Fact 3: The SEMANTIC INTERPRETATION is Conjunctive

/-
The empirical observation (from Phenomena/Coordination/Data.lean):
  "John likes and Mary hates beans" means likes(beans, john) ∧ hates(beans, mary)

CCG's prediction: the compositional semantics yields this interpretation
via type-raising + composition + generalized conjunction.
-/

-- Toy semantic lexicon over the toy English fragment

/-- The toy semantic lexicon for CCG derivations. -/
def toySemLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  -- Common noun phrases (using pizza entity as placeholder)
  | "beans", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "likes", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩  -- using sees_sem as placeholder
  | "hates", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩  -- using sees_sem as placeholder
  | _, _ => none

/-- Interpretation of "John sleeps" produces the correct truth value. -/
theorem john_sleeps_interp_correct :
    getMeaning (john_sleeps.interp toySemLexicon) = some True := rfl

/-- Interpretation of "John sees Mary" produces the correct truth value. -/
theorem john_sees_mary_interp_correct :
    getMeaning (john_sees_mary.interp toySemLexicon) = some True := rfl

-- Type-raising and composition

/-- Type-raised "John": NP → S/(S\NP) via forward type-raising. -/
def john_typeraised : DerivStep := .ftr (.lex ⟨"John", NP⟩) S

#guard (john_typeraised.interp toySemLexicon).isSome

/-- "John sees Mary" with a type-raised subject: the raised subject uses
    FORWARD application (it is S/(S\NP), seeking S\NP to its right). -/
def john_sees_mary_via_tr : DerivStep :=
  .fapp john_typeraised (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

/-- The type-raised derivation produces the same truth value. -/
theorem john_sees_mary_via_tr_correct :
    getMeaning (john_sees_mary_via_tr.interp toySemLexicon) = some True := rfl

/-- "John likes" as S/NP via type-raising + composition — the constituent
    that coordinates with "Mary hates" in "John likes and Mary hates beans". -/
def john_likes_composed : DerivStep :=
  .fcomp john_typeraised (.lex ⟨"likes", TV⟩)

#guard (john_likes_composed.interp toySemLexicon).isSome
#guard (john_likes_and_mary_hates.interp toySemLexicon).isSome
#guard (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome

/--
**LINKING THEOREM: CCG derives both sides of the semantic equivalence**

The phenomena-level data (from Phenomena/Coordination/Data.lean):
  "John likes and Mary hates beans" ≡ "John likes beans and Mary hates beans"

CCG's prediction: both sentences derive and receive equivalent meanings.

This theorem proves CCG derives the non-constituent coordination sentence.
(The full equivalence proof would require implementing the spelled-out derivation too.)
-/
theorem ccg_derives_nonconstituent_coordination :
    -- The phenomena data specifies a semantic equivalence
    johnLikesAndMaryHatesBeans.bothGrammatical = true ∧
    -- CCG derives the non-constituent coordination sentence
    john_likes_and_mary_hates_beans.cat = some S ∧
    -- CCG's compositional semantics produces a well-formed interpretation
    (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome = true := by
  constructor
  · rfl  -- The phenomena data specifies both are grammatical
  constructor
  · rfl  -- CCG derives category S
  · native_decide  -- CCG's derivation succeeds

/-- The predicate "John likes and Mary hates" (category S/NP) evaluated
    at an entity. -/
def coordMeaningAt (e : ToyEntity) : Option Prop :=
  match john_likes_and_mary_hates.interp toySemLexicon with
  | some ⟨.rslash (.atom .S) (.atom .NP), m⟩ => some (m e)
  | _ => none

/-- The pointwise conjunction of "John likes" and "Mary hates" at an entity. -/
def pointwiseConjAt (e : ToyEntity) : Option Prop :=
  match john_likes.interp toySemLexicon, mary_hates.interp toySemLexicon with
  | some ⟨.rslash (.atom .S) (.atom .NP), m₁⟩, some ⟨.rslash (.atom .S) (.atom .NP), m₂⟩ =>
      some (m₁ e ∧ m₂ e)
  | _, _ => none

/--
**THE SUBSTANTIVE SEMANTIC THEOREM**

CCG derives the meaning of "John likes and Mary hates beans" as the
conjunction of two predications:

  ⟦John likes and Mary hates beans⟧ = ⟦John likes⟧(beans) ∧ ⟦Mary hates⟧(beans)

This is non-trivial because it requires:
1. Type-raising John and Mary to S/(S\NP)
2. Composing with the verbs to get S/NP
3. Coordinating with generalized conjunction (pointwise ∧)
4. Applying to the shared object

The theorem proves CCG's compositional semantics matches the empirical observation.
-/
theorem ccg_coordination_semantics_correct :
    -- The coordinated meaning is pointwise conjunction
    ∀ e : ToyEntity,
      coordMeaningAt e = pointwiseConjAt e := by
  intro e
  cases e <;> rfl

/-- The truth value of "John likes and Mary hates beans" is the conjunction
    of the two predications (in the toy model, likes = hates = sees). -/
theorem coordination_truth_conditions_correct :
    getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon) =
      some (ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.john ∧
            ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.mary) := rfl

-- Summary: CCG Captures Non-Constituent Coordination

/-
## What CCG Explains

| Empirical Fact                        | CCG Prediction                    | Theorem                                |
|---------------------------------------|-----------------------------------|----------------------------------------|
| Sentence is grammatical               | Derivation yields category S     | nonConstituentCoord_is_grammatical     |
| Processing is harder than standard    | More combinatory operations      | nonConstituentCoord_harder_than_standard|
| Interpretation is conjunctive         | Generalized conjunction applies  | ccg_coordination_semantics_correct     |

## Why This Matters

Other theories require special mechanisms for non-constituent coordination:
- Transformational grammar: Across-The-Board movement
- GPSG: Metarules for coordination
- LFG: Functional uncertainty

CCG needs NO special mechanism. The same type-raising and composition rules
that handle word order flexibility also enable non-constituent coordination.
The interpretation falls out automatically from generalized conjunction.

This is the hallmark of a good theory: diverse phenomena explained by
the same core mechanisms, with correct empirical predictions.
-/

end Steedman2000
