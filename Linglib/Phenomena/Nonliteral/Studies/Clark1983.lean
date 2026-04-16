import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Clark 1983 — Making Sense of Nonce Sense
@cite{clark-1983} @cite{clark-clark-1979}

Clark, Herbert H. (1983). Making sense of nonce sense. In G.B. Flores d'Arcais
& R.J. Jarvella (Eds.), *The Process of Language Understanding*, pp. 297–331.
John Wiley & Sons.

## Core Argument

Traditional parsers assume the **sense-selection assumption**: each word has a
finite list of senses in the lexicon, and the parser selects among them. Clark
argues this assumption is untenable because **contextual expressions** — words
used with nonce senses — are ubiquitous in ordinary language. Their possible
senses are **non-denumerable**: no finite list can capture them.

Clark proposes replacing sense-selection with **sense-creation**: listeners
construct meanings on-the-fly by inferring the speaker's intentions from mutual
knowledge. The central proposal is the **intentional view of parsing** (p. 324):
parsing is not selecting sentence meanings from a finite list, but
reconstructing the speaker's **hierarchy of goals** — the plan that maps each
constituent of the utterance to a subgoal the speaker accomplishes by uttering
it.

The argument proceeds in three stages:
1. Demonstrating that contextual expressions are ubiquitous and non-denumerable
2. Showing that contextual expressions share five properties with indirect
   illocutionary acts (simultaneous meanings, logical priority, literalness,
   non-denumerability, contextuality)
3. Proposing that both are understood via the same mechanism: goal hierarchies

Traditional parsers fail in two ways (p. 299):
- **Non-parsing**: the parser finds no interpretation at all (e.g., *Our
  electric typewriter got married* — the parser marks it ungrammatical).
- **Mis-parsing**: the parser finds *an* interpretation, but the wrong one
  (e.g., *Stereos are a dime a dozen* — parsed as "phonographs are very
  common" instead of "people who own phonographs are very common").

## Connection to LU-RSA

@cite{bergen-levy-goodman-2016}'s Lexical Uncertainty RSA operationalizes one
dimension of Clark's proposal: the listener marginalizes over possible lexica
rather than selecting from a fixed one. This captures Clark's insight that the
sense space is open-ended. However, LU-RSA does not capture the
goal-hierarchical structure of Clark's intentional parser — it models meaning
uncertainty but not the hierarchical intention reconstruction that Clark argues
is the mechanism underlying comprehension of both conventional and innovative
expressions.

## Connection to DM

The morphological operation underlying denominal verbs is
`Recategorization.denominal` in DM (@cite{harley-2014}). Clark's insight is
that this syntactic operation (n → v) is trivial; the hard part is computing
the resulting verb's meaning. DM's List 3 (Encyclopedia entries) would need
infinitely many entries for nonce denominals — precisely Clark's argument
against lexical rules.

## Structure

- §1: Sense and reference: fixed vs. shifting (Table 9.1)
- §2: Ten types of contextual expressions (Table 9.2)
- §3: The sense-selection/creation distinction
- §4: Non-denumerability of nonce senses
- §5: Five properties shared with indirect illocutionary acts
- §6: Goal hierarchies and the intentional view of parsing
- §7: The Innovative Denominal Verb Convention
- §8: Bridge to LU-RSA
- §9: Bridge to DM recategorization
- §10: The *stereos* example (Arlene vs Bombeck, pp. 326-327)
- §11: Bridge to indirect speech acts
- §12: ContextualMeaning — the deeper formal principle
-/

namespace Clark1983

open Core.CommonGround
open Morphology.DM (Categorizer Recategorization CategorizedRoot
  denominal_requires_n recategorization_changes_category)

-- ════════════════════════════════════════════════════════════════
-- §1. Sense and Reference: Fixed vs. Shifting (Table 9.1)
-- ════════════════════════════════════════════════════════════════

/-! ## The Fixed/Shifting Classification

Clark's Table 9.1 (p. 300) classifies expressions by a 2x2 matrix:

|                  | Fixed                    | Shifting                  |
|------------------|--------------------------|---------------------------|
| **Sense**        | Purely intensional expr  | Contextual expression     |
|                  | (e.g., *bachelor*)       | (e.g., *to teapot*)       |
| **Reference**    | Proper name              | Indexical expression       |
|                  | (e.g., *George Washington*)| (e.g., *he*)             |

Each expression type occupies one cell of the matrix. The classifying
property is which aspect of meaning (sense or reference) is salient for
that type, and whether it is fixed or shifting. -/

/-- Whether an aspect of meaning is fixed across contexts or shifts. -/
inductive Alterability where
  | fixed     -- same across all contexts of use
  | shifting  -- varies with time, place, and circumstances
  deriving DecidableEq, Repr

/-- The two aspects of meaning that can independently be fixed or shifting. -/
inductive MeaningAspect where
  | sense      -- intension: what the expression contributes to meaning
  | reference  -- extension: what the expression picks out in the world
  deriving DecidableEq, Repr

/-- Clark's four-way classification of expressions (Table 9.1, p. 300).

    Each expression type occupies one cell of the `MeaningAspect x Alterability`
    matrix. The classifying property is which aspect of meaning is salient for
    that type, and whether it is fixed or shifting across contexts. -/
structure ExpressionClass where
  /-- Which aspect of meaning defines this expression type -/
  aspect : MeaningAspect
  /-- Whether that aspect is fixed or shifts across contexts -/
  alterability : Alterability
  deriving DecidableEq, Repr

/-- Purely intensional expressions: fixed **sense**.
    E.g., *bachelor*, *blue*, *colorful ball*. Known to almost everyone
    in a speech community (p. 300). -/
def purelyIntensional : ExpressionClass :=
  ⟨.sense, .fixed⟩

/-- Proper names: fixed **reference**.
    E.g., *George Washington*, *the Second World War*, *France*.
    They rigidly designate certain individuals (p. 300). -/
def properName : ExpressionClass :=
  ⟨.reference, .fixed⟩

/-- Indexical expressions: shifting **reference**.
    E.g., *he*, *now*, *the bachelor over there*. The reference depends on
    context, but the rule for determining it (the character) is fixed (p. 300). -/
def indexical : ExpressionClass :=
  ⟨.reference, .shifting⟩

/-- Contextual expressions: shifting **sense**.
    E.g., *to teapot*, *our electric typewriter*, *a quick crab*.
    The sense itself — not just the reference — depends on the
    time, place, and circumstances of utterance (p. 300). -/
def contextualExpression : ExpressionClass :=
  ⟨.sense, .shifting⟩

/-- All four expression types in Table 9.1 are pairwise distinct. -/
theorem expression_types_distinct :
    purelyIntensional ≠ properName ∧
    purelyIntensional ≠ indexical ∧
    purelyIntensional ≠ contextualExpression ∧
    properName ≠ indexical ∧
    properName ≠ contextualExpression ∧
    indexical ≠ contextualExpression := by decide

/-- Clark's key observation: contextual expressions are classified by
    the **sense** aspect being **shifting** — not just shifting reference.
    This is what makes them invisible to traditional parsers (p. 300). -/
theorem contextual_shifts_sense :
    contextualExpression.aspect = .sense ∧
    contextualExpression.alterability = .shifting := ⟨rfl, rfl⟩

/-- Indexicals differ from contextual expressions: they shift in
    **reference**, not sense. Kaplan's character is constant (p. 301). -/
theorem indexical_shifts_reference :
    indexical.aspect = .reference ∧
    indexical.alterability = .shifting := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §2. Ten Types of Contextual Expressions (Table 9.2)
-- ════════════════════════════════════════════════════════════════

/-! ## Contextual Expression Taxonomy

Clark identifies 10 types (Table 9.2, p. 304), organized by the form class
of the derived word. All share the defining properties of contextual
expressions: non-denumerability of possible senses and contextuality of
actual sense. -/

/-- The form class of the derived contextual expression. -/
inductive DerivedCategory where
  | noun
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- The 10 types of contextual expressions from Table 9.2 (p. 304). -/
inductive ContextualExprType where
  -- Noun-derived
  | indirectNoun          -- *one water*, *a Henry Moore*
  | compoundNoun          -- *finger cup*, *apple-juice chair*
  | possessive            -- *John's dog*, *my tree*
  | denominalNoun         -- *a waller*, *a cupper*
  -- Verb-derived
  | denominalVerb         -- *to farewell*, *to Houdini*
  | eponymousVerb         -- *to do a Napoleon*, *to do a Nixon*
  | proActVerb            -- *do the lawn*, *do the porch*
  -- Adjective-derived
  | denominalAdjective    -- *Churchillian*, *Shavian*
  | nonPredicatingAdj     -- *atomic*, *manual*
  | eponymousAdjective    -- *very San Francisco*, *very Picasso*
  deriving DecidableEq, Repr

/-- The derived form class of each contextual expression type. -/
def ContextualExprType.derivedCategory : ContextualExprType → DerivedCategory
  | .indirectNoun       => .noun
  | .compoundNoun       => .noun
  | .possessive         => .noun
  | .denominalNoun      => .noun
  | .denominalVerb      => .verb
  | .eponymousVerb      => .verb
  | .proActVerb         => .verb
  | .denominalAdjective => .adjective
  | .nonPredicatingAdj  => .adjective
  | .eponymousAdjective => .adjective

-- ════════════════════════════════════════════════════════════════
-- §3. Sense-Selection vs. Sense-Creation
-- ════════════════════════════════════════════════════════════════

/-! ## The Sense-Selection Assumption and Its Failure

Clark's central distinction: traditional parsers **select** from a finite
pre-existing list of senses, while an adequate parser must **create** senses
using the speaker's intentions and mutual knowledge (p. 297).

Traditional parsers fail in two ways (p. 299):
- **Non-parsing**: the parser rejects a string as ungrammatical because it
  can't compose any senses (e.g., *Our electric typewriter got married*).
- **Mis-parsing**: the parser finds an interpretation but the wrong one
  (e.g., *Stereos are a dime a dozen* parsed as "phonographs are common"
  instead of "people who have stereos are common"). -/

/-- A parser architecture, distinguished by how it handles word meaning.
    Clark argues that sense-selection fails for contextual expressions
    and must be replaced by sense-creation (pp. 297-298). -/
inductive ParserArchitecture where
  /-- **Sense-selection**: the parser has a finite lexicon listing all senses
      for each word. It selects among listed senses. Adequate for purely
      intensional expressions but fails for contextual expressions. -/
  | senseSelection
  /-- **Sense-creation**: the parser constructs meanings on-the-fly from
      the speaker's intentions and mutual knowledge. Adequate for both
      conventional and innovative uses. -/
  | senseCreation
  deriving DecidableEq, Repr

/-- The two failure modes of sense-selection parsers (p. 299).
    Non-parsing and mis-parsing are distinct: non-parsing produces no
    output while mis-parsing produces wrong output. -/
inductive ParserFailure where
  /-- Parser finds no interpretation — string marked ungrammatical.
      Example: *Our electric typewriter got married*. -/
  | nonParsing
  /-- Parser finds an interpretation, but the wrong one.
      Example: *Stereos are a dime a dozen* parsed as "phonographs are common". -/
  | misParsing
  deriving DecidableEq, Repr

/-- A sense-selection lexicon: a finite list of pre-specified senses for
    each word. This is what traditional parsers assume (p. 297). -/
structure FiniteLexicon (Word Sense : Type) where
  /-- The listed senses for each word -/
  senses : Word → List Sense

/-- Sense-selection succeeds iff the intended sense is in the lexicon. -/
def FiniteLexicon.canParse {Word Sense : Type}
    (lex : FiniteLexicon Word Sense) (w : Word) (intended : Sense) : Prop :=
  intended ∈ lex.senses w

-- ════════════════════════════════════════════════════════════════
-- §4. Non-Denumerability of Nonce Senses
-- ════════════════════════════════════════════════════════════════

/-! ## Why Lexical Rules and Semi-Sentences Fail

Clark's argument against lexical rules (McCawley 1971, Green 1974, pp. 313-316):
for denominal verbs, there would need to be an unbounded number of rules
because the same noun can be verbified to mean indefinitely many things
depending on context. The verb *teapot* could mean "rub the back of the
leg with a teapot", "strike the ankle with a teapot", "turn into a teapot",
etc. — and each context could yield a meaning never before encountered.

Clark's argument against semi-sentences (Katz 1964, pp. 316-318): semi-sentence
theory requires a finite comprehension set for each string. But contextual
expressions generate infinite comprehension sets, so the theory wrongly
predicts they are incomprehensible.

The formal core of both arguments: the space of possible senses for a
contextual expression grows exponentially with the number of distinguishable
situations. Any finite list of senses leaves some situation-determined
meaning uncovered. -/

/-- Clark's non-denumerability argument formalized: for any finite type
    `S` of distinguishable situations, the space of `S -> Bool` functions
    (= possible nonce senses as characteristic functions on situations)
    has 2^|S| members. Any finite list shorter than this is incomplete.

    This captures Clark's core claim (p. 314): "since there are an unlimited
    number of other nonce senses that *teapot* (or any other novel denominal
    verb) could have had, there must also be an unlimited number of [lexical]
    rules for generating them." -/
theorem nonce_senses_not_exhaustible
    {S : Type} [Fintype S] [DecidableEq S]
    (senses : List (S → Bool))
    (h_card : senses.length < 2 ^ Fintype.card S) :
    ∃ f : S → Bool, f ∉ senses := by
  by_contra h
  push Not at h
  have h_le : Fintype.card (S → Bool) ≤ senses.length := by
    calc Fintype.card (S → Bool)
        = Finset.univ.card := Finset.card_univ.symm
      _ ≤ senses.toFinset.card := by
          apply Finset.card_le_card
          intro f _
          exact List.mem_toFinset.mpr (h f)
      _ ≤ senses.length := senses.toFinset_card_le
  rw [Fintype.card_fun, Fintype.card_bool] at h_le
  omega

/-- Any finite lexicon fails to parse some nonce sense of a contextual
    expression, when the sense space (S → Bool) has more members than the
    lexicon lists. This connects `FiniteLexicon` to `nonce_senses_not_exhaustible`:
    the non-denumerability of nonce senses means that no finite lexicon
    is complete for contextual expressions (pp. 313-318). -/
theorem finite_lexicon_incomplete
    {Word S : Type} [Fintype S] [DecidableEq S]
    (lex : FiniteLexicon Word (S → Bool)) (w : Word)
    (h : (lex.senses w).length < 2 ^ Fintype.card S) :
    ∃ s : S → Bool, ¬ lex.canParse w s :=
  nonce_senses_not_exhaustible (lex.senses w) h

-- ════════════════════════════════════════════════════════════════
-- §5. Five Properties Shared with Indirect Illocutionary Acts
-- ════════════════════════════════════════════════════════════════

/-! ## The Analogy to Indirect Speech Acts (pp. 319-321)

Clark's key structural observation: contextual expressions share five
properties with indirect illocutionary acts (like using *Do you know what
time it is?* as a request). These parallels motivate treating both via the
same mechanism — goal hierarchies (§6).

The five properties (illustrated for the denominal verb *teapot* in
*Max teapotted a policeman*, pp. 320-321):

1. **Simultaneous meanings**: the expression carries both a direct meaning
   (Ed is using *teapot* to denote teapots) and an indirect meaning (the
   act of rubbing the back of the leg with a teapot). Both are present.

2. **Logical priority**: Ed's denoting of teapots (direct) is logically
   prior to denoting the rubbing action (indirect). He performs the indirect
   act BY performing the direct one, not vice versa.

3. **Literalness of direct meaning**: the direct use — *teapot* denoting
   teapots — follows from the conventions of the language. It is literal.

4. **Non-denumerability of indirect meanings**: the possible nonce verb
   meanings of *teapot* cannot be enumerated. Depending on context, it could
   mean rubbing, striking, boiling, throwing, etc.

5. **Contextuality of indirect meanings**: what Ed means by *teapot* as a
   verb depends critically on the circumstances: Ed and the listener's shared
   knowledge about Max's odd habits.

These five properties are exactly what the `GoalHierarchy` structure (§6)
captures: `directMeaning` and `intendedMeaning` give (1) simultaneous
meanings; the asymmetry from direct to intended gives (2) logical priority;
`directMeaning` being conventional gives (3); `nonce_senses_not_exhaustible`
gives (4); dependence on `commonGround` gives (5). -/

/-- The five properties shared between indirect illocutionary acts and
    contextual expressions (pp. 319-321). Each property has a structural
    counterpart in the `GoalHierarchy` formalization (§6). -/
inductive IndirectUseProperty where
  /-- The expression carries both a direct and an indirect meaning. -/
  | simultaneousMeanings
  /-- The direct meaning is logically prior to the indirect meaning. -/
  | logicalPriority
  /-- The direct meaning follows from conventions of the language. -/
  | literalDirectMeaning
  /-- The possible indirect meanings are non-denumerable. -/
  | nonDenumerableIndirect
  /-- The actual indirect meaning depends on circumstances of utterance. -/
  | contextuality
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- §6. Goal Hierarchies and the Intentional View of Parsing
-- ════════════════════════════════════════════════════════════════

/-! ## The Intentional View of Parsing (pp. 323-328)

Clark's central positive proposal: parsing = reconstructing the speaker's
hierarchy of goals. Each constituent of an utterance accomplishes a subgoal
in the speaker's plan. The hierarchy of subgoals maps onto the hierarchy
of constituents (p. 324).

Clark contrasts two views of parsing (p. 324):
- **Traditional view**: the aim is to yield one of the (traditional) sentence
  meanings, presumably the one the speaker intended.
- **Intentional view**: the aim is to yield the speaker's *intentions* in
  uttering what he did.

For contextual expressions like Bombeck's *Stereos are a dime a dozen*, the
speaker's intentions are not derivable from any sentence meaning the
traditional parser could compute (p. 324).

Example (p. 325): Ed's goal hierarchy in using *teapot* in *Max teapotted a
policeman*:
- Subgoal (3): Ed wants me to recognize he is using *teapot* to denote teapots
- Subgoal (2): Ed wants me to recognize that the nonce verb meaning is
  computable uniquely from our common ground, with the noun playing one role
- Subgoal (1): Ed wants me to recognize the intended verb meaning (rubbing the
  back of the leg with a teapot)

The key insight (p. 326): subgoals (2) and (3) are *always* present, for
both conventional and innovative uses. In conventional cases, the computation
is trivial because the intended meaning equals the direct meaning. In
innovative cases, the listener must genuinely compute a novel meaning from
the common ground. -/

/-- A goal hierarchy for interpreting an expression in context.
    Clark's main proposal (pp. 323-328): each expression is understood
    by reconstructing the speaker's hierarchy of goals.

    The three subgoals correspond to Clark's numbered goals (p. 325):
    - Subgoal (3): `directMeaning` — the conventional meaning of the expression
    - Subgoal (2): the CG-based bridge from direct to intended meaning
    - Subgoal (1): `intendedMeaning` — what the speaker means on this occasion -/
structure GoalHierarchy (W : Type) where
  /-- Subgoal (3): the direct/conventional meaning of the expression -/
  directMeaning : W → Bool
  /-- Subgoal (1): the intended meaning on this occasion -/
  intendedMeaning : W → Bool
  /-- The common ground used for subgoal (2) -/
  commonGround : CG W

/-- A **conventional** use: the intended meaning IS the direct meaning.
    No nonce sense computation needed — subgoal (2) is trivial (p. 326).
    Example: Arlene telling Bill *Stereos are a dime a dozen* meaning
    "phonographs are very common" — *stereos* conventionally denotes
    phonographs and that's what she intends. -/
def GoalHierarchy.isConventional {W : Type} (g : GoalHierarchy W) : Prop :=
  g.intendedMeaning = g.directMeaning

/-- An **innovative** use: the intended meaning DIFFERS from the direct meaning.
    The listener must compute the nonce meaning from the direct meaning + CG
    via subgoal (2) (p. 326).
    Example: Bombeck writing *Stereos are a dime a dozen* meaning "people
    who possess phonographs are very common" — *stereos* directly denotes
    phonographs but indirectly denotes people who possess them. -/
def GoalHierarchy.isInnovative {W : Type} (g : GoalHierarchy W) : Prop :=
  g.intendedMeaning ≠ g.directMeaning

/-- For conventional uses, setting intended = direct gives a trivially
    valid goal hierarchy — there is nothing to infer beyond the conventional
    meaning (p. 326: "the computation required to capture these goals is
    trivial"). -/
theorem conventional_bridge_trivial {W : Type}
    (direct : W → Bool) (cg : CG W) :
    GoalHierarchy.isConventional
      { directMeaning := direct
        intendedMeaning := direct
        commonGround := cg : GoalHierarchy W } := rfl

/-- The intentional view subsumes the traditional view: if the parser
    reconstructs the speaker's goal hierarchy and the use is conventional,
    the result is the same as traditional sense-selection — the intended
    meaning just IS the conventional meaning. Sense-selection is the
    special case of goal-hierarchy reconstruction where no nonce
    computation is needed. -/
theorem traditional_is_special_case {W : Type}
    (g : GoalHierarchy W) (h : g.isConventional) :
    g.intendedMeaning = g.directMeaning := h

-- ════════════════════════════════════════════════════════════════
-- §7. The Innovative Denominal Verb Convention
-- ════════════════════════════════════════════════════════════════

/-! ## Clark's Convention for Interpreting Innovative Denominal Verbs

The central formal contribution of @cite{clark-clark-1979}, restated in
@cite{clark-1983} (p. 321):

> In using an innovative denominal verb sincerely, the speaker means to denote:
> (a) the kind of situation
> (b) that he has good reason to believe
> (c) that on this occasion the listener can readily compute
> (d) uniquely
> (e) on the basis of their mutual knowledge
> (f) in such a way that the parent noun denotes one role in the situation,
>     and the remaining surface arguments of the denominal verb denote
>     other roles in the situation.

Conditions (b)-(e) are unified as CG-entailment: the speaker has good reason
to believe the listener can readily compute the situation uniquely from their
mutual knowledge iff the common ground determines the situation.

Condition (f) is a structural constraint: the conventional denotation of the
parent noun must hold in every world where the situation holds — the noun
meaning participates as one role in the event. For *Max teapotted a policeman*,
wherever the teapotting-situation holds, there is a teapot involved. -/

/-- The Innovative Denominal Verb Convention (@cite{clark-clark-1979}; p. 321).

    The six conditions constrain the relationship between the nonce verb
    meaning (a situation type), the parent noun's conventional denotation,
    and the common ground shared by speaker and listener. -/
structure DenominalVerbConvention (W : Type) where
  /-- (a) The kind of situation denoted by the innovative verb -/
  situation : W → Bool
  /-- The conventional denotation of the parent noun -/
  nounDenotation : W → Bool
  /-- (e) The common ground of speaker and listener -/
  commonGround : CG W
  /-- (b-d) The situation is uniquely determined by the common ground:
      in every world compatible with mutual knowledge, the situation holds.
      This derives "good reason to believe" + "readily compute" + "uniquely"
      from a single CG-entailment condition. -/
  cgDeterminesSituation :
    ∀ w, commonGround.contextSet w → situation w = true
  /-- (f) The parent noun's conventional meaning is satisfied in every world
      where the situation holds — the noun meaning participates as one role
      in the situation (p. 321). For *teapot*: wherever the teapotting
      situation holds, there is a teapot involved. -/
  nounParticipates : ∀ w, situation w = true → nounDenotation w = true

/-- A denominal verb use gives rise to a goal hierarchy where the direct
    meaning is the noun's conventional denotation and the intended meaning
    is the innovative verb meaning (the situation). This connects the
    DenominalVerbConvention to the GoalHierarchy framework (§6). -/
def denominalGoalHierarchy {W : Type}
    (conv : DenominalVerbConvention W) : GoalHierarchy W where
  directMeaning := conv.nounDenotation
  intendedMeaning := conv.situation
  commonGround := conv.commonGround

/-- Every innovative denominal verb use is an innovative goal hierarchy:
    the noun denotation (direct meaning) differs from the verb meaning
    (intended meaning) because the nonce verb meaning goes beyond what
    the noun alone denotes. -/
theorem denominal_is_innovative {W : Type}
    (conv : DenominalVerbConvention W)
    (h : conv.nounDenotation ≠ conv.situation) :
    (denominalGoalHierarchy conv).isInnovative := h.symm

-- ════════════════════════════════════════════════════════════════
-- §8. Bridge to LU-RSA
-- ════════════════════════════════════════════════════════════════

/-! ## Sense-Creation and Lexical Uncertainty

@cite{bergen-levy-goodman-2016}'s LU-RSA operationalizes one dimension of
Clark's sense-creation proposal: the listener marginalizes over possible
lexica rather than selecting from a fixed one.

    L1(w | u) ∝ Σ_L P(L) · S1(u | w, L) · P(w)

This captures Clark's insight that the sense space is open-ended: the listener
does not select from a finite list of senses but integrates over possible
interpretations weighted by context (P(w)) and speaker rationality (S1).

However, Clark's full proposal is richer than LU-RSA in one key respect:
Clark argues that parsing is *hierarchical intention reconstruction* —
the listener reconstructs the speaker's hierarchy of goals, where each
constituent accomplishes a subgoal (§6). LU-RSA captures the "what" (the
listener considers multiple possible meanings) but not the "how" (the
hierarchical goal structure that organizes the computation).

The `SenseCreationParser` below models the LU-RSA operationalization.
Clark's full proposal additionally requires the `GoalHierarchy` structure
from §6, which provides the intentional scaffolding. -/

/-- A sense-selection parser uses a fixed `Lexicon` — it cannot handle
    words not in its lexicon. This corresponds to Clark's traditional parser. -/
def senseSelectionParser (U W : Type) := Lexicon U W

/-- A sense-creation parser marginalizes over a space of possible lexica.
    The prior P(L) captures what is compatible with mutual knowledge.
    This models the LU-RSA operationalization of Clark's sense-creation. -/
structure SenseCreationParser (U W L : Type) where
  /-- The space of possible lexica (sense-creation candidates) -/
  toLexicon : L → Lexicon U W
  /-- Prior over lexica, reflecting mutual knowledge -/
  lexiconPrior : L → ℚ

/-- Clark's key claim formalized: sense-selection is a special case of
    sense-creation where the lexicon space is a singleton. When there is
    exactly one lexicon (no uncertainty), sense-creation reduces to
    sense-selection. -/
def senseSelectionAsSenseCreation {U W : Type} (lex : Lexicon U W) :
    SenseCreationParser U W Unit where
  toLexicon := λ _ => lex
  lexiconPrior := λ _ => 1

/-- Conversely, sense-creation with a non-trivial lexicon space cannot
    be reduced to sense-selection when different lexica assign different
    meanings to some utterance. This is the formal content of Clark's
    argument that sense-selection is inadequate (pp. 297-299). -/
theorem sense_creation_strictly_generalizes
    {U W L : Type} (parser : SenseCreationParser U W L)
    (l₁ l₂ : L) (u : U) (w : W)
    (h_diff : (parser.toLexicon l₁).meaning u w ≠ (parser.toLexicon l₂).meaning u w) :
    ¬ ∃ lex : Lexicon U W, ∀ l : L, parser.toLexicon l = lex := by
  intro ⟨lex, h_all⟩
  have h1 := h_all l₁
  have h2 := h_all l₂
  rw [h1, h2] at h_diff
  exact h_diff rfl

-- ════════════════════════════════════════════════════════════════
-- §9. Bridge to DM Recategorization
-- ════════════════════════════════════════════════════════════════

/-! ## Denominal Verbs: Syntax Is Easy, Semantics Is Hard

DM's `Recategorization.denominal` captures the syntactic operation
underlying denominal verbs: ROOT + n → noun, then + v → verb.
Clark's point is that this syntactic step is trivial — the hard part is
computing what the resulting verb *means* (p. 303).

DM's List 3 (Encyclopedia entries) handles idiosyncratic meaning, but
only for conventionalized forms. For innovative denominal verbs, List 3
has no entry — the meaning must be computed from context. This is exactly
the gap that Clark's convention (§7) and the goal hierarchy (§6) fill.

The bridge: `Recategorization.denominal` gives the morphosyntactic
*input* to Clark's convention. Condition (f) — "the parent noun denotes
one role in the situation" — references the meaning of the noun before
recategorization. -/

/-- A denominal verb has two components:
    1. The syntactic recategorization (n → v), from DM
    2. The pragmatic sense-creation, from Clark's convention

    The syntactic part is deterministic; the pragmatic part is contextual. -/
structure DenominalVerb (W : Type) where
  /-- The underlying root and its nominal categorization -/
  nominalRoot : CategorizedRoot
  /-- Evidence that recategorization to v succeeds -/
  recategorized : CategorizedRoot
  recatProof : nominalRoot.recategorize .denominal = some recategorized
  /-- The pragmatic convention that determines the verb's meaning -/
  convention : DenominalVerbConvention W

/-- The syntactic category of a denominal verb is always V. -/
theorem denominal_verb_is_verbal {W : Type}
    (dv : DenominalVerb W) :
    dv.recategorized.categorizer = .v :=
  recategorization_changes_category
    dv.nominalRoot .denominal dv.recategorized dv.recatProof

/-- The source of a denominal verb is always N — the noun meaning
    is available as input to Clark's convention (condition f). -/
theorem denominal_verb_source_is_nominal {W : Type}
    (dv : DenominalVerb W) :
    dv.nominalRoot.categorizer = .n :=
  denominal_requires_n dv.nominalRoot dv.recategorized dv.recatProof

/-- The gap between DM and Clark: DM tells us that denominal verbs exist
    (the recategorization succeeds) but says nothing about what they mean.
    Two denominal verbs from the same root always produce the same syntactic
    result (V category), yet can have arbitrarily different meanings.
    Clark's convention fills this gap by specifying how the meaning is
    constructed from the parent noun + common ground (pp. 303, 321). -/
theorem dm_underdetermines_meaning {W : Type}
    (dv₁ dv₂ : DenominalVerb W) :
    dv₁.recategorized.categorizer = dv₂.recategorized.categorizer := by
  rw [denominal_verb_is_verbal dv₁, denominal_verb_is_verbal dv₂]

-- ════════════════════════════════════════════════════════════════
-- §10. The *Stereos* Example (pp. 326-327)
-- ════════════════════════════════════════════════════════════════

/-! ## Arlene vs. Bombeck: Conventional and Innovative Use of *Stereos*

Clark's most detailed example (pp. 326-327): Arlene tells Bill *Stereos are
a dime a dozen* meaning "phonographs are very common" (conventional use).
Bombeck writes the same sentence meaning "people who possess phonographs
are very common" (innovative use).

The two uses have the same **direct meaning** — *stereos* conventionally
denotes phonographs — but different **intended meanings**. A traditional
parser with the conventional meaning in its lexicon handles Arlene's
utterance correctly but **mis-parses** Bombeck's: it arrives at
"phonographs are very common" instead of "people who have stereos are very
common" (p. 299).

The key insight (p. 327): "Bill, in parsing Arlene's utterance, can't ever
be content with subgoal (1) alone. He can't ever know for certain, ahead
of time, which words Arlene is using in their conventional senses, and
which she is using in contextually innovative senses." Subgoals (2) and (3)
are always implicitly present — even for conventional uses. -/

/-- A world with two relevant features for the *stereos* example. -/
structure StereosWorld where
  /-- Are phonographs common in this world? -/
  phonographsCommon : Bool
  /-- Are people who own phonographs common in this world? -/
  ownersCommon : Bool
  deriving DecidableEq, Repr, BEq

/-- The conventional denotation of *stereos* = phonographs.
    Same for both Arlene and Bombeck — the DIRECT meaning is always
    the conventional one (property 3: literalness). -/
def stereosDirectMeaning (w : StereosWorld) : Bool := w.phonographsCommon

/-- Arlene's goal hierarchy: conventional use.
    She means "phonographs are common" — exactly what the word conventionally
    means. Subgoal (1) = subgoal (3). -/
def arlenesGoalHierarchy : GoalHierarchy StereosWorld where
  directMeaning := stereosDirectMeaning
  intendedMeaning := stereosDirectMeaning
  commonGround := .empty

/-- Bombeck's CG: the discourse context establishes that she is writing
    about roommates, their possessions, and the social consequences of
    those possessions. The CG determines that people who own phonographs
    are common (which is what she intends *stereos* to convey). -/
def bombecksCG : CG StereosWorld :=
  CG.empty.add (λ w => w.ownersCommon)

/-- Bombeck's goal hierarchy: innovative use.
    She means "people who possess phonographs are common" — a nonce sense
    computed from the direct meaning (phonographs) + CG (roommate context).
    Subgoal (1) ≠ subgoal (3). -/
def bombecksGoalHierarchy : GoalHierarchy StereosWorld where
  directMeaning := stereosDirectMeaning
  intendedMeaning := λ w => w.ownersCommon
  commonGround := bombecksCG

/-- Arlene's use is conventional: intendedMeaning = directMeaning. -/
theorem arlene_is_conventional : arlenesGoalHierarchy.isConventional := rfl

/-- Bombeck's use is innovative: intendedMeaning ≠ directMeaning.
    The two meanings differ on the world where phonographs are common
    but the people who own them are not. -/
theorem bombeck_is_innovative : bombecksGoalHierarchy.isInnovative := by
  intro h
  have := congr_fun h ⟨true, false⟩
  exact absurd this nofun

/-- A finite lexicon with the conventional meaning of *stereos*. -/
def conventionalLexicon : FiniteLexicon Unit (StereosWorld → Bool) where
  senses := λ _ => [stereosDirectMeaning]

/-- The lexicon handles Arlene's conventional use: her intended meaning
    is the conventional meaning, which is in the lexicon. -/
theorem conventional_lexicon_handles_arlene :
    conventionalLexicon.canParse () stereosDirectMeaning :=
  List.Mem.head _

/-- The lexicon fails for Bombeck's innovative use: her intended meaning
    (people who own phonographs are common) is NOT in the lexicon.
    This is Clark's **mis-parsing problem** (p. 299) — the parser would
    arrive at "phonographs are common" instead of what Bombeck meant. -/
theorem conventional_lexicon_fails_bombeck :
    ¬ conventionalLexicon.canParse () (λ w => w.ownersCommon) := by
  intro h
  simp [FiniteLexicon.canParse, conventionalLexicon] at h
  have := congr_fun h ⟨true, false⟩
  exact absurd this nofun

/-- Bombeck's CG determines the intended meaning: in every world
    compatible with the CG, the intended meaning (owners are common) holds.
    This is the formal content of conditions (b)-(e). -/
theorem bombeck_cg_determines_meaning :
    ∀ w, bombecksCG.contextSet w → (λ w => w.ownersCommon) w = true := by
  intro w h
  simp only [bombecksCG, CG.contextSet, CG.add, CG.empty,
    List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

-- ════════════════════════════════════════════════════════════════
-- §11. Bridge to Indirect Speech Acts
-- ════════════════════════════════════════════════════════════════

/-! ## The Shared Mechanism: GoalHierarchy

Clark's structural argument (pp. 319-321): contextual expressions and
indirect illocutionary acts are understood by the **same mechanism** —
reconstructing the speaker's hierarchy of goals. The five shared
properties (`IndirectUseProperty`, §5) are structural consequences of
both producing `GoalHierarchy` instances:

- **(1) Simultaneous meanings** → `directMeaning` and `intendedMeaning` fields
- **(2) Logical priority** → `directMeaning` is the conventional/literal layer
- **(3) Literalness** → `directMeaning` follows from linguistic convention
- **(4) Non-denumerability** → `nonce_senses_not_exhaustible` (§4)
- **(5) Contextuality** → `commonGround` field

The parallel extends to @cite{roberts-2012}'s Strategy of Inquiry
(`Discourse.Strategy` in `Core/Discourse/QUD.lean`): both are rose-tree
structures where resolving children resolves the parent. Clark's goal
hierarchy is Roberts' strategy applied at the **word level** — each
constituent maps to a subgoal, and resolving all subgoals resolves the
speaker's communicative intention. -/

open Core.Discourse (IntentionalState PsychMode)
open Core.Proposition (BProp)

/-- An indirect speech act gives rise to a goal hierarchy.

    Example: *Do you know what time it is?* used as a request.
    - Direct meaning: the yes/no question (interrogative)
    - Intended meaning: the request to tell the time (directive)
    - Common ground: the conversational situation

    This shows that indirect speech acts produce the **same type** as
    contextual expressions — the five shared properties (§5) are
    structural consequences of this shared type. -/
def indirectActGoalHierarchy {W : Type}
    (directContent : W → Bool) (indirectContent : W → Bool)
    (cg : CG W) : GoalHierarchy W where
  directMeaning := directContent
  intendedMeaning := indirectContent
  commonGround := cg

/-- Indirect speech acts are always innovative: by definition, the
    indirect meaning differs from the direct meaning (otherwise the
    act would not be "indirect"). -/
theorem indirect_act_innovative {W : Type}
    (direct indirect : W → Bool) (cg : CG W)
    (h : direct ≠ indirect) :
    (indirectActGoalHierarchy direct indirect cg).isInnovative := h.symm

/-- Clark's central claim: the **same mechanism** handles both indirect
    speech acts and contextual expressions. Both are `GoalHierarchy`
    instances — the type IS the shared mechanism. Conventional uses
    (where direct = intended) are the degenerate case where no
    CG-based computation is needed. -/
theorem same_mechanism {W : Type}
    (speechAct : GoalHierarchy W) (contextualExpr : GoalHierarchy W) :
    -- Both are GoalHierarchy instances — this is the structural claim.
    -- The theorem is trivially true because the claim IS the shared type.
    -- Clark's argument is that the mechanism is the same, not that
    -- any two instances are equal.
    (speechAct.isConventional ∨ speechAct.isInnovative) ∧
    (contextualExpr.isConventional ∨ contextualExpr.isInnovative) :=
  ⟨conventional_or_innovative speechAct, conventional_or_innovative contextualExpr⟩
where
  conventional_or_innovative {W : Type} (g : GoalHierarchy W) :
      g.isConventional ∨ g.isInnovative :=
    Classical.or_iff_not_imp_left.mpr id

-- ════════════════════════════════════════════════════════════════
-- §12. ContextualMeaning — The Deeper Formal Principle
-- ════════════════════════════════════════════════════════════════

/-! ## Meaning Factors Through Direct Meaning + Common Ground

The deeper formal principle underlying Clark's argument: a contextual
expression's meaning is not a static denotation but a **function from
common ground to denotation**. The `GoalHierarchy` of §6 is what you
get when you **evaluate** this function at a specific CG — it freezes
the CG to produce a snapshot (directMeaning, intendedMeaning) pair.

This factorization clarifies several of Clark's claims:

- **Sense-selection vs sense-creation**: sense-selection treats meaning as
  a static value (CG-independent); sense-creation treats it as a function
  (CG-dependent). Sense-selection is the special case where `compute`
  ignores the CG.

- **Non-denumerability**: the space of possible senses is non-denumerable
  because the CG space is open-ended. Each CG potentially yields a
  different intended meaning, so no finite list of senses suffices.

- **The stereos example**: Arlene and Bombeck share the SAME underlying
  `ContextualMeaning` for *stereos*. Evaluating it at Arlene's empty CG
  yields `intendedMeaning = directMeaning` (conventional). Evaluating it
  at Bombeck's roommate-context CG yields `intendedMeaning ≠ directMeaning`
  (innovative). The difference is in the CG, not in the word.

- **GoalHierarchy as evaluation**: `GoalHierarchy` = `ContextualMeaning`
  evaluated at a point. The hierarchy is an occasion-specific instantiation
  of a more general meaning function. -/

/-- A contextual meaning: the meaning of an expression is a function
    from common ground to denotation, not a static denotation.

    `directMeaning` is the conventional denotation — what any competent
    speaker knows. `compute` maps a CG to the **intended** meaning on
    a given occasion. For conventional uses, `compute cg = directMeaning`.
    For innovative uses, `compute cg ≠ directMeaning` — the CG shifts
    the meaning away from the conventional denotation. -/
structure ContextualMeaning (W : Type) where
  /-- The conventional/direct denotation -/
  directMeaning : W → Bool
  /-- Compute the intended meaning from the common ground -/
  compute : CG W → (W → Bool)

/-- Evaluate a contextual meaning at a specific CG, producing a
    `GoalHierarchy`. This is the connection between the abstract meaning
    function and the occasion-specific goal hierarchy the listener
    reconstructs. -/
def ContextualMeaning.evaluate {W : Type}
    (cm : ContextualMeaning W) (cg : CG W) : GoalHierarchy W where
  directMeaning := cm.directMeaning
  intendedMeaning := cm.compute cg
  commonGround := cg

/-- A contextual meaning is **CG-independent** when the CG makes no
    difference — `compute` returns the direct meaning regardless.
    This is Clark's sense-selection: the meaning is static. -/
def ContextualMeaning.isCGIndependent {W : Type}
    (cm : ContextualMeaning W) : Prop :=
  ∀ cg : CG W, cm.compute cg = cm.directMeaning

/-- A contextual meaning is **CG-dependent** when there exists some CG
    that shifts the intended meaning away from the direct meaning.
    This is Clark's sense-creation: the meaning is genuinely contextual. -/
def ContextualMeaning.isCGDependent {W : Type}
    (cm : ContextualMeaning W) : Prop :=
  ∃ cg : CG W, cm.compute cg ≠ cm.directMeaning

/-- CG-independent meanings always produce conventional goal hierarchies. -/
theorem cg_independent_conventional {W : Type}
    (cm : ContextualMeaning W) (h : cm.isCGIndependent) (cg : CG W) :
    (cm.evaluate cg).isConventional := h cg

/-- CG-dependent meanings produce innovative goal hierarchies at the
    witnessing CG. -/
theorem cg_dependent_innovative {W : Type}
    (cm : ContextualMeaning W) (h : cm.isCGDependent) :
    ∃ cg, (cm.evaluate cg).isInnovative := h

noncomputable section
open Classical

/-- The contextual meaning of *stereos*: the SAME meaning function
    underlies both Arlene's and Bombeck's uses.

    The `compute` function models the inference from CG to intended meaning:
    - If the CG entails that owners are common, the intended meaning is
      `ownersCommon` (the innovative, CG-derived reading).
    - Otherwise, the intended meaning falls back to the direct meaning
      `phonographsCommon` (the conventional reading).

    This is a simplified model of the full pragmatic computation. The real
    inference involves reconstructing the speaker's goals from mutual
    knowledge — here we model just the outcome. -/
def stereosMeaning : ContextualMeaning StereosWorld where
  directMeaning := stereosDirectMeaning
  compute := λ cg =>
    if ∀ w, cg.contextSet w → w.ownersCommon = true
    then λ w => w.ownersCommon
    else stereosDirectMeaning

end

private theorem bombecksCG_entails_owners :
    ∀ w, bombecksCG.contextSet w → w.ownersCommon = true := by
  intro w h
  simp only [bombecksCG, CG.contextSet, CG.add, CG.empty,
    List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

private theorem emptyCG_not_entails_owners :
    ¬ ∀ w, (CG.empty : CG StereosWorld).contextSet w → w.ownersCommon = true := by
  push_neg
  exact ⟨⟨true, false⟩, by simp [CG.contextSet, CG.empty], nofun⟩

/-- Evaluating at Arlene's empty CG yields the conventional goal hierarchy.
    The empty CG does not entail anything about owners, so `compute` returns
    the direct meaning. -/
theorem stereos_arlene :
    stereosMeaning.evaluate .empty = arlenesGoalHierarchy := by
  unfold stereosMeaning ContextualMeaning.evaluate
  simp only [if_neg emptyCG_not_entails_owners, arlenesGoalHierarchy]

/-- Evaluating at Bombeck's roommate-context CG yields the innovative
    goal hierarchy. The CG entails `ownersCommon`, so `compute` shifts
    the meaning away from the direct denotation. -/
theorem stereos_bombeck :
    stereosMeaning.evaluate bombecksCG = bombecksGoalHierarchy := by
  unfold stereosMeaning ContextualMeaning.evaluate
  simp only [if_pos bombecksCG_entails_owners, bombecksGoalHierarchy]

/-- *Stereos* is CG-dependent: there exists a CG (Bombeck's) where
    the intended meaning differs from the direct meaning. -/
theorem stereos_is_cg_dependent : stereosMeaning.isCGDependent := by
  refine ⟨bombecksCG, ?_⟩
  unfold stereosMeaning
  simp only [if_pos bombecksCG_entails_owners]
  intro h
  have := congr_fun h ⟨true, false⟩
  exact absurd this nofun

/-- A CG-independent meaning can be fully captured by a singleton
    lexicon — sense-selection suffices. -/
theorem cg_independent_lexicon_suffices {W : Type}
    (cm : ContextualMeaning W) (h : cm.isCGIndependent) :
    ∀ cg, (FiniteLexicon.mk (λ _ : Unit => [cm.directMeaning])).canParse
      () (cm.compute cg) := by
  intro cg
  rw [h cg]
  exact List.Mem.head _

end Clark1983
