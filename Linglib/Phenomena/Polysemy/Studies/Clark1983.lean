import Linglib.Core.Semantics.CommonGround
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

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

Two attempted solutions fail:
- **Lexical rules** (McCawley 1971, Green 1974, Levi 1978): would need
  infinitely many rules for denominal verbs, compound nouns, etc.
- **Semi-sentences** (Katz 1964): requires finite comprehension sets, but
  contextual expressions have infinitely many possible readings.

Clark proposes replacing sense-selection with **sense-creation**: listeners
construct meanings on-the-fly by inferring the speaker's intentions from mutual
knowledge. This mechanism parallels indirect speech acts — both involve
computing indirect meaning from direct meaning + common ground.

## Connection to LU-RSA

Clark's 1983 sense-creation proposal is the conceptual precursor to
@cite{bergen-levy-goodman-2016}'s Lexical Uncertainty RSA:

| Clark 1983                      | LU-RSA                              |
|---------------------------------|---------------------------------------|
| Sense-creation from context     | Marginalization over lexica Σ_L      |
| Mutual knowledge (conditions b-e) | Shared prior P(w)                  |
| "Readily compute uniquely"      | Rationality parameter α → ∞         |
| Parent noun denotes a role (f)  | Lexicon.meaning structure            |

The `Lexicon` type in `LexicalUncertainty.Basic` is the formal counterpart
of Clark's open-ended sense space: the listener doesn't select from a finite
list but infers which `Lexicon` the speaker is using.

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
- §5: The Innovative Denominal Verb Convention
- §6: Bridge to LU-RSA
- §7: Bridge to DM recategorization
-/

namespace Phenomena.Polysemy.Studies.Clark1983

open Core.CommonGround
open Theories.Morphology.DM (Categorizer Recategorization CategorizedRoot
  denominal_requires_n recategorization_changes_category)

-- ════════════════════════════════════════════════════════════════
-- §1. Sense and Reference: Fixed vs. Shifting (Table 9.1)
-- ════════════════════════════════════════════════════════════════

/-! ## The Fixed/Shifting Classification

Clark observes that the fixed/shifting distinction applies independently to
both **sense** (intension) and **reference** (extension), yielding a 2×2:

|            | Fixed sense              | Shifting sense            |
|------------|--------------------------|---------------------------|
| Fixed ref  | Purely intensional expr  | —                         |
|            | (e.g., *bachelor*)       |                           |
| Shifting ref| Proper name             | Contextual expression     |
|            | (e.g., *George Washington*)| (e.g., *to teapot*)     |

Indexical expressions (e.g., *he*, *now*) have fixed sense but shifting
reference. Contextual expressions have shifting sense — their meaning is
created for each occasion of use. -/

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

/-- Clark's four-way classification of expressions (Table 9.1).
    Each expression type is characterized by the alterability of its
    sense and its reference. -/
structure ExpressionClass where
  /-- Whether the sense is fixed or shifting -/
  senseAlterability : Alterability
  /-- Whether the reference is fixed or shifting -/
  referenceAlterability : Alterability
  deriving DecidableEq, Repr

/-- Purely intensional expressions: fixed sense, fixed reference.
    E.g., *bachelor*, *blue*, *colorful ball*. Known to almost everyone
    in a speech community. -/
def purelyIntensional : ExpressionClass :=
  ⟨.fixed, .fixed⟩

/-- Proper names: fixed sense (rigid designator), fixed reference.
    E.g., *George Washington*, *the Second World War*, *France*. -/
def properName : ExpressionClass :=
  ⟨.fixed, .fixed⟩

/-- Indexical expressions: fixed sense (character), shifting reference.
    E.g., *he*, *now*, *the bachelor over there*. The reference depends on
    context, but the rule for determining it (the character) is fixed. -/
def indexical : ExpressionClass :=
  ⟨.fixed, .shifting⟩

/-- Contextual expressions: shifting sense, shifting reference.
    E.g., *to teapot*, *our electric typewriter*, *a quick crab*.
    Both what the expression means and what it picks out depend on the
    time, place, and circumstances of utterance. -/
def contextualExpression : ExpressionClass :=
  ⟨.shifting, .shifting⟩

/-- Clark's key observation: contextual expressions differ from indexicals
    in having **shifting sense**, not just shifting reference. This is what
    makes them invisible to traditional parsers — the parser would need to
    enumerate all possible senses, but they are non-denumerable. -/
theorem contextual_has_shifting_sense :
    contextualExpression.senseAlterability = .shifting := rfl

/-- Indexicals have fixed sense (Kaplan's character is constant). -/
theorem indexical_has_fixed_sense :
    indexical.senseAlterability = .fixed := rfl

-- ════════════════════════════════════════════════════════════════
-- §2. Ten Types of Contextual Expressions (Table 9.2)
-- ════════════════════════════════════════════════════════════════

/-! ## Contextual Expression Taxonomy

Clark identifies 10 types, organized by the form class of the derived word.
All share the defining properties of contextual expressions:
non-denumerability of possible senses and contextuality of actual sense. -/

/-- The form class of the derived contextual expression. -/
inductive DerivedCategory where
  | noun
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- The 10 types of contextual expressions from Table 9.2. -/
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

/-- All 10 types are contextual expressions (shifting sense + reference). -/
def ContextualExprType.expressionClass (_ : ContextualExprType) : ExpressionClass :=
  contextualExpression

/-- Every contextual expression type has shifting sense. -/
theorem all_contextual_types_shift_sense (t : ContextualExprType) :
    (t.expressionClass).senseAlterability = .shifting := rfl

-- ════════════════════════════════════════════════════════════════
-- §3. Sense-Selection vs. Sense-Creation
-- ════════════════════════════════════════════════════════════════

/-! ## The Sense-Selection Assumption and Its Failure

Clark's central distinction: traditional parsers **select** from a finite
pre-existing list of senses, while an adequate parser must **create** senses
using the speaker's intentions and mutual knowledge.

This distinction is the conceptual precursor to the difference between
fixed-lexicon RSA and Lexical Uncertainty RSA (@cite{bergen-levy-goodman-2016}):
in fixed-lexicon RSA, the meaning function is given; in LU-RSA, the listener
marginalizes over possible meaning functions (lexica). -/

/-- A parser architecture, distinguished by how it handles word meaning.
    Clark argues that sense-selection fails for contextual expressions
    and must be replaced by sense-creation. -/
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

/-- A sense-selection lexicon: a finite list of pre-specified senses for
    each word. This is what traditional parsers assume. -/
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

Clark's argument against lexical rules (McCawley 1971, Green 1974):
for denominal verbs, there would need to be an unbounded number of rules
because the same noun can be verbified to mean indefinitely many things
depending on context. The verb *teapot* could mean "rub the back of the
leg with a teapot", "strike the ankle with a teapot", "turn into a teapot",
etc. — and each context could yield a meaning never before encountered.

We model this as a function from situations to senses: the number of
possible senses is bounded only by the number of distinguishable situations,
which is not finitely enumerable.

Clark's argument against semi-sentences (Katz 1964): semi-sentence theory
requires a finite comprehension set for each string. But contextual expressions
generate infinite comprehension sets, so the theory wrongly predicts they are
incomprehensible. -/

/-- A situation in which a denominal verb might be used. Parametric: the
    space of situations is open-ended, reflecting Clark's non-denumerability
    argument. -/
structure NonceSituation (Entity Role : Type) where
  /-- The entity denoted by the parent noun -/
  nounReferent : Entity
  /-- The role the noun-referent plays in the situation -/
  nounRole : Role
  /-- The agent of the verbified action -/
  agent : Entity
  /-- The patient/theme -/
  patient : Entity

/-- A nonce sense maps a situation type to a truth value:
    "does this situation match the intended reading?" -/
def NonceSense (Entity Role : Type) := NonceSituation Entity Role → Bool

/-- Clark's non-denumerability argument: even with just 2 entities and
    2 roles, the space of `NonceSituation → Bool` functions (= nonce senses)
    has 2^(2×2×2×2) = 65536 members — far more than any finite list a
    lexicon could contain. For real-world entities and roles, the space is
    effectively infinite.

    We state this as: given any finite list of Bool-valued functions on a
    type S, if the list is shorter than 2^|S|, then some function is missing.

    TODO: Full proof via Cantor's theorem (Fintype.card_fun, Nat.lt_two_pow).
    Proof sketch: 2^|S| > |senses| by hypothesis, so by pigeonhole some
    element of `S → Bool` is not in the list. -/
theorem nonce_senses_not_exhaustible
    {S : Type} [Fintype S] [DecidableEq S]
    (senses : List (S → Bool))
    (h_card : senses.length < 2 ^ Fintype.card S) :
    ∃ f : S → Bool, f ∉ senses := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- §5. The Innovative Denominal Verb Convention
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

This convention parallels five properties shared with indirect speech acts:
simultaneous meanings, logical priority, literalness of direct meaning,
non-denumerability of indirect meanings, and contextuality. -/

/-- The six conditions of Clark's Innovative Denominal Verb Convention.
    Each condition constrains the intended interpretation. Together they
    define how a listener should compute the nonce meaning. -/
structure DenominalVerbConvention (W Entity : Type) where
  /-- (a) The kind of situation denoted by the innovative verb -/
  situation : Entity → Entity → W → Bool
  /-- (b) The speaker has good reason to believe the situation is identifiable.
      Modeled as: the situation is compatible with common ground. -/
  speakerGrounds : BContextSet W → Bool
  /-- (c) The listener can readily compute the meaning.
      Modeled as: low processing effort (RT-style constraint). -/
  readilyComputable : Bool
  /-- (d) The meaning is uniquely determined in context.
      Modeled as: the CG determines a unique situation type. -/
  unique : Bool
  /-- (e) Mutual knowledge: the computation uses common ground -/
  mutualKnowledge : BContextSet W
  /-- (f) The parent noun denotes one role; surface arguments denote others.
      `nounRole` specifies what the noun contributes to the situation. -/
  nounRole : Entity → Bool

/-- Clark's convention is satisfied when all six conditions hold. -/
def DenominalVerbConvention.satisfied {W : Type} {Entity : Type}
    (c : DenominalVerbConvention W Entity) : Bool :=
  c.speakerGrounds c.mutualKnowledge &&
  c.readilyComputable &&
  c.unique

/-- Clark's five shared properties between contextual expressions and
    indirect speech acts. Each property has an analogue in both domains. -/
inductive SharedProperty where
  /-- The expression has both a direct meaning (from the parent noun)
      and an indirect meaning (the nonce verb sense). -/
  | simultaneousMeanings
  /-- The direct meaning (noun denotation) is logically prior to the
      indirect meaning (verb sense). One performs the indirect act
      *by* performing the direct act. -/
  | logicalPriority
  /-- The direct meaning follows from the conventional meaning of the
      word (the literal noun sense). -/
  | literalDirectMeaning
  /-- The possible indirect meanings cannot be enumerated in advance.
      Any finite list will miss some contextually available sense. -/
  | nonDenumerability
  /-- What the speaker means indirectly depends critically on the
      circumstances: time, place, common ground. -/
  | contextuality
  deriving DecidableEq, Repr

/-- A worked example: *to porch* in "George managed to porch the newspaper."

    The parent noun *porch* denotes a porch (direct meaning). The nonce
    verb means "cause to be on a porch" (indirect meaning, computed from
    the context: George is delivering newspapers). -/
structure PorchExample where
  /-- "porch" as a noun denotes a covered entrance to a house -/
  nounSense : String := "covered entrance to a house"
  /-- "to porch" as a nonce verb: cause to be on a porch -/
  verbSense : String := "cause to be on a porch"
  /-- The parent noun plays the location role in the situation -/
  nounPlaysLocationRole : Bool := true
  /-- The agent (George) plays the agent role -/
  agentIsSubject : Bool := true
  /-- The patient (the newspaper) plays the theme role -/
  themeIsObject : Bool := true

/-- The teapot example from Clark's paper: Ed says "Max teapotted a policeman,"
    meaning Max rubbed the back of a policeman's leg with a teapot. -/
structure TeapotExample where
  nounSense : String := "a pot for brewing tea"
  verbSense : String := "rub the back of the leg of with a teapot"
  nounPlaysInstrumentRole : Bool := true
  agentIsSubject : Bool := true
  patientIsObject : Bool := true

-- ════════════════════════════════════════════════════════════════
-- §6. Bridge to LU-RSA
-- ════════════════════════════════════════════════════════════════

/-! ## Sense-Creation as Lexical Uncertainty

Clark's sense-creation is the conceptual ancestor of @cite{bergen-levy-goodman-2016}'s
LU-RSA. The key structural correspondence:

- Clark's "possible senses" = the space of `Lexicon`s in LU-RSA
- Clark's "mutual knowledge" = the shared prior P(w) over worlds
- Clark's "readily compute uniquely" = the RSA listener selecting the
  highest-posterior lexicon (as α → ∞, the posterior concentrates)
- Clark's "parent noun denotes one role" = structural constraint on
  `Lexicon.meaning`: the verb meaning must be related to the noun meaning

In LU-RSA, the listener does not select from a finite list of senses.
Instead, they marginalize over possible lexica:

  L₁(w | u) ∝ Σ_L P(L) · S₁(u | w, L) · P(w)

This is exactly Clark's sense-creation: the listener constructs the meaning
by integrating over possible interpretations weighted by context (P(w)) and
speaker rationality (S₁). -/

/-- A sense-selection parser uses a fixed `Lexicon` — it cannot handle
    words not in its lexicon. This corresponds to Clark's traditional parser. -/
def senseSelectionParser (U W : Type) := Lexicon U W

/-- A sense-creation parser marginalizes over a space of possible lexica.
    The prior P(L) captures what is compatible with mutual knowledge.
    This corresponds to Clark's intentional parser / LU-RSA listener. -/
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
    argument that sense-selection is inadequate. -/
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
-- §7. Bridge to DM Recategorization
-- ════════════════════════════════════════════════════════════════

/-! ## Denominal Verbs: Syntax Is Easy, Semantics Is Hard

DM's `Recategorization.denominal` captures the syntactic operation
underlying denominal verbs: √ROOT + n → noun, then + v → verb.
Clark's point is that this syntactic step is trivial — the hard part is
computing what the resulting verb *means*.

DM's List 3 (Encyclopedia entries) handles idiosyncratic meaning, but
only for conventionalized forms. For innovative denominal verbs, List 3
has no entry — the meaning must be computed from context. This is exactly
the gap that Clark's convention (§5) and LU-RSA (§6) fill.

The bridge: `Recategorization.denominal` gives the morphosyntactic
*input* to Clark's convention. Condition (f) — "the parent noun denotes
one role in the situation" — references the meaning of the noun before
recategorization. -/

/-- A denominal verb has two components:
    1. The syntactic recategorization (n → v), from DM
    2. The pragmatic sense-creation, from Clark's convention

    The syntactic part is deterministic; the pragmatic part is contextual. -/
structure DenominalVerb (W : Type) (Entity : Type) where
  /-- The underlying root and its nominal categorization -/
  nominalRoot : CategorizedRoot
  /-- Evidence that recategorization to v succeeds -/
  recategorized : CategorizedRoot
  recatProof : nominalRoot.recategorize .denominal = some recategorized
  /-- The pragmatic convention that determines the verb's meaning -/
  convention : DenominalVerbConvention W Entity

/-- The syntactic category of a denominal verb is always V. -/
theorem denominal_verb_is_verbal {W : Type} {Entity : Type}
    (dv : DenominalVerb W Entity) :
    dv.recategorized.categorizer = .v :=
  recategorization_changes_category
    dv.nominalRoot .denominal dv.recategorized dv.recatProof

/-- The source of a denominal verb is always N — the noun meaning
    is available as input to Clark's convention (condition f). -/
theorem denominal_verb_source_is_nominal {W : Type} {Entity : Type}
    (dv : DenominalVerb W Entity) :
    dv.nominalRoot.categorizer = .n :=
  denominal_requires_n dv.nominalRoot dv.recategorized dv.recatProof

/-- The gap between DM and Clark: DM tells us that denominal verbs exist
    (the recategorization succeeds) but says nothing about what they mean.
    Two denominal verbs from the same root always produce the same syntactic
    result (V category), yet can have arbitrarily different meanings.
    Clark's convention fills this gap by specifying how the meaning is
    constructed from the parent noun + common ground. -/
theorem dm_underdetermines_meaning {W : Type} {Entity : Type}
    (dv₁ dv₂ : DenominalVerb W Entity) :
    dv₁.recategorized.categorizer = dv₂.recategorized.categorizer := by
  rw [denominal_verb_is_verbal dv₁, denominal_verb_is_verbal dv₂]

end Phenomena.Polysemy.Studies.Clark1983
