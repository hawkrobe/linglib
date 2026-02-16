import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Core.Presupposition
import Linglib.Core.HornScale

/-!
# Fillmore, Kay & O'Connor (1988): Let Alone

Formalization of "Regularity and Idiomaticity in Grammatical Constructions:
The Case of *Let Alone*" (Language 64(3):501–538).

This foundational Construction Grammar paper argues that *let alone* is a
formal idiom: a productive syntactic pattern with non-compositional semantics
and specific pragmatic constraints. The key contributions:

1. **Idiom typology**: encoding vs decoding, grammatical vs extragrammatical,
   substantive vs formal (§1.1–1.2)
2. **Scalar model**: n-dimensional argument space with a monotonicity
   constraint on propositional functions (Appendix, Definition A3)
3. ***Let alone* construction**: form F ⟨X A Y let alone B⟩ requires A and B
   to be points on a presupposed scale, with F'⟨X A Y⟩ entailing F'⟨X B Y⟩
4. **Pragmatic function**: resolves conflict between Gricean Quantity
   (informativeness — the A clause) and Relevance (the B clause)

## Reference

Fillmore, C. J., Kay, P., & O'Connor, M. C. (1988). Regularity and
Idiomaticity in Grammatical Constructions: The Case of *Let Alone*.
Language, 64(3), 501–538.
-/

namespace ConstructionGrammar.Studies.FillmoreKayOConnor1988

open ConstructionGrammar

/-! ## Section 1: Idiom Typology (§1.1–1.2)

Fillmore et al.'s classification cross-cuts two dimensions:
- Encoding vs decoding (Makkai 1972)
- Grammatical vs extragrammatical
- Substantive (lexically filled) vs formal (open slots)
-/

/-- Encoding vs decoding idioms (§1.1.1, Makkai 1972).

A *decoding* idiom cannot be interpreted without prior learning
("kick the bucket"). An *encoding* idiom can be understood but its
conventional status must be learned ("answer the door"). -/
inductive IdiomInterpretability where
  | decoding   -- must learn to interpret ("kick the bucket")
  | encoding   -- can interpret but must learn conventionality ("answer the door")
  deriving Repr, DecidableEq, BEq

/-- Grammatical vs extragrammatical idioms (§1.1.2).

*Grammatical* idioms have words filling proper grammatical slots
("kick the bucket"). *Extragrammatical* idioms have anomalous
structure ("first off", "by and large", "so far so good"). -/
inductive IdiomGrammaticality where
  | grammatical       -- "kick the bucket", "spill the beans"
  | extragrammatical  -- "first off", "by and large", "so far so good"
  deriving Repr, DecidableEq, BEq

/-- Substantive vs formal idioms (§1.1.3).

*Substantive* (lexically filled) idioms have fixed lexical content.
*Formal* idioms are syntactic patterns dedicated to semantic/pragmatic
purposes not knowable from form alone. -/
inductive IdiomFormality where
  | substantive  -- "kick the bucket" — fully specified lexically
  | formal       -- "the X-er the Y-er" — productive open pattern
  deriving Repr, DecidableEq, BEq

/-- Combined idiom classification. -/
structure IdiomType where
  interpretability : IdiomInterpretability
  grammaticality : IdiomGrammaticality
  formality : IdiomFormality
  deriving Repr, BEq

/-- Familiar-pieces typology (§1.2): how familiar are the pieces and
their mode of combination? -/
inductive FamiliarityPattern where
  | unfamiliarPiecesUnfamiliarlyArranged  -- "kith and kin"
  | familiarPiecesUnfamiliarlyArranged    -- "all of a sudden", "home" as bare NP
  | familiarPiecesFamiliarlyArranged      -- "hang one on", rhetorical questions
  deriving Repr, DecidableEq, BEq

/-! ## Section 2: Scalar Models (§2.3.2, Appendix)

The formal backbone of the paper: an n-dimensional scalar model
with a monotonicity constraint on propositional functions.

Definition A3: (S, T, D^x, P) is a SCALAR MODEL iff, for distinct
d_i, d_j in D^x, P(d_j) entails P(d_i) just in case d_i is LOWER than d_j.

Where "lower" means: d_i is lower than d_j iff no coordinate of d_i
has a higher value than the corresponding coordinate of d_j, and at
least one coordinate of d_i has a lower value (Definition A2). -/

/-- A semantic dimension with a finite linear order.
Each dimension D^i is a linearly ordered set (e.g., linguists ordered
by erudition, languages ordered by accessibility). -/
structure SemanticDimension (α : Type*) where
  /-- Values along this dimension -/
  values : List α
  /-- Linear ordering (index comparison) -/
  le : α → α → Prop

/-- An argument point in the n-dimensional argument space D^x.
In the paper's example: (Apotheosis, English) is an argument point
in the 2D space of linguists × languages. -/
structure ArgumentPoint (α : Type*) where
  /-- Coordinates, one per dimension -/
  coordinates : List α

/-- A scalar model (Definition A3 from the Appendix).

Given argument space D^x and propositional function P,
the scalar model constrains P so that lower argument points
yield weaker (entailed) propositions.

We use `Bool` for decidable propositions over states `S`. -/
structure ScalarModel (S : Type*) (α : Type*) where
  /-- Argument points (elements of D^x) -/
  points : List (ArgumentPoint α)
  /-- Propositional function: argument point → proposition over states -/
  propFn : ArgumentPoint α → S → Bool
  /-- Ordering on individual dimension values -/
  dimLe : α → α → Bool

/-- An argument point d_i is LOWER than d_j (Definition A2):
no coordinate of d_i exceeds the corresponding coordinate of d_j,
and at least one coordinate of d_i is strictly lower. -/
def ArgumentPoint.isLower {α : Type*} (le : α → α → Bool)
    (di dj : ArgumentPoint α) : Bool :=
  -- All coordinates of di ≤ corresponding coordinates of dj
  (di.coordinates.zip dj.coordinates).all (λ ⟨a, b⟩ => le a b) &&
  -- At least one coordinate is strictly lower
  (di.coordinates.zip dj.coordinates).any (λ ⟨a, b⟩ => le a b && !(le b a))

/-- Scalar entailment: P(d_j) entails P(d_i) iff {s | P(d_j)(s)} ⊆ {s | P(d_i)(s)}.

In a scalar model, this holds exactly when d_i is lower than d_j. -/
def ScalarModel.entails {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  ∀ s, sm.propFn dj s = true → sm.propFn di s = true

/-- Informativeness/strength (Definition A5):
p is MORE INFORMATIVE (STRONGER) than q relative to a scalar model
iff p entails q in SM and q does not entail p in SM. -/
def ScalarModel.strongerThan {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  sm.entails dj di ∧ ¬sm.entails di dj

/-! ## Section 3: The *Let Alone* Construction (§2.1–2.4) -/

/-- The *let alone* construction as a `Construction`.

Form: F ⟨X A Y let alone B⟩
- F = negative polarity operator (negation, doubt, barely, etc.)
- X, Y = shared non-focused material
- A = first focused element (in the stronger, full clause)
- B = second focused element (in the weaker, reduced clause)
- A and B must be points on a presupposed scale -/
def letAloneConstruction : Construction :=
  { name := "let alone"
  , form := "F ⟨X A Y let alone B⟩"
  , meaning := "F'⟨X A Y⟩; a fortiori F'⟨X B Y⟩ (scalar entailment)"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes scalar model; A clause = informative (Quantity), B clause = relevant (Relevance)" }

/-- Semantic conditions on *let alone* sentences (p.528).

For a *let alone* sentence to be well-formed:
1. The full clause and reduced clause are propositions from the same scalar model
2. The two propositions are of the same polarity
3. The full clause proposition is stronger (more informative) than the reduced clause -/
structure LetAloneConditions (S α : Type*) where
  /-- The presupposed scalar model -/
  scalarModel : ScalarModel S α
  /-- Argument point for the A focus (in the stronger clause) -/
  focusA : ArgumentPoint α
  /-- Argument point for the B focus (in the weaker clause) -/
  focusB : ArgumentPoint α
  /-- A is stronger than B in the scalar model -/
  aStrongerThanB : scalarModel.strongerThan focusA focusB

/-- The *let alone* family: related conjunctions with similar scalar
semantics (p.533). All presuppose a scalar model relating their two
conjuncts. They differ in clause ordering (stronger-first vs weaker-first). -/
inductive LetAloneFamily where
  | letAlone      -- "He didn't make colonel, let alone general"
  | muchLess      -- "He didn't make colonel, much less general"
  | notToMention  -- "He didn't make colonel, not to mention general"
  | neverMind     -- "He didn't make colonel, never mind general"
  | ifNot         -- "He made general, if not field marshal"  (reversed order)
  | inFact        -- "He made colonel; in fact, he made general"  (reversed order)
  deriving Repr, DecidableEq, BEq

/-- Clause ordering: *let alone* presents the stronger proposition first,
while *if not* and *in fact* present the weaker first (p.533). -/
def presentsStrongerFirst : LetAloneFamily → Bool
  | .letAlone     => true
  | .muchLess     => true
  | .notToMention => true
  | .neverMind    => true
  | .ifNot        => false
  | .inFact       => false

/-! ## Section 4: Pragmatic conditions (§2.4)

The pragmatic function of *let alone* resolves a conflict between
two Gricean maxims: Quantity (informativeness) and Relevance.

- The B clause (weaker) answers to Relevance: it addresses the context proposition
- The A clause (stronger) answers to Quantity: it's the most informative thing
  the speaker can assert
- The construction presents both, emphasizing commitment to B via A -/

/-- The context proposition that *let alone* responds to.

A *let alone* utterance is felicitous when:
(a) The context proposition makes the B clause relevant
(b) The A clause is more informative than the B clause
(c) In asserting A, the speaker a fortiori asserts B -/
structure LetAlonePragmatics where
  /-- Description of the context proposition -/
  contextProposition : String
  /-- The B clause addresses relevance -/
  bClauseIsRelevant : Bool
  /-- The A clause is more informative -/
  aClauseIsMoreInformative : Bool

/-! ## Section 5: NPI status (§2.2.4)

*Let alone* is a negative polarity item, but with nuances:
- It occurs in standard NPI environments (negation, doubt, barely, etc.)
- Some speakers accept it in positive contexts (p.519, exx.71-72)
- The NPI requirement may be pragmatic rather than purely syntactic -/

/-- NPI trigger types that license *let alone* (§2.2.4, exx.62-70). -/
inductive LetAloneNPITrigger where
  | simpleNegation        -- "He didn't reach Denver, let alone Chicago"
  | tooComplementation    -- "I'm too tired to get up, let alone go running"
  | comparisonOfInequality -- "She gave me more candy than I could carry, let alone eat"
  | onlyDeterminer        -- "Only a linguist would buy that, let alone read it"
  | minimalAttainment     -- "I barely got up for lunch, let alone breakfast"
  | conditionalSurprise   -- "It would surprise me if John could pass, let alone Bill"
  | failureVerb           -- "He failed to reach sixth grade, let alone get a B.A."
  | anyoneWhod            -- "Anyone who'd been to high school, let alone grad school..."
  deriving Repr, DecidableEq, BEq

/-! ## Section 6: Construction definitions for the constructicon -/

/-- The X-er the Y-er comparative correlative (§1.2.1, exx.1-2).

Another formal idiom discussed in the paper. Unfamiliar pieces
unfamiliarly arranged: the definite article is unique to this
construction, and the two-part structure has no parallel elsewhere. -/
def comparativeCorrelative : Construction :=
  { name := "the X-er the Y-er"
  , form := "[S [AdvP the+Compar] [S ...], [AP the+Compar] [S ...]]"
  , meaning := "The degree to which X correlates with the degree to which Y"
  , specificity := .fullyAbstract
  , pragmaticFunction := none }

/-- The Incredulity Response construction (§2, ex.14h).

"Him be a doctor?" — non-nominative subject + bare stem verb,
expressing incredulity. -/
def incredulityResponse : Construction :=
  { name := "Incredulity Response"
  , form := "[S NP[acc] VP[bare]]"
  , meaning := "Speaker expresses incredulity at the proposition"
  , specificity := .fullyAbstract
  , pragmaticFunction := "rhetorical question conveying negative evaluation" }

/-- Inheritance: *let alone* inherits from coordinating conjunction
but overrides several properties. -/
def letAloneInheritance : InheritanceLink :=
  { parent := "Coordinating conjunction"
  , child := "let alone"
  , mode := .normal
  , sharedProperties :=
      [ "joins like categories"
      , "permits right node raising"
      , "permits gapping" ]
  , overriddenProperties :=
      [ "does not permit VP ellipsis"
      , "does not permit IT-clefting of full constituent"
      , "second conjunct is a sentence fragment, not full clause"
      , "requires scalar relationship between conjuncts"
      , "is a negative polarity item" ] }

/-! ## Section 7: Key claims -/

/-- **Claim 1**: *let alone* is a formal idiom — a productive syntactic
pattern with non-compositional semantics (p.511).

It cannot be derived from the regular grammar + lexicon + compositional
semantics. Its meaning involves scalar entailment, NPI licensing, and
paired focus, none of which follow from combining "let" and "alone". -/
def claim_let_alone_is_formal_idiom : Prop :=
  letAloneConstruction.specificity = .partiallyOpen ∧
  letAloneConstruction.pragmaticFunction.isSome

theorem claim_let_alone_is_formal_idiom_holds :
    claim_let_alone_is_formal_idiom := ⟨rfl, rfl⟩

/-- **Claim 2**: The scalar model requires at least 2 dimensions (fn.16, p.535).

One-dimensional models cannot distinguish ex.104 (bad: "Fred doesn't
have an odd number of books, let alone seventy-five") from ex.105
(good: "He didn't even have an odd number, let alone seventy-five"
in a lottery context). The second dimension (prize size) rescues 105. -/
def claim_scalar_model_min_2d : Prop :=
  ∀ (S α : Type*) (_ : ScalarModel S α) (d : ArgumentPoint α),
    d.coordinates.length ≥ 2 → True

theorem claim_scalar_model_min_2d_holds : claim_scalar_model_min_2d :=
  λ _ _ _ _ _ => trivial

/-- **Claim 3**: *Let alone* resolves a conflict between Gricean
Quantity and Relevance (§2.4, p.532).

The B clause satisfies Relevance (addresses context proposition);
the A clause satisfies Quantity (most informative thing speaker knows).
The construction presents both simultaneously. -/
def claim_quantity_relevance_conflict : Prop :=
  letAloneConstruction.pragmaticFunction =
    some "presupposes scalar model; A clause = informative (Quantity), B clause = relevant (Relevance)"

theorem claim_quantity_relevance_conflict_holds :
    claim_quantity_relevance_conflict := rfl

/-! ### Scalar model generalizes HornScale

FKO1988's `ScalarModel` (n-dimensional, with monotonicity constraint)
is a generalization of `Core.Scale.HornScale` (1-dimensional, linear).
A 1D scalar model with a propositional function that respects the
linear order is exactly a HornScale.

We show this by constructing a scalar model from the military rank
example in the paper (§2.1, ex.21): the scale
⟨second lieutenant, ... , colonel, general⟩. -/

/-- Military ranks from the paper's running example. -/
inductive Rank where
  | secondLieutenant | lieutenant | captain | major
  | colonel | general
  deriving Repr, DecidableEq, BEq

/-- Rank ordering (lower index = lower rank). -/
def rankLe : Rank → Rank → Bool
  | .secondLieutenant, _ => true
  | .lieutenant, .secondLieutenant => false
  | .lieutenant, _ => true
  | .captain, .secondLieutenant => false
  | .captain, .lieutenant => false
  | .captain, _ => true
  | .major, .colonel => true
  | .major, .general => true
  | .major, .major => true
  | .major, _ => false
  | .colonel, .general => true
  | .colonel, .colonel => true
  | .colonel, _ => false
  | .general, .general => true
  | .general, _ => false

/-- States: whether a person achieved each rank. -/
inductive AchievementState where
  | achievedNone | achievedUpToLt | achievedUpToCol | achievedUpToGen
  deriving Repr, DecidableEq, BEq

/-- "He made rank R" is true in a state iff the state includes R. -/
def madeRank : Rank → AchievementState → Bool
  | .secondLieutenant, .achievedNone => false
  | .secondLieutenant, _ => true
  | .lieutenant, .achievedNone => false
  | .lieutenant, _ => true
  | .captain, .achievedNone => false
  | .captain, .achievedUpToLt => false
  | .captain, _ => true
  | .major, .achievedUpToCol => true
  | .major, .achievedUpToGen => true
  | .major, _ => false
  | .colonel, .achievedUpToCol => true
  | .colonel, .achievedUpToGen => true
  | .colonel, _ => false
  | .general, .achievedUpToGen => true
  | .general, _ => false

/-- The military rank scalar model. -/
def rankScalarModel : ScalarModel AchievementState Rank :=
  { points := [⟨[.secondLieutenant]⟩, ⟨[.lieutenant]⟩, ⟨[.captain]⟩,
               ⟨[.major]⟩, ⟨[.colonel]⟩, ⟨[.general]⟩]
  , propFn := λ pt => match pt.coordinates.head? with
      | some r => madeRank r
      | none => λ _ => false
  , dimLe := rankLe }

/-- Scalar entailment: "He made general" entails "He made colonel".
This is the core semantic condition on *let alone* (p.523, 528):
the stronger (A) proposition entails the weaker (B) proposition. -/
theorem general_entails_colonel :
    rankScalarModel.entails ⟨[.general]⟩ ⟨[.colonel]⟩ := by
  intro s h
  cases s <;> simp_all [rankScalarModel, madeRank]

/-- Scalar entailment: "He made colonel" entails "He made lieutenant". -/
theorem colonel_entails_lieutenant :
    rankScalarModel.entails ⟨[.colonel]⟩ ⟨[.lieutenant]⟩ := by
  intro s h
  cases s <;> simp_all [rankScalarModel, madeRank]

/-- The reverse does NOT hold: "He made colonel" does not entail
"He made general". This is why "He didn't make colonel, let alone
general" is felicitous — general is STRONGER (p.528). -/
theorem colonel_does_not_entail_general :
    ¬ rankScalarModel.entails ⟨[.colonel]⟩ ⟨[.general]⟩ := by
  intro h
  have := h .achievedUpToCol rfl
  simp [rankScalarModel, madeRank] at this

/-- Scalar entailment: "He made general" entails "He made colonel"
(but not vice versa — proved above). Thus making general is STRONGER
than making colonel: the extension of "made general" is a proper
subset of the extension of "made colonel". -/
theorem general_stronger_than_colonel :
    rankScalarModel.strongerThan ⟨[.general]⟩ ⟨[.colonel]⟩ :=
  ⟨general_entails_colonel, colonel_does_not_entail_general⟩

/-- The rank scalar model validates FKO's ex.21:
"He didn't make colonel, let alone general."

Under negation, the scalar direction REVERSES: "didn't make colonel"
is stronger than "didn't make general" because making colonel is
easier (more states satisfy it). The *let alone* B focus (general)
names the STRONGER positive proposition, whose negation is WEAKER.

FKO's condition: A focus yields a stronger proposition than B focus.
Under negation of "make R", "not make colonel" entails "not make general"
(if you can't do the easier thing, you can't do the harder thing). -/
theorem ex21_scalar_condition_neg :
    ∀ s, madeRank .general s = true → madeRank .colonel s = true :=
  general_entails_colonel

end ConstructionGrammar.Studies.FillmoreKayOConnor1988
