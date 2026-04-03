import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Core.Semantics.Presupposition

/-!
# @cite{fillmore-kay-oconnor-1988}: Let Alone

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

-/

namespace ConstructionGrammar.Studies.FillmoreKayOConnor1988

open ConstructionGrammar

/-! ## Section 1: Idiom Typology (§1.1–1.2)

Fillmore et al.'s classification cross-cuts two dimensions:
- Encoding vs decoding
- Grammatical vs extragrammatical
- Substantive (lexically filled) vs formal (open slots)
-/

/-- Encoding vs decoding idioms (§1.1.1, @cite{makkai-1972}).

A *decoding* idiom cannot be interpreted without prior learning
("kick the bucket"). An *encoding* idiom can be understood but its
conventional status must be learned ("answer the door"). -/
inductive IdiomInterpretability where
  | decoding   -- must learn to interpret ("kick the bucket")
  | encoding   -- can interpret but must learn conventionality ("answer the door")
  deriving Repr, DecidableEq

/-- Grammatical vs extragrammatical idioms (§1.1.2).

*Grammatical* idioms have words filling proper grammatical slots
("kick the bucket"). *Extragrammatical* idioms have anomalous
structure ("first off", "by and large", "so far so good"). -/
inductive IdiomGrammaticality where
  | grammatical       -- "kick the bucket", "spill the beans"
  | extragrammatical  -- "first off", "by and large", "so far so good"
  deriving Repr, DecidableEq

/-- Substantive vs formal idioms (§1.1.3).

*Substantive* (lexically filled) idioms have fixed lexical content.
*Formal* idioms are syntactic patterns dedicated to semantic/pragmatic
purposes not knowable from form alone. -/
inductive IdiomFormality where
  | substantive  -- "kick the bucket" — fully specified lexically
  | formal       -- "the X-er the Y-er" — productive open pattern
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

/-! ## Section 2: Scalar Models (§2.3.2, Appendix)

The formal backbone of the paper: an n-dimensional scalar model
with a monotonicity constraint on propositional functions.

Definition A3: (S, T, D^x, P) is a SCALAR MODEL iff, for distinct
d_i, d_j in D^x, P(d_j) entails P(d_i) just in case d_i is LOWER than d_j.

Where "lower" means: d_i is lower than d_j iff no coordinate of d_i
has a higher value than the corresponding coordinate of d_j, and at
least one coordinate of d_i has a lower value (Definition A2). -/

/-- An argument point in the n-dimensional argument space D^x.
In the paper's example: (Apotheosis, English) is an argument point
in the 2D space of linguists × languages. -/
structure ArgumentPoint (α : Type*) where
  /-- Coordinates, one per dimension -/
  coordinates : List α
  deriving DecidableEq, Repr

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

In a valid scalar model, this holds exactly when d_i is lower than d_j. -/
def ScalarModel.entails {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  ∀ s, sm.propFn dj s = true → sm.propFn di s = true

/-- Informativeness/strength (Definition A5):
p is MORE INFORMATIVE (STRONGER) than q relative to a scalar model
iff p entails q in SM and q does not entail p in SM. -/
def ScalarModel.strongerThan {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  sm.entails dj di ∧ ¬sm.entails di dj

/-- Definition A3 validity: a scalar model satisfies the monotonicity
constraint iff for all distinct argument points d_i, d_j in D^x,
P(d_j) entails P(d_i) exactly when d_i is lower than d_j.

We check the forward direction (lower → entails) for all point pairs.
This is the computable check used by `native_decide`. -/
def ScalarModel.satisfiesA3 {S α : Type*} [BEq α]
    (sm : ScalarModel S α) (states : List S) : Bool :=
  sm.points.all λ di =>
    sm.points.all λ dj =>
      -- If di is lower than dj, then P(dj) entails P(di)
      if di.isLower sm.dimLe dj then
        states.all λ s => !(sm.propFn dj s) || sm.propFn di s
      else true

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
  deriving Repr, DecidableEq

/-- Clause ordering: *let alone* presents the stronger proposition first,
while *if not* and *in fact* present the weaker first (p.533). -/
def presentsStrongerFirst : LetAloneFamily → Bool
  | .letAlone     => true
  | .muchLess     => true
  | .notToMention => true
  | .neverMind    => true
  | .ifNot        => false
  | .inFact       => false

/-! ## Section 4: NPI status (§2.2.4)

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
  deriving Repr, DecidableEq

/-! ## Section 5: Construction definitions for the constructicon -/

/-- The X-er the Y-er comparative correlative (§1.2.1, exx.1-2).

A formal idiom with unfamiliar pieces unfamiliarly arranged. The
definite article "the" is unique to this construction (p.507) —
a fixed element — and the two-part structure has no parallel
elsewhere in English. The open comparative phrases make it
partially open (mix of fixed "the" and open comparatives). -/
def comparativeCorrelative : Construction :=
  { name := "the X-er the Y-er"
  , form := "[S [AdvP the+Compar] [S ...], [AP the+Compar] [S ...]]"
  , meaning := "The degree to which X correlates with the degree to which Y"
  , specificity := .partiallyOpen
  , pragmaticFunction := none }

/-- The Incredulity Response construction (§1.1.4, ex.14h).

"Him be a doctor?" — non-nominative subject + bare stem verb,
expressing incredulity. A formal idiom: the pattern (NP[acc] VP[bare])
is productive and dedicated to a rhetorical/evaluative pragmatic function
not derivable from its component meanings. -/
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

/-! ## Section 6: 1D Scalar Model — Military Ranks (§2.1, ex.21)

The running example: ⟨second lieutenant,..., colonel, general⟩. -/

/-- Military ranks from the paper's running example. -/
inductive Rank where
  | secondLieutenant | lieutenant | captain | major
  | colonel | general
  deriving Repr, DecidableEq

instance : Fintype Rank where
  elems := {.secondLieutenant, .lieutenant, .captain, .major, .colonel, .general}
  complete := λ x => by cases x <;> decide

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
  deriving Repr, DecidableEq

instance : Fintype AchievementState where
  elems := {.achievedNone, .achievedUpToLt, .achievedUpToCol, .achievedUpToGen}
  complete := λ x => by cases x <;> decide

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

/-- The rank scalar model satisfies Definition A3: for every pair
of points where d_i is lower than d_j, P(d_j) entails P(d_i). -/
theorem rank_model_valid :
    rankScalarModel.satisfiesA3
      [.achievedNone, .achievedUpToLt, .achievedUpToCol, .achievedUpToGen] = true := by
  native_decide

/-- The rank scalar model is one-dimensional: every argument point
has exactly one coordinate. The paper argues (fn.16, p.535) that
some examples require ≥2 dimensions. -/
theorem rank_model_is_1d :
    rankScalarModel.points.all (λ p => p.coordinates.length == 1) = true := by
  native_decide

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

/-- Making general is STRONGER than making colonel: the extension of
"made general" is a proper subset of "made colonel" (Definition A5). -/
theorem general_stronger_than_colonel :
    rankScalarModel.strongerThan ⟨[.general]⟩ ⟨[.colonel]⟩ :=
  ⟨general_entails_colonel, colonel_does_not_entail_general⟩

/-- Second lieutenant is the LOWEST point: no other rank is lower.
This explains the anomaly in ex.107: "let alone a second lieutenant"
is anomalous because you cannot scalar-entail the negation of the
lowest point from the negation of a non-lowest point (p.526). -/
theorem secondLieutenant_is_lowest :
    ∀ pt ∈ rankScalarModel.points,
      ¬ pt.isLower rankLe ⟨[.secondLieutenant]⟩ = true := by
  intro pt hpt h
  simp [rankScalarModel] at hpt
  rcases hpt with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ArgumentPoint.isLower, rankLe] at h

/-- The rank scalar model validates FKO's ex.21:
"He didn't make colonel, let alone general."

Under negation, the scalar direction reverses: "not make colonel"
entails "not make general" (if you can't do the easier thing, you
can't do the harder thing). -/
theorem ex21_scalar_condition_neg :
    ∀ s, madeRank .general s = true → madeRank .colonel s = true :=
  general_entails_colonel

/-! ## Section 7: 2D Scalar Model — Linguists × Languages (§2.3.2, Tables 1–4)

The paper's most carefully developed example: four professors
(Apotheosis, Brilliant, Competent, Dimm) and four languages
(English, French, Greek, Hittite), ordered by erudition and
accessibility respectively.

The propositional function P: "professor X can read language L"
is monotone: if X is more erudite and L is more accessible, P
is more likely to be true.

This 2D model is the basis for the Appendix definitions (A1–A5). -/

/-- Linguists ordered by erudition (most → least). -/
inductive Linguist where
  | apotheosis | brilliant | competent | dimm
  deriving Repr, DecidableEq

instance : Fintype Linguist where
  elems := {.apotheosis, .brilliant, .competent, .dimm}
  complete := λ x => by cases x <;> decide

/-- Languages ordered by accessibility (most → least). -/
inductive Lang where
  | english | french | greek | hittite
  deriving Repr, DecidableEq

instance : Fintype Lang where
  elems := {.english, .french, .greek, .hittite}
  complete := λ x => by cases x <;> decide

/-- Dimension value: either a linguist or a language.
The argument space D^x = Linguist × Lang, encoded as 2-element
coordinate lists of `LingLangVal`. -/
inductive LingLangVal where
  | ling : Linguist → LingLangVal
  | lang : Lang → LingLangVal
  deriving Repr, DecidableEq

/-- Dimension ordering (≤) for the linguist/language scalar model.

From Definition A2 (p.536) and the worked example on p.537: d_i is LOWER
than d_j when d_i has coordinatewise ≤ values with at least one strict.
A LOWER argument point yields a WEAKER proposition (true in more states).

- Linguist: Apotheosis ≤ Brilliant ≤ Competent ≤ Dimm
  (more erudite = LOWER = weaker — "Apotheosis reads L" is easiest to satisfy)
- Language: English ≤ French ≤ Greek ≤ Hittite
  (more accessible = LOWER = weaker — "X reads English" is easiest to satisfy)

The paper confirms (p.537): "(B, E) is lower than (B, G)" — Brilliant with
English is lower than Brilliant with Greek. Cross-type comparisons return
false (dimensions are independent). -/
def lingLangLe : LingLangVal → LingLangVal → Bool
  -- Linguist dimension: Apotheosis ≤ Brilliant ≤ Competent ≤ Dimm
  | .ling .apotheosis, .ling _ => true
  | .ling .brilliant,  .ling .apotheosis => false
  | .ling .brilliant,  .ling _ => true
  | .ling .competent,  .ling .apotheosis => false
  | .ling .competent,  .ling .brilliant => false
  | .ling .competent,  .ling _ => true
  | .ling .dimm,       .ling .dimm => true
  | .ling .dimm,       .ling _ => false
  -- Language dimension: English ≤ French ≤ Greek ≤ Hittite
  | .lang .english, .lang _ => true
  | .lang .french,  .lang .english => false
  | .lang .french,  .lang _ => true
  | .lang .greek,   .lang .english => false
  | .lang .greek,   .lang .french => false
  | .lang .greek,   .lang _ => true
  | .lang .hittite, .lang .hittite => true
  | .lang .hittite, .lang _ => false
  -- Cross-dimension: incomparable
  | .ling _, .lang _ => false
  | .lang _, .ling _ => false

/-- States of affairs for the linguist/language model.
Each state specifies which (linguist, language) pairs satisfy
"X can read L". We use a few representative states from Table 2
in the paper (p.527). -/
inductive LLState where
  | allFalse    -- Table 2a: nobody reads anything
  | topLeft     -- Table 2b: only Apotheosis reads English
  | twoTrue     -- Table 2c: Apotheosis reads English & French, Brilliant reads English
  | allTrue     -- Table 2d: everybody reads everything
  | diagonal    -- Apotheosis reads all, Brilliant reads Eng/Fr/Gr, Competent reads Eng/Fr, Dimm reads Eng
  deriving Repr, DecidableEq

instance : Fintype LLState where
  elems := {.allFalse, .topLeft, .twoTrue, .allTrue, .diagonal}
  complete := λ x => by cases x <;> decide

/-- "Professor X can read language L" in each state.
The diagonal state is the paper's primary example: knowledge
forms a staircase from the 1-corner (Apotheosis, English) outward. -/
def canRead : Linguist → Lang → LLState → Bool
  | _, _, .allFalse => false
  | _, _, .allTrue  => true
  | .apotheosis, .english, .topLeft => true
  | _, _, .topLeft => false
  | .apotheosis, .english, .twoTrue => true
  | .apotheosis, .french, .twoTrue  => true
  | .brilliant, .english, .twoTrue  => true
  | _, _, .twoTrue => false
  -- Diagonal: staircase pattern
  | .apotheosis, _, .diagonal => true
  | .brilliant, .hittite, .diagonal => false
  | .brilliant, _, .diagonal => true
  | .competent, .english, .diagonal => true
  | .competent, .french, .diagonal  => true
  | .competent, _, .diagonal => false
  | .dimm, .english, .diagonal => true
  | .dimm, _, .diagonal => false

/-- Convenience constructor for 2D argument points. -/
def llPoint (l : Linguist) (lang : Lang) : ArgumentPoint LingLangVal :=
  ⟨[.ling l, .lang lang]⟩

/-- The linguist/language scalar model from §2.3.2 (Tables 1–4, p.526–527). -/
def linguistLangModel : ScalarModel LLState LingLangVal :=
  { points := do
      let l ← [Linguist.apotheosis, .brilliant, .competent, .dimm]
      let lang ← [Lang.english, .french, .greek, .hittite]
      return llPoint l lang
  , propFn := λ pt =>
      match pt.coordinates with
      | [.ling l, .lang lang] => canRead l lang
      | _ => λ _ => false
  , dimLe := lingLangLe }

/-- The linguist/language model is two-dimensional. -/
theorem ll_model_is_2d :
    linguistLangModel.points.all (λ p => p.coordinates.length == 2) = true := by
  native_decide

/-- The 2D model satisfies Definition A3. -/
theorem ll_model_valid :
    linguistLangModel.satisfiesA3
      [.allFalse, .topLeft, .twoTrue, .allTrue, .diagonal] = true := by
  native_decide

/-- In the 2D model, "Brilliant can read Hittite" entails
"Brilliant can read English" — Hittite is less accessible,
so knowing it is stronger (p.528, exx.109–112). -/
theorem brilliant_hittite_entails_english :
    linguistLangModel.entails (llPoint .brilliant .hittite) (llPoint .brilliant .english) := by
  intro s h; cases s <;> simp_all [linguistLangModel, llPoint, canRead]

/-- "Brilliant can read Hittite" is stronger than
"Competent can read French" (Definition A5). Note: these
points are INCOMPARABLE in the partial order (Brilliant < Competent
on linguist, Hittite > French on language), but the entailment
holds empirically — the scalar model constrains more than just
comparable pairs. -/
theorem brilliant_hittite_stronger_than_competent_french :
    linguistLangModel.strongerThan
      (llPoint .brilliant .hittite) (llPoint .competent .french) := by
  constructor
  · intro s h; cases s <;> simp_all [linguistLangModel, llPoint, canRead]
  · intro h; have := h .diagonal; simp [linguistLangModel, llPoint, canRead] at this

/-- (Brilliant, English) is lower than (Brilliant, Greek): the paper's
own worked example (p.537). Same linguist, but English is more
accessible (lower) than Greek. -/
theorem brilliant_english_lower_than_brilliant_greek :
    (llPoint .brilliant .english).isLower lingLangLe (llPoint .brilliant .greek) = true := by
  native_decide

/-- (Competent, French) and (Brilliant, Hittite) are INCOMPARABLE:
Competent > Brilliant on linguist but French < Hittite on language.
Neither is uniformly ≤ the other (Definition A2). -/
theorem competent_french_incomparable_brilliant_hittite :
    (llPoint .competent .french).isLower lingLangLe (llPoint .brilliant .hittite) = false ∧
    (llPoint .brilliant .hittite).isLower lingLangLe (llPoint .competent .french) = false := by
  constructor <;> native_decide

end ConstructionGrammar.Studies.FillmoreKayOConnor1988
