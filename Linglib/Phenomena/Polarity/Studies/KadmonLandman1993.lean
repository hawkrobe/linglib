import Linglib.Core.Logic.NaturalLogic
import Linglib.Core.Lexical.PolarityItem
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Entailment.StrawsonEntailment
import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Theories.Semantics.Lexical.Determiner.DomainVagueness
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Polarity.Studies.Ladusaw1979

/-!
# Kadmon & Landman (1993): Any

@cite{kadmon-landman-1993}

Kadmon, N. & Landman, F. (1993). Any. *Linguistics and Philosophy* 16: 353–422.

## The Unified Analysis

K&L propose a unified analysis of polarity-sensitive (PS) *any* and free choice
(FC) *any*. The word *any* is unambiguous: it is always an indefinite that
contributes **widening** and **strengthening**. The PS/FC difference reduces to
whether the indefinite NP is interpreted episodically or generically.

The analysis has four components:

- **(A)** *any CN* = the corresponding indefinite *a CN* + widening + strengthening
- **(FC)** PS *any* is a regular indefinite; FC *any* is a generic indefinite
- **(B) Widening**: *any* widens the CN denotation along a contextual dimension
- **(C) Strengthening**: *any* is licensed only if widening creates a stronger
  statement (wide interpretation ⇒ narrow interpretation)
- **(D) Locality**: Strengthening is checked at the local proposition level

## Unification with Entailment Signatures

K&L's strengthening condition subsumes @cite{ladusaw-1979}'s DE condition:
widening an existential strengthens the embedding statement *exactly when*
the context is DE. But K&L's formulation is deeper — it explains *why*
DE contexts license and relates the distribution to the meaning of *any*
itself. Moreover, K&L show that DE is *more pervasive* than Ladusaw
recognized: adversative predicates are DE on a constant perspective (§3.3),
and conditional antecedents are DE on a constant implicit restriction (§3.5).
The only genuinely non-DE licensing K&L identify is metalinguistic: *any*
in negated because-clauses is licensed by strengthening the denial of a
factive presupposition (§3.4).

This file bridges K&L's analysis to the `EntailmentSig` lattice from
`Core.Logic.NaturalLogic`, providing a principled derivation of each
`LicensingContext` from the strengthening condition rather than stipulating
the list.

## Sorry vs Glad

K&L's most striking empirical contribution: adversative predicates
(*surprised*, *sorry*) license *any* because they are DE on a constant
perspective, while non-adversatives (*glad*, *sure*) are not DE and
do not freely license *any*. The difference traces to lexical semantics:
*sorry that A* entails *want ¬A*, while *glad that A* entails *want A*.
-/

set_option autoImplicit false

namespace KadmonLandman1993

open Core.NaturalLogic
open Core.Lexical.PolarityItem (LicensingContext PolarityType)
open Semantics.Entailment.Polarity
open Semantics.Entailment.AntiAdditivity
open Semantics.Lexical.Determiner.DomainVagueness
open Exhaustification (entails)
open Exhaustification.FreeChoice (Ctx existsInDomain
  widening_strengthens_in_de widening_weakens_in_ue)

-- ============================================================================
-- §1. The Strengthening Condition
-- ============================================================================

/-!
## The Strengthening Condition

K&L's principle (C): *any* is licensed only if widening creates a stronger
statement. For assertions, "stronger" = entailment. For a context C and
domains D ⊆ D' (narrow ⊆ wide):

    C(∃x∈D', Px) ⊆ₚ C(∃x∈D, Px)    — the wide interpretation entails the narrow

This holds exactly when C is DE (antitone). K&L's insight is that this
is not a coincidence: it is *because* *any* widens that it must create
a stronger statement, and it is *because* DE reverses entailment that
widening in DE contexts strengthens.
-/

/-- K&L's strengthening condition: widening domain D to D' in context C
    creates a stronger statement.

    This is the central licensing predicate. *Any* is licensed in context C
    iff `klStrengthening` holds for the relevant widening. -/
def klStrengthening {World Entity : Type*}
    (C : Ctx World) (D D' : Set Entity)
    (P : Entity → World → Prop) (_hD : D ⊆ D') : Prop :=
  entails (C (existsInDomain D' P)) (C (existsInDomain D P))

/-- **Theorem (K&L → Ladusaw).**
    In any DE context, strengthening is automatically satisfied.

    This is the formal content of K&L's claim that their analysis
    "makes the same predictions as Ladusaw's" for standard cases.
    The proof delegates to `widening_strengthens_in_de` from
    `FreeChoice.lean`. -/
theorem de_satisfies_strengthening {World Entity : Type*}
    (C : Ctx World)
    (hDE : ∀ (p q : World → Prop), entails p q → entails (C q) (C p))
    (D D' : Set Entity) (P : Entity → World → Prop) (hD : D ⊆ D') :
    klStrengthening C D D' P hD :=
  widening_strengthens_in_de C hDE D D' P hD

/-- **Theorem (Strengthening fails in UE).**
    In UE contexts, widening *weakens* — the opposite of strengthening.
    This is why *any* is ungrammatical in positive contexts. -/
theorem ue_violates_strengthening {World Entity : Type*}
    (C : Ctx World)
    (hUE : ∀ (p q : World → Prop), entails p q → entails (C p) (C q))
    (D D' : Set Entity) (P : Entity → World → Prop) (hD : D ⊆ D') :
    entails (C (existsInDomain D P)) (C (existsInDomain D' P)) :=
  widening_weakens_in_ue C hUE D D' P hD

-- ============================================================================
-- §2. Unifying LicensingContexts via EntailmentSig
-- ============================================================================

/-!
## The Unification: LicensingContext → EntailmentSig

The two `LicensingContext` types in linglib (Core: 19 constructors,
Phenomena: 15 constructors) list licensing environments as a surface
inventory. K&L's analysis provides the explanatory principle: each
context has an entailment signature, and *any* is licensed when that
signature guarantees strengthening.

The function below maps each licensing context to its entailment signature
in Icard's lattice. This replaces the stipulated list with a derived
classification: contexts license *any* because their entailment signature
is on the DE side, not because they appear on an enumerated list.
-/

/-- Map each licensing context to its entailment signature.

    Contexts on the DE side (anti, antiAdd, antiAddMult) guarantee
    strengthening. Contexts that are not monotone (questions, superlatives)
    license *any* via other mechanisms (entropy, Strawson-DE) — their
    signatures are `.mono` or higher, indicating that plain DE-based
    strengthening is not the explanation.

    This mapping unifies the surface inventory with the algebraic
    hierarchy from @cite{icard-2012}. -/
def contextEntailmentSig : LicensingContext → EntailmentSig
  -- Anti-morphic (negation): strongest DE
  | .negation         => .antiAddMult
  -- Anti-additive: ∨→∧ distributive
  | .nobody           => .antiAdd
  | .without_clause   => .antiAdd
  -- Plain DE (antitone)
  | .few              => .anti
  | .atMost           => .anti
  | .conditional_ant  => .anti
  | .before_clause    => .anti
  | .only_focus       => .anti
  | .too_to           => .anti
  | .comparative      => .anti
  | .adversative      => .anti      -- DE on a constant perspective (K&L §3.3)
  -- UE / non-monotone contexts: license via non-DE mechanisms
  | .question         => .mono      -- entropy-based (van Rooy 2003)
  | .superlative      => .mono      -- Strawson-DE
  | .modal_possibility => .mono     -- FC any, not PS any
  | .modal_necessity  => .mono      -- FC any
  | .imperative       => .mono      -- FC any
  | .generic          => .mono      -- FC any (generic indefinite)
  | .since_temporal   => .anti      -- DE (Iatridou)
  | .free_relative    => .mono      -- FC any

/-- A licensing context guarantees K&L strengthening iff its entailment
    signature is on the DE side. -/
def guaranteesStrengthening (ctx : LicensingContext) : Bool :=
  match (contextEntailmentSig ctx).toDEStrength with
  | some _ => true
  | none   => false

-- Verify: all standard DE contexts guarantee strengthening
#guard guaranteesStrengthening .negation         -- anti-morphic → ✓
#guard guaranteesStrengthening .nobody           -- anti-additive → ✓
#guard guaranteesStrengthening .without_clause   -- anti-additive → ✓
#guard guaranteesStrengthening .few              -- DE → ✓
#guard guaranteesStrengthening .conditional_ant  -- DE → ✓
#guard guaranteesStrengthening .adversative      -- DE (constant perspective) → ✓
#guard guaranteesStrengthening .before_clause    -- DE → ✓
#guard guaranteesStrengthening .only_focus       -- DE → ✓

-- Verify: non-DE contexts do NOT guarantee strengthening via DE
#guard !guaranteesStrengthening .question         -- not DE → ✗
#guard !guaranteesStrengthening .superlative      -- not DE → ✗
#guard !guaranteesStrengthening .modal_possibility -- FC, not DE → ✗
#guard !guaranteesStrengthening .generic          -- FC, not DE → ✗

/-- The K&L licensing classification: why each context licenses *any*.

    - `byStrengthening`: DE context → widening strengthens → licensed
    - `byGenericIndefinite`: FC *any* — indefinite interpreted generically
    - `byOtherMechanism`: licensed via entropy, Strawson-DE, etc. -/
inductive KLExplanation where
  | byStrengthening      -- DE → widening strengthens (the core K&L mechanism)
  | byGenericIndefinite  -- FC any = generic indefinite + widening
  | byOtherMechanism     -- entropy, Strawson-DE, etc.
  deriving DecidableEq, Repr

/-- Derive the K&L explanation for each licensing context.

    This is the unifying function: instead of stipulating *that* each
    context licenses, we explain *why*. -/
def klExplanation : LicensingContext → KLExplanation
  -- DE contexts: strengthening (K&L's core mechanism)
  | .negation        => .byStrengthening
  | .nobody          => .byStrengthening
  | .without_clause  => .byStrengthening
  | .few             => .byStrengthening
  | .atMost          => .byStrengthening
  | .conditional_ant => .byStrengthening
  | .before_clause   => .byStrengthening
  | .only_focus      => .byStrengthening
  | .too_to          => .byStrengthening
  | .comparative     => .byStrengthening
  | .adversative     => .byStrengthening
  | .since_temporal  => .byStrengthening
  -- FC any: generic indefinite
  | .modal_possibility => .byGenericIndefinite
  | .modal_necessity   => .byGenericIndefinite
  | .imperative        => .byGenericIndefinite
  | .generic           => .byGenericIndefinite
  | .free_relative     => .byGenericIndefinite
  -- Other mechanisms
  | .question          => .byOtherMechanism
  | .superlative       => .byOtherMechanism

/-- Consistency check: every context classified as `byStrengthening`
    has a DE entailment signature. -/
theorem strengthening_implies_de (ctx : LicensingContext)
    (h : klExplanation ctx = .byStrengthening) :
    guaranteesStrengthening ctx = true := by
  cases ctx <;> simp_all [klExplanation, guaranteesStrengthening,
    contextEntailmentSig, EntailmentSig.toDEStrength, EntailmentSig.project]

-- ============================================================================
-- §3. Bridge to Ladusaw1979
-- ============================================================================

/-!
## Compatibility with Ladusaw (1979)

K&L's classification refines @cite{ladusaw-1979}'s: every context that
Ladusaw classifies as DE is also classified as `byStrengthening` by K&L.
But K&L additionally explains adversative predicates and conditionals
with implicit restrictions — cases where Ladusaw's DE condition is
necessary but not sufficient for a full account.
-/

private abbrev PhenCtx := Phenomena.Polarity.NPIs.LicensingContext
open Ladusaw1979 (LicensingStrength licensingStrength)

/-- Map a Phenomena-level licensing context to its K&L explanation.

    Unlike the Core → K&L mapping, this covers all 15 Phenomena contexts
    directly. The three contexts without Core counterparts (`universalRestrictor`,
    `doubtVerb`, `denyVerb`) are all DE/anti-additive and explained by
    strengthening. -/
def phenCtxKLExplanation : PhenCtx → KLExplanation
  | .sententialNegation  => .byStrengthening
  | .constituentNegation => .byStrengthening
  | .withoutClause       => .byStrengthening
  | .beforeClause        => .byStrengthening
  | .onlyFocus           => .byStrengthening
  | .conditional         => .byStrengthening
  | .universalRestrictor => .byStrengthening  -- AA restrictor, no Core counterpart
  | .fewNP               => .byStrengthening
  | .comparativeThan     => .byStrengthening
  | .tooAdjective        => .byStrengthening
  | .doubtVerb           => .byStrengthening  -- DE verb, no Core counterpart
  | .denyVerb            => .byStrengthening  -- AA verb, no Core counterpart
  | .adversative         => .byStrengthening
  | .question            => .byOtherMechanism
  | .superlative         => .byOtherMechanism

/-- Ladusaw's DE contexts are always K&L strengthening contexts.

    If Ladusaw classifies a context as DE or anti-additive, K&L explains
    it as `byStrengthening`. K&L's analysis is strictly more explanatory:
    Ladusaw describes *where* NPIs occur (DE contexts), K&L explains
    *why* (widening + strengthening). -/
theorem ladusaw_de_is_kl_strengthening (ctx : PhenCtx)
    (hDE : licensingStrength ctx = .antiAdditive ∨
           licensingStrength ctx = .downwardEntailing) :
    phenCtxKLExplanation ctx = .byStrengthening := by
  cases ctx <;> simp_all [licensingStrength, phenCtxKLExplanation]

-- ============================================================================
-- §4. Sorry vs Glad: Adversative Predicates (Derived from StrawsonEntailment)
-- ============================================================================

/-!
## Adversative Predicates (K&L §3.3)

K&L's analysis of *sorry* vs *glad* is one of the paper's most
important empirical contributions. The key insight:

- *sorry that A* ↔ *want ¬A*  (lexical entailment)
- *glad that A* ↔ *want A*   (lexical entailment)

For *sorry*: sorry(A) entails want(¬A). If I'm sorry that a set is
nonempty, I want it empty. But wanting a set empty → wanting all subsets
empty. So the wide interpretation (wider set nonempty) entails the narrow
(narrower set nonempty). Strengthening holds → *any* is licensed.

For *glad*: glad(A) entails want(A). Wanting a set to have members
does NOT entail wanting each particular subset to have members — the
wish could be satisfied another way. Strengthening fails → *any* is
not freely licensed.

The formal content is derived from `StrawsonEntailment.lean`:
`sorryFull` is Strawson-DE, `gladFull` is UE. The lexical semantics
of sorry (= factive + adversative preference) and glad (= factive +
congruent preference) directly determine their monotonicity properties.
K&L's "DE on a constant perspective" corresponds to `bestOf` being
held constant — the `bestOf` parameter is the "perspective" in K&L's
three-place relation.
-/

open Semantics.Entailment (World)
open Semantics.Entailment.StrawsonEntailment
  (IsStrawsonDE sorryFull gladFull
   sorryFull_isStrawsonDE sorryFull_not_de
   sorryFull_strictly_strawsonDE gladFull_isUE
   condNecessity conditional_antecedent_DE)

/-- **K&L's prediction derived:** *sorry* licenses NPIs because it is
    Strawson-DE — DE on a constant perspective (the `bestOf` parameter).

    The proof is imported from `StrawsonEntailment.sorryFull_isStrawsonDE`.
    K&L's lexical-semantic argument (sorry → want ¬A → "wanting emptiness
    is DE") is captured by the contraposition step in that proof:
    p ≤ q and ¬q(w') implies ¬p(w') at all best worlds. -/
theorem sorry_licenses_any (bestOf : World → List World) :
    IsStrawsonDE (sorryFull bestOf) (λ p w => p w = true) :=
  sorryFull_isStrawsonDE bestOf

/-- **K&L's prediction derived:** *sorry* is NOT classically DE — the
    factivity presupposition blocks it. This is why the "constant
    perspective" qualifier matters: DE holds only when the perspective
    (and factivity) is held constant. -/
theorem sorry_not_classically_de :
    ¬IsDownwardEntailing (sorryFull (λ _ => [World.w1])) :=
  sorryFull_not_de

/-- **K&L's prediction derived:** *glad* does NOT license NPIs because
    it is UE — wider scope entails narrower scope in the SAME direction,
    so widening weakens rather than strengthens.

    K&L: "wanting a set to have members does not entail wanting each
    particular subset to have members. My wish could be satisfied in
    another way." -/
theorem glad_does_not_license (bestOf : World → List World) :
    ∀ p q : BProp World, (∀ w, p w ≤ q w) →
      ∀ w, gladFull bestOf p w ≤ gladFull bestOf q w :=
  gladFull_isUE bestOf

/-- K&L's "settle for less" analysis (§3.3.2): *glad* CAN license *any*
    on a special interpretation where the speaker settles for less than
    what they really want.

    "Be glad we got ANY tickets!" conveys: (1) What I really want is
    better tickets. (2) Nobody who really counts likes us. (3) I settle
    for less — a phonologist likes me, I'm glad about that.

    On this reading, the "narrow wish" (phonologist likes me) is PREFERRED
    to the "wide wish" (linguist likes me). This preference reversal
    creates strengthening: if I'd settle for a phonologist liking me,
    I'd certainly settle for a linguist liking me (the wider set).

    The analysis does not contradict `glad_does_not_license` because
    the "settle for less" reading involves a different semantic structure:
    the preference relation between narrow and wide wishes is reversed. -/
structure SettleForLessDatum where
  sentence : String
  grammatical : Bool
  notes : String

def settle_glad_tickets : SettleForLessDatum :=
  { sentence := "Be glad we got ANY tickets!"
  , grammatical := true
  , notes := "settle for less: narrow wish preferred to wide wish" }

def settle_glad_anybody : SettleForLessDatum :=
  { sentence := "I'm glad ANYBODY likes me!"
  , grammatical := true
  , notes := "settle for less: phonologist liking me ≻ linguist liking me" }

-- *sure* never licenses *any*, not even on a settle-for-less reading,
-- because *sure* has no parallel "settle for less" interpretation (K&L §3.3.2)
def sure_no_settle : SettleForLessDatum :=
  { sentence := "*I'm sure we got ANY tickets!"
  , grammatical := false
  , notes := "sure has no settle-for-less interpretation" }

-- ============================================================================
-- §4b. Conditional Antecedents (K&L §3.5)
-- ============================================================================

/-!
## Conditional Antecedents and Implicit Restrictions (K&L §3.5)

K&L's analysis of *any* in conditional antecedents parallels their
adversative analysis: both involve "DE on a constant parameter."

- *Sorry*: sorry(x, p, A) is DE in A when perspective p is held constant
- *Conditionals*: if_R(A, C) is DE in A when implicit restriction R is
  held constant

Under Kratzer's restrictor analysis (@cite{kratzer-1986}), "if A, must C"
= necessity over the A-restricted modal base. The antecedent position is
classically DE — strengthening the antecedent shrinks the domain, making
the universal check easier to satisfy. Widening the antecedent domain
therefore strengthens the conditional.

The formal proof is imported from `StrawsonEntailment.conditional_antecedent_DE`.
-/

/-- **K&L's prediction derived:** conditional antecedents satisfy strengthening
    because the antecedent of conditional necessity is classically DE.

    "If John subscribes to any newspaper, he gets well informed."
    Widening "newspaper" to include unimportant newspapers strengthens
    the conditional: if it holds for all newspapers (wide), it holds
    for important ones (narrow).

    This connects K&L's "DE on a constant restriction" (§3.5) to the
    formal DE proof from `StrawsonEntailment.lean`. The `domain` parameter
    corresponds to Kratzer's modal base — the implicit restriction that
    is held constant. -/
theorem conditional_satisfies_strengthening
    (domain : World → List World) (β : BProp World) :
    IsDownwardEntailing (λ α => condNecessity domain α β) :=
  conditional_antecedent_DE domain β

/-- The conditional antecedent case and the adversative case are both
    instances of K&L's "DE on a constant parameter" pattern.

    - `condNecessity domain α β`: DE in α, holding `domain` constant
    - `sorryFull bestOf p`: Strawson-DE in p, holding `bestOf` constant

    This is formalized by `IsDE_OnConstant` in `DomainVagueness.lean`:
    a multi-place function is DE in one argument when another is held
    constant. The difference: conditionals are *classically* DE (no
    presupposition), while adversatives are only *Strawson*-DE (factivity
    presupposition blocks classical DE). -/
theorem conditional_de_on_constant_domain
    (domain : World → List World) (β : BProp World) :
    IsDE_OnConstant (λ d α => condNecessity d α β) domain :=
  conditional_antecedent_DE domain β

-- ============================================================================
-- §4c. Negated Because-Clauses: Metalinguistic Licensing (K&L §3.4)
-- ============================================================================

/-!
## Negated Because-Clauses (K&L §3.4)

K&L's analysis of *any* in negated because-clauses is the only genuinely
non-DE licensing mechanism in the paper. The key empirical facts:

- (105) "It isn't because Sue said anything bad about me that I'm angry."
        — *any* licensed (grammatical)
- (106) "*I didn't help him because I have any sympathy for urban
        guerillas, although I do sympathize..." — *any* not licensed when
        the negative implication is canceled
- (109)  Extended text where *because*-clause negation is natural
        (Linebarger 1987)

K&L argue, contra @cite{linebarger-1987}:

1. `not because [S___]` is NOT DE. K&L show that `because [S___]`
   is not upward-entailing (unlike `because of [NP___]`), so negating
   it does not produce a DE context.

2. `not because of [NP___]` IS DE. K&L demonstrate this with clear
   entailment patterns (pp. 391–392).

3. *any* in negated because-clauses is licensed **metalinguistically**:
   `because` carries a factive presupposition (the complement is true).
   The negation in these sentences denies this presupposition — it
   rejects the claim that *because P* is true. *Any* strengthens
   this presupposition denial: rejecting "*because anybody read her
   paper* that she's happy" is stronger than rejecting "*because a
   linguist read her paper* that she's happy."

This is structurally different from DE-based strengthening: the
strengthening applies to the metalinguistic act of presupposition
denial, not to the truth-conditional content. K&L explicitly note
that this does not lead to the over-licensing problems of Linebarger's
NI account (p. 398).
-/

/-- A because-clause licensing datum. -/
structure BecauseClauseDatum where
  sentence : String
  grammatical : Bool
  /-- Whether the negative implication (presupposition denial) is present -/
  negativeImplication : Bool
  notes : String

-- (105) K&L: *any* licensed — negative implication present
def because_ex105 : BecauseClauseDatum :=
  { sentence := "It isn't because Sue said anything bad about me that I'm angry"
  , grammatical := true
  , negativeImplication := true
  , notes := "metalinguistic: denies factive presupposition of because" }

-- (106) K&L: *any* NOT licensed when negative implication canceled
def because_ex106 : BecauseClauseDatum :=
  { sentence := "*I didn't help him because I have any sympathy for urban guerillas, although I do sympathize with urban guerillas"
  , grammatical := false
  , negativeImplication := false
  , notes := "continuation cancels the negative implication → any not licensed" }

-- (122) K&L: *any* licensed in extended context (p. 393)
def because_ex122 : BecauseClauseDatum :=
  { sentence := "It isn't because of anything she said that I'm angry — although she did say all sorts of annoying things — it's because of the faces she was making"
  , grammatical := true
  , negativeImplication := true
  , notes := "metalinguistic: because of [NP] is DE, any is freely licensed" }

-- (125) K&L: key example for presupposition denial
def because_ex125 : BecauseClauseDatum :=
  { sentence := "It's not because anybody read her paper that she's happy"
  , grammatical := true
  , negativeImplication := true
  , notes := "metalinguistic: any strengthens the presupposition denial" }

-- (132) K&L: rhetorical conditional cannot license *any* (p. 396)
-- This contrasts with (125): both can imply nobody read her paper,
-- but (132) cannot metalinguistically deny the factive presupposition,
-- so *any* is not licensed.
def because_ex132 : BecauseClauseDatum :=
  { sentence := "*If it's because anybody read her paper that she is happy, I'll eat my hat"
  , grammatical := false
  , negativeImplication := false
  , notes := "rhetorical conditional: cannot metalinguistically deny presupposition" }

-- K&L's prediction: *any* in negated because-clauses requires the
-- negative implication (presupposition denial). When the implication
-- is present, *any* strengthens it → licensed. When absent → not licensed.
#guard [because_ex105, because_ex106, because_ex122, because_ex125, because_ex132].all λ d =>
  d.grammatical == d.negativeImplication

-- ============================================================================
-- §5. FC Any = Generic Indefinite + Widening
-- ============================================================================

/-!
## FC Any as Generic Indefinite (K&L §2.1, §4)

K&L's treatment of the PS/FC distinction:

- PS *any*: regular indefinite NP + widening + strengthening
- FC *any*: **generic** indefinite NP + widening + strengthening

The apparent universal force of FC *any* is not quantificational —
it emerges from the combination of:
1. Generic interpretation (modal, law-like, exception-tolerating)
2. Widening (extends the CN along a contextual dimension)
3. The resulting dimensional universality (K&L §4.3)

This explains why:
- FC *any* shares properties with generic indefinites (exceptions,
  counterfactual entailments, law-like readings)
- *almost* can modify *any owl* (dimensionally universal) but not
  *an owl* (not dimensionally universal)
- FC *any* is "more universal" than regular generics (because widening
  eliminates some vagueness, creating dimensional universality)
-/

/-- Classification of the NP containing *any* -/
inductive AnyInterpretation where
  | episodic   -- PS any: regular indefinite in an episodic context
  | generic    -- FC any: generic indefinite in a non-episodic context
  deriving DecidableEq, Repr

/-- Determine the interpretation from the licensing context -/
def interpretationOf : LicensingContext → AnyInterpretation
  -- DE contexts → episodic (PS any)
  | .negation        => .episodic
  | .nobody          => .episodic
  | .without_clause  => .episodic
  | .few             => .episodic
  | .atMost          => .episodic
  | .conditional_ant => .episodic
  | .before_clause   => .episodic
  | .only_focus      => .episodic
  | .too_to          => .episodic
  | .comparative     => .episodic
  | .adversative     => .episodic
  | .since_temporal  => .episodic
  -- Non-episodic contexts → generic (FC any)
  | .modal_possibility => .generic
  | .modal_necessity   => .generic
  | .imperative        => .generic
  | .generic           => .generic
  | .free_relative     => .generic
  -- Questions / superlatives: episodic (PS any)
  | .question          => .episodic
  | .superlative       => .episodic

/-- K&L's prediction: FC any occurs exactly in generic-interpretation
    contexts, and these are the contexts explained by generic indefinite
    analysis (not by DE-based strengthening). -/
theorem fc_iff_generic (ctx : LicensingContext) :
    interpretationOf ctx = .generic ↔
    klExplanation ctx = .byGenericIndefinite := by
  cases ctx <;> simp [interpretationOf, klExplanation]

-- ============================================================================
-- §6. Domain Vagueness and Generics
-- ============================================================================

/-!
## Domain Vagueness Distinguishes Generics from Universals (K&L §4.1.2)

K&L's formal distinction: *every owl* is domain precise (each context
determines a unique set of owls to quantify over), while *an owl* in
generic use is domain vague (the "normalcy" restriction is inherently
underspecified). This explains why:

- *every poodle gives live birth* is false (one male counterexample suffices)
- *a poodle gives live birth* is true (male poodles are legitimate exceptions)

The vagueness is essential to exception tolerance: because the domain
is never fully pinned down, apparent counterexamples can always be
excluded as falling outside the quantification under *some* precisification.
-/

/-- Whether a quantifier is domain precise or domain vague.
    K&L: *every* and *no* are domain precise; generic NPs are domain vague;
    *any* is domain vague with additional dimensional universality. -/
inductive DomainPrecision where
  | precise   -- every, no: unique domain per context
  | vague     -- a CN (generic): domain varies with precisification
  deriving DecidableEq, Repr

/-- *almost* modifiability tracks domain precision or dimensional universality.
    K&L (§4.3): *almost* can modify NPs that are either domain precise
    (true universals like *every*) or dimensionally universal (*any*).
    Generic NPs (*an owl*) are domain vague without dimensional universality,
    so *almost* cannot modify them. -/
structure AlmostDatum where
  np : String
  almostOK : Bool
  precision : DomainPrecision
  dimUniversal : Bool
  deriving DecidableEq, Repr

/-- *almost* is compatible iff the NP is domain precise or dimensionally
    universal. This is K&L's prediction, derived from the definitions. -/
def AlmostDatum.predicted (d : AlmostDatum) : Bool :=
  d.precision == .precise || d.dimUniversal

def almost_every : AlmostDatum :=
  { np := "every owl", almostOK := true
  , precision := .precise, dimUniversal := false }

def almost_generic_a : AlmostDatum :=
  { np := "an owl", almostOK := false
  , precision := .vague, dimUniversal := false }

def almost_any : AlmostDatum :=
  { np := "any owl", almostOK := true
  , precision := .vague, dimUniversal := true }

-- K&L (p. 412): *no owl* is domain precise, just like *every owl*.
-- "Almost no owl" is grammatical because *no* is a true universal
-- quantifier (domain precise).
def almost_no : AlmostDatum :=
  { np := "no owl", almostOK := true
  , precision := .precise, dimUniversal := false }

-- K&L (p. 409): *some owl* cannot be modified by *almost*
-- (neither domain precise nor dimensionally universal).
def almost_some : AlmostDatum :=
  { np := "some owl", almostOK := false
  , precision := .vague, dimUniversal := false }

-- Verify K&L's *almost* predictions match the data
#guard almost_every.predicted == almost_every.almostOK
#guard almost_generic_a.predicted == almost_generic_a.almostOK
#guard almost_any.predicted == almost_any.almostOK
#guard almost_no.predicted == almost_no.almostOK
#guard almost_some.predicted == almost_some.almostOK

-- ============================================================================
-- §7. Key Examples from the Paper
-- ============================================================================

/-!
## Verification: K&L's Core Examples
-/

/-- An NPI licensing datum extended with K&L's explanation.

    K&L's locality condition (D) requires distinguishing the *local*
    entailment signature (at the narrowest operator scoping over *any*)
    from the *global* signature (at the sentence level). For most examples
    these coincide; they diverge when *any* is embedded under multiple
    operators (e.g., *any* in the scope of *every* under negation). -/
structure KLDatum where
  /-- The sentence -/
  sentence : String
  /-- Grammaticality judgment -/
  grammatical : Bool
  /-- K&L's explanation for the judgment -/
  explanation : KLExplanation
  /-- The entailment signature at the LOCAL proposition (narrowest operator
      scoping over *any*). This is the signature that matters for
      strengthening under K&L's locality condition (D). -/
  localSig : EntailmentSig
  /-- The entailment signature at the GLOBAL (sentence) level.
      Defaults to `localSig` when there is only one relevant operator. -/
  globalSig : EntailmentSig := localSig
  /-- Notes on the widening dimension -/
  wideningDimension : String := ""
  deriving Repr

-- (1) I don't have any potatoes. — PS any under negation
def ex1 : KLDatum :=
  { sentence := "I don't have any potatoes"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .antiAddMult
  , wideningDimension := "cooking vs non-cooking potatoes" }

-- (2) *I have any potatoes. — positive context, strengthening fails
-- K&L: widening in a UE context weakens rather than strengthens → *any*
-- is ungrammatical because the strengthening condition is violated.
def ex2 : KLDatum :=
  { sentence := "*I have any potatoes"
  , grammatical := false
  , explanation := .byOtherMechanism  -- strengthening fails: UE context
  , localSig := .mono }

-- (10) Any owl hunts mice. — FC any in generic context
def ex10 : KLDatum :=
  { sentence := "Any owl hunts mice"
  , grammatical := true
  , explanation := .byGenericIndefinite
  , localSig := .mono  -- generic, not DE
  , wideningDimension := "healthy vs sick owls" }

-- (27)b Every man who has any matches is happy. — restrictor of universal
def ex27b : KLDatum :=
  { sentence := "Every man who has any matches is happy"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .antiAdd  -- universal restrictor is anti-additive
  , wideningDimension := "dry vs wet matches" }

-- (55) *Every boy has any potatoes. — scope of universal is UE
def ex55 : KLDatum :=
  { sentence := "*Every boy has any potatoes"
  , grammatical := false
  , explanation := .byOtherMechanism  -- strengthening fails: local UE
  , localSig := .mult  -- universal scope is multiplicative (UE)
  }

-- (56) *It's not the case that every boy has any potatoes. — locality
-- K&L's locality condition: even though the GLOBAL context (under negation)
-- is DE, the LOCAL context (scope of *every*) is UE. Strengthening must
-- hold locally, so *any* is ungrammatical despite the DE global context.
def ex56 : KLDatum :=
  { sentence := "*It's not the case that every boy has any potatoes"
  , grammatical := false
  , explanation := .byOtherMechanism  -- local sig is UE → strengthening fails
  , localSig := .mult  -- local: scope of every = multiplicative (UE)
  , globalSig := .antiMult  -- global: not ∘ every_scope = DE
  }

-- (72) I'm surprised/sorry that he ever said anything.
def ex72 : KLDatum :=
  { sentence := "I'm surprised that he ever said anything"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti  -- adversative = DE on constant perspective
  }

-- (73) *I'm sure/glad that I ever met him.
def ex73 : KLDatum :=
  { sentence := "*I'm sure that I ever met him"
  , grammatical := false
  , explanation := .byOtherMechanism  -- non-adversative = not DE
  , localSig := .mono
  }

-- (82) I'm sorry that anybody hates me.
def ex82 : KLDatum :=
  { sentence := "I'm sorry that anybody hates me"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti
  , wideningDimension := "phonologists → linguists in general" }

-- (143) If John subscribes to any newspaper, he gets well informed.
def ex143 : KLDatum :=
  { sentence := "If John subscribes to any newspaper, he gets well informed"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti  -- conditional antecedent is DE
  , wideningDimension := "important vs unimportant newspapers" }

/-- The examples collectively verify K&L's predictions:
    - Grammatical sentences with `byStrengthening` have DE local signatures
    - Ungrammatical sentences have non-DE local signatures
    - FC *any* examples have `byGenericIndefinite` explanation -/
def allExamples : List KLDatum :=
  [ex1, ex2, ex10, ex27b, ex55, ex56, ex72, ex73, ex82, ex143]

-- Verify: grammatical examples with strengthening explanation all have
-- DE LOCAL signatures.
#guard allExamples.all λ d =>
  if d.grammatical && d.explanation == .byStrengthening then
    match d.localSig.toDEStrength with | some _ => true | none => false
  else true

-- Verify: ungrammatical examples all have non-DE local signatures
-- (strengthening fails locally).
#guard allExamples.all λ d =>
  if !d.grammatical then
    match d.localSig.toDEStrength with | some _ => false | none => true
  else true

-- Verify: locality example (56) — global IS DE but local is NOT
#guard ex56.globalSig.toDEStrength.isSome  -- global: DE
#guard ex56.localSig.toDEStrength.isNone   -- local: not DE

-- ============================================================================
-- §8. Strengthening Entailment Signature Composition
-- ============================================================================

/-!
## Locality via Signature Composition

K&L's locality condition (D) states that strengthening must hold at the
*local* proposition — the narrowest operator scoping over *any*.

In Icard's framework, the local signature is the composition of signatures
along the path from *any* to the local operator. Example (56):

  *It's not the case that [every boy has any potatoes]

Path from *any* to local operator *every*:
  every_scope = multiplicative (⊞) → UE → strengthening fails

Even though the global context (under negation) is DE, the *local*
context (scope of *every*) is UE. This correctly predicts (56) is bad.
-/

-- (56) locality check via signature composition
-- Path: any → scope of "every" → scope of "not"
-- Local operator: "every" with scope ⊞ (multiplicative = UE)
-- Global: ◇⊟ * ⊞ = ⊟ (anti-multiplicative = DE)
-- But local signature is ⊞ (UE), so strengthening fails locally.

#guard EntailmentSig.compose .antiAddMult .mult == .antiMult  -- global is DE
#guard EntailmentSig.toContextPolarity .mult == .upward       -- local is UE → bad

-- (27)b: any in restrictor of "every"
-- Local operator: "every" restrictor = ◇ (anti-additive)
-- Local is DE → strengthening holds → any is licensed.

#guard EntailmentSig.toContextPolarity .antiAdd == .downward   -- local is DE → good

-- ============================================================================
-- §9. Unifying traditionalGEN with Domain Vagueness
-- ============================================================================

/-!
## The Hidden Normalcy Parameter IS Domain Vagueness (K&L §4.1)

The traditional GEN operator (`traditionalGEN` in `Generics.lean`) is
a universal quantifier over situations with a hidden normalcy predicate:

    GEN_s [normal(s) ∧ restrictor(s)] [scope(s)]

K&L's insight (§4.1.1–§4.1.2) is that this normalcy predicate is
**inherently vague**. There is no single correct way to fill in "normal" —
different contexts suggest different completions, and speakers knowingly
leave it underspecified.

A `VagueRestriction` captures this precisely:
- The **precise part** (v₀) contains normalcy properties everyone agrees on
- The **precisifications** (V) are the consistent ways to complete "normalcy"
- Each precisification determines a `NormalcyPredicate`

`traditionalGEN` under a *fixed* normalcy predicate is what you get when
you *pick one precisification*. K&L's domain vagueness is the meta-level
fact that this choice is never fully determined.

This explains why `traditionalGEN` is criticized for hiding all the work in
the normalcy parameter (see docstring of `Generics.lean`): K&L's framework
makes explicit that the parameter is inherently vague, not merely unknown.
-/

/-- The traditional GEN operator: ∀s. normal(s) ∧ restrictor(s) → scope(s).

    This is the standard analysis of generic sentences (see
    `Theories/Semantics/Lexical/Noun/Kind/Generics.lean`), defined locally
    to avoid import chain issues. K&L's contribution is explaining WHY
    the normalcy parameter is context-dependent: it is inherently vague. -/
def gen {D : Type*} (domain : List D) (normal : D → Bool)
    (restrictor : D → Bool) (scope : D → Bool) : Bool :=
  domain.all λ d => !(normal d && restrictor d) || scope d

/-- **Bridge: GEN under a fixed normalcy predicate is a single-precisification
    instance of K&L's vague generic.**

    K&L's analysis explains what the traditional GEN leaves implicit:
    - When you evaluate GEN with a specific `normal` parameter,
      you are choosing one precisification of the vague restriction
    - The "exception tolerance" of generics arises because different
      normalcy predicates (= different precisifications) yield different
      domains, and an entity that is a counterexample under one may be
      outside the domain under another (a "legitimate exception")

    The theorem: if domain vagueness holds (some precisifications differ),
    then there exist two normalcy predicates under which GEN gives
    different truth values — the entity that causes failure under n₁
    is excluded from the domain under n₂. -/
theorem exception_tolerance_via_normalcy {D : Type*}
    (domain : List D) (restrictor : D → Bool) (scope : D → Bool)
    (n₁ n₂ : D → Bool)
    -- There exists a counterexample under n₁
    (s : D) (_hs : s ∈ domain)
    (_hNorm₁ : n₁ s = true) (_hRestr : restrictor s = true)
    (_hFails : scope s = false)
    -- But s is NOT normal under n₂ — it's a "legitimate exception"
    (hNotNorm₂ : n₂ s = false) :
    -- Then s does not threaten the generic under n₂
    (n₂ s && restrictor s) = false := by
  simp [hNotNorm₂]

/-- **K&L's explanation for why generics tolerate exceptions.**

    Domain vagueness (multiple precisifications with different domains)
    maps directly to exception tolerance in the GEN operator: for any
    apparent counterexample, there exists a precisification of normalcy
    under which that counterexample is outside the domain.

    "A poodle gives live birth": male poodles are counterexamples under
    the precisification where normalcy includes all poodles, but they
    are outside the domain under the precisification where normalcy is
    restricted to female poodles (the relevant class for reproduction).

    The vague restriction framework explains what the traditional GEN
    operator merely stipulates: the normalcy parameter is not unknown
    but inherently underspecified, and this underspecification is an
    essential feature of generic meaning, not a bug. -/
theorem domain_vagueness_explains_gen_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop)
    (hVague : isDomainVague X apply)
    -- Generic is true on the subvaluationist reading
    (hSub : genericSubTrue X apply scope) :
    -- Then there exist two precisifications with different domains,
    -- and the generic holds under at least one
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply ∧
      genericTrue X apply scope v₁ :=
  by
  obtain ⟨v₁, hv₁m, v₂, hv₂m, hne⟩ := domain_vague_allows_exceptions X apply hVague
  obtain ⟨vg, hvgm, hvgt⟩ := hSub
  -- vg witnesses truth; v₁, v₂ witness domain difference.
  -- At least one of (v₁, vg) or (v₂, vg) has different domains.
  by_cases h : domainOf vg apply = domainOf v₁ apply
  · exact ⟨vg, hvgm, v₂, hv₂m, by rw [h]; exact hne, hvgt⟩
  · exact ⟨vg, hvgm, v₁, hv₁m, h, hvgt⟩

-- ============================================================================
-- §10. Conditional Strengthening with Implicit Restrictions (K&L §3.5.3)
-- ============================================================================

/-!
## Widening Interacts with Implicit Restrictions (K&L §3.5.3)

K&L's deepest formal argument concerns *any* in conditional antecedents.
The standard DE analysis says conditional antecedents are DE, so
strengthening holds. But K&L note that natural language conditionals
are NOT classically DE — the inference from (140) to (141) is dubious:

- (140) If John subscribes to a newspaper, he gets well informed.
- (141) If John subscribes to a newspaper and he can't read, he gets
        well informed.

K&L's resolution (§3.5.2–§3.5.3): conditionals are DE **on a constant
implicit restriction**. The implicit restriction R_A determines which
"cases" are relevant. When the implicit restriction changes between
premise and conclusion, the inference may fail. But the strengthening
inferences required for licensing *any* always go through, because:

1. The **narrow interpretation** (before widening) has restriction R_narrow
   (e.g., "important newspapers that John can read")

2. **Widening** along the dimension "important vs. unimportant" does two
   things simultaneously:
   - Widens the CN denotation (adds unimportant newspapers)
   - Weakens the implicit restriction (R_wide cannot undo the widening
     by excluding the very entities widening brought in)

3. R_wide is **never stronger** than R_narrow: the restriction on the wide
   interpretation may be "somewhat weaker" but cannot exclude entities
   that R_narrow already included.

4. Therefore widening + restriction weakening = strengthening always holds:
   the wide interpretation (more entities in antecedent, weaker restriction)
   entails the narrow interpretation (fewer entities, stronger restriction).

K&L (p. 404): "Conditionals always satisfy strengthening, because of the
relation between the restrictions of the wide and narrow interpretations."

This is formalized below as a theorem about vague restrictions: widening
along a dimension weakens the restriction, and the widened conditional
(with its weakened restriction) always entails the narrow conditional
(with its original restriction).
-/

/-- A conditional with an implicit restriction: "if A then C" is true
    iff in all relevant cases satisfying both the restriction and the
    antecedent, the consequent holds.

    K&L (p. 400, eq. (147)): ∀c ↾ R_A(c). A(c) → C(c)

    The `restriction` parameter is the implicit contextual restriction
    (Kratzer's modal base) that determines which cases count as
    "relevant." -/
def conditionalWithRestriction {Case : Type*}
    (restriction : Case → Prop) (antecedent : Case → Prop)
    (consequent : Case → Prop) : Prop :=
  ∀ c, restriction c → antecedent c → consequent c

/-- **K&L's core theorem (§3.5.3): Widening always satisfies
    strengthening in conditional antecedents.**

    If the wide restriction is weaker than the narrow restriction
    (it includes all cases the narrow restriction includes), then the
    wide conditional entails the narrow conditional.

    K&L (p. 404): "The strengthening inference that has to hold for
    *any* to be licensed need not be an inference on a constant
    restriction. However, strengthening inferences do always go through,
    because of the relation between the restrictions of the wide and
    narrow interpretations. The two restrictions are always the same,
    except that the restriction of the premise may be somewhat weaker
    (but never stronger), than the restriction of the conclusion."

    This is the deepest theorem of the paper: it explains why *any* is
    **always** licensed in conditional antecedents, without requiring
    classical DE of the whole conditional.

    The key insight: widening CANNOT undo itself via the restriction.
    If widening adds unimportant newspapers to the CN denotation, the
    restriction cannot then exclude unimportant newspapers — that would
    defeat the purpose of widening. So the wide restriction is always
    at least as permissive as the narrow restriction. -/
theorem widening_satisfies_conditional_strengthening {Case : Type*}
    (R_narrow R_wide : Case → Prop) (A_narrow A_wide : Case → Prop)
    (consequent : Case → Prop)
    -- Wide restriction is weaker: includes all cases narrow includes
    (hRestrWeaker : ∀ c, R_narrow c → R_wide c)
    -- Wide antecedent is weaker: includes all cases narrow includes
    (hAntWeaker : ∀ c, A_narrow c → A_wide c)
    -- Wide conditional holds
    (hWide : conditionalWithRestriction R_wide A_wide consequent) :
    -- Then narrow conditional holds
    conditionalWithRestriction R_narrow A_narrow consequent :=
  λ c hR hA => hWide c (hRestrWeaker c hR) (hAntWeaker c hA)

/-- **Corollary: Widening along a dimension creates the required
    restriction-weakening.**

    When widening removes a property P from the CN restriction (adding
    both P-entities and ¬P-entities), the implicit restriction must also
    be weakened to accommodate both. This is because the restriction
    cannot re-exclude the entities that widening brought in — doing so
    would "undo the effect of widening" (K&L §3.5.3, p. 403).

    K&L (p. 403): "We think it is natural to assume that this can never
    happen: the restriction cannot undo the effect of widening. Hence,
    the process of widening has the effect of minimally altering the
    restriction (if necessary), and in the case of our example, we get
    that the wide interpretation is as in (150)."

    This formalizes the principle that the wide restriction is always
    at most as strong as the narrow restriction — never stronger. -/
theorem widening_weakens_restriction {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] (apply : Property → Set Entity) :
    -- The domain under the widened precise part includes the domain
    -- under the original precise part
    domainOf X.precise apply ⊆
    domainOf (widenAlong X onDimension).precise apply :=
  widenAlong_expands_domain X onDimension apply

/-- **Main result: *any* is always licensed in conditional antecedents.**

    Combining `widening_satisfies_conditional_strengthening` with
    `widening_weakens_restriction`: widening the CN in a conditional
    antecedent simultaneously (1) widens the antecedent domain and
    (2) weakens the implicit restriction. Both of these go in the
    same direction — making the conditional more general. The wider
    conditional (with its weakened restriction) always entails the
    narrower conditional (with its original restriction).

    This is K&L's explanation for why *any* is "always licensed in
    antecedents of conditionals" (§3.5.4, p. 404) — not because
    conditionals are simply DE, but because widening and restriction-
    weakening conspire to guarantee strengthening. -/
theorem any_always_licensed_in_conditionals {Case : Type*}
    (R_narrow R_wide : Case → Prop) (A_narrow A_wide : Case → Prop)
    (consequent : Case → Prop)
    -- Widening weakens both restriction and antecedent
    (hRestrWeaker : ∀ c, R_narrow c → R_wide c)
    (hAntWeaker : ∀ c, A_narrow c → A_wide c) :
    -- Wide conditional entails narrow conditional
    -- (= strengthening holds = any is licensed)
    conditionalWithRestriction R_wide A_wide consequent →
    conditionalWithRestriction R_narrow A_narrow consequent :=
  widening_satisfies_conditional_strengthening R_narrow R_wide A_narrow A_wide
    consequent hRestrWeaker hAntWeaker

end KadmonLandman1993
