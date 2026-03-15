import Linglib.Core.Modality.ModalIndefinite
import Linglib.Fragments.Spanish.ModalIndefinites

/-!
# Alonso-Ovalle & Menéndez-Benito (2010): Modal Indefinites
@cite{alonso-ovalle-menendez-benito-2010}

Formalization of the core analysis: *algún* imposes an **anti-singleton
constraint** on its domain of quantification, and the Modal Variation
effect (speaker ignorance) is **derived** as a conversational implicature
via scalar competition with singleton-domain alternatives.

## Subset Selection Functions (§4.1)

Indefinite determiners take a subset selection function `f` as argument
(@cite{alonso-ovalle-menendez-benito-2010}, building on von Fintel 1999a).
The function `f` maps a predicate `P` to a contextually relevant subset
`f(P)`:

- (50): `⟦un⟧ = λf.λP.λQ. ∃x[f(P)(x) ∧ Q(x)]`
- (54): `⟦algún⟧ = λf.λP.λQ : anti-singleton(f). ∃x[f(P)(x) ∧ Q(x)]`

The sole lexical difference: *algún* presupposes that `f` is
anti-singleton (`|f(P)| > 1`). *Un* allows singleton `f`.

## Two Derivation Paths (§§4.2, 4.3)

The Modal Variation effect is derived by scalar competition.
The paper presents two parallel derivations:

- **§4.2 (Necessity/ASSERT)**: Singleton competitors □(bedroom), □(living room),
  □(bathroom) are too strong — the speaker would have used one if she could.
  Negating them yields: the speaker doesn't know which room.
- **§4.3 (Possibility/◇)**: Anti-exhaustivity implicatures — if ◇(bedroom),
  then also ◇(other rooms). Rules out singleton epistemic states.

Both paths derive the same Modal Variation effect.

## Modal Variation vs Free Choice (§§2, 4.4)

The anti-singleton constraint derives a WEAKER modal effect than the
domain widening of *irgendein* (@cite{kratzer-shimoyama-2002}):

- **Modal Variation** (*algún*): at least two domain members are
  epistemic possibilities — competitors are singleton subdomains only.
- **Free Choice** (*irgendein*): EVERY domain member is a possibility —
  competitors are ALL subdomains.

## Typology (Table 1)

Two parameters (uniqueness × domain constraint) yield a 2×2 typology:
- Cell 1: *irgendein*, *uno qualsiasi* (widening + uniqueness → FC)
- Cell 4: *algún* (anti-singleton + non-uniqueness → MV + number ignorance)
- Cells 2, 3: predicted but unattested at time of publication

-/

namespace Phenomena.ModalIndefinites.Studies.AlonsoOvalleMenendezBenito2010

open Core.ModalIndefinite
open Fragments.Spanish.ModalIndefinites


-- ════════════════════════════════════════════════════════════════
-- Part I: Subset Selection Functions (§4.1)
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 1. Abstract Framework
-- ════════════════════════════════════════════════════

/-- A subset selection function maps predicates to predicates ((50)).

    In @cite{alonso-ovalle-menendez-benito-2010}'s analysis, `f` models
    contextual domain restriction: `f(P)` selects the subset of `P` that
    the determiner quantifies over. Following von Fintel (1999a), different
    indefinite determiners impose different constraints on `f`. -/
abbrev SubsetSelFn (Entity : Type*) := (Entity → Bool) → Entity → Bool

/-- The cardinality of the selected subdomain: |f(P)| in a finite domain. -/
def selectedSize {Entity : Type*} [BEq Entity]
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P : Entity → Bool) : Nat :=
  (domain.filter (f P)).length

/-- Singleton SSF ((52)): `f` is singleton iff `|f(P)| = 1`.

    Singleton selection functions yield specific indefinites — the speaker
    has a particular witness in mind. *Un* allows these; *algún* does not. -/
def isSingletonSSF {Entity : Type*} [BEq Entity]
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P : Entity → Bool) : Bool :=
  selectedSize f domain P == 1

/-- Anti-singleton SSF ((53)): `f` is anti-singleton iff `|f(P)| > 1`.

    *Algún* presupposes that its selection function is anti-singleton:
    the domain of quantification must contain more than one individual.
    This is the paper's core lexical-semantic claim. -/
def isAntiSingletonSSF {Entity : Type*} [BEq Entity]
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P : Entity → Bool) : Bool :=
  selectedSize f domain P > 1


-- ════════════════════════════════════════════════════
-- § 2. Denotations of *un* and *algún* ((50), (54))
-- ════════════════════════════════════════════════════

/-- ⟦un⟧ = λf.λP.λQ. ∃x[f(P)(x) ∧ Q(x)] ((50)).

    The plain indefinite *un*: existential quantification over `f(P)`.
    No constraint on `f` — the domain CAN be a singleton. -/
def un_sat {Entity : Type*}
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P Q : Entity → Bool) : Bool :=
  domain.any λ x => f P x && Q x

/-- ⟦algún⟧ = λf.λP.λQ : **anti-singleton**(f). ∃x[f(P)(x) ∧ Q(x)] ((54)).

    Same assertive content as *un* but with an anti-singleton
    presupposition on `f`. Returns `(presupposition, assertion)`. -/
def algún_sat {Entity : Type*} [BEq Entity]
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P Q : Entity → Bool) : Bool × Bool :=
  (isAntiSingletonSSF f domain P, un_sat f domain P Q)

/-- When the presupposition is satisfied, *algún* and *un* have the
    same assertive content. The ONLY lexical difference is the
    presupposition on `f`. -/
theorem algún_un_same_assertion {Entity : Type*} [BEq Entity]
    (f : SubsetSelFn Entity) (domain : List Entity)
    (P Q : Entity → Bool) :
    (algún_sat f domain P Q).2 = un_sat f domain P Q := rfl


-- ════════════════════════════════════════════════════════════════
-- Part II: The Hide-and-Seek Scenario (§§4.1–4.3)
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 3. Model Setup ((15), (56)–(57))
-- ════════════════════════════════════════════════════

/-- The three rooms of the house ((57)).

    Scenario (15): María, Juan, and Pedro are playing hide-and-seek.
    Pedro believes Juan is inside but not in the bathroom or kitchen. -/
inductive Room where | bedroom | livingRoom | bathroom
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Epistemic worlds: which room Juan is in. -/
inductive HideWorld where
  | inBedroom
  | inLivingRoom
  | inBathroom
  deriving DecidableEq, BEq, Repr, Inhabited

private def allRooms : List Room := [.bedroom, .livingRoom, .bathroom]
private def allHW : List HideWorld := [.inBedroom, .inLivingRoom, .inBathroom]

/-- "is a room of the house": the restrictor P. -/
private def isRoom : Room → Bool := λ _ => true

/-- Which room Juan is in, by world. -/
private def juanRoom : HideWorld → Room
  | .inBedroom => .bedroom
  | .inLivingRoom => .livingRoom
  | .inBathroom => .bathroom

/-- "Juan is in room r" as a world-relative predicate. -/
private def juanIn (r : Room) (w : HideWorld) : Bool :=
  juanRoom w == r

/-- Pedro's epistemic alternatives ((15)):
    he knows Juan is not in the bathroom or kitchen.
    Only bedroom and living room are compatible with his beliefs. -/
private def pedroEpist : List HideWorld := [.inBedroom, .inLivingRoom]


-- ════════════════════════════════════════════════════
-- § 4. Anti-Singleton Constraint: *Un* vs *Algún* ((46)–(49))
-- ════════════════════════════════════════════════════

/-- A singleton selection function: picks only the bedroom. -/
private def fSingleton : SubsetSelFn Room := λ _ r => r == .bedroom

/-- An anti-singleton SSF: picks bedroom and living room. -/
private def fAntiSingleton : SubsetSelFn Room :=
  λ _ r => r == .bedroom || r == .livingRoom

/-- The identity SSF (full domain): all rooms. -/
private def fFull : SubsetSelFn Room := λ P r => P r

theorem singleton_selects_one :
    selectedSize fSingleton allRooms isRoom = 1 := by native_decide

theorem antisingleton_selects_two :
    selectedSize fAntiSingleton allRooms isRoom = 2 := by native_decide

theorem full_selects_all :
    selectedSize fFull allRooms isRoom = 3 := by native_decide

/-- *Un* is felicitous with a singleton domain ((46)):
    "Juan compró un libro que resultó ser el más caro." -/
theorem un_allows_singleton :
    un_sat fSingleton allRooms isRoom (λ _ => true) = true := by native_decide

/-- *Algún* rejects singleton domains ((47)):
    "# Juan compró algún libro que resultó ser el más caro."
    The anti-singleton presupposition fails. -/
theorem algún_rejects_singleton :
    (algún_sat fSingleton allRooms isRoom (λ _ => true)).1 = false := by native_decide

/-- *Algún* accepts non-singleton domains. -/
theorem algún_accepts_antisingleton :
    (algún_sat fAntiSingleton allRooms isRoom (λ _ => true)).1 = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 5. The ASSERT Operator ((20)) and Necessity Derivation (§4.2)
-- ════════════════════════════════════════════════════

/-- The covert assertoric operator ((20)):
    ⟦ASSERT⟧ᶜ = λp.λw. ∀w' ∈ Epistemicₛₚₑₐₖₑᵣ(w)[p(w')]

    Ranges over the speaker's epistemic alternatives. Following
    @cite{kratzer-shimoyama-2002}, unembedded *algún* sentences are
    in the scope of this operator, unifying the modal and non-modal cases. -/
def assertOp (epist : List HideWorld) (p : HideWorld → Bool) : Bool :=
  epist.all p

/-- Full sentence under ASSERT:
    □[∃r ∈ f(room). Juan is in r]
    = ∀w' ∈ Epistemic. ∃r ∈ f(room). juanIn(r)(w')

    Adapted from (55b) to the room scenario. -/
def sentenceUnderAssert (f : SubsetSelFn Room) (epist : List HideWorld) : Bool :=
  assertOp epist λ w => allRooms.any λ r => f isRoom r && juanIn r w

/-- With the full domain: Pedro believes Juan is in SOME room. Trivially true. -/
theorem assert_full_holds :
    sentenceUnderAssert fFull pedroEpist = true := by native_decide

/-- With a singleton domain {bedroom}: ASSERT requires Pedro to believe
    Juan is in the bedroom in ALL epistemic alternatives. He doesn't —
    he also considers the living room. So this is FALSE. -/
theorem assert_singleton_fails :
    sentenceUnderAssert fSingleton pedroEpist = false := by native_decide

/-- With anti-singleton {bedroom, living room}: Pedro believes Juan is
    in one of these two rooms. Holds in all his alternatives. -/
theorem assert_antisingleton_holds :
    sentenceUnderAssert fAntiSingleton pedroEpist = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 6. Deriving MV by Scalar Competition under □ (§4.2)
-- ════════════════════════════════════════════════════

/-! The Modal Variation effect is NOT stipulated — it is DERIVED:

1. Speaker used *algún* (anti-singleton f) rather than singleton
   competitors □(Juan is in the bedroom), □(… living room), etc.
2. By the quantity maxim, the speaker cannot assert any singleton.
3. Therefore: the speaker doesn't know which room → ignorance.

The competitors ((58)) are SINGLETON subdomain alternatives.
The implicature ((59b)) negates each:
  ¬□(bedroom) ∧ ¬□(living room) ∧ ¬□(bathroom) -/

/-- A singleton competitor: □(Juan is in room r). -/
def singletonCompetitor (r : Room) (epist : List HideWorld) : Bool :=
  assertOp epist (juanIn r)

/-- The strengthened meaning ((59)): assertion + negated singleton competitors.

    assertion: □(∃r ∈ f(room). Juan is in r)
    implicature: ¬□(bedroom) ∧ ¬□(living room) ∧ ¬□(bathroom)

    The conjunction derives the Modal Variation effect. -/
def strengthenedMeaning (f : SubsetSelFn Room) (epist : List HideWorld) : Bool :=
  sentenceUnderAssert f epist &&
    !singletonCompetitor .bedroom epist &&
    !singletonCompetitor .livingRoom epist &&
    !singletonCompetitor .bathroom epist

/-- The strengthened meaning holds for Pedro: he believes Juan is in
    some room (bedroom or living room) but cannot assert which. -/
theorem strengthened_holds :
    strengthenedMeaning fAntiSingleton pedroEpist = true := by native_decide

/-- Each singleton competitor individually fails — Pedro doesn't know
    which room Juan is in. This IS the Modal Variation effect. -/
theorem not_know_bedroom :
    singletonCompetitor .bedroom pedroEpist = false := by native_decide

theorem not_know_livingRoom :
    singletonCompetitor .livingRoom pedroEpist = false := by native_decide

theorem not_know_bathroom :
    singletonCompetitor .bathroom pedroEpist = false := by native_decide

/-- The strengthened meaning correctly RULES OUT scenarios where the
    speaker knows the answer. If Pedro's epistemic state were a singleton
    (only the bedroom world), the strengthened meaning would fail. -/
theorem singleton_epist_fails_strengthened :
    strengthenedMeaning fFull [.inBedroom] = false := by native_decide


-- ════════════════════════════════════════════════════
-- § 6b. Deriving MV under ◇: Anti-Exhaustivity (§4.3)
-- ════════════════════════════════════════════════════

/-! The paper gives a SECOND derivation path when *algún* is under a
possibility modal (§4.3, (60)–(68)). The reasoning:

1. Speaker uses ◇(algún room) rather than a singleton ◇(bedroom).
2. The hearer infers anti-exhaustivity: if one room is possible,
   some other room must also be possible.
3. This rules out singleton epistemic states → Modal Variation.

The anti-exhaustivity implicatures ((68b)):
  ◇(bedroom)     → ◇(living room ∨ bathroom)
  ◇(living room)  → ◇(bedroom ∨ bathroom)
  ◇(bathroom)     → ◇(bedroom ∨ living room) -/

/-- Possibility modal ◇ ((60b)):
    ◇(p) = ∃w' ∈ Epistemic. p(w') -/
def possOp (epist : List HideWorld) (p : HideWorld → Bool) : Bool :=
  epist.any p

/-- Sentence under ◇ ((60b)):
    ◇[∃r ∈ f(room). Juan is in r] -/
def sentenceUnderPoss (f : SubsetSelFn Room) (epist : List HideWorld) : Bool :=
  possOp epist λ w => allRooms.any λ r => f isRoom r && juanIn r w

/-- Anti-exhaustivity implicature for room `r` ((68b)):
    ◇(Juan is in r) → ◇(Juan is in some OTHER room).
    As a Boolean: `¬◇(r) ∨ ◇(other rooms)`.
    Blocks exhaustive readings where only one room is possible. -/
def antiExhaustImplicature (r : Room) (epist : List HideWorld) : Bool :=
  !possOp epist (juanIn r) ||
    (allRooms.filter (· != r)).any λ r' => possOp epist (juanIn r')

/-- Strengthened meaning under ◇ ((68)):
    assertion + anti-exhaustivity implicatures for all singleton competitors.

    This is the §4.3 analog of `strengthenedMeaning` (§4.2). -/
def strengthenedMeaningPoss (f : SubsetSelFn Room) (epist : List HideWorld) : Bool :=
  sentenceUnderPoss f epist &&
    antiExhaustImplicature .bedroom epist &&
    antiExhaustImplicature .livingRoom epist &&
    antiExhaustImplicature .bathroom epist

/-- Under ◇, the strengthened meaning holds for Pedro. -/
theorem strengthened_poss_holds :
    strengthenedMeaningPoss fAntiSingleton pedroEpist = true := by native_decide

/-- Under ◇, singleton epistemic states are ruled out: if Pedro only
    considers the bedroom, the anti-exhaustivity implicature for
    bedroom fails (there's no other room that's possible). -/
theorem singleton_epist_fails_poss :
    strengthenedMeaningPoss fFull [.inBedroom] = false := by native_decide

/-- Both derivation paths (§4.2 under □, §4.3 under ◇) agree:
    they accept the same epistemic states for Pedro. -/
theorem necessity_poss_agree :
    strengthenedMeaning fAntiSingleton pedroEpist =
    strengthenedMeaningPoss fAntiSingleton pedroEpist := by native_decide


-- ════════════════════════════════════════════════════
-- § 7. Modal Variation ≠ Free Choice (§§2, 4.4)
-- ════════════════════════════════════════════════════

/-! *Algún*'s Modal Variation is WEAKER than *irgendein*'s Free Choice:

- **Modal Variation** ((18)): the witnesses vary across epistemic
  alternatives — at least two domain members are possibilities.
- **Free Choice** ((13c)): ∀x[P(w)(x) → ∃w' ∈ 𝒜ᵥ. Q(w')(x)] —
  EVERY domain member is a possibility.

Scenario (27)–(30): Pedro knows Juan is NOT in the bathroom.
*Cualquiera* (FC) is ruled out: not ALL rooms are possibilities.
*Algún* (MV) is felicitous: at least two rooms are. -/

/-- Free Choice ((13c)): every room is an epistemic possibility for Juan. -/
def freeChoice (epist : List HideWorld) : Bool :=
  allRooms.all λ r => epist.any (juanIn r)

/-- Modal Variation (counting version): at least two rooms are
    epistemic possibilities. -/
def modalVariation (epist : List HideWorld) : Bool :=
  (allRooms.filter λ r => epist.any (juanIn r)).length > 1

/-- The witness set at world w: {r : isRoom(r) ∧ juanIn(r)(w)}.
    Under uniqueness (one room per world), this is always a singleton.
    MV requires that DIFFERENT worlds yield different singletons. -/
private def witnessSet (w : HideWorld) : List Room :=
  allRooms.filter (juanIn · w)

/-- Modal Variation ((18), formal definition):
    ∃w', w'' ∈ 𝒟_w [{x : P(w')(x) & Q(w')(x)} ≠ {x : P(w'')(x) & Q(w'')(x)}]

    There exist two epistemic alternatives where the sets of individuals
    satisfying both the restrictor and the scope differ. -/
def modalVariation18 (epist : List HideWorld) : Bool :=
  epist.any λ w' => epist.any λ w'' => witnessSet w' != witnessSet w''

/-- The formal definition (18) and the counting definition agree
    in the hide-and-seek model. -/
theorem mv_eq_mv18_pedro :
    modalVariation pedroEpist = modalVariation18 pedroEpist := by native_decide

theorem mv_eq_mv18_full :
    modalVariation allHW = modalVariation18 allHW := by native_decide

/-- Pedro's situation ((27)–(30)): MV holds but FC doesn't.
    *Algún* is appropriate; *cualquiera* is not. -/
theorem mv_not_fc :
    modalVariation pedroEpist = true ∧
    freeChoice pedroEpist = false := by
  constructor <;> native_decide

/-- With full uncertainty (all three rooms possible), BOTH hold. -/
theorem full_uncertainty_both :
    modalVariation allHW = true ∧
    freeChoice allHW = true := by
  constructor <;> native_decide

/-- FC entails MV (for non-trivial domains): if ALL are possibilities
    then certainly more than one is. But not vice versa. -/
theorem fc_strictly_stronger :
    (freeChoice allHW = true → modalVariation allHW = true) ∧
    (modalVariation pedroEpist = true ∧ freeChoice pedroEpist = false) := by
  refine ⟨λ _ => by native_decide, ?_, ?_⟩ <;> native_decide


-- ════════════════════════════════════════════════════════════════
-- Part III: Typology (§§4.4, 5, 6)
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 8. Domain Widening vs Anti-Singleton (§4.4)
-- ════════════════════════════════════════════════════

/-- The two domain constraint strategies for modal indefinites.

    @cite{alonso-ovalle-menendez-benito-2010} §4.4 argues that the
    contrast between *irgendein* and *algún* reduces to different
    constraints on the selection function:
    - Widening: f(P) = P (maximal domain; competitors = all subdomains)
    - Anti-singleton: |f(P)| > 1 (competitors = singleton subdomains only)

    Different competitor sets → different exhaustification outcomes →
    different modal effects (Free Choice vs Modal Variation). -/
inductive DomainConstraint where
  | widening
  | antiSingleton
  deriving DecidableEq, BEq, Repr

/-- The predicted modal effect from each domain constraint type. -/
def DomainConstraint.modalEffect : DomainConstraint → String
  | .widening => "Free Choice"
  | .antiSingleton => "Modal Variation"

/-- Different constraints yield different modal effects. -/
theorem different_constraints_different_effects :
    DomainConstraint.widening.modalEffect ≠
    DomainConstraint.antiSingleton.modalEffect := by decide


-- ════════════════════════════════════════════════════
-- § 9. Competitor Sets (§4.4, (58), (70))
-- ════════════════════════════════════════════════════

/-! The critical mechanism: different constraints generate different
competitor sets for exhaustification.

For *irgendein* (domain widener, (70)): competitors = ALL proper subdomains:
  ◇(bedroom), ◇(living room), ◇(bathroom),
  ◇(bedroom ∨ living room), ◇(bedroom ∨ bathroom), ◇(living room ∨ bathroom)

The full domain ◇(bedroom ∨ living room ∨ bathroom) is the assertion (69)
itself, NOT a competitor.

For *algún* (anti-singleton, (58)): competitors = SINGLETON subdomains:
  □(bedroom), □(living room), □(bathroom)

Exhaustifying over all subdomains → Free Choice (every room possible).
Exhaustifying over singletons only → Modal Variation (≥2 rooms possible). -/

/-- Singleton competitor set (for anti-singleton items like *algún*). -/
def singletonSubdomains : List (List Room) :=
  [[.bedroom], [.livingRoom], [.bathroom]]

/-- Proper subdomain competitors ((70a–f), for domain wideners like
    *irgendein*). Excludes the full domain, which is the assertion
    itself ((69)), not a competitor. -/
def allSubdomains : List (List Room) :=
  [[.bedroom], [.livingRoom], [.bathroom],
   [.bedroom, .livingRoom], [.bedroom, .bathroom], [.livingRoom, .bathroom]]

/-- Anti-singleton items have strictly fewer competitors. This is WHY
    their modal effect is weaker: fewer negated competitors = weaker
    implicature (MV instead of FC). -/
theorem fewer_competitors :
    singletonSubdomains.length < allSubdomains.length := by native_decide


-- ════════════════════════════════════════════════════
-- § 10. 2×2 Typology (Table 1, p.27)
-- ════════════════════════════════════════════════════

/-- Whether uniqueness of the existential witness is assumed.

    Uniqueness: at most one individual per world satisfies the claim
    (e.g., María can only marry one person). Ignorance is about
    IDENTITY ("the speaker doesn't know who").

    Non-uniqueness: multiple witnesses possible (e.g., multiple flies
    in the soup, (73)–(78)). Ignorance is about NUMBER ("the speaker
    doesn't know how many"). -/
inductive UniquenessParam where
  | uniqueness
  | nonUniqueness
  deriving DecidableEq, BEq, Repr

/-- A cell in the 2010 typology (Table 1). -/
structure TypologyCell where
  uniqueness : UniquenessParam
  constraint : DomainConstraint
  modalEffect : String
  numberIgnorance : Bool
  exemplars : List String
  deriving Repr

/-- Cell 1: Widening + Uniqueness → FC, no number ignorance.
    *Irgendein*, *uno qualsiasi*: "any doctor" — every doctor is a
    permitted option, but no ignorance about how many. -/
def cell1_widening_unique : TypologyCell where
  uniqueness := .uniqueness
  constraint := .widening
  modalEffect := "Free Choice"
  numberIgnorance := false
  exemplars := ["irgendein", "uno qualsiasi"]

/-- Cell 4: Anti-singleton + Non-uniqueness → MV + number ignorance.
    *Algún*: "alguna mosca" — the speaker doesn't know how many flies
    are in the soup ((73)–(78)). -/
def cell4_antisingleton_nonunique : TypologyCell where
  uniqueness := .nonUniqueness
  constraint := .antiSingleton
  modalEffect := "Modal Variation"
  numberIgnorance := true
  exemplars := ["algún"]

/-- Cell 2: Anti-singleton + Uniqueness (predicted, unattested in 2010).
    Would show MV without number ignorance. -/
def cell2_predicted : TypologyCell where
  uniqueness := .uniqueness
  constraint := .antiSingleton
  modalEffect := "Modal Variation"
  numberIgnorance := false
  exemplars := []

/-- Cell 3: Widening + Non-uniqueness (predicted, unattested in 2010).
    Would show FC with number ignorance. -/
def cell3_predicted : TypologyCell where
  uniqueness := .nonUniqueness
  constraint := .widening
  modalEffect := "Free Choice"
  numberIgnorance := true
  exemplars := []

/-- The two filled cells differ on BOTH dimensions. -/
theorem filled_cells_contrast :
    cell1_widening_unique.uniqueness ≠ cell4_antisingleton_nonunique.uniqueness ∧
    cell1_widening_unique.constraint ≠ cell4_antisingleton_nonunique.constraint := by
  constructor <;> decide

/-- Two cells are attested, two are predicted gaps. -/
theorem typology_coverage :
    cell1_widening_unique.exemplars.length > 0 ∧
    cell4_antisingleton_nonunique.exemplars.length > 0 ∧
    cell2_predicted.exemplars.length = 0 ∧
    cell3_predicted.exemplars.length = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide


-- ════════════════════════════════════════════════════
-- § 11. Bridge to Fragment Entries
-- ════════════════════════════════════════════════════

/-- The 2010 paper's anti-singleton constraint maps to the `upperBounded`
    field in the fragment entry. `upperBounded = true` records that
    *algún*'s domain cannot be a singleton. -/
theorem algún_entry_captures_antisingleton :
    algúnEntry.upperBounded = true := rfl

/-- The Modal Variation component is classified as `notAtIssue` in the
    fragment entry, consistent with the paper's §3.3 argument that it is
    a conversational implicature: cancellable ((42)), disappears under
    DE operators ((43)–(44)), reinforceable without redundancy ((45d)). -/
theorem algún_entry_not_at_issue :
    algúnEntry.status = .notAtIssue := rfl

/-- The 2010 paper analyzes *algún* as having epistemic content only:
    the Modal Variation inference concerns the SPEAKER's beliefs, mediated
    by ASSERT ((20)). The fragment entry records epistemic-only flavor. -/
theorem algún_entry_epistemic_only :
    algúnEntry.hasEpistemic = true ∧ algúnEntry.hasCircumstantial = false := by
  constructor <;> native_decide


end Phenomena.ModalIndefinites.Studies.AlonsoOvalleMenendezBenito2010
