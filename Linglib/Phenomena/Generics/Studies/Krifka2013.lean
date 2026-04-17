import Linglib.Theories.Semantics.Noun.Kind.Generics
import Linglib.Core.Genericity

/-!
# @cite{krifka-2013}: Definitional Generics

Manfred Krifka, "Definitional Generics", ch. 15 of
*Genericity* (eds. Mari, Beyssade, Del Prete), Oxford University Press, 2013.

## Core Claim

IS-generics ("A madrigal is polyphonic") and BP-generics ("Madrigals are
popular") correlate with two fundamentally different types of generic
meaning:

- **Descriptive generics**: empirical generalizations about the world.
  Restrict possible *worlds* (DES update).
- **Definitional generics**: restrict admissible *interpretations* of
  linguistic expressions (DEF update).

The asymmetry is shown by minimal pairs (exx. 1–2):
- (1) "Madrigals are polyphonic" / "A madrigal is polyphonic" — both OK
- (2) "Madrigals are popular" / "#A madrigal is popular" — IS infelicitous

Being popular is not a defining property of the kind *madrigal*, so the IS
form in (2b) fails as a definitional generic; meanwhile, the syntactic
structure of IS blocks existential closure (the default mechanism), leaving
only universal closure which requires a rule-like interpretation.

## Chapter Sections Covered

- **§15.1**: IS/BP asymmetry, Lawler (1973a), Leslie et al. (2009)
- **§15.2**: Previous accounts — Burton-Roberts (1976, 1977),
  @cite{cohen-1999a}, Greenberg (2003, 2007). Rule types: physical,
  moral, legal, linguistic (exx. 5–9)
- **§15.3.1**: Two-index semantics, DES/DEF update operations,
  descriptive vs definitional readings of "Boys don't cry" (ex. 13),
  madrigal worked examples (exx. 20–21)
- **§15.3.2**: Topic-comment structure — definiendum (topic) vs definiens
  (comment) determines which expression's interpretation gets restricted
- **§15.3.3**: Definitions and facts — empirical discoveries become
  definitional via Kripke/Putnam causal theory of reference
  ("A donkey has 62 chromosomes", ex. 29)
- **§15.3.4**: IS applies to atomic individuals (suited for definitions
  checkable on single exemplars), BP to sum individuals (suited for
  empirical generalizations requiring many observations). But the
  IS→definitional tendency is not absolute (ex. 44).
- **§15.4**: Conclusion

## Connection to Other Generics Studies

- @cite{cohen-1999a} (`Studies/Cohen1999.lean`): Cohen's rule-based
  account of IS generics — Krifka builds on Cohen's insight that IS
  generics express rules (physical, moral, legal, linguistic) but
  reanalyzes "rules" as interpretation restrictions rather than
  ontological entities
- @cite{asher-pelletier-2012} (`Studies/AsherPelletier2013.lean`):
  normality orderings — orthogonal to Krifka's theory, which targets
  the descriptive/definitional distinction rather than default reasoning
-/

namespace Krifka2013

open Core.Genericity (GenericForm GenericReading)


-- ═══ Two-Index Semantics (§15.3.1) ═══

/-- An interpretation index: determines how expressions are interpreted.
    Different interpretations assign different extensions to predicates.
    E.g., different height thresholds for "tall" (Barker 2002, exx. 10–11). -/
structure Interp where
  id : Nat
  deriving DecidableEq, Repr

/-- A world index: determines what factual state of affairs obtains. -/
structure World where
  id : Nat
  deriving DecidableEq, Repr

/-- A denotation under two indices: ⟦α⟧^{i,w} in Krifka's notation. -/
abbrev Denotation := Interp → World → Bool

/-- A common ground: a set of admissible interpretations paired with
    a set of possible worlds (§15.3.1, p. 377). -/
structure CommonGround where
  interps : List Interp
  worlds : List World
  deriving Repr


-- ═══ Update Operations ═══

/-- **DES** (Descriptive update): restricts worlds, keeps interpretations.

    ⟨I, W⟩ + DES(⟦Φ⟧) = ⟨I, {w∈W | ∃i∈I. ⟦Φ⟧^{i,w}}⟩

    Descriptive assertions inform about the world. The existential
    reflects that we may not yet know which interpretation to settle on;
    we keep worlds consistent with at least one admissible reading. -/
def des (cg : CommonGround) (φ : Denotation) : CommonGround where
  interps := cg.interps
  worlds := cg.worlds.filter λ w => cg.interps.any λ i => φ i w

/-- **DEF** (Definitional update): restricts interpretations, keeps worlds.

    ⟨I, W⟩ + DEF(⟦Φ⟧) = ⟨{i∈I | ∀w∈W. ⟦Φ⟧^{i,w}}, W⟩

    Definitional assertions restrict the language: only interpretations
    under which the proposition holds in ALL worlds survive. The universal
    reflects that definitions must hold unconditionally. -/
def def_ (cg : CommonGround) (φ : Denotation) : CommonGround where
  interps := cg.interps.filter λ i => cg.worlds.all λ w => φ i w
  worlds := cg.worlds


-- ═══ Algebraic Properties ═══

/-- DES preserves interpretations. -/
theorem des_preserves_interps (cg : CommonGround) (φ : Denotation) :
    (des cg φ).interps = cg.interps := rfl

/-- DEF preserves worlds. -/
theorem def_preserves_worlds (cg : CommonGround) (φ : Denotation) :
    (def_ cg φ).worlds = cg.worlds := rfl

/-- DES restricts worlds (result is a subset). -/
theorem des_restricts_worlds (cg : CommonGround) (φ : Denotation) :
    ∀ w, w ∈ (des cg φ).worlds → w ∈ cg.worlds :=
  λ _ hw => (List.mem_filter.mp hw).1

/-- DEF restricts interpretations (result is a subset). -/
theorem def_restricts_interps (cg : CommonGround) (φ : Denotation) :
    ∀ i, i ∈ (def_ cg φ).interps → i ∈ cg.interps :=
  λ _ hi => (List.mem_filter.mp hi).1

/-- Any function of worlds alone is invariant under DEF, because DEF only
    changes interpretations. Since threshold semantics measures world-prevalence,
    it cannot capture definitional generics that change truth value through DEF.

    Since traditional GEN (a descriptive operator) reduces to threshold
    semantics (`CovertQuantifier.reduces_to_threshold`), this theorem shows
    definitional generics escape that reduction entirely. -/
theorem def_invariant_world_measure {α : Type} (cg : CommonGround) (φ : Denotation)
    (f : List World → α) :
    f (def_ cg φ).worlds = f cg.worlds := by
  rw [def_preserves_worlds]


-- ═══ Madrigal Worked Example (§15.3.1, exx. 20–21) ═══

/-- Three interpretations of "madrigal" varying in strictness.
    - i₁: strict — only polyphonic pieces count as madrigals
    - i₂: medium — mostly polyphonic, some exceptions allowed
    - i₃: loose — includes monophonic pieces as madrigals -/
def i₁ : Interp := ⟨1⟩
def i₂ : Interp := ⟨2⟩
def i₃ : Interp := ⟨3⟩

/-- Three possible worlds.
    - w₁, w₂: madrigals are generally popular
    - w₃: madrigals are not popular -/
def w₁ : World := ⟨1⟩
def w₂ : World := ⟨2⟩
def w₃ : World := ⟨3⟩

/-- Initial common ground: all interpretations, all worlds. -/
def cg₀ : CommonGround :=
  { interps := [i₁, i₂, i₃]
  , worlds := [w₁, w₂, w₃] }

/-- "Madrigals are popular" — a descriptive claim (ex. 20).
    True in w₁ and w₂ under all interpretations, false in w₃.
    Depends only on the world index: popularity is a fact about the
    world, not about how we interpret "madrigal." -/
def madrigalsPopular : Denotation := λ _i w =>
  match w.id with
  | 1 | 2 => true
  | _ => false

/-- "Madrigals are polyphonic" — a definitional claim (ex. 21).
    True under i₁ and i₂ (in all worlds), false under i₃.
    Depends only on the interpretation index: whether madrigals are
    polyphonic is a matter of how "madrigal" is interpreted. -/
def madrigalsPolyphonic : Denotation := λ i _w =>
  match i.id with
  | 1 | 2 => true
  | _ => false


-- Ex. (20): DES("Madrigals are popular") restricts worlds

/-- After DES("Madrigals are popular"), w₃ is eliminated. -/
theorem des_popular_eliminates_w3 :
    (des cg₀ madrigalsPopular).worlds = [w₁, w₂] := by native_decide

/-- DES preserves all three interpretations. -/
theorem des_popular_keeps_interps :
    (des cg₀ madrigalsPopular).interps = [i₁, i₂, i₃] := rfl


-- Ex. (21): DEF("Madrigals are polyphonic") restricts interpretations

/-- After DEF("Madrigals are polyphonic"), i₃ is eliminated. -/
theorem def_polyphonic_eliminates_i3 :
    (def_ cg₀ madrigalsPolyphonic).interps = [i₁, i₂] := by native_decide

/-- DEF preserves all three worlds. -/
theorem def_polyphonic_keeps_worlds :
    (def_ cg₀ madrigalsPolyphonic).worlds = [w₁, w₂, w₃] := rfl


-- Combined updates: order doesn't matter for the madrigal model

/-- DES then DEF: 2 interpretations, 2 worlds. -/
theorem des_then_def :
    let cg := def_ (des cg₀ madrigalsPopular) madrigalsPolyphonic
    cg.interps = [i₁, i₂] ∧ cg.worlds = [w₁, w₂] := by
  constructor <;> native_decide

/-- DEF then DES: same result.
    This holds because madrigalsPopular depends only on w and
    madrigalsPolyphonic depends only on i, making their filter conditions
    independent. In general, DES and DEF do NOT commute (each references
    the other index in its quantifier scope). -/
theorem def_then_des :
    let cg := des (def_ cg₀ madrigalsPolyphonic) madrigalsPopular
    cg.interps = [i₁, i₂] ∧ cg.worlds = [w₁, w₂] := by
  constructor <;> native_decide


-- Definitional generics escape prevalence thresholds

/-- Definitional generics cannot be reduced to prevalence thresholds because
    they operate on interpretations, not worlds. -/
theorem def_not_world_reducible :
    (def_ cg₀ madrigalsPolyphonic).worlds = cg₀.worlds ∧
    (def_ cg₀ madrigalsPolyphonic).interps ≠ cg₀.interps := by
  constructor
  · rfl
  · native_decide


-- ═══ Rule Types (§15.2, exx. 5–9) ═══

/-- Types of rules that definitional generics can express.
    Following @cite{cohen-1999a}'s categorization as cited by Krifka §15.2. -/
inductive RuleType where
  | physical    -- (5) "An electron has a negative electric charge"
  | moral       -- (6) "A gentleman opens doors for ladies"
  | legal       -- (7) "A bishop moves diagonally" / (8) pomegranate cost
  | linguistic  -- (9) "A madrigal is polyphonic"
  deriving DecidableEq, Repr


-- ═══ IS/BP Felicity Data ═══

/-- Data entry for generics from Krifka's chapter.
    The `felicitous` field captures acceptability judgments —
    critical for encoding the IS/BP asymmetry. -/
structure GenericDatum where
  sentence : String
  subjectForm : GenericForm
  preferredReading : GenericReading
  felicitous : Bool := true
  ruleType : Option RuleType
  exNumber : String
  notes : String := ""
  deriving Repr


-- §15.1, ex. (1): "polyphonic" — both IS and BP felicitous

def madrigalPolyphonicBP : GenericDatum :=
  { sentence := "Madrigals are polyphonic"
  , subjectForm := .barePlural
  , preferredReading := .definitional
  , ruleType := some .linguistic
  , exNumber := "(1a)" }

def madrigalPolyphonicIS : GenericDatum :=
  { sentence := "A madrigal is polyphonic"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .linguistic
  , exNumber := "(1b)/(9)"
  , notes := "Also ex. (9): linguistic rule, definition of the musical form" }

-- §15.1, ex. (2): "popular" — IS infelicitous

def madrigalPopularBP : GenericDatum :=
  { sentence := "Madrigals are popular"
  , subjectForm := .barePlural
  , preferredReading := .descriptive
  , ruleType := none
  , exNumber := "(2a)" }

def madrigalPopularIS : GenericDatum :=
  { sentence := "#A madrigal is popular"
  , subjectForm := .indefiniteSingular
  , preferredReading := .descriptive
  , felicitous := false
  , ruleType := none
  , exNumber := "(2b)"
  , notes := "Popularity is not a defining property — IS blocks EC, forcing UC, which requires rule-like content" }


-- §15.2, exx. (3)–(4): Analyticity contrast

def kangarooMarsupialIS : GenericDatum :=
  { sentence := "A kangaroo is a marsupial"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .physical
  , exNumber := "(3a)"
  , notes := "Analytic — Burton-Roberts (1976): 'to be a kangaroo is to be a marsupial'" }

/-- Bolinger considers (4a) "To be a tiger is to climb trees" analytic
    (but wrongly so), and (4b) true but not analytic. This shows IS-generics
    are not uniformly analytic or definitional. -/
def tigerClimbsTreesIS : GenericDatum :=
  { sentence := "A tiger climbs trees"
  , subjectForm := .indefiniteSingular
  , preferredReading := .descriptive
  , ruleType := none
  , exNumber := "(4a)"
  , notes := "Per Bolinger: not an analytic sentence; IS can be used descriptively" }


-- §15.2, exx. (5)–(8): Cohen's rule types

def electronChargeIS : GenericDatum :=
  { sentence := "An electron has a negative electric charge"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .physical
  , exNumber := "(5)" }

def gentlemanDoorsIS : GenericDatum :=
  { sentence := "A gentleman opens doors for ladies"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .moral
  , exNumber := "(6)" }

def bishopDiagonalIS : GenericDatum :=
  { sentence := "A bishop moves diagonally"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .legal
  , exNumber := "(7)"
  , notes := "Legal rule in chess" }

def pomegranateAppleCost : GenericDatum :=
  { sentence := "A pomegranate apple costs 49 cents"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .legal
  , exNumber := "(8)"
  , notes := "Legal/commercial rule — price set by the shop manager" }


-- ═══ Descriptive vs Definitional Ambiguity (§15.3.1, ex. 13) ═══

/-- "Boys don't cry" (ex. 13) can be read either descriptively or
    definitionally — the same sentence under two interpretive modes:

    **Descriptive**: the speaker assumes a shared interpretation of "boys"
    and communicates about the world — boys in fact don't cry.

    **Definitional**: the speaker proposes restricting the admissible
    interpretations of "boys" to those where entities falling under
    "boys" don't cry in situations that could lead to crying. This
    restricts the *language*, not the *world*. -/
structure AmbiguousGeneric where
  sentence : String
  descriptiveReading : String
  definitionalReading : String
  exNumber : String
  deriving Repr

def boysDontCry : AmbiguousGeneric :=
  { sentence := "Boys don't cry"
  , descriptiveReading := "Boys in fact don't cry (generalization about the world)"
  , definitionalReading := "Restrict 'boys' to entities that don't cry (restricts interpretation)"
  , exNumber := "(13)" }


-- ═══ Definitions and Facts (§15.3.3) ═══

/-- §15.3.3, ex. (29): "A donkey has 62 chromosomes."

    The chromosome number was an empirical discovery, yet the sentence
    reads as definitional. Krifka explains this via Kripke (1972, 1980)
    and Putnam (1975): "donkey" picks out a natural kind via type
    specimens and the causal theory of reference. Properties that "run
    in the kind" at the species level (like chromosome number) become
    definitional properties of the word's meaning. Thus a descriptive
    discovery (Chiquita has 62 chromosomes, DES update) translates into
    a definitional property of "donkey" (DEF update, exx. 31–36). -/
def donkeyChromosomesIS : GenericDatum :=
  { sentence := "A donkey has 62 chromosomes"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .physical
  , exNumber := "(29)"
  , notes := "§15.3.3: empirical discovery becomes definitional via Kripke/Putnam causal theory" }

/-- §15.3.3, ex. (37): "#An animal in this cage has 62 chromosomes."

    Deviant because "animal in this cage" does not pick out a natural
    kind — it's an arbitrary extensional set. Definitional generics
    require the subject to denote a natural kind so that properties
    can be understood as "running in" the kind. -/
def animalCageChromosomes : GenericDatum :=
  { sentence := "#An animal in this cage has 62 chromosomes"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , felicitous := false
  , ruleType := none
  , exNumber := "(37)"
  , notes := "Non-natural-kind subject blocks definitional reading" }


-- ═══ IS Can Be Descriptive (§15.3.4, ex. 44) ═══

/-- §15.3.4 argues that the IS→definitional tendency is NOT absolute.
    Examples like (44a) show IS-generics with clearly descriptive content:
    the methods for catching trout are not part of the definition of "trout."

    §15.4 concludes: "descriptive generalizations are typically expressed
    by bare plurals because they tend to rely on observing many instances;
    definitional statements are typically expressed with indefinite singulars
    because the decision whether entities fall under a concept can typically
    be made by looking at single individuals." But these are tendencies,
    not strict grammatical constraints. -/
def troutCaughtIS : GenericDatum :=
  { sentence := "A trout can be caught by many different methods"
  , subjectForm := .indefiniteSingular
  , preferredReading := .descriptive
  , ruleType := none
  , exNumber := "(44a)"
  , notes := "IS can be descriptive — counterexample to strict IS→definitional" }


-- ═══ IS-Atom / BP-Sum (§15.3.4) ═══

/-- §15.3.4 observes a key structural difference:

    - IS ("a madrigal"): applies to **atomic** individuals. One can check
      whether a single piece of music is polyphonic → suited for definitions
    - BP ("madrigals"): applies to **sum** individuals. Checking popularity
      requires observing many instances → suited for generalizations

    This atomic/sum distinction explains WHY IS-generics tend toward
    definitional readings and BP-generics toward descriptive ones,
    even though neither correlation is absolute. -/
inductive NumberDomain where
  | atomic  -- IS: single individuals; suited for checking defining properties
  | plural  -- BP: sums of individuals; suited for empirical generalizations
  deriving DecidableEq, Repr

def isAtomicDomain : GenericForm → NumberDomain
  | .indefiniteSingular => .atomic
  | .barePlural => .plural
  | .definiteSingular => .atomic
  | .definitePlural => .plural


-- ═══ All Example Data ═══

def exampleData : List GenericDatum :=
  [ madrigalPolyphonicBP, madrigalPolyphonicIS
  , madrigalPopularBP, madrigalPopularIS
  , kangarooMarsupialIS, tigerClimbsTreesIS
  , electronChargeIS, gentlemanDoorsIS, bishopDiagonalIS
  , pomegranateAppleCost
  , donkeyChromosomesIS, animalCageChromosomes
  , troutCaughtIS ]


-- ═══ Key Predictions ═══

/-- The central IS/BP asymmetry: both forms are fine for the definitional
    "polyphonic" predicate, but only BP is fine for the descriptive
    "popular" predicate. -/
theorem is_bp_asymmetry :
    madrigalPolyphonicBP.felicitous = true ∧
    madrigalPolyphonicIS.felicitous = true ∧
    madrigalPopularBP.felicitous = true ∧
    madrigalPopularIS.felicitous = false := ⟨rfl, rfl, rfl, rfl⟩

/-- All BP-generics in the data are felicitous — BPs are the unmarked
    form for both descriptive and definitional content. -/
theorem bp_always_felicitous :
    (exampleData.filter (λ d => d.subjectForm == .barePlural)).all
      (λ d => d.felicitous) = true := by native_decide

/-- Infelicitous IS-generics have no rule type — the infelicity arises
    when IS is used for content that cannot serve as a definition. -/
theorem infelicitous_is_lacks_rule_type :
    (exampleData.filter (λ d =>
      d.subjectForm == .indefiniteSingular && !d.felicitous)).all
      (λ d => d.ruleType.isNone) = true := by native_decide

/-- IS-generics with a rule type are all felicitous. -/
theorem rule_typed_is_felicitous :
    (exampleData.filter (λ d =>
      d.subjectForm == .indefiniteSingular && d.ruleType.isSome)).all
      (λ d => d.felicitous) = true := by native_decide

/-- Natural-kind subjects with definitional readings are felicitous;
    non-natural-kind subjects (like "animal in this cage") fail even
    with definitional intent (ex. 37). -/
theorem natural_kind_required :
    donkeyChromosomesIS.felicitous = true ∧
    animalCageChromosomes.felicitous = false := ⟨rfl, rfl⟩


-- ═══ Topic-Comment: Definiendum vs Definiens (§15.3.2) ═══

/-! §15.3.2 observes that definitional generics have topic-comment structure
where the **definiendum** (the term being defined) is the topic, and the
**definiens** (the defining property) is the comment. "A madrigal is
polyphonic" defines *madrigal* (topic), not *polyphonic* (comment).

The formal DEF rule (ex. 25) restricts interpretations of the topic
expression α to those where the comment β holds for the topic's extension:

  ⟨I, W⟩ + DEF(⟦α⟧, ⟦β⟧) =
    ⟨{i∈I | ∀w∈W ∀X [⟦α⟧^{i,w}(X) → ∀i'∈I ⟦β⟧^{i',w}(X)]}, W⟩

This formalizes the intuition that "A madrigal is polyphonic" defines
*madrigal* rather than *polyphonic*: the definiendum occupies the topic
position and is the expression whose interpretation gets restricted.

The distinction matters for examples like the Greenhorn definition
(ex. 28, from Karl May's *Winnetou I*, 1892): a series of predicational
definitional sentences successively fix the meaning of a new word. -/


-- ═══ Cross-Study Connections ═══

/-- Krifka's definitional generics are orthogonal to the default reasoning
    framework of @cite{asher-pelletier-2012}: normality orderings target
    descriptive generics (which worlds are normal), while Krifka's DEF
    targets the interpretation index. The two theories operate on
    different components of the common ground. -/
theorem orthogonal_to_normality :
    -- DEF doesn't change worlds at all — normality orderings over
    -- worlds are unaffected by definitional updates
    (def_ cg₀ madrigalsPolyphonic).worlds = cg₀.worlds := rfl

/-- @cite{cohen-1999a}'s rule types (physical, moral, legal, linguistic)
    provide the content classification for what Krifka formalizes as
    interpretation restrictions. Cohen claims IS-generics EXPRESS rules;
    Krifka claims IS-generics are INTERPRETED as universal quantification
    (via UC) when the IS form blocks existential closure.

    Both accounts predict the same felicity pattern: IS is natural for
    rule-like content. The difference is architectural — Cohen posits
    "rules" as ontological entities; Krifka derives the rule-like flavor
    from the interaction of IS syntax with closure mechanisms. -/
theorem cohen_krifka_felicity_agreement :
    -- Both predict: IS + rule-type content → felicitous
    electronChargeIS.felicitous = true ∧
    gentlemanDoorsIS.felicitous = true ∧
    bishopDiagonalIS.felicitous = true ∧
    -- Both predict: IS + non-rule content → infelicitous
    madrigalPopularIS.felicitous = false := ⟨rfl, rfl, rfl, rfl⟩


end Krifka2013
