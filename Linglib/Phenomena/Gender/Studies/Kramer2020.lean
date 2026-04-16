import Linglib.Core.Gender
import Linglib.Phenomena.Gender.Typology
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Fragments.Spanish.Gender
import Linglib.Fragments.Russian.Gender

/-!
# Kramer 2020: Grammatical Gender — A Close Look at Gender Assignment
@cite{kramer-2020} @cite{kramer-2015} @cite{corbett-1991} @cite{harris-1991}

Formalizes the core contributions of @cite{kramer-2020}, a review article
that sharpens and extends @cite{kramer-2015}'s structural approach to gender
assignment. Three main results:

1. **The Semantic Core Generalization** (ex. 2/28): every language with
   grammatical gender assigns gender semantically to at least some nouns,
   based on animacy, humanness, and/or social gender/biological sex.

2. **Lexical vs structural gender assignment** (§3): a comparison of
   @cite{harris-1991}'s lexical rules with @cite{kramer-2015}'s structural
   *n*-based approach, identifying three phenomena that differentiate them:
   phonological assignment (§3.3.1), hybrid nouns (§3.3.2), and the
   Semantic Core (§3.3.3).

3. **Cross-linguistic variation in arbitrary assignment** (Table 2):
   remainder nouns vary along two dimensions — same vs different gender(s),
   recycled vs novel vs both.

## Integration

- **Typology ↔ DM bridge**: `SemanticBasis.toGenderDimension` connects the
  typological `SemanticBasis` (from `Phenomena/Gender/Typology.lean`) to
  the DM `GenderDimension` (from `Theories/Morphology/DM/Categorizer.lean`),
  making explicit that the semantic core properties are the *same things*
  parameterized as feature dimensions in the structural approach.

- **DM → Minimalism bridge**: `GenderFeature.toGramFeature` (in
  `Categorizer.lean`) maps DM gender features to Minimalist `GramFeature`,
  with interpretable gender → valued and uninterpretable → unvalued.

- **Semantic Core verified**: `semantic_core_holds` proves the generalization
  over the existing 21-language sample from `Typology.lean`.

-/

-- ============================================================================
-- § 2: SemanticBasis ↔ GenderDimension Bridge (in source namespaces)
-- ============================================================================

/-! The typological `SemanticBasis` and the DM `GenderDimension` describe the
same underlying distinction from different perspectives: typology asks *what
semantic property organizes the system*, while DM asks *what binary feature
sits on n*. @cite{kramer-2020} makes this connection explicit by analyzing
sex-based systems as [±FEM] or [±MASC], and animacy-based systems as [±ANIM].

The mapping is partial in two ways:

1. `SemanticBasis.shape` and `.rationality` have no standard DM feature
   dimension (no [±SHAPE] or [±RATIONAL] in the literature).

2. `SemanticBasis.humanness` maps to `.anim` because @cite{kramer-2015}
   does not posit a [±HUMAN] dimension — the closest is [±ANIM]. This is
   a limitation of the current DM feature inventory, not a claim that
   humanness is a subset of animacy (e.g. Akɔɔse distinguishes human vs
   nonhuman, which is orthogonal to animate vs inanimate).
-/

namespace Phenomena.Gender.Typology

open Morphology.DM

/-- Whether a `SemanticBasis` falls within the semantic core.

    @cite{kramer-2020} ex. 3 identifies three core properties; `shape` and
    `rationality` are *additional* semantic bases (§2.2.1) that go beyond
    the core but never constitute the *only* basis for a gender system. -/
def SemanticBasis.isCore : SemanticBasis → Bool
  | .sex       => true   -- social gender / biological sex
  | .animacy   => true
  | .humanness => true
  | .shape     => false  -- additional, not core
  | .rationality => false

/-- The Semantic Core Generalization: a gender profile satisfies it iff
    it either has no gender system, or at least one of its semantic bases
    falls within the core {animacy, humanness, social gender/sex}. -/
def GenderProfile.satisfiesSemanticCore (p : GenderProfile) : Bool :=
  p.genderCount == .none || p.semanticBases.any SemanticBasis.isCore

/-- Map a typological semantic basis to its corresponding DM gender dimension,
    when one exists. (@cite{kramer-2020} §3)

    The `.humanness` → `.anim` mapping reflects a gap in @cite{kramer-2015}'s
    feature inventory: no [±HUMAN] dimension is posited, so humanness-based
    systems are approximated by [±ANIM]. -/
def SemanticBasis.toGenderDimension : SemanticBasis → Option GenderDimension
  | .sex         => some .fem   -- default: feminine as marked value
  | .animacy     => some .anim
  | .humanness   => some .anim  -- no [±HUMAN] in Kramer 2015; closest is [±ANIM]
  | .shape       => none
  | .rationality => none

end Phenomena.Gender.Typology

namespace Morphology.DM

open Phenomena.Gender.Typology

/-- Inverse direction: map a DM gender dimension to its typological basis.
    (@cite{kramer-2020} §3) -/
def GenderDimension.toSemanticBasis : GenderDimension → SemanticBasis
  | .fem  => .sex
  | .masc => .sex
  | .anim => .animacy

end Morphology.DM

-- ============================================================================
-- Main study namespace
-- ============================================================================

namespace Phenomena.Gender.Studies.Kramer2020

open Phenomena.Gender.Typology
open Morphology.DM

-- ============================================================================
-- § 1: The Semantic Core Generalization (@cite{kramer-2020} ex. 2/28)
-- ============================================================================

/-- **Semantic Core Generalization** (@cite{kramer-2020} ex. 2/28):
    every language in the sample satisfies the semantic core. -/
theorem semantic_core_holds :
    allProfiles.all (·.satisfiesSemanticCore) = true := by native_decide

/-- No language has gender without at least one core semantic basis. -/
theorem no_gender_without_core :
    allProfiles.all (λ p =>
      if p.genderCount != .none
      then p.semanticBases.any SemanticBasis.isCore
      else true) = true := by native_decide

/-- Core semantic properties correspond to DM feature dimensions:
    every core basis has a `toGenderDimension` target. -/
theorem core_properties_have_dimensions :
    SemanticBasis.sex.toGenderDimension.isSome ∧
    SemanticBasis.animacy.toGenderDimension.isSome ∧
    SemanticBasis.humanness.toGenderDimension.isSome := ⟨rfl, rfl, rfl⟩

/-- Non-core properties lack a standard DM dimension. -/
theorem noncore_properties_no_dimension :
    SemanticBasis.shape.toGenderDimension.isNone ∧
    SemanticBasis.rationality.toGenderDimension.isNone := ⟨rfl, rfl⟩

/-- Round-trip: `.sex` → `.fem` (the default parameterization). -/
theorem roundtrip_sex_fem :
    SemanticBasis.sex.toGenderDimension = some .fem := rfl

/-- Round-trip: `.anim` → `.animacy` → `.anim`. -/
theorem roundtrip_anim :
    GenderDimension.anim.toSemanticBasis.toGenderDimension = some .anim := rfl

-- ============================================================================
-- § 3: Cross-Linguistic Variation in Arbitrary Assignment (Table 2)
-- ============================================================================

/-- Whether remainder nouns use recycled genders, novel genders, or both.
    (@cite{kramer-2020} Table 2) -/
inductive RemainderGenderSource where
  | recycled  -- gender reused from semantic core (e.g. Dieri: masc, Spanish: masc/fem)
  | novel     -- novel gender not used for semantic core (e.g. Tamil: neuter)
  | both      -- mix of recycled and novel genders (e.g. Blackfoot: animate + inanimate)
  deriving DecidableEq, Repr

/-- How remainder nouns (those not assigned gender by the semantic core)
    are distributed across genders (@cite{kramer-2020} Table 2).

    Two independent parameters:
    1. Are all remainder nouns in the same gender, or spread across genders?
    2. Is the remainder gender recycled, novel, or a mix of both? -/
structure RemainderPattern where
  /-- Are all remainder nouns assigned to a single gender? -/
  sameGender : Bool
  /-- Source of the remainder gender(s). -/
  genderSource : RemainderGenderSource
  deriving DecidableEq, Repr

/-- Dieri (Pama-Nyungan): all remainder nouns are masculine (= same gender
    used for male humans). Same gender, recycled. (@cite{kramer-2020} Table 2) -/
def dieri : RemainderPattern := ⟨true, .recycled⟩

/-- Tamil (Dravidian): remainder nouns go to neuter — a novel gender not
    used for the male/female semantic core. Same gender, novel.
    (@cite{kramer-2020} Table 2; Asher 1982) -/
def tamil : RemainderPattern := ⟨true, .novel⟩

/-- Spanish: remainder nouns are split arbitrarily across masculine and
    feminine — both recycled genders. Different genders, recycled.
    (@cite{kramer-2020} Table 1, Table 2; @cite{harris-1991}) -/
def spanishRemainder : RemainderPattern := ⟨false, .recycled⟩

/-- Akɔɔse (Niger-Congo: Bantu): remainder nouns spread across at least
    7 noun classes — novel genders. Different genders, novel.
    (@cite{kramer-2020} Table 2; Hedinger 2008) -/
def akoose : RemainderPattern := ⟨false, .novel⟩

/-- Blackfoot (Algic: Algonquian): inanimate nouns are assigned either a
    novel inanimate gender or a recycled animate gender. Different genders,
    both recycled and novel. (@cite{kramer-2020} Table 2; Frantz 2017) -/
def blackfoot : RemainderPattern := ⟨false, .both⟩

-- NOTE: Table 2 marks "same gender + both recycled and novel" as
-- "Not applicable" — if all remainder nouns go to ONE gender, that gender
-- is either recycled or novel, not both. This is a conceptual constraint,
-- not derivable from our type. (@cite{kramer-2020} Table 2)

/-- All five attested cells of Table 2 are distinct patterns. -/
theorem table2_all_cells :
    dieri ≠ tamil ∧ dieri ≠ spanishRemainder ∧ dieri ≠ akoose ∧
    dieri ≠ blackfoot ∧ tamil ≠ spanishRemainder ∧ tamil ≠ akoose ∧
    tamil ≠ blackfoot ∧ spanishRemainder ≠ akoose ∧
    spanishRemainder ≠ blackfoot ∧ akoose ≠ blackfoot := by decide

-- ============================================================================
-- § 4: Lexical vs Structural Gender Assignment (@cite{kramer-2020} §3)
-- ============================================================================

/-! @cite{kramer-2020} §3.2 contrasts two theoretical approaches:

**Lexical** (@cite{harris-1991}): gender assigned via lexical rules that
map semantic features (e.g. [FEMALE]) to grammatical gender features
(e.g. [F]). Each noun is listed with its gender feature in the lexicon.
Gender is a property of the *lexical entry*.

**Structural** (@cite{kramer-2015}): gender is a phi-feature on the
categorizing head *n*. A root combines with an *n* bearing gender features
via syntactic Merge. Gender is a property of the *syntactic structure*.

Three phenomena differentiate them (§3.3):
1. Phonological gender assignment
2. Hybrid nouns (e.g. Russian *vrač*)
3. The Semantic Core Generalization
-/

/-- A lexical gender rule: maps a semantic feature to a grammatical gender
    feature in a specified context. (@cite{harris-1991})

    The `semanticBasis` identifies which semantic property triggers the
    rule; `targetDimension` identifies which DM gender dimension is
    assigned; `context` describes the conditioning environment. -/
structure LexicalGenderRule where
  /-- Semantic trigger (e.g. sex → social gender triggers the rule) -/
  semanticBasis : SemanticBasis
  /-- DM gender dimension assigned (e.g. fem) -/
  targetDimension : GenderDimension
  /-- Context restriction (e.g. humanness) -/
  context : SemanticBasis
  deriving DecidableEq, Repr

/-- Harris's Human Gender rule for Spanish:
    [FEMALE] → [F] / __ [HUMAN]
    The semantic feature [FEMALE] triggers assignment of the grammatical
    gender feature [F] (feminine) in the context of [HUMAN] nouns.
    (@cite{harris-1991}; @cite{kramer-2020} ex. 23) -/
def harrisHumanGenderRule : LexicalGenderRule :=
  ⟨.sex, .fem, .humanness⟩

/-- Harris's rule connects two core semantic bases: assignment is triggered
    by social gender/sex and conditioned on humanness. -/
theorem harris_rule_uses_core_bases :
    harrisHumanGenderRule.semanticBasis.isCore ∧
    harrisHumanGenderRule.context.isCore := ⟨rfl, rfl⟩

/-- The status of a diagnostic phenomenon for a theoretical approach.
    @cite{kramer-2020} §3.3 argues that some phenomena are genuinely
    diagnostic while others are inconclusive. -/
inductive DiagnosticStatus where
  | handled       -- the approach handles this phenomenon
  | problematic   -- the approach cannot handle this phenomenon
  | inconclusive  -- the phenomenon may not exist or can be reanalyzed
  deriving DecidableEq, Repr

/-- A gender assignment approach, characterized by how it handles
    each of the three diagnostic phenomena from §3.3. -/
structure ApproachCapabilities where
  /-- §3.3.1: phonological gender assignment -/
  phonologicalAssignment : DiagnosticStatus
  /-- §3.3.2: hybrid nouns (simultaneous dual agreement) -/
  hybridAgreement : DiagnosticStatus
  /-- §3.3.3: the Semantic Core Generalization -/
  predictsSemanticCore : DiagnosticStatus
  deriving DecidableEq, Repr

/-- The lexical approach (@cite{harris-1991}).

    - **Phonological assignment**: handled (lexical rules can reference
      phonology), but @cite{kramer-2020} §3.3.1 argues the phenomenon may
      not exist — Hausa -ā is morphophonological realization, not assignment.
    - **Hybrid agreement**: problematic — a lexical entry has one gender
      feature; a single entry cannot be both [M] and [F]
      (@cite{kramer-2020} §3.3.2)
    - **Semantic Core**: problematic — nothing prevents a language from
      having only arbitrary gender rules without any semantic connection
      (@cite{kramer-2020} §3.3.3) -/
def lexicalApproach : ApproachCapabilities :=
  ⟨.handled, .problematic, .problematic⟩

/-- The structural approach (@cite{kramer-2015}).

    - **Phonological assignment**: inconclusive — syntax cannot see phonology,
      but @cite{kramer-2020} §3.3.1 argues the phenomenon is better analyzed
      as morphophonological realization of a gender feature on *n*, so the
      structural approach is not genuinely challenged.
    - **Hybrid agreement**: handled — a root can combine with different *n*
      heads, or a social-gender projection can override morphosyntactic
      gender (@cite{kramer-2020} §3.3.2)
    - **Semantic Core**: handled — via the Thesis of Radical Interpretability:
      if a language has gender features, at least some must be interpretable,
      which forces semantic assignment for at least some nouns
      (@cite{kramer-2020} §3.3.3) -/
def structuralApproach : ApproachCapabilities :=
  ⟨.inconclusive, .handled, .handled⟩

/-- The approaches differ on all three diagnostic phenomena. -/
theorem approaches_differ :
    lexicalApproach.phonologicalAssignment ≠ structuralApproach.phonologicalAssignment ∧
    lexicalApproach.hybridAgreement ≠ structuralApproach.hybridAgreement ∧
    lexicalApproach.predictsSemanticCore ≠ structuralApproach.predictsSemanticCore := by
  decide

/-- The structural approach handles 2 of the 3 diagnostic phenomena;
    the lexical approach handles 1. Phonological assignment is inconclusive
    for both (the structural approach because syntax can't see phonology;
    the lexical approach because Kramer argues the phenomenon doesn't exist
    as described). This is the basis for @cite{kramer-2020} §3.4's conclusion
    that "structural gender assignment has a slight edge." -/
theorem structural_edge :
    structuralApproach.hybridAgreement = .handled ∧
    structuralApproach.predictsSemanticCore = .handled ∧
    lexicalApproach.hybridAgreement = .problematic ∧
    lexicalApproach.predictsSemanticCore = .problematic := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Thesis of Radical Interpretability (@cite{kramer-2020} ex. 29)
-- ============================================================================

/-- Radical Interpretability (Brody 1997; Pesetsky & Torrego 2001, 2007):
    each syntactic feature must receive a semantic interpretation in some
    syntactic location.

    In formal terms: if a feature F has an uninterpretable instantiation
    in a language, then F also has an interpretable instantiation in that
    language. The converse need not hold. -/
def radicalInterpretability (features : List GenderFeature) : Prop :=
  ∀ gf ∈ features, gf.interp = .u →
    ∃ gf' ∈ features, gf'.interp = .i ∧ gf'.val.dim = gf.val.dim

/-- Amharic's n types satisfy Radical Interpretability: the
    uninterpretable u[+FEM] is accompanied by interpretable i[+FEM]
    and i[−FEM] in the same dimension. -/
theorem amharic_radical_interpretability :
    radicalInterpretability
      [ GenderFeature.mk .i ⟨.fem, .pos⟩,   -- n i[+FEM]
        GenderFeature.mk .i ⟨.fem, .neg⟩,   -- n i[−FEM]
        GenderFeature.mk .u ⟨.fem, .pos⟩ ]  -- n u[+FEM]
    := by
  intro gf hgf hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hgf
  rcases hgf with rfl | rfl | rfl
  · exact absurd hu (by decide)
  · exact absurd hu (by decide)
  · exact ⟨⟨.i, ⟨.fem, .pos⟩⟩, by simp, rfl, rfl⟩

/-- Spanish's n types (Set 1) satisfy Radical Interpretability: u[+FEM]
    is accompanied by i[+FEM] in the same dimension. -/
theorem spanish_radical_interpretability :
    radicalInterpretability
      [ GenderFeature.mk .i ⟨.fem, .pos⟩,   -- n i[+FEM]
        GenderFeature.mk .i ⟨.fem, .neg⟩,   -- n i[−FEM]
        GenderFeature.mk .u ⟨.fem, .pos⟩ ]  -- n u[+FEM]
    := amharic_radical_interpretability  -- same inventory

/-- Russian's n types (5-n) satisfy Radical Interpretability: both
    u[+FEM] and u[−FEM] are paired with i[+FEM] and i[−FEM]. -/
theorem russian_radical_interpretability :
    radicalInterpretability
      [ GenderFeature.mk .i ⟨.fem, .pos⟩,   -- n i[+FEM]
        GenderFeature.mk .i ⟨.fem, .neg⟩,   -- n i[−FEM]
        GenderFeature.mk .u ⟨.fem, .pos⟩,   -- n u[+FEM]
        GenderFeature.mk .u ⟨.fem, .neg⟩ ]  -- n u[−FEM]
    := by
  intro gf hgf hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hgf
  rcases hgf with rfl | rfl | rfl | rfl
  · exact absurd hu (by decide)
  · exact absurd hu (by decide)
  · exact ⟨⟨.i, ⟨.fem, .pos⟩⟩, by simp, rfl, rfl⟩
  · exact ⟨⟨.i, ⟨.fem, .neg⟩⟩, by simp, rfl, rfl⟩

/-- The Semantic Core follows from Radical Interpretability + structural
    assignment: if a language has any gender feature (even uninterpretable),
    it must have an interpretable one in the same dimension, which forces
    at least some nouns to be assigned gender semantically.

    Contrapositively: a language with *only* uninterpretable gender
    (pure arbitrary assignment, no semantic core) violates Radical
    Interpretability. -/
theorem no_purely_arbitrary_under_ri
    (features : List GenderFeature)
    (hRI : radicalInterpretability features)
    (hNonempty : ∃ gf ∈ features, True)
    (hAllU : ∀ gf ∈ features, gf.interp = .u) :
    False := by
  obtain ⟨gf, hgf, _⟩ := hNonempty
  obtain ⟨gf', hgf', hi, _⟩ := hRI gf hgf (hAllU gf hgf)
  exact absurd hi (by rw [hAllU gf' hgf']; decide)

/-- Positive direction of the RI → Semantic Core derivation:
    if a language has gender features and satisfies Radical Interpretability,
    then it has at least one interpretable gender feature (which, being
    interpretable, forces semantic gender assignment for at least some nouns).
    (@cite{kramer-2020} §3.3.3) -/
theorem ri_implies_interpretable_exists
    (features : List GenderFeature)
    (hRI : radicalInterpretability features)
    (hNonempty : ∃ gf ∈ features, True) :
    ∃ gf ∈ features, gf.interp = .i := by
  by_contra h
  push_neg at h
  have hAllU : ∀ gf ∈ features, gf.interp = .u := by
    intro gf hgf
    cases hInterp : gf.interp with
    | i => exact absurd hInterp (by intro heq; exact h gf hgf heq)
    | u => rfl
  exact no_purely_arbitrary_under_ri features hRI hNonempty hAllU

-- ============================================================================
-- § 6: Referent-Based Gender Assignment (@cite{kramer-2020} §2.2.3)
-- ============================================================================

/-- Same-root nominals: nouns that can be assigned different grammatical
    genders depending on the social gender of their referent.
    (@cite{kramer-2020} §2.2.3; @cite{kramer-2015}; @cite{corbett-1991})

    In the structural approach, the root itself is ungendered; gender
    depends on which *n* head it merges with. Same-root nominals combine
    with alternative n heads depending on the referent.

    Examples: Amharic *hakim* 'doctor' (ex. 13), Spanish *estudiante*
    'student', Greek *odigós* 'driver'. -/
structure SameRootNominal where
  /-- The noun form -/
  form : String
  /-- Language -/
  language : String
  /-- Possible gender assignments (> 1 for same-root nominals) -/
  possibleNHeads : List CatHead
  deriving Repr

/-- Whether this is a genuine same-root nominal (multiple n options). -/
def SameRootNominal.isSameRoot (n : SameRootNominal) : Bool :=
  n.possibleNHeads.length > 1

/-- Amharic *hakim* 'doctor': combines with either i[+FEM] or i[−FEM]
    depending on the referent. (@cite{kramer-2020} ex. 13) -/
def amharicHakim : SameRootNominal :=
  { form := "hakim"
    language := "Amharic"
    possibleNHeads := [CatHead.n_iFem, CatHead.n_iMasc] }

theorem hakim_is_same_root : amharicHakim.isSameRoot = true := rfl

/-- Same-root nominals pose a challenge for lexical approaches: a single
    lexical entry cannot carry both [M] and [F]. The structural approach
    handles them by allowing the same root to merge with different n heads. -/
theorem same_root_two_n_heads :
    amharicHakim.possibleNHeads.length = 2 := rfl

/-- The two n heads for *hakim* are distinct gender features. -/
theorem hakim_distinct_genders :
    CatHead.n_iFem ≠ CatHead.n_iMasc := by decide

-- ============================================================================
-- § 7: Hybrid Nouns (@cite{kramer-2020} §2.2.3, §3.3.2)
-- ============================================================================

/-! Hybrid nouns are distinct from same-root nominals. Where same-root
nominals alternate gender depending on the referent (Amharic *hakim* is
EITHER masculine OR feminine), hybrid nouns trigger BOTH genders
SIMULTANEOUSLY on different agreement targets in the same sentence.

@cite{kramer-2020} ex. 16/27: Russian *vrač* 'doctor'
  *očen' xoroš-aja glavn-yj vrač*
   very  good-F    head-M   doctor
  'a very good head doctor'

Here *xoroš-aja* shows feminine agreement and *glavn-yj* shows masculine
agreement with the SAME noun *vrač* in the SAME clause.

@cite{kramer-2020} §3.3.2 argues this is problematic for lexical approaches
(a lexical entry has one gender feature) but handled by structural approaches
(a social-gender projection can coexist with morphosyntactic gender on n).
-/

/-- A hybrid noun: a single lexical item that triggers different genders
    on different agreement targets simultaneously.
    (@cite{kramer-2020} §2.2.3, §3.3.2; @cite{corbett-1991}) -/
structure HybridNoun where
  /-- The noun form -/
  form : String
  /-- Language -/
  language : String
  /-- Morphosyntactic gender (from n head) -/
  morphGender : GenderVal
  /-- Semantic gender (from social-gender projection, triggered by referent) -/
  semGender : GenderVal
  /-- The two genders must differ for hybrid agreement to arise. -/
  distinct : morphGender ≠ semGender
  deriving Repr

/-- Russian *vrač* 'doctor': morphologically masculine (from n), but
    can trigger feminine agreement when referring to a female doctor.
    (@cite{kramer-2020} ex. 15-16/27; @cite{corbett-1991}) -/
def russianVrac : HybridNoun :=
  { form := "vrač"
    language := "Russian"
    morphGender := ⟨.fem, .neg⟩  -- [−FEM] = morphological masculine
    semGender := ⟨.fem, .pos⟩    -- [+FEM] = semantic feminine (female referent)
    distinct := by decide }

/-- Hybrid nouns are problematic for lexical approaches: a lexical entry
    can bear only one gender feature, but hybrid nouns need two genders
    simultaneously. The structural approach handles this via separate
    projections for morphosyntactic and social gender.
    (@cite{kramer-2020} §3.3.2) -/
theorem hybrid_nouns_favor_structural :
    structuralApproach.hybridAgreement = .handled ∧
    lexicalApproach.hybridAgreement = .problematic := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: N Inventory Typology (@cite{kramer-2015} Chs 5-7)
-- ============================================================================

/-- An inventory of n heads for a language, with the number of surface
    genders that result from VI (@cite{kramer-2015} Chs 5-7).

    The key insight: surface gender count is determined by VI rules, not
    directly by the n inventory. Two languages can have the SAME set of
    n heads but different numbers of surface genders (e.g., Dieri 2 vs
    Mangarayi 3). -/
structure NInventory where
  language : String
  nHeads : List CatHead
  surfaceGenders : Nat
  deriving Repr

/-- Does this inventory include any arbitrary (uninterpretable) gender? -/
def NInventory.hasArbitraryGender (inv : NInventory) : Bool :=
  inv.nHeads.any (λ ch => match ch.phi.gender with
    | some gf => gf.isArbitrary | none => false)

/-- Is this a purely semantic gender system (no u-features)? -/
def NInventory.purelySemanticGender (inv : NInventory) : Bool :=
  !inv.hasArbitraryGender

-- 3-n languages: no u-feature (@cite{kramer-2015} Ch 5)

def dieriNs : NInventory :=
  ⟨"Dieri", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain], 2⟩

def mangarayiNs : NInventory :=
  ⟨"Mangarayi", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain], 3⟩

-- 4-n languages, Set 1: u[+FEM] (@cite{kramer-2015} Ch 6)

def amharicNs : NInventory :=
  ⟨"Amharic", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
               CatHead.n_uFem], 2⟩

def spanishNs : NInventory :=
  ⟨"Spanish", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
               CatHead.n_uFem], 2⟩

-- 4-n languages, Set 2: u[−FEM] (@cite{kramer-2015} Ch 6)

def maaNs : NInventory :=
  ⟨"Maa", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
           CatHead.n_uNegFem], 2⟩

-- 3-n languages with animacy features (@cite{kramer-2015} Ch 5, §5.3)

def lealaoNs : NInventory :=
  ⟨"Lealao Chinantec", [CatHead.n_iAnim, CatHead.n_iInanim,
                         CatHead.n_plain], 2⟩

-- 4-n languages, animacy dimension (@cite{kramer-2015} Ch 6, §6.4)

def ojibweNs : NInventory :=
  ⟨"Ojibwe", [CatHead.n_iAnim, CatHead.n_iInanim, CatHead.n_plain,
              CatHead.n_uAnim], 2⟩

-- 5-n languages (@cite{kramer-2015} Ch 7)

def lavukaleveNs : NInventory :=
  ⟨"Lavukaleve", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
                  CatHead.n_uFem, CatHead.n_uNegFem], 3⟩

/-- Same n inventory, different surface genders: Dieri (2) vs Mangarayi (3).
    This demonstrates that surface gender count depends on VI, not the
    inventory itself. -/
theorem same_ns_different_genders :
    dieriNs.nHeads = mangarayiNs.nHeads ∧
    dieriNs.surfaceGenders ≠ mangarayiNs.surfaceGenders := ⟨rfl, by decide⟩

/-- Set 1 languages share the same n inventory (@cite{kramer-2015} Ch 6). -/
theorem set1_shared : amharicNs.nHeads = spanishNs.nHeads := rfl

/-- 3-n languages have purely semantic gender (no u-features).
    (@cite{kramer-2015} Ch 5) -/
theorem dieri_purely_semantic :
    dieriNs.purelySemanticGender = true := rfl

/-- Lealao Chinantec is also purely semantic (animacy-based, Ch 5). -/
theorem lealao_purely_semantic :
    lealaoNs.purelySemanticGender = true := rfl

/-- Ojibwe is a 4-n animacy language with arbitrary animate assignment
    (u[+ANIM]). (@cite{kramer-2015} Ch 6, §6.4) -/
theorem ojibwe_has_uAnim :
    ojibweNs.hasArbitraryGender = true := rfl

/-- Ojibwe has the same structure as Set 1 sex-based languages (Amharic,
    Spanish) but in the animacy dimension: i[+ANIM], i[−ANIM], plain n,
    u[+ANIM]. -/
theorem ojibwe_four_ns : ojibweNs.nHeads.length = 4 := rfl

/-- Lavukaleve is maximal: 5 n heads (both u[+FEM] and u[−FEM]). -/
theorem lavukaleve_maximal :
    lavukaleveNs.nHeads.length = 5 := rfl

/-- More n heads does not entail more surface genders:
    Amharic has 4 ns but only 2 surface genders. -/
theorem more_ns_same_genders :
    amharicNs.nHeads.length > dieriNs.nHeads.length ∧
    amharicNs.surfaceGenders = dieriNs.surfaceGenders := ⟨by decide, rfl⟩

-- ============================================================================
-- § 9: Spanish Gender Case Study (@cite{kramer-2015} Ch 6)
-- ============================================================================

/-- Derive from fragment: *hombre* 'man' has natural masculine gender (i[−FEM]). -/
theorem hombre_natural_masculine :
    Fragments.Spanish.Gender.hombre.nHead.phi.gender =
      some ⟨.i, ⟨.fem, .neg⟩⟩ := rfl

/-- Derive from fragment: *mujer* 'woman' has natural feminine gender (i[+FEM]). -/
theorem mujer_natural_feminine :
    Fragments.Spanish.Gender.mujer.nHead.phi.gender =
      some ⟨.i, ⟨.fem, .pos⟩⟩ := rfl

/-- Derive from fragment: *mesa* 'table' has arbitrary feminine gender (u[+FEM]). -/
theorem mesa_arbitrary_feminine :
    Fragments.Spanish.Gender.mesa.nHead.phi.gender =
      some ⟨.u, ⟨.fem, .pos⟩⟩ := rfl

/-- Derive from fragment: *libro* 'book' has default masculine (plain n). -/
theorem libro_default_masculine :
    Fragments.Spanish.Gender.libro.nHead.phi.gender = none := rfl

/-- Bridge: convert a Spanish `SameRootEntry` to the cross-linguistic
    `SameRootNominal` type. -/
def spanishSameRoot (e : Fragments.Spanish.Gender.SameRootEntry) : SameRootNominal :=
  { form := e.form
    language := "Spanish"
    possibleNHeads := e.possibleNHeads }

/-- Spanish *soldado* 'soldier' as a same-root nominal:
    the root √SOLDAD can combine with i[+FEM] or i[−FEM]. -/
theorem soldado_is_same_root :
    Fragments.Spanish.Gender.soldado.mascHead ≠
    Fragments.Spanish.Gender.soldado.femHead := by decide

/-- Spanish same-root nominals are genuine same-root nominals
    (they have two possible n heads). -/
theorem spanish_same_roots_genuine :
    (spanishSameRoot Fragments.Spanish.Gender.soldado).isSameRoot = true ∧
    (spanishSameRoot Fragments.Spanish.Gender.estudiante).isSameRoot = true ∧
    (spanishSameRoot Fragments.Spanish.Gender.artista).isSameRoot = true :=
  ⟨rfl, rfl, rfl⟩

/-- Spanish has the full Set 1 inventory: 4 n types. -/
theorem spanish_four_n_types :
    spanishNs.nHeads.length = 4 := rfl

/-- The fragment inventory covers all four n-types from the NInventory. -/
theorem fragment_covers_inventory :
    Fragments.Spanish.Gender.allNouns.any (·.nHead == CatHead.n_iFem) = true ∧
    Fragments.Spanish.Gender.allNouns.any (·.nHead == CatHead.n_iMasc) = true ∧
    Fragments.Spanish.Gender.allNouns.any (·.nHead == CatHead.n_uFem) = true ∧
    Fragments.Spanish.Gender.allNouns.any (·.nHead == CatHead.n_plain) = true :=
  Fragments.Spanish.Gender.four_n_types_covered

-- ============================================================================
-- § 10: Root Licensing (@cite{kramer-2015} §3.4, Table 6.2)
-- ============================================================================

/-! @cite{kramer-2015} §3.4 identifies four classes of roots, distinguished by
which n heads they are licensed to combine with:

1. **Female-denoting roots** (√WOMAN, √QUEEN): semantic licensing (List 3)
   requires n i[+FEM]. The Encyclopedia entry only provides a denotation in the
   context of an n head bearing [+FEM].
2. **Male-denoting roots** (√MAN, √KING): semantic licensing requires n i[−FEM].
3. **Arbitrarily feminine roots** (√TABLE, √CHAIR): PF licensing (List 2)
   requires n u[+FEM]. A VI rule specifies the exponent in the context of
   [+FEM] on n.
4. **Default roots** (√BOOK, √CAR): no licensing requirement. Combine with
   plain n (the elsewhere case).

This classification generates the licensing tables found in Tables 3.1
(Amharic, 3 ns) and 6.2 (Spanish, 4 ns). -/

/-- Root classes from @cite{kramer-2015} §3.4, parameterized by which n head
    the root is licensed to combine with.

    The first four classes are from Tables 3.1/6.2 (3-n and Set 1 4-n systems).
    `arbitraryMasc` extends the typology to 5-n systems (Russian, Lavukaleve)
    and Set 2 4-n systems (Maa, Wari'), where u[−FEM] is also attested. -/
inductive RootClass where
  | femaleReferent    -- √WOMAN, √QUEEN: semantically requires i[+FEM]
  | maleReferent      -- √MAN, √KING: semantically requires i[−FEM]
  | arbitraryFem      -- √TABLE, √CHAIR: PF-licensed with u[+FEM]
  | arbitraryMasc     -- √LAW, √DOCTOR: PF-licensed with u[−FEM] (5-n / Set 2)
  | default           -- √BOOK, √CAR: no requirement, combines with plain n
  deriving DecidableEq, Repr

/-- The n head each root class is licensed to combine with. -/
def RootClass.licensedNHead : RootClass → CatHead
  | .femaleReferent => CatHead.n_iFem
  | .maleReferent   => CatHead.n_iMasc
  | .arbitraryFem   => CatHead.n_uFem
  | .arbitraryMasc  => CatHead.n_uNegFem
  | .default        => CatHead.n_plain

/-- The licensing type for each root class. -/
def RootClass.licensing : RootClass → LicensingType
  | .femaleReferent => .semantic   -- Encyclopedia / List 3
  | .maleReferent   => .semantic   -- Encyclopedia / List 3
  | .arbitraryFem   => .arbitrary  -- PF / List 2
  | .arbitraryMasc  => .arbitrary  -- PF / List 2
  | .default        => .arbitrary  -- elsewhere

/-- Natural-gender roots are semantically licensed. -/
theorem natural_roots_semantic :
    RootClass.femaleReferent.licensing = .semantic ∧
    RootClass.maleReferent.licensing = .semantic := ⟨rfl, rfl⟩

/-- Arbitrary and default roots are PF-licensed. -/
theorem arbitrary_roots_pf :
    RootClass.arbitraryFem.licensing = .arbitrary ∧
    RootClass.arbitraryMasc.licensing = .arbitrary ∧
    RootClass.default.licensing = .arbitrary := ⟨rfl, rfl, rfl⟩

/-- Each root class maps to a distinct n head. -/
theorem root_classes_distinct_n :
    RootClass.femaleReferent.licensedNHead ≠ RootClass.maleReferent.licensedNHead ∧
    RootClass.femaleReferent.licensedNHead ≠ RootClass.arbitraryFem.licensedNHead ∧
    RootClass.femaleReferent.licensedNHead ≠ RootClass.arbitraryMasc.licensedNHead ∧
    RootClass.femaleReferent.licensedNHead ≠ RootClass.default.licensedNHead ∧
    RootClass.maleReferent.licensedNHead ≠ RootClass.arbitraryFem.licensedNHead ∧
    RootClass.maleReferent.licensedNHead ≠ RootClass.arbitraryMasc.licensedNHead ∧
    RootClass.maleReferent.licensedNHead ≠ RootClass.default.licensedNHead ∧
    RootClass.arbitraryFem.licensedNHead ≠ RootClass.arbitraryMasc.licensedNHead ∧
    RootClass.arbitraryFem.licensedNHead ≠ RootClass.default.licensedNHead ∧
    RootClass.arbitraryMasc.licensedNHead ≠ RootClass.default.licensedNHead := by
  decide

/-- Verify that the Spanish fragment's nouns match their expected root classes.
    Each noun's nHead should equal the licensed n head for its root class. -/
theorem spanish_licensing_mujer :
    Fragments.Spanish.Gender.mujer.nHead = RootClass.femaleReferent.licensedNHead := rfl
theorem spanish_licensing_hombre :
    Fragments.Spanish.Gender.hombre.nHead = RootClass.maleReferent.licensedNHead := rfl
theorem spanish_licensing_mesa :
    Fragments.Spanish.Gender.mesa.nHead = RootClass.arbitraryFem.licensedNHead := rfl
theorem spanish_licensing_libro :
    Fragments.Spanish.Gender.libro.nHead = RootClass.default.licensedNHead := rfl

/-- Bridge: the licensing type of a root class agrees with the licensing
    type derived from its n head's gender feature. For gendered root classes,
    the `GenderFeature.licensingType` (defined in `Categorizer.lean`) produces
    the same result as `RootClass.licensing`. -/
theorem licensing_bridge_femaleReferent :
    (CatHead.n_iFem.phi.gender.get (by rfl)).licensingType =
      RootClass.femaleReferent.licensing := rfl
theorem licensing_bridge_maleReferent :
    (CatHead.n_iMasc.phi.gender.get (by rfl)).licensingType =
      RootClass.maleReferent.licensing := rfl
theorem licensing_bridge_arbitraryFem :
    (CatHead.n_uFem.phi.gender.get (by rfl)).licensingType =
      RootClass.arbitraryFem.licensing := rfl
theorem licensing_bridge_arbitraryMasc :
    (CatHead.n_uNegFem.phi.gender.get (by rfl)).licensingType =
      RootClass.arbitraryMasc.licensing := rfl

/-- Russian fragment nouns match their root classes. -/
theorem russian_licensing_otec :
    Fragments.Russian.Gender.otec.nHead = RootClass.maleReferent.licensedNHead := rfl
theorem russian_licensing_mat' :
    Fragments.Russian.Gender.mat'.nHead = RootClass.femaleReferent.licensedNHead := rfl
theorem russian_licensing_zakon :
    Fragments.Russian.Gender.zakon.nHead = RootClass.arbitraryMasc.licensedNHead := rfl
theorem russian_licensing_škola :
    Fragments.Russian.Gender.škola.nHead = RootClass.arbitraryFem.licensedNHead := rfl
theorem russian_licensing_vino :
    Fragments.Russian.Gender.vino.nHead = RootClass.default.licensedNHead := rfl

/-- *persona* is human-denoting but has u[+FEM] (arbitrary feminine), not
    i[+FEM] (natural feminine). This is the key exception to the pattern
    that human-denoting nouns get interpretable gender features.
    (@cite{kramer-2020} §3.2, p. 59; @cite{kramer-2015} §6.2)

    In root-class terms: persona's root is licensed as `arbitraryFem`
    despite denoting humans — its root is only licensed to combine with
    n u[+FEM], never n i[+FEM] or n i[−FEM]. -/
theorem persona_exception :
    Fragments.Spanish.Gender.persona.nHead = RootClass.arbitraryFem.licensedNHead ∧
    Fragments.Spanish.Gender.persona.gloss = "person" := ⟨rfl, rfl⟩

-- ============================================================================
-- § 11: NInventory ↔ GenderProfile Bridge
-- ============================================================================

/-! The `NInventory` (from the DM analysis of n heads, @cite{kramer-2015}) and
the `GenderProfile` (from WALS typology, @cite{corbett-2013}) describe the
same languages from different theoretical perspectives. The key bridge:
the `NInventory.surfaceGenders` count should match `GenderProfile.rawGenderCount`
for the same language. -/

/-- Spanish: the DM n-inventory predicts the same number of surface genders
    as the WALS typological profile. -/
theorem spanish_ninventory_matches_profile :
    spanishNs.surfaceGenders = spanish.rawGenderCount := rfl

/-- Spanish surface genders are consistent with the WALS gender count bin. -/
theorem spanish_surface_genders_consistent :
    Phenomena.Gender.Typology.GenderCount.two.contains spanishNs.surfaceGenders = true := rfl

/-- For Spanish, the n-inventory has 4 structural heads mapping to 2 surface
    genders — a many-to-one mapping mediated by VI (@cite{kramer-2015} Ch 6).
    This is the central insight: structural richness (4 n types) does not
    imply surface richness (only 2 genders). -/
theorem spanish_structural_vs_surface :
    spanishNs.nHeads.length > spanishNs.surfaceGenders := by decide

/-- NInventory ↔ AssignmentSystem bridge: having arbitrary (u) features
    in the n-inventory corresponds to `semanticAndFormal` assignment in
    the WALS typology. 3-n languages with no u-features are `semanticOnly`.
    (@cite{kramer-2020} §2.3; @cite{corbett-2013} Ch 32) -/
theorem spanish_assignment_consistent :
    spanishNs.hasArbitraryGender = true ∧
    spanish.assignment = .semanticAndFormal := ⟨rfl, rfl⟩

-- ============================================================================
-- § 12: Default Gender Derivation (@cite{kramer-2015} §6.2)
-- ============================================================================

/-! In Set 1 languages (Spanish, Amharic), masculine is the DEFAULT gender:
nouns with plain n (no gender feature) surface as masculine. The derivation:

  1. The root combines with plain n (no gender feature on n).
  2. At PF, Vocabulary Insertion looks for a matching exponent.
  3. The [+FEM] exponent requires [+FEM] on n — it does NOT match.
  4. The elsewhere/default exponent (masculine) is inserted.

In Set 2 languages (Maa, Wari'), the same logic yields feminine as default:
  1. The root combines with plain n (no gender feature on n).
  2. The [−FEM] exponent requires [−FEM] on n — it does NOT match.
  3. The elsewhere/default exponent (feminine) is inserted.

The polarity of the u-feature determines which gender is arbitrary vs default. -/

open Core (SurfaceGender)

-- Set 1 (Spanish) derivation chain — uses DM bridge (CatHead.surfaceGenderSet1)

/-- Plain n → masculine (the default). -/
theorem set1_plain_n_masculine :
    CatHead.n_plain.surfaceGenderSet1 = .masculine := rfl

/-- i[+FEM] → feminine (natural female). -/
theorem set1_iFem_feminine :
    CatHead.n_iFem.surfaceGenderSet1 = .feminine := rfl

/-- i[−FEM] → masculine (natural male). -/
theorem set1_iMasc_masculine :
    CatHead.n_iMasc.surfaceGenderSet1 = .masculine := rfl

/-- u[+FEM] → feminine (arbitrary feminine). -/
theorem set1_uFem_feminine :
    CatHead.n_uFem.surfaceGenderSet1 = .feminine := rfl

-- Set 2 (Maa) derivation chain — uses DM bridge (CatHead.surfaceGenderSet2)

/-- Plain n → feminine (the default in Set 2). -/
theorem set2_plain_n_feminine :
    CatHead.n_plain.surfaceGenderSet2 = .feminine := rfl

/-- u[−FEM] → masculine (arbitrary masculine in Set 2). -/
theorem set2_uNegFem_masculine :
    CatHead.n_uNegFem.surfaceGenderSet2 = .masculine := rfl

/-- i[−FEM] → masculine (natural male, same in both sets). -/
theorem set2_iMasc_masculine :
    CatHead.n_iMasc.surfaceGenderSet2 = .masculine := rfl

/-- i[+FEM] → feminine (natural female, same in both sets). -/
theorem set2_iFem_feminine :
    CatHead.n_iFem.surfaceGenderSet2 = .feminine := rfl

/-- Verify the full derivation chain for Spanish fragment nouns:
    the surface gender computed from each noun's CatHead matches
    the expected gender assignment. -/
theorem spanish_derivation_chain :
    Fragments.Spanish.Gender.mujer.nHead.surfaceGenderSet1 = .feminine ∧
    Fragments.Spanish.Gender.hombre.nHead.surfaceGenderSet1 = .masculine ∧
    Fragments.Spanish.Gender.mesa.nHead.surfaceGenderSet1 = .feminine ∧
    Fragments.Spanish.Gender.libro.nHead.surfaceGenderSet1 = .masculine ∧
    Fragments.Spanish.Gender.persona.nHead.surfaceGenderSet1 = .feminine ∧
    Fragments.Spanish.Gender.ángel.nHead.surfaceGenderSet1 = .masculine :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fixed-gender nouns: *persona* surfaces as feminine despite denoting
    persons of any sex; *ángel* surfaces as masculine. The derivation
    chain correctly predicts this from their n heads. -/
theorem fixed_gender_from_n_head :
    Fragments.Spanish.Gender.persona.nHead.surfaceGenderSet1 = .feminine ∧
    Fragments.Spanish.Gender.ángel.nHead.surfaceGenderSet1 = .masculine := ⟨rfl, rfl⟩

-- ============================================================================
-- § 13: Russian Gender (@cite{kramer-2020} §2.3.2, §3.3.2)
-- ============================================================================

/-! Russian is a 5-n language with 3 surface genders — the same inventory
as Lavukaleve, supporting @cite{kramer-2015}'s prediction that n-inventory
size and surface gender count are independent (mediated by VI). -/

def russianNs : NInventory :=
  ⟨"Russian", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
               CatHead.n_uFem, CatHead.n_uNegFem], 3⟩

/-- Russian and Lavukaleve share the same n-inventory (5 heads). -/
theorem russian_lavukaleve_same_ns :
    russianNs.nHeads = lavukaleveNs.nHeads := rfl

/-- Both have 3 surface genders despite the 5-n inventory. -/
theorem russian_lavukaleve_same_surface :
    russianNs.surfaceGenders = lavukaleveNs.surfaceGenders := rfl

/-- Russian has 5 structural heads mapping to 3 surface genders. -/
theorem russian_structural_vs_surface :
    russianNs.nHeads.length > russianNs.surfaceGenders := by decide

/-- Russian: the DM n-inventory predicts the same number of surface genders
    as the WALS typological profile. -/
theorem russian_ninventory_matches_profile :
    russianNs.surfaceGenders = russian.rawGenderCount := rfl

/-- Russian n-inventory matches the WALS gender count bin. -/
theorem russian_surface_genders_consistent :
    Phenomena.Gender.Typology.GenderCount.three.contains
      russianNs.surfaceGenders = true := rfl

/-- Russian has u-features → `semanticAndFormal` assignment, consistent
    with the WALS profile. -/
theorem russian_assignment_consistent :
    russianNs.hasArbitraryGender = true ∧
    russian.assignment = .semanticAndFormal := ⟨rfl, rfl⟩

-- Bridge: Russian fragment nouns ↔ DM study types

/-- Fragment-derived: *vrač* has morphological masculine (u[−FEM]). -/
theorem vrač_morph_masculine :
    Fragments.Russian.Gender.vrač.nHead.phi.gender =
      some ⟨.u, ⟨.fem, .neg⟩⟩ := rfl

/-- *vrač* is a hybrid noun: its morphological gender (u[−FEM] = masculine)
    differs from the semantic gender triggered by a female referent ([+FEM]).
    This matches the `russianVrac` definition from §7. -/
theorem vrač_matches_hybrid :
    russianVrac.morphGender = ⟨.fem, .neg⟩ ∧
    Fragments.Russian.Gender.vrač.nHead.phi.gender =
      some ⟨.u, russianVrac.morphGender⟩ := ⟨rfl, rfl⟩

/-- Fragment-derived: *zakon* (Class I) surfaces as masculine. -/
theorem zakon_fragment_masculine :
    Fragments.Russian.Gender.surfaceGender
      Fragments.Russian.Gender.zakon.nHead = .masculine := rfl

/-- Fragment-derived: *vino* (default) surfaces as neuter. -/
theorem vino_fragment_neuter :
    Fragments.Russian.Gender.surfaceGender
      Fragments.Russian.Gender.vino.nHead = .neuter := rfl

/-- Fragment-derived: Russian has all 5 n-types in its lexicon. -/
theorem russian_fragment_covers_inventory :
    Fragments.Russian.Gender.allNouns.any (·.nHead == CatHead.n_iFem) = true ∧
    Fragments.Russian.Gender.allNouns.any (·.nHead == CatHead.n_iMasc) = true ∧
    Fragments.Russian.Gender.allNouns.any (·.nHead == CatHead.n_uFem) = true ∧
    Fragments.Russian.Gender.allNouns.any (·.nHead == CatHead.n_uNegFem) = true ∧
    Fragments.Russian.Gender.allNouns.any (·.nHead == CatHead.n_plain) = true :=
  Fragments.Russian.Gender.five_n_types_covered

-- ============================================================================
-- § 14: VI-Derived Surface Gender Count
-- ============================================================================

/-! The `NInventory.surfaceGenders` field is currently stipulated. Here we
derive the surface gender count from VI rules applied to each n-head,
verifying that the computed count matches the stipulated count.

The key VI patterns from @cite{kramer-2015}:
- **Set 1** (Spanish, Amharic): [+FEM] → feminine, else → masculine (2)
- **Set 2** (Maa): [−FEM] → masculine, else → feminine (2)
- **3-gender** (Russian, Mangarayi, Lavukaleve): [+FEM] → fem,
  [−FEM] → masc, no feature → neuter (3)
-/

/-- A VI gender-class assignment: maps each n-head to a surface gender
    class (encoded as Nat). Two n-heads yielding the same Nat surface
    as the same gender. -/
def NInventory.computeSurfaceGenders (inv : NInventory)
    (viMap : CatHead → Nat) : Nat :=
  (inv.nHeads.map viMap).eraseDups.length

/-- Set 1 VI: [+FEM] → 0 (feminine), everything else → 1 (masculine). -/
def viSet1 (ch : CatHead) : Nat :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then 0 else 1
  | none    => 1

/-- Set 2 VI: [−FEM] → 1 (masculine), everything else → 0 (feminine). -/
def viSet2 (ch : CatHead) : Nat :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .neg⟩ then 1 else 0
  | none    => 0

/-- 3-gender VI: [+FEM] → 0, [−FEM] → 1, no feature → 2. -/
def viThreeGender (ch : CatHead) : Nat :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then 0 else 1
  | none    => 2

-- Set 1 verification
theorem spanish_vi_derived :
    spanishNs.computeSurfaceGenders viSet1 = spanishNs.surfaceGenders := by native_decide

theorem amharic_vi_derived :
    amharicNs.computeSurfaceGenders viSet1 = amharicNs.surfaceGenders := by native_decide

-- Set 2 verification
theorem maa_vi_derived :
    maaNs.computeSurfaceGenders viSet2 = maaNs.surfaceGenders := by native_decide

-- 3-gender verification
theorem russian_vi_derived :
    russianNs.computeSurfaceGenders viThreeGender = russianNs.surfaceGenders := by native_decide

theorem mangarayi_vi_derived :
    mangarayiNs.computeSurfaceGenders viThreeGender =
      mangarayiNs.surfaceGenders := by native_decide

theorem lavukaleve_vi_derived :
    lavukaleveNs.computeSurfaceGenders viThreeGender =
      lavukaleveNs.surfaceGenders := by native_decide

/-- Dieri: same 3-n inventory as Mangarayi but 2 surface genders under
    Set 1 VI (where plain n → masculine, not neuter). -/
theorem dieri_vi_derived :
    dieriNs.computeSurfaceGenders viSet1 = dieriNs.surfaceGenders := by native_decide

/-- The Dieri vs Mangarayi contrast: same n-heads, different VI → different
    surface gender counts. This is now DERIVED, not stipulated. -/
theorem dieri_mangarayi_vi_contrast :
    dieriNs.nHeads = mangarayiNs.nHeads ∧
    dieriNs.computeSurfaceGenders viSet1 ≠
      mangarayiNs.computeSurfaceGenders viThreeGender := ⟨rfl, by native_decide⟩

end Phenomena.Gender.Studies.Kramer2020
