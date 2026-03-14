import Linglib.Phenomena.Gender.Typology
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Fragments.Spanish.Gender

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

/-- The three minimal semantic properties for gender assignment
    (@cite{kramer-2020} ex. 3). Every language with gender uses at least
    one to assign gender to some nouns. -/
inductive SemanticCoreProperty where
  | animacy       -- animate vs inanimate (e.g. Sochiapan Chinantec)
  | humanness     -- human vs nonhuman (e.g. Akɔɔse)
  | socialGender  -- social gender for humans / biological sex for animals
                   -- (e.g. Amharic, Spanish)
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

/-- A gender assignment approach, characterized by how it handles
    each of the three diagnostic phenomena from §3.3. -/
structure ApproachCapabilities where
  /-- §3.3.1: phonological gender assignment -/
  phonologicalAssignment : DiagnosticStatus
  /-- §3.3.2: hybrid nouns (simultaneous dual agreement) -/
  hybridAgreement : DiagnosticStatus
  /-- §3.3.3: the Semantic Core Generalization -/
  predictsSemanticCore : DiagnosticStatus
  deriving DecidableEq, BEq, Repr

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

/-- Agreement gender triggered on a specific target type. -/
structure AgreementGender where
  /-- The agreement target (attributive, predicate, etc.) -/
  target : AgreementTarget
  /-- The gender triggered on this target -/
  gender : GenderDimension
  /-- Polarity of the gender feature -/
  polarity : Polarity
  deriving DecidableEq, BEq, Repr

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

/-- Whether a hybrid noun shows mixed agreement: morphosyntactic gender on
    some targets, semantic gender on others. -/
def HybridNoun.showsMixedAgreement (hn : HybridNoun) : Bool :=
  hn.morphGender ≠ hn.semGender

/-- Russian *vrač* 'doctor': morphologically masculine (from n), but
    can trigger feminine agreement when referring to a female doctor.
    (@cite{kramer-2020} ex. 15-16/27; @cite{corbett-1991}) -/
def russianVrac : HybridNoun :=
  { form := "vrač"
    language := "Russian"
    morphGender := ⟨.fem, .neg⟩  -- [−FEM] = morphological masculine
    semGender := ⟨.fem, .pos⟩    -- [+FEM] = semantic feminine (female referent)
    distinct := by decide }

/-- Hybrid nouns have distinct morphological and semantic genders. -/
theorem vrac_mixed_agreement : russianVrac.showsMixedAgreement = true := rfl

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

def zayseNs : NInventory :=
  ⟨"Zayse", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain], 2⟩

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

-- 4-n languages with 3 surface genders

def lealaoNs : NInventory :=
  ⟨"Lealao Chinantec", [CatHead.n_iAnim, CatHead.n_iInanim,
                         CatHead.n_plain, CatHead.n_uAnim], 3⟩

def wariNs : NInventory :=
  ⟨"Wari'", [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain,
             CatHead.n_uNegFem], 3⟩

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

/-- 3-n languages have purely semantic gender (no u-features). -/
theorem dieri_purely_semantic :
    dieriNs.purelySemanticGender = true := rfl

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

/-- Spanish *soldado* 'soldier' as a same-root nominal:
    the root √SOLDAD can combine with i[+FEM] or i[−FEM]. -/
theorem soldado_is_same_root :
    Fragments.Spanish.Gender.soldado.mascHead ≠
    Fragments.Spanish.Gender.soldado.femHead := by decide

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

end Phenomena.Gender.Studies.Kramer2020
