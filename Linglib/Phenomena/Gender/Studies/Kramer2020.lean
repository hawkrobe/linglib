import Linglib.Phenomena.Gender.Typology
import Linglib.Theories.Morphology.DM.Categorizer

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
   recycled vs novel gender.

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

The mapping is partial because `SemanticBasis.shape` and `.rationality` have
no standard DM feature dimension (no [±SHAPE] or [±RATIONAL] in the literature).
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
    when one exists. (@cite{kramer-2020} §3) -/
def SemanticBasis.toGenderDimension : SemanticBasis → Option GenderDimension
  | .sex         => some .fem   -- default: feminine as marked value
  | .animacy     => some .anim
  | .humanness   => some .anim  -- human/nonhuman ⊂ animate/inanimate
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

/-- How remainder nouns (those not assigned gender by the semantic core)
    are distributed across genders (@cite{kramer-2020} Table 2).

    Two independent parameters:
    1. Are all remainder nouns in the same gender, or spread across genders?
    2. Is the remainder gender recycled from a semantically-assigned gender,
       or is it a novel gender not used for the semantic core? -/
structure RemainderPattern where
  /-- Are all remainder nouns assigned to a single gender? -/
  sameGender : Bool
  /-- Is the remainder gender recycled from a semantic-core gender? -/
  recycled : Bool
  deriving DecidableEq, BEq, Repr

/-- Dieri (Pama-Nyungan): all remainder nouns are masculine (= same gender
    used for male humans). One gender, recycled. (@cite{kramer-2020} Table 2) -/
def dieri : RemainderPattern := ⟨true, true⟩

/-- Tamil (Dravidian): remainder nouns go to neuter — a novel gender not
    used for the male/female semantic core.
    (@cite{kramer-2020} Table 2; Asher 1982) -/
def tamil : RemainderPattern := ⟨true, false⟩

/-- Spanish: remainder nouns are split arbitrarily across masculine and
    feminine — both recycled genders. (@cite{kramer-2020} Table 1, Table 2;
    @cite{harris-1991}) -/
def spanishRemainder : RemainderPattern := ⟨false, true⟩

/-- Akɔɔse (Niger-Congo: Bantu): remainder nouns spread across at least
    7 noun classes — novel genders. (@cite{kramer-2020} Table 2;
    Hedinger 2008) -/
def akoose : RemainderPattern := ⟨false, false⟩

/-- All four cells of Table 2 are attested. -/
theorem table2_all_cells :
    dieri ≠ tamil ∧ dieri ≠ spanishRemainder ∧ dieri ≠ akoose ∧
    tamil ≠ spanishRemainder ∧ tamil ≠ akoose ∧
    spanishRemainder ≠ akoose := by decide

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
    feature in a specified context. (@cite{harris-1991}) -/
structure LexicalGenderRule where
  /-- Semantic trigger (e.g. "FEMALE", "ANIMATE") -/
  semanticFeature : String
  /-- Grammatical gender feature assigned (e.g. "F") -/
  genderFeature : String
  /-- Context restriction (e.g. "HUMAN") -/
  context : String
  deriving DecidableEq, BEq, Repr

/-- Harris's Human Gender rule for Spanish:
    [FEMALE] → [F] / __ [HUMAN]
    (@cite{harris-1991}; @cite{kramer-2020} ex. 23) -/
def harrisHumanGenderRule : LexicalGenderRule :=
  ⟨"FEMALE", "F", "HUMAN"⟩

/-- A gender assignment approach, abstractly characterized by what
    phenomena it can and cannot handle. -/
structure ApproachCapabilities where
  /-- Can the approach handle phonological gender assignment? -/
  phonologicalAssignment : Bool
  /-- Can a single entry trigger both masculine and feminine agreement? -/
  hybridAgreement : Bool
  /-- Does the approach predict the Semantic Core? -/
  predictsSemanticCore : Bool
  deriving DecidableEq, BEq, Repr

/-- The lexical approach (@cite{harris-1991}).

    - **Phonological assignment**: yes (lexical rules can reference phonology)
    - **Hybrid agreement**: no — a lexical entry has one gender feature;
      a single entry cannot be both [M] and [F] (@cite{kramer-2020} §3.3.2)
    - **Semantic Core**: not predicted — nothing prevents a language from
      having only arbitrary gender rules without any semantic connection
      (@cite{kramer-2020} §3.3.3) -/
def lexicalApproach : ApproachCapabilities :=
  ⟨true, false, false⟩

/-- The structural approach (@cite{kramer-2015}).

    - **Phonological assignment**: no — syntax cannot see phonology, so gender
      cannot be assigned by phonological rule. Apparent cases (e.g. Hausa -ā)
      are reanalyzed as morphophonological *realization* of a gender feature
      on *n* (@cite{kramer-2020} §3.3.1)
    - **Hybrid agreement**: yes — a root can combine with different *n* heads
      bearing different features, or a social-gender projection can override
      the morphosyntactic gender (@cite{kramer-2020} §3.3.2)
    - **Semantic Core**: yes — via the Thesis of Radical Interpretability:
      if a language has gender features, at least some must be interpretable,
      which forces semantic assignment for at least some nouns
      (@cite{kramer-2020} §3.3.3) -/
def structuralApproach : ApproachCapabilities :=
  ⟨false, true, true⟩

/-- The approaches differ on all three diagnostic phenomena. -/
theorem approaches_differ :
    lexicalApproach.phonologicalAssignment ≠ structuralApproach.phonologicalAssignment ∧
    lexicalApproach.hybridAgreement ≠ structuralApproach.hybridAgreement ∧
    lexicalApproach.predictsSemanticCore ≠ structuralApproach.predictsSemanticCore := by
  decide

/-- The structural approach handles 2 out of 3 diagnostic phenomena;
    the lexical approach handles 1. This is the basis for
    @cite{kramer-2020}'s conclusion favoring the structural approach. -/
theorem structural_advantage :
    let s := structuralApproach
    let l := lexicalApproach
    (s.hybridAgreement.toNat + s.predictsSemanticCore.toNat) >
    (l.hybridAgreement.toNat + l.predictsSemanticCore.toNat) := by
  native_decide

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

-- ============================================================================
-- § 6: Referent-Based Gender Assignment (@cite{kramer-2020} §2.2.3)
-- ============================================================================

/-- Same-root nominals: nouns that can be assigned different grammatical
    genders depending on the social gender of their referent.
    (@cite{kramer-2020} §2.2.3; @cite{corbett-1991})

    Examples: Russian *vrač* 'doctor', Spanish *juez* 'judge',
    Greek *odigós* 'driver', Amharic *hakim* 'doctor'. -/
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

end Phenomena.Gender.Studies.Kramer2020
