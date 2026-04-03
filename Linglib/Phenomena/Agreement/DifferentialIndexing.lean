import Linglib.Core.Prominence

/-!
# Differential Indexing Typology @cite{just-2024}
@cite{aissen-2003} @cite{haspelmath-2019} @cite{siewierska-2004} @cite{harris-1981} @cite{laka-1996} @cite{haspelmath-2021}

Formalizes the typological survey from:

- Just, E. (2024). A structural and functional comparison of differential A
  and P indexing. Linguistics 62(2): 295–321.

## Key Distinction: Flagging vs. Indexing (@cite{haspelmath-2019}, Just §2)

**Flagging** = case morphology on the NP (e.g., accusative suffix).
**Indexing** = verbal agreement / cross-referencing (e.g., Bantu object markers).

These serve different functions:
- Flagging: disambiguate thematic roles (who did what to whom)
- Indexing: track prominent referents through discourse

Both channels are governed by the same prominence scales (person, animacy,
definiteness) but because they serve different functions, the patterns are
not redundant.

## Core Claim: Same Scales, Opposite Polarity

The same referential properties condition both differential P and A
indexing. The directions form a **mirror
image** (§4.2, p. 311):

- P indexing targets **prominent** Ps (high person, animacy, definiteness)
- A indexing targets **non-prominent** As (low person, animacy, definiteness)

This follows from the unified functional principle (§6, p. 315):
*prominent arguments tend to be indexed more readily, regardless of role*.
A arguments are prominent by default; P arguments are not. Differential
marking targets departures from these defaults.

-/

namespace Phenomena.Agreement.DifferentialIndexing

open Core.Prominence

-- ============================================================================
-- § 1: Person Prominence Scale
-- ============================================================================

/-- Person prominence for differential indexing.

    The person scale for indexing is a **binary** split between speech act
    participants (SAP: 1st/2nd person) and non-participants (3rd person).
    This mirrors @cite{preminger-2014}'s [±participant] feature decomposition.

    This is coarser than `Core.Prominence.PersonLevel` (1st > 2nd > 3rd),
    which is needed for scenario splits. The binary split suffices for
    indexing because indexing does not distinguish 1st from 2nd. -/
inductive IndexingPersonLevel where
  /-- Speech act participants: 1st and 2nd person -/
  | sap
  /-- Non-participants: 3rd person -/
  | third
  deriving DecidableEq, Repr, Inhabited

/-- Rank on the indexing person scale: SAP (1) > 3rd (0). -/
def IndexingPersonLevel.rank : IndexingPersonLevel → Nat
  | .sap   => 1
  | .third => 0

/-- All indexing person levels. -/
def IndexingPersonLevel.all : List IndexingPersonLevel := [.sap, .third]

theorem person_sap_gt_third : IndexingPersonLevel.sap.rank > IndexingPersonLevel.third.rank := by decide

-- ============================================================================
-- § 2: Indexing Fragment
-- ============================================================================

/-- A differential indexing fragment for a single language.

    Extends `DifferentialMarkingProfile` with language metadata and
    per-dimension marking predicates. The 2D `marks` predicate is computed
    from `animacyIndexed` and `definitenessIndexed` by the `mk'` constructor,
    and the channel is always `.indexing`.

    For P indexing: `true` at a level means "P arguments at this level
    ARE indexed." The expectation (Just §4.2) is that P indexing targets
    the prominent end of each scale.

    For A indexing: `true` at a level means "A arguments at this level
    ARE indexed." The expectation is that A indexing targets the
    non-prominent end. -/
structure IndexingFragment extends DifferentialMarkingProfile where
  /-- ISO 639-3 code -/
  iso639 : String
  /-- Language family -/
  family : String
  /-- Which person levels trigger indexing -/
  personIndexed : IndexingPersonLevel → Bool
  /-- Which animacy levels trigger indexing -/
  animacyIndexed : AnimacyLevel → Bool
  /-- Which definiteness levels trigger indexing -/
  definitenessIndexed : DefinitenessLevel → Bool

/-- Smart constructor for `IndexingFragment`.
    Computes the 2D `marks` predicate as the product of
    `animacyIndexed` and `definitenessIndexed`, and sets `channel :=.indexing`. -/
def IndexingFragment.mk' (name iso639 family : String) (role : ArgumentRole)
    (personIndexed : IndexingPersonLevel → Bool)
    (animacyIndexed : AnimacyLevel → Bool)
    (definitenessIndexed : DefinitenessLevel → Bool) : IndexingFragment :=
  { name, iso639, family, role, channel := .indexing
    marks := λ a d => animacyIndexed a && definitenessIndexed d
    personIndexed, animacyIndexed, definitenessIndexed }

-- ============================================================================
-- § 3: Derived Conditioning Factors
-- ============================================================================

/-- A dimension is **conditioning** if the marking predicate is non-uniform:
    some levels are indexed and some are not. -/
def IndexingFragment.personConditioned (f : IndexingFragment) : Bool :=
  IndexingPersonLevel.all.any f.personIndexed && !(IndexingPersonLevel.all.all f.personIndexed)

def IndexingFragment.animacyConditioned (f : IndexingFragment) : Bool :=
  AnimacyLevel.all.any f.animacyIndexed && !(AnimacyLevel.all.all f.animacyIndexed)

def IndexingFragment.definitenessConditioned (f : IndexingFragment) : Bool :=
  DefinitenessLevel.all.any f.definitenessIndexed &&
    !(DefinitenessLevel.all.all f.definitenessIndexed)

/-- At least one dimension conditions the indexing (i.e., is non-uniform). -/
def IndexingFragment.isDifferential (f : IndexingFragment) : Bool :=
  f.personConditioned || f.animacyConditioned || f.definitenessConditioned

-- ============================================================================
-- § 4: Polarity — Which End of the Scale Is Indexed?
-- ============================================================================

/-- P indexing has correct polarity if it targets the PROMINENT end:
    SAP over 3rd, human over inanimate, definite over nonspecific. -/
def IndexingFragment.pPolarityCorrect (f : IndexingFragment) : Bool :=
  (if f.personConditioned then
    f.personIndexed .sap && !f.personIndexed .third else true) &&
  (if f.animacyConditioned then
    f.animacyIndexed .human && !f.animacyIndexed .inanimate else true) &&
  (if f.definitenessConditioned then
    f.definitenessIndexed .personalPronoun && !f.definitenessIndexed .nonSpecific else true)

/-- A indexing has correct polarity if it targets the NON-PROMINENT end:
    3rd over SAP, inanimate over human, nonspecific over definite. -/
def IndexingFragment.aPolarityCorrect (f : IndexingFragment) : Bool :=
  (if f.personConditioned then
    f.personIndexed .third && !f.personIndexed .sap else true) &&
  (if f.animacyConditioned then
    f.animacyIndexed .inanimate && !f.animacyIndexed .human else true) &&
  (if f.definitenessConditioned then
    f.definitenessIndexed .nonSpecific && !f.definitenessIndexed .personalPronoun else true)

/-- Role-appropriate polarity check. T behaves like P (targets prominent),
    R behaves like A (targets non-prominent). S is vacuously correct. -/
def IndexingFragment.polarityCorrect (f : IndexingFragment) : Bool :=
  match f.role with
  | .P => f.pPolarityCorrect
  | .T => f.pPolarityCorrect  -- T indexes like P (@cite{haspelmath-2021})
  | .A => f.aPolarityCorrect
  | .R => f.aPolarityCorrect  -- R indexes like A (@cite{haspelmath-2021})
  | .S => true                -- S is the reference point

-- ============================================================================
-- § 5: Differential P Indexing Fragments (@cite{just-2024}, Table 1)
-- ============================================================================

/-! Languages where the P argument is differentially indexed. Prominent Ps
    (SAP, human, definite) are MORE likely to be indexed.

    Marking predicates encode the actual pattern per scale. For scales that
    are not conditioning, the predicate is uniformly `true` (all levels
    indexed). For conditioning scales, the predicate marks the prominent
    end as `true` and the non-prominent end as `false`.

    Source references are from @cite{just-2024}. -/

section PIndexing

/-- Abkhaz (NW Caucasian): P indexed only for SAP. -/
def abkhaz : IndexingFragment := .mk'
  "Abkhaz" "abk" "Northwest Caucasian" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Amharic (Semitic): P indexed for SAP and definite objects. -/
def amharic : IndexingFragment := .mk'
  "Amharic" "amh" "Semitic" .P
  (λ | .sap => true | .third => false)
  (λ _ => true)
  (λ | .personalPronoun | .properName | .definite => true
     | .indefiniteSpecific | .nonSpecific => false)

/-- Basque (Isolate): object agreement only for SAP objects. -/
def basque : IndexingFragment := .mk'
  "Basque" "eus" "Isolate" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Georgian (Kartvelian): P agreement conditioned by person — indirect
    objects (dative) are indexed for SAP only. -/
def georgian : IndexingFragment := .mk'
  "Georgian" "kat" "Kartvelian" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Hungarian (Uralic): definite conjugation triggered by definite objects;
    indefinite conjugation for indefinite objects.
    See also `Fragments.Hungarian.Predicates` for the conjugation split. -/
def hungarian : IndexingFragment := .mk'
  "Hungarian" "hun" "Uralic" .P
  (λ _ => true) (λ _ => true)
  (λ | .personalPronoun | .properName | .definite => true
     | .indefiniteSpecific | .nonSpecific => false)

/-- Kagulu (Bantu): object marker for animate+ objects. -/
def kagulu : IndexingFragment := .mk'
  "Kagulu" "kki" "Bantu" .P
  (λ _ => true)
  (λ | .human | .animate => true | .inanimate => false)
  (λ _ => true)

/-- KiNzadi (Bantu): P indexed for SAP only. -/
def kinzadi : IndexingFragment := .mk'
  "KiNzadi" "nzd" "Bantu" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Koorete (Omotic): P indexed for SAP only. -/
def koorete : IndexingFragment := .mk'
  "Koorete" "kqy" "Omotic" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Maltese (Semitic): definite object agreement — verb agrees with definite
    objects via suffixed object markers (Just & Čéplö 2022). -/
def maltese : IndexingFragment := .mk'
  "Maltese" "mlt" "Semitic" .P
  (λ _ => true) (λ _ => true)
  (λ | .personalPronoun | .properName | .definite => true
     | .indefiniteSpecific | .nonSpecific => false)

/-- Nkore-Kiga (Bantu): object marker for SAP objects. -/
def nkoreKiga : IndexingFragment := .mk'
  "Nkore-Kiga" "nyn" "Bantu" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Romanian (Romance): clitic doubling conditioned by person, animacy, and
    definiteness. SAP + human + definite = doubled. -/
def romanian : IndexingFragment := .mk'
  "Romanian" "ron" "Romance" .P
  (λ | .sap => true | .third => false)
  (λ | .human => true | .animate | .inanimate => false)
  (λ | .personalPronoun | .properName | .definite => true
     | .indefiniteSpecific | .nonSpecific => false)

/-- Somali (Cushitic): P indexed for SAP — full paradigm for SAP objects,
    reduced for 3rd person. Focus/topicality also plays a role
    but is not captured in the prominence grid. -/
def somali : IndexingFragment := .mk'
  "Somali" "som" "Cushitic" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Swahili (Bantu): object marker obligatory for human objects, optional/
    absent for non-human. -/
def swahili : IndexingFragment := .mk'
  "Swahili" "swh" "Bantu" .P
  (λ _ => true)
  (λ | .human => true | .animate | .inanimate => false)
  (λ _ => true)

/-- Teiwa (Trans-New Guinea): P indexed for animate objects. -/
def teiwa : IndexingFragment := .mk'
  "Teiwa" "twe" "Trans-New Guinea" .P
  (λ _ => true)
  (λ | .human | .animate => true | .inanimate => false)
  (λ _ => true)

/-- Welsh (Celtic): synthetic agreement only with pronominal (SAP) objects;
    analytic (no agreement) with 3rd person full NPs. -/
def welsh : IndexingFragment := .mk'
  "Welsh" "cym" "Celtic" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

/-- Zulu (Bantu): object marker for animate objects. -/
def zulu : IndexingFragment := .mk'
  "Zulu" "zul" "Bantu" .P
  (λ _ => true)
  (λ | .human | .animate => true | .inanimate => false)
  (λ _ => true)

/-- Spoken Arabic varieties (Semitic): P indexed for SAP only —
    object suffixes restricted to pronominal objects. -/
def spokenArabic : IndexingFragment := .mk'
  "Spoken Arabic" "arb" "Semitic" .P
  (λ | .sap => true | .third => false)
  (λ _ => true) (λ _ => true)

end PIndexing

-- ============================================================================
-- § 6: Differential A Indexing Fragments (@cite{just-2024}, Table 2)
-- ============================================================================

/-! Languages where the A argument is differentially indexed. Non-prominent
    As (3rd person, inanimate, indefinite) are MORE likely to be indexed.
    The polarity is REVERSED relative to P indexing.

    Source references from @cite{just-2024}. -/

section AIndexing

/-- Jamsay (Dogon): A indexed only for 3rd person agents — SAP agents are
    not cross-referenced on the verb. -/
def jamsay : IndexingFragment := .mk'
  "Jamsay" "djm" "Dogon" .A
  (λ | .sap => false | .third => true)
  (λ _ => true) (λ _ => true)

/-- Kharia (Munda): A indexed for 3rd person agents. -/
def kharia : IndexingFragment := .mk'
  "Kharia" "khr" "Austroasiatic (Munda)" .A
  (λ | .sap => false | .third => true)
  (λ _ => true) (λ _ => true)

/-- Mundari (Munda): A indexed for 3rd person agents. -/
def mundari : IndexingFragment := .mk'
  "Mundari" "unr" "Austroasiatic (Munda)" .A
  (λ | .sap => false | .third => true)
  (λ _ => true) (λ _ => true)

/-- Juang (Munda): A indexed for 3rd person agents. -/
def juang : IndexingFragment := .mk'
  "Juang" "jun" "Austroasiatic (Munda)" .A
  (λ | .sap => false | .third => true)
  (λ _ => true) (λ _ => true)

/-- Anywa (Nilotic): A indexed for 3rd person agents only — SAP agents
    are not cross-referenced. -/
def anywa : IndexingFragment := .mk'
  "Anywa" "anu" "Nilotic" .A
  (λ | .sap => false | .third => true)
  (λ _ => true) (λ _ => true)

/-- Reyesano (Tacanan): A indexed for 3rd person and non-human agents. -/
def reyesano : IndexingFragment := .mk'
  "Reyesano" "rey" "Tacanan" .A
  (λ | .sap => false | .third => true)
  (λ | .human => false | .animate | .inanimate => true)
  (λ _ => true)

/-- Eastern Mansi (Uralic): A indexed for indefinite/non-topical agents. -/
def easternMansi : IndexingFragment := .mk'
  "Eastern Mansi" "mns" "Uralic" .A
  (λ _ => true) (λ _ => true)
  (λ | .personalPronoun | .properName | .definite => false
     | .indefiniteSpecific | .nonSpecific => true)

end AIndexing

-- ============================================================================
-- § 7: Profile Collections
-- ============================================================================

/-- All differential P indexing languages in the sample. -/
def pIndexingLanguages : List IndexingFragment :=
  [ abkhaz, amharic, basque, georgian, hungarian, kagulu, kinzadi
  , koorete, maltese, nkoreKiga, romanian, somali, swahili, teiwa
  , welsh, zulu, spokenArabic ]

/-- All differential A indexing languages in the sample. -/
def aIndexingLanguages : List IndexingFragment :=
  [ jamsay, kharia, mundari, juang, anywa, reyesano, easternMansi ]

/-- All differential indexing languages. -/
def allIndexingLanguages : List IndexingFragment :=
  pIndexingLanguages ++ aIndexingLanguages

-- ============================================================================
-- § 8: Consistency Verification
-- ============================================================================

/-- All P indexing languages have role P. -/
theorem pIndexing_all_roleP :
    pIndexingLanguages.all (·.role == .P) = true := by native_decide

/-- All A indexing languages have role A. -/
theorem aIndexing_all_roleA :
    aIndexingLanguages.all (·.role == .A) = true := by native_decide

/-- All profiles are genuinely differential (at least one conditioning
    factor is non-uniform). Derived from the marking predicates. -/
theorem all_differential :
    allIndexingLanguages.all (·.isDifferential) = true := by native_decide

-- ============================================================================
-- § 9: Derived Conditioning Factor Counts
-- ============================================================================

/-! The counts below are COMPUTED from the marking predicates via
    `personConditioned`, `animacyConditioned`, `definitenessConditioned`.
    No hard-coded numbers — if a language's marking predicate changes,
    the counts update automatically. -/

/-- P indexing languages conditioned by person (derived). -/
def pPersonConditioned : List IndexingFragment :=
  pIndexingLanguages.filter (·.personConditioned)

/-- P indexing languages conditioned by animacy (derived). -/
def pAnimacyConditioned : List IndexingFragment :=
  pIndexingLanguages.filter (·.animacyConditioned)

/-- P indexing languages conditioned by definiteness (derived). -/
def pDefinitenessConditioned : List IndexingFragment :=
  pIndexingLanguages.filter (·.definitenessConditioned)

/-- A indexing languages conditioned by person (derived). -/
def aPersonConditioned : List IndexingFragment :=
  aIndexingLanguages.filter (·.personConditioned)

-- ============================================================================
-- § 10: @cite{just-2024} — Person Is the Dominant Conditioning Factor
-- ============================================================================

/-! "The very same referential properties condition both differential P
    and differential A indexing."

    Person is the most frequent conditioning factor for BOTH P and A
    indexing. This is derived from the marking predicates. -/

/-- Person is the most common conditioning factor for P indexing:
    more P-indexing languages are person-conditioned than animacy- or
    definiteness-conditioned. -/
theorem person_dominates_P :
    pPersonConditioned.length > pAnimacyConditioned.length ∧
    pPersonConditioned.length > pDefinitenessConditioned.length := by
  native_decide

/-- Person is the most common conditioning factor for A indexing:
    more A-indexing languages are person-conditioned than animacy- or
    definiteness-conditioned. -/
theorem person_dominates_A :
    aPersonConditioned.length >
      (aIndexingLanguages.filter (·.animacyConditioned)).length ∧
    aPersonConditioned.length >
      (aIndexingLanguages.filter (·.definitenessConditioned)).length := by
  native_decide

-- ============================================================================
-- § 11: @cite{just-2024} — Same Scales Condition Both P and A
-- ============================================================================

/-! "The very same referential properties condition both differential P
    and differential A indexing." -/

/-- Person conditions both P and A indexing. -/
theorem person_conditions_both :
    pIndexingLanguages.any (·.personConditioned) &&
    aIndexingLanguages.any (·.personConditioned) = true := by native_decide

/-- Animacy conditions both P and A indexing. -/
theorem animacy_conditions_both :
    pIndexingLanguages.any (·.animacyConditioned) &&
    aIndexingLanguages.any (·.animacyConditioned) = true := by native_decide

/-- Definiteness conditions both P and A indexing. -/
theorem definiteness_conditions_both :
    pIndexingLanguages.any (·.definitenessConditioned) &&
    aIndexingLanguages.any (·.definitenessConditioned) = true := by native_decide

-- ============================================================================
-- § 12: @cite{just-2024} — Mirror Image / Opposite Polarity
-- ============================================================================

/-! "The directions in which these scales operate form a mirror image:
    indexing targets prominent P arguments on the one hand and non-prominent
    A arguments on the other." -/

/-- All P indexing languages have correct polarity: they target the
    prominent end of each conditioning scale. -/
theorem p_indexing_targets_prominent :
    pIndexingLanguages.all (·.pPolarityCorrect) = true := by native_decide

/-- All A indexing languages have correct polarity: they target the
    non-prominent end of each conditioning scale. -/
theorem a_indexing_targets_nonprominent :
    aIndexingLanguages.all (·.aPolarityCorrect) = true := by native_decide

/-- The mirror image holds universally across the sample: every language
    has role-appropriate polarity. -/
theorem mirror_image_universal :
    allIndexingLanguages.all (·.polarityCorrect) = true := by native_decide

-- ============================================================================
-- § 13: Monotonicity on the Animacy × Definiteness Grid
-- ============================================================================

/-! For languages where animacy and/or definiteness condition indexing,
    we verify monotonicity of the inherited `DifferentialMarkingProfile`
    on the 2D grid. The `marks` predicate is derived from the fragment's
    `animacyIndexed` and `definitenessIndexed` — no separate stipulation. -/

/-- All animacy/definiteness-conditioned profiles are monotone. -/
theorem hungarian_monotone : hungarian.isMonotone = true := by native_decide
theorem swahili_monotone : swahili.isMonotone = true := by native_decide
theorem kagulu_monotone : kagulu.isMonotone = true := by native_decide
theorem easternMansi_monotone : easternMansi.isMonotone = true := by native_decide

/-- Swahili P indexing depends only on animacy (definiteness is irrelevant). -/
theorem swahili_animacy_only : swahili.isAnimacyOnly = true := by native_decide

/-- Kagulu P indexing depends only on animacy. -/
theorem kagulu_animacy_only : kagulu.isAnimacyOnly = true := by native_decide

/-- Hungarian P indexing depends only on definiteness (animacy is irrelevant). -/
theorem hungarian_definiteness_only : hungarian.isDefinitenessOnly = true := by native_decide

/-- Eastern Mansi A indexing depends only on definiteness. -/
theorem easternMansi_definiteness_only : easternMansi.isDefinitenessOnly = true := by native_decide

-- ============================================================================
-- § 14: Family Clustering (@cite{just-2024}, §2.2, §3.1)
-- ============================================================================

/-- Bantu languages in the sample all show P indexing. -/
theorem bantu_all_P :
    allIndexingLanguages.all (λ p =>
      if p.family == "Bantu" then p.role == .P else true) = true := by native_decide

/-- Munda languages in the sample all show A indexing. -/
theorem munda_all_A :
    allIndexingLanguages.all (λ p =>
      if p.family == "Austroasiatic (Munda)" then p.role == .A
      else true) = true := by native_decide

/-- The sample covers at least 10 distinct language families. -/
theorem family_diversity :
    (allIndexingLanguages.map (·.family)).eraseDups.length ≥ 10 := by native_decide

-- ============================================================================
-- § 15: @cite{just-2024} — Unified Principle
-- ============================================================================

/-! "Prominent arguments, be it A or P (or probably any other role), tend
    to be indexed more readily than arguments which are low in
    identifiability, animacy or topicality."

    The mirror image is NOT a coincidence — it follows from a single
    principle (indexing tracks prominent referents) combined with different
    default prominence per role (A defaults high, P defaults low). -/

/-- For every person-conditioned P-indexing language, SAP is indexed
    (= prominent P gets indexed). -/
theorem prominent_P_indexed :
    pPersonConditioned.all (·.personIndexed .sap) = true := by native_decide

/-- For every person-conditioned A-indexing language, 3rd person is indexed
    (= non-prominent A gets indexed, because A's default is prominent). -/
theorem nonprominent_A_indexed :
    aPersonConditioned.all (·.personIndexed .third) = true := by native_decide

/-- The unified principle predicts that the COMPLEMENT of "indexed" differs
    by role: P-indexing excludes 3rd person, A-indexing excludes SAP.
    Both follow from "index the prominent referent" + role defaults. -/
theorem complement_differs_by_role :
    pPersonConditioned.all (λ f => !f.personIndexed .third) = true ∧
    aPersonConditioned.all (λ f => !f.personIndexed .sap) = true := by
  exact ⟨by native_decide, by native_decide⟩

end Phenomena.Agreement.DifferentialIndexing
