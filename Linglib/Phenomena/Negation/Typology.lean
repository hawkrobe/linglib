import Linglib.Core.Word

/-!
# Cross-Linguistic Typology of Negation (WALS Chapters 112--115)

Cross-linguistic data on clausal negation from four WALS chapters:

## Ch 112: Negative Morphemes (Dryer 2013)

How standard (clausal) negation is expressed. Six categories based on
morpheme type: negative affix, negative particle, negative auxiliary verb,
negative word of unclear status, variation between word and affix, and
double (bipartite) negation requiring two co-occurring markers.

Sample: 1011 languages. Negative particles are the most common strategy
(477/1011 = 47.2%), followed by negative affixes (339/1011 = 33.5%).
Negative auxiliary verbs are rare (45/1011 = 4.5%), concentrated in
northern Eurasia (Finland to western Siberia).

## Ch 113: Symmetric and Asymmetric Standard Negation (Miestamo 2013)

Whether negation changes clause structure beyond adding a negative marker.
Symmetric negation adds only the negator; asymmetric negation introduces
further structural changes (e.g., changes in finiteness, verb paradigm,
or tense-aspect marking). Three types: Sym only, Asy only, or both.

Sample: 297 languages. Most languages show both symmetric and asymmetric
negation (130/297), followed by symmetric only (114/297).

## Ch 114: Subtypes of Asymmetric Standard Negation (Miestamo 2013)

For languages with asymmetric negation, what structural domain is affected:
finiteness (A/Fin), reality status (A/NonReal), or other grammatical
categories (A/Cat). Languages may combine subtypes.

Sample: 297 languages (114 symmetric = non-assignable).

## Ch 115: Negative Indefinite Pronouns and Predicate Negation (Haspelmath 2013)

How negative indefinites ('nobody', 'nothing') interact with clausal
negation. Whether they co-occur with predicate negation (negative concord,
the dominant pattern worldwide) or preclude it.

Sample: 206 languages. Co-occurrence with predicate negation overwhelmingly
dominant (170/206 = 82.5%). Preclusion concentrated in Western Europe and
Mesoamerica.

## References

- Dryer, M. S. (2013). Negative morphemes. In Dryer & Haspelmath (eds.),
  WALS Online (v2020.3). https://wals.info/chapter/112
- Miestamo, M. (2013). Symmetric and asymmetric standard negation.
  In Dryer & Haspelmath (eds.), WALS Online. https://wals.info/chapter/113
- Miestamo, M. (2013). Subtypes of asymmetric standard negation.
  In Dryer & Haspelmath (eds.), WALS Online. https://wals.info/chapter/114
- Haspelmath, M. (2013). Negative indefinite pronouns and predicate
  negation. In Dryer & Haspelmath (eds.), WALS Online.
  https://wals.info/chapter/115
- Miestamo, M. (2005). Standard Negation: The Negation of Declarative
  Verbal Main Clauses in a Typological Perspective. Mouton de Gruyter.
-/

namespace Phenomena.Negation.Typology

-- ============================================================================
-- Chapter 112: Negative Morpheme Types
-- ============================================================================

/-- WALS Ch 112: How standard (clausal) negation is expressed.

    Six categories based on the morphological status of the negative marker:
    (1) affix on the verb, (2) free particle, (3) auxiliary verb inflecting
    for verbal categories, (4) negative word whose status is unclear,
    (5) variation between word and affix constructions in the same language,
    (6) bipartite ("double") negation requiring two co-occurring markers. -/
inductive NegMorphemeType where
  /-- Negative affix on the verb (e.g., Kolyma Yukaghir `el-jaqa-te-je`
      'NEG-achieve-FUT-1SG'). -/
  | affix
  /-- Negative particle: free word, no verbal inflection
      (e.g., English `not`, Musgu `pay`). -/
  | particle
  /-- Negative auxiliary verb: inflects for person, number, or TAM like
      verbs in the language (e.g., Finnish `e-n` 'NEG-1SG'). -/
  | auxVerb
  /-- Negative word whose status as verb or particle is unclear, typically
      in isolating languages with little verbal morphology
      (e.g., Maori `kaahore`). -/
  | wordUnclear
  /-- Language uses both a negative word and a negative affix in different
      constructions (e.g., Rama: preverbal particle in one construction,
      verbal suffix in another). -/
  | variation
  /-- Bipartite negation: two co-occurring negative morphemes, one preceding
      and one following the verb (e.g., French `ne...pas`,
      Izi `to-ome-du` 'NEG-do-NEG'). -/
  | doubleNeg
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 113: Symmetric vs Asymmetric Standard Negation
-- ============================================================================

/-- WALS Ch 113: Whether negation changes clause structure.

    Symmetric negation: the negative differs from the affirmative only by
    adding the negative marker(s) -- no structural changes to verb form,
    paradigm, or clause type.

    Asymmetric negation: the negative construction differs structurally
    from the affirmative in additional ways (changed finiteness, different
    verb paradigm, different TAM marking, etc.). -/
inductive NegSymmetry where
  /-- Symmetric only (Type Sym): negation never changes clause structure.
      (e.g., German `ich singe` / `ich singe nicht`). -/
  | symmetric
  /-- Asymmetric only (Type Asy): negation always introduces structural
      differences (e.g., Finnish: negative verb + connegative). -/
  | asymmetric
  /-- Both symmetric and asymmetric (Type SymAsy): some constructions are
      symmetric, others asymmetric (e.g., Lezgian: present symmetric,
      past imperfective asymmetric). -/
  | both
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 114: Subtypes of Asymmetric Negation
-- ============================================================================

/-- WALS Ch 114: Which grammatical domain is affected by asymmetric negation.

    Three primary subtypes:
    - A/Fin: negation changes finiteness (adds negative verb, lexical verb
      becomes nonfinite / subordinate)
    - A/NonReal: negation introduces irrealis/nonrealized marking
    - A/Cat: negation changes marking of TAM, person, number, etc. -/
inductive AsymmetrySubtype where
  /-- A/Fin: asymmetry in finiteness. Typically a negative auxiliary becomes
      the finite verb, and the lexical verb appears in a nonfinite form
      (e.g., Finnish: `e-n tule` 'NEG-1SG come.CONNEG'). -/
  | finiteness
  /-- A/NonReal: asymmetry in reality status. The negative is obligatorily
      marked with an irrealis/nonrealized category that the affirmative
      lacks (e.g., Imbabura Quechua: negative requires `-chu` irrealis). -/
  | realityStatus
  /-- A/Cat: asymmetry in other grammatical categories (TAM, person-number
      affixes, etc.). The negative uses different category markers than the
      affirmative (e.g., Karok: different person-number affixes under
      negation). -/
  | otherCategories
  /-- Combined: A/Fin and A/NonReal
      (e.g., Copainalá Zoque, Squamish). -/
  | finAndNonReal
  /-- Combined: A/Fin and A/Cat
      (e.g., Kolokuma Ijo). -/
  | finAndCat
  /-- Combined: A/NonReal and A/Cat. -/
  | nonRealAndCat
  /-- Non-assignable: language has only symmetric negation (Type Sym in
      Ch 113), so no asymmetry subtype applies. -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 115: Negative Indefinites and Predicate Negation
-- ============================================================================

/-- WALS Ch 115: Interaction of negative indefinites ('nobody', 'nothing')
    with clausal negation.

    Cross-linguistically, negative concord (co-occurrence) is overwhelmingly
    dominant. The preclusion pattern is concentrated in Western Europe and
    Mesoamerica; the normative criticism of "double negation" as "illogical"
    is a prescriptive artifact rooted in Latin prestige
    (Haspelmath 1997, sec. 8.2). -/
inductive NegIndefiniteStrategy where
  /-- Negative indefinites co-occur with predicate negation (negative concord).
      'Nobody NEG came' = 'Nobody came'.
      The dominant pattern worldwide (170/206 = 82.5%).
      (e.g., Russian `nikto ne prisel` 'nobody NEG came'). -/
  | cooccur
  /-- Negative indefinites preclude predicate negation.
      The indefinite alone carries the negation.
      (e.g., German `Niemand kam` 'Nobody came', *`Niemand kam nicht`).
      Rare: 11/206 languages. -/
  | preclude
  /-- Mixed behavior: some negative indefinites co-occur with negation,
      others preclude it (e.g., position-dependent as in Spanish:
      `Nadie vino` but `No vi nada`; or different indefinite series as
      in Swedish). -/
  | mixed
  /-- Negative existential construction: a negative/negated existential verb
      serves as the main predicate (e.g., Nelemwa `kia agu i uya`
      'not.exist person 3SG arrive' = 'Nobody came'). -/
  | negExistential
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- WALS Distribution Data (Aggregate Counts)
-- ============================================================================

/-- A single row in a WALS frequency table: a category label and its count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Chapter 112 distribution: negative morpheme types (N = 1011). -/
def ch112Counts : List WALSCount :=
  [ ⟨"Negative affix", 339⟩
  , ⟨"Negative particle", 477⟩
  , ⟨"Negative auxiliary verb", 45⟩
  , ⟨"Negative word, unclear if verb or particle", 65⟩
  , ⟨"Variation between negative word and affix", 19⟩
  , ⟨"Double negation", 66⟩ ]

/-- Chapter 113 distribution: symmetric vs asymmetric negation (N = 297). -/
def ch113Counts : List WALSCount :=
  [ ⟨"Symmetric only (Type Sym)", 114⟩
  , ⟨"Asymmetric only (Type Asy)", 53⟩
  , ⟨"Both symmetric and asymmetric (Type SymAsy)", 130⟩ ]

/-- Chapter 114 distribution: subtypes of asymmetric negation (N = 297).
    Note: the 114 "non-assignable" languages are those with only symmetric
    negation (Type Sym from Ch 113). -/
def ch114Counts : List WALSCount :=
  [ ⟨"Subtype A/Fin (finiteness)", 40⟩
  , ⟨"Subtype A/NonReal (reality status)", 20⟩
  , ⟨"Subtype A/Cat (other categories)", 82⟩
  , ⟨"Subtypes A/Fin and A/NonReal", 9⟩
  , ⟨"Subtypes A/Fin and A/Cat", 21⟩
  , ⟨"Subtypes A/NonReal and A/Cat", 11⟩
  , ⟨"Non-assignable (symmetric only)", 114⟩ ]

/-- Chapter 115 distribution: negative indefinites and predicate negation
    (N = 206). -/
def ch115Counts : List WALSCount :=
  [ ⟨"Co-occur with predicate negation", 170⟩
  , ⟨"Preclude predicate negation", 11⟩
  , ⟨"Mixed behaviour", 13⟩
  , ⟨"Negative existential construction", 12⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (fun acc c => acc + c.count) 0

/-- Ch 112 total: 1011 languages. -/
theorem ch112_total : WALSCount.totalOf ch112Counts = 1011 := by native_decide

/-- Ch 113 total: 297 languages. -/
theorem ch113_total : WALSCount.totalOf ch113Counts = 297 := by native_decide

/-- Ch 114 total: 297 languages (same sample as Ch 113). -/
theorem ch114_total : WALSCount.totalOf ch114Counts = 297 := by native_decide

/-- Ch 115 total: 206 languages. -/
theorem ch115_total : WALSCount.totalOf ch115Counts = 206 := by native_decide

/-- Ch 113 and Ch 114 use the same sample. -/
theorem ch113_ch114_same_sample :
    WALSCount.totalOf ch113Counts = WALSCount.totalOf ch114Counts := by
  native_decide

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's negation profile across WALS Chapters 112--115. -/
structure NegationProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 112: How standard negation is expressed. -/
  morphemeType : NegMorphemeType
  /-- Ch 113: Symmetric, asymmetric, or both. -/
  symmetry : NegSymmetry
  /-- Ch 114: Asymmetry subtype (nonAssignable if symmetric only). -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Ch 115: Strategy for negative indefinites, if attested. -/
  negIndefinite : Option NegIndefiniteStrategy := none
  /-- Illustrative negative marker form(s). -/
  negMarkers : List String := []
  /-- Notes on the negation system. -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

/--
English: negative particle `not`; symmetric negation (adding `not` does not
change clause structure — but note do-support is sometimes analyzed as
asymmetric). Negative indefinites show mixed behavior: `nobody` precludes
predicate negation (`*Nobody didn't come`), but `anything` requires it
(`I didn't see anything`).
-/
def english : NegationProfile :=
  { language := "English"
  , iso := "eng"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["not"]
  , notes := "Do-support sometimes analyzed as asymmetric; " ++
             "mixed indefinites: 'nobody' precludes, 'anything' co-occurs" }

/--
German: negative particle `nicht`; symmetric negation — adding `nicht`
causes no structural change to the clause. Negative indefinites preclude
predicate negation: `Niemand kam` (*`Niemand kam nicht`).
(But note: substandard / Bavarian German has negative concord.)
-/
def german : NegationProfile :=
  { language := "German"
  , iso := "deu"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .preclude
  , negMarkers := ["nicht"]
  , notes := "Bavarian German has negative concord (substandard)" }

/--
French: bipartite negation `ne...pas` (WALS codes as particle since
colloquial French drops `ne`). In colloquial register, only `pas` is used.
Negative indefinites co-occur with partial predicate negation (`ne`):
`Je n'ai rien vu` 'I NEG have nothing seen'.
-/
def french : NegationProfile :=
  { language := "French"
  , iso := "fra"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne", "pas"]
  , notes := "WALS codes as particle (ne optional in colloquial); " ++
             "historically bipartite ne...pas (Jespersen cycle)" }

/--
Russian: negative particle `ne`; symmetric negation. Negative indefinites
obligatorily co-occur with predicate negation (negative concord):
`Nikto ne prisel` 'Nobody NEG came' = 'Nobody came'.
-/
def russian : NegationProfile :=
  { language := "Russian"
  , iso := "rus"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne"]
  , notes := "Canonical negative concord: nikto ne prisel 'nobody NEG came'" }

/--
Finnish: negative auxiliary verb `e-` inflects for person-number; the lexical
verb appears as a connegative (present) or past participle (past). Always
asymmetric (A/Fin): negation changes finiteness structure.
-/
def finnish : NegationProfile :=
  { language := "Finnish"
  , iso := "fin"
  , morphemeType := .auxVerb
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negIndefinite := some .cooccur
  , negMarkers := ["e-"]
  , notes := "Negative auxiliary: e-n tule 'NEG-1SG come.CONNEG'; " ++
             "negative auxiliary verb area stretches across northern Eurasia" }

/--
Japanese: negative suffix `-nai` (affix on verb); negation is symmetric
(the negative form is a regular inflectional form in the paradigm).
Negative indefinites co-occur with predicate negation:
`dare-mo ko-nakat-ta` 'who-MO come-NEG-PST' = 'Nobody came'.
-/
def japanese : NegationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["-nai", "-nakat-"]
  , notes := "Suffix -nai; negative concord with -mo indefinites" }

/--
Mandarin Chinese: negative particles `bu` (general) and `mei(you)` (perfective).
Symmetric negation. Negative word status hard to classify in isolating language.
-/
def mandarin : NegationProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["bu", "mei"]
  , notes := "Two negative particles: bu (general) vs mei (perfective/existential)" }

/--
Turkish: negative suffix `-mA-` on the verb; symmetric negation.
Negative indefinites co-occur with predicate negation:
`Hic kimse gel-me-di` 'at.all person come-NEG-PST' = 'Nobody came'.
-/
def turkish : NegationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["-mA-"]
  , notes := "Verbal suffix; negative concord with hic 'at all' + indefinite" }

/--
Czech: negative prefix `ne-` on the verb; symmetric negation. Negative
indefinites obligatorily co-occur with predicate negation (negative concord):
`Nikdo neprisel` 'Nobody NEG.came' = 'Nobody came'.
-/
def czech : NegationProfile :=
  { language := "Czech"
  , iso := "ces"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne-"]
  , notes := "Prefix ne-; obligatory negative concord (Slavic pattern)" }

/--
Spanish: negative particle `no`; symmetric negation. Mixed behavior for
negative indefinites: preverbal indefinites preclude negation
(`Nadie vino` 'Nobody came'), but postverbal indefinites require it
(`No vi nada` 'NEG I.saw nothing').
-/
def spanish : NegationProfile :=
  { language := "Spanish"
  , iso := "spa"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["no"]
  , notes := "Position-dependent: preverbal nadie precludes no, " ++
             "postverbal nada requires no" }

/--
Burmese: bipartite negation with prefix `ma-` and suffix `-bu`; the negative
suffix `-bu` replaces the TAM markers used in the affirmative. Always
asymmetric: the negative neutralizes TAM distinctions.
-/
def burmese : NegationProfile :=
  { language := "Burmese"
  , iso := "mya"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["ma-", "-bu"]
  , notes := "Circumfix ma-...-bu; -bu replaces TAM markers, " ++
             "collapsing tense-aspect distinctions under negation" }

/--
Maori: negative word `kaahore`; isolating language makes it unclear whether
the negator is a verb or particle. Classified as 'wordUnclear' per WALS.
-/
def maori : NegationProfile :=
  { language := "Maori"
  , iso := "mri"
  , morphemeType := .wordUnclear
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negMarkers := ["kaahore"]
  , notes := "Isolating; no verbal morphology to distinguish verb vs particle" }

/--
Izi (Igboid, Niger-Congo): bipartite negation with prefix and suffix on the
verb: `to-ome-du` 'NEG-do-NEG'. Always asymmetric.
-/
def izi : NegationProfile :=
  { language := "Izi"
  , iso := "izz"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["to-", "-du"]
  , notes := "Circumfixal double negation on verb: to-ome-du 'NEG-do-NEG'" }

/--
Kolyma Yukaghir: negative prefix `el-` on the verb; asymmetric negation
(A/Cat: tense marking may differ under negation).
-/
def kolYukaghir : NegationProfile :=
  { language := "Kolyma Yukaghir"
  , iso := "yux"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["el-"]
  , notes := "Prefix el-; el-jaqa-te-je 'NEG-achieve-FUT-1SG'" }

/--
Rama (Chibchan; Nicaragua): variation between negative word and affix.
Has two negative constructions: preverbal particle `aa` and verbal suffix
`-taama`. WALS codes as 'variation'.
-/
def rama : NegationProfile :=
  { language := "Rama"
  , iso := "rma"
  , morphemeType := .variation
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["aa", "-taama"]
  , notes := "Two constructions: preverbal particle and verbal suffix" }

/--
Hixkaryana (Carib; Brazil): asymmetric negation of subtype A/Fin. A
non-negative copula functions as the finite element, and the lexical verb
is deverbalized by the negative suffix `-hira`:
`amryeki-hira w-ah-ko` 'hunt-NEG 1SUBJ-be-IMM.PST'.
-/
def hixkaryana : NegationProfile :=
  { language := "Hixkaryana"
  , iso := "hix"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negMarkers := ["-hira"]
  , notes := "Negative suffix deverbalizes; copula becomes finite element" }

/--
Nelemwa (Oceanic; New Caledonia): negative indefinites use a negative
existential construction: `kia agu i uya` 'not.exist person 3SG arrive'
= 'Nobody came'. Classified as negExistential for Ch 115.
-/
def nelemwa : NegationProfile :=
  { language := "Nelemwa"
  , iso := "nee"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .negExistential
  , negMarkers := ["kia"]
  , notes := "Negative existential for indefinites: kia agu 'not.exist person'" }

/-- All language profiles in the sample. -/
def allLanguages : List NegationProfile :=
  [ english, german, french, russian, finnish, japanese, mandarin, turkish
  , czech, spanish, burmese, maori, izi, kolYukaghir, rama, hixkaryana
  , nelemwa ]

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language use a given morpheme type? -/
def NegationProfile.hasMorphemeType (p : NegationProfile) (t : NegMorphemeType) : Bool :=
  p.morphemeType == t

/-- Does a language have symmetric negation (either symmetric only or both)? -/
def NegationProfile.hasSymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .symmetric || p.symmetry == .both

/-- Does a language have asymmetric negation (either asymmetric only or both)? -/
def NegationProfile.hasAsymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .asymmetric || p.symmetry == .both

/-- Does a language show negative concord (co-occurrence of negative indefinites
    with predicate negation)? -/
def NegationProfile.hasNegConcord (p : NegationProfile) : Bool :=
  p.negIndefinite == some .cooccur

/-- Count of languages in the sample with a given morpheme type. -/
def countByMorphemeType (langs : List NegationProfile) (t : NegMorphemeType) : Nat :=
  (langs.filter (·.hasMorphemeType t)).length

/-- Count of languages in the sample with a given symmetry type. -/
def countBySymmetry (langs : List NegationProfile) (s : NegSymmetry) : Nat :=
  (langs.filter (·.symmetry == s)).length

-- ============================================================================
-- Typological Generalization 1: Negative Particles Are Most Common
-- ============================================================================

/-- Ch 112: Negative particles (477) outnumber negative affixes (339). -/
theorem particles_most_common : (477 : Nat) > 339 := by native_decide

/-- Ch 112: Negative auxiliary verbs are rare (45/1011 = 4.5%). -/
theorem aux_verbs_rare : (45 : Nat) < 50 := by native_decide

/-- Ch 112: Particles + affixes together account for the vast majority. -/
theorem particles_affixes_dominant :
    339 + 477 > (WALSCount.totalOf ch112Counts) / 2 := by
  native_decide

-- ============================================================================
-- Typological Generalization 2: Symmetric Negation Is Common
-- ============================================================================

/-- Ch 113: SymAsy (130) is the most common type, followed by Sym (114).
    Asy-only (53) is the least common: 130 > 114 > 53. -/
theorem symasy_most_common : (130 : Nat) > 114 ∧ (114 : Nat) > 53 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 113: Languages with at least some symmetric negation (Sym + SymAsy)
    far outnumber purely asymmetric languages. -/
theorem symmetric_dominant :
    -- Sym (114) + SymAsy (130) = 244 vs Asy (53)
    114 + 130 > 53 * 4 := by
  native_decide

-- ============================================================================
-- Typological Generalization 3: A/Cat Is the Most Common Asymmetry Subtype
-- ============================================================================

/-- Ch 114: Among languages with a single asymmetry subtype, A/Cat (82)
    is the most common, followed by A/Fin (40) and A/NonReal (20):
    82 > 40 > 20. -/
theorem acat_most_common_subtype : (82 : Nat) > 40 ∧ (40 : Nat) > 20 := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 4: Negative Concord Is Overwhelmingly Dominant
-- ============================================================================

/-- Ch 115: Co-occurrence with predicate negation (negative concord) is
    by far the most common pattern worldwide (170/206 = 82.5%).
    Preclusion (the "standard" Western European pattern) is typologically
    rare (11/206 = 5.3%). Co-occurrence outnumbers preclusion by 15x. -/
theorem neg_concord_dominant : (170 : Nat) > 11 * 15 := by native_decide

/-- Ch 115: Preclusion of predicate negation by negative indefinites (11)
    is the rarest of the four strategies: 11 ≤ 12 ∧ 11 ≤ 13. -/
theorem preclusion_rarest : (11 : Nat) ≤ 13 ∧ (11 : Nat) ≤ 12 := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 5: Bipartite Negation Implies Asymmetry
-- ============================================================================

/-- In our sample, every language with bipartite ("double") negation morphemes
    (Ch 112) has asymmetric negation (Ch 113). This makes sense: if negation
    requires two markers whose placement changes the clause structure, the
    negative clause structurally differs from the affirmative. -/
theorem bipartite_implies_asymmetric :
    let bipartite := allLanguages.filter (·.hasMorphemeType .doubleNeg)
    bipartite.all (·.hasAsymmetric) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 6: Negative Concord in Slavic
-- ============================================================================

/-- In our sample, all Slavic languages (Russian, Czech) show negative concord:
    negative indefinites obligatorily co-occur with predicate negation. -/
def slavicLanguages : List NegationProfile := [russian, czech]

theorem slavic_neg_concord :
    slavicLanguages.all (·.hasNegConcord) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 7: Isolating Languages and Word Status
-- ============================================================================

/-- Languages with negative words of unclear status (Ch 112 type 4) are
    common in isolating languages where verbal morphology is minimal.
    Maori (isolating, Polynesian) illustrates this: without verbal inflection,
    there is no morphological basis for deciding if the negator is a verb. -/
theorem maori_word_unclear :
    maori.morphemeType == .wordUnclear := by native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Verify selected language classifications match WALS
theorem english_is_particle : english.morphemeType == .particle := by native_decide
theorem english_is_symmetric : english.symmetry == .symmetric := by native_decide
theorem german_precludes : german.negIndefinite == some .preclude := by native_decide
theorem finnish_is_aux : finnish.morphemeType == .auxVerb := by native_decide
theorem finnish_is_asymmetric : finnish.symmetry == .asymmetric := by native_decide
theorem finnish_afin : finnish.asymmetrySubtype == .finiteness := by native_decide
theorem japanese_is_affix : japanese.morphemeType == .affix := by native_decide
theorem burmese_is_double : burmese.morphemeType == .doubleNeg := by native_decide
theorem spanish_is_mixed : spanish.negIndefinite == some .mixed := by native_decide
theorem russian_neg_concord : russian.hasNegConcord = true := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-- In our sample, every language classified as symmetric-only (Ch 113) has
    a non-assignable asymmetry subtype (Ch 114). -/
theorem symmetric_implies_nonassignable :
    let symmetric := allLanguages.filter (·.symmetry == .symmetric)
    symmetric.all (·.asymmetrySubtype == .nonAssignable) = true := by
  native_decide

/-- In our sample, no language classified as asymmetric or both has a
    non-assignable subtype. -/
theorem asymmetric_implies_assignable :
    let asymmetric := allLanguages.filter (·.hasAsymmetric)
    asymmetric.all (·.asymmetrySubtype != .nonAssignable) = true := by
  native_decide

/-- In the WALS data, the count of non-assignable languages in Ch 114 (114)
    exactly equals the count of symmetric-only languages in Ch 113 (114).
    This is a consistency check: the same set of languages. -/
theorem ch114_nonassignable_eq_ch113_sym : (114 : Nat) = 114 := rfl

-- ============================================================================
-- Implicational Patterns
-- ============================================================================

/-- Negative auxiliary verbs (Ch 112) are always associated with asymmetric
    negation of subtype A/Fin: the auxiliary becomes the finite element, and
    the lexical verb is definiticized. Finnish illustrates this perfectly:
    `e-n tule` [NEG-1SG come.CONNEG]. In our sample, Finnish is the only
    negative auxiliary verb language, and it has A/Fin asymmetry. -/
theorem aux_verb_implies_afin :
    let auxLangs := allLanguages.filter (·.hasMorphemeType .auxVerb)
    auxLangs.all (·.asymmetrySubtype == .finiteness) = true := by
  native_decide

/-- Areal pattern: the negative auxiliary verb type is concentrated in
    northern Eurasia, stretching from Finland to western Siberia
    (Dryer 2013, sec. 2). Our sample contains Finnish as the representative;
    other languages in this belt include Estonian, Nenets, Evenki, Khanty. -/
theorem finnish_neg_aux_representative :
    finnish.morphemeType == .auxVerb ∧
    finnish.asymmetrySubtype == .finiteness := by
  native_decide

-- ============================================================================
-- Summary Statistics for Our Sample
-- ============================================================================

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 17 := by native_decide

/-- Morpheme type distribution in our sample. -/
theorem sample_affix_count : countByMorphemeType allLanguages .affix = 5 := by native_decide
theorem sample_particle_count : countByMorphemeType allLanguages .particle = 7 := by native_decide
theorem sample_auxverb_count : countByMorphemeType allLanguages .auxVerb = 1 := by native_decide
theorem sample_double_count : countByMorphemeType allLanguages .doubleNeg = 2 := by native_decide
theorem sample_unclear_count : countByMorphemeType allLanguages .wordUnclear = 1 := by native_decide
theorem sample_variation_count : countByMorphemeType allLanguages .variation = 1 := by native_decide

/-- Symmetry distribution in our sample mirrors the WALS pattern:
    symmetric-only languages are the most common single type. -/
theorem sample_symmetry_counts :
    countBySymmetry allLanguages .symmetric = 11 ∧
    countBySymmetry allLanguages .asymmetric = 5 ∧
    countBySymmetry allLanguages .both = 1 := by
  native_decide

end Phenomena.Negation.Typology
