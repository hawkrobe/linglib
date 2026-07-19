import Linglib.Syntax.Negation
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Italian.Negation
import Linglib.Fragments.German.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.Romance.French.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Spanish.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.Slavic.Russian.Negation
import Linglib.Fragments.Slavic.Czech.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation
import Linglib.Fragments.Quechua.Negation

/-!
# Miestamo (2005): Standard Negation
[miestamo-2005]

[miestamo-2005] refines the WALS symmetric/asymmetric classification
(Ch 113-114) with the orthogonal distinction between **constructional**
and **paradigmatic** asymmetry:

- **Constructional**: the *structure* of the negative clause differs from
  the affirmative beyond adding the negation marker — added finite
  elements (Finnish neg aux + connegative, A/Fin) and marker
  *replacement* (Turkish aorist `-(I)r` → `-z`; replacement asymmetry is
  constructional A/Cat).

- **Paradigmatic**: the *paradigm* of available distinctions differs in
  the negative — neutralization (Burmese *-bu* collapses three TAM
  distinctions to one; English negatives lack the periphrastic emphatic,
  A/Emph/Neutr) or displacement (Imbabura Quechua negatives require the
  validator *-chu*, A/NonReal/Displc).

The dimensions are orthogonal: Finnish is constructional-only, Imbabura
Quechua paradigmatic-only, Burmese both.

## Derived vs independent asymmetry

When a language shows multiple asymmetries, one may be **derived** from
another rather than being a direct consequence of negation: Maung's TAM
neutralization follows from its obligatory irrealis-marking (A/NonReal),
and Imbabura Quechua's ban on other validators follows from the
A/NonReal validator *-chu*. Derivedness relates asymmetries *to each
other*, not asymmetries to marker types; it is noted in datum docstrings
where relevant rather than carried as a field (no sample language here
has an independent multiple asymmetry).

## WALS consistency

Datum codings follow the book's Appendix III analyses. They agree with
the (later, same-author) WALS Ch 112A-114A codings for every sample
language except English: the book analyses English SN as symmetric
AUX+*not* with paradigmatic A/Emph/Neutr asymmetry, where WALS Ch 114A
codes English A/Cat (`english_subtype_diverges_from_wals`). Czech is
absent from the book's sample and from WALS Ch 113A-115A; its datum
applies the book's criteria.

## Quantitative data

The book's representative sample (RS) covers **179 languages** (Table 3,
p. 171): Sym 72 (40%), SymAsy 76 (42%), Asy 31 (17%). The WALS Ch 113
sample (also by Miestamo) covers 297 languages with different numbers;
those live in `Data.WALS.F113A`.
-/

namespace Miestamo2005

open Syntax.Negation
  (NegSymmetry AsymmetrySubtype NegMorphemeType
   morphemeTypeOfISO symmetryOfISO asymmetrySubtypeOfISO)

/-! ## Miestamo's asymmetry dimensions (beyond WALS) -/

/-- [miestamo-2005]'s two dimensions of asymmetry. WALS Ch 113 collapses
    these into a single symmetric/asymmetric distinction; Miestamo decomposes
    asymmetry into two independent dimensions. Local to this study file
    because the dimensions are framework-distinctive. -/
inductive AsymmetryDimension where
  /-- The negative clause differs structurally from the affirmative beyond
      the negation marker: added finite elements (A/Fin) or marker
      replacement (replacement asymmetry is constructional A/Cat). -/
  | constructional
  /-- The negative paradigm makes different formal distinctions than the
      affirmative: neutralization (Burmese TAM, English A/Emph) or
      displacement (Quechua validators). -/
  | paradigmatic
  deriving DecidableEq, BEq, Repr

/-! ## Datum -/

/-- A Miestamo-style negation datum: the WALS-chapter classification plus
    the book's constructional/paradigmatic dimension coding (Appendix III). -/
structure MiestamoDatum where
  language : String
  /-- ISO 639-3 code; the key for the WALS-consistency checks. -/
  iso : String
  /-- WALS Ch 112: morpheme type -/
  morphemeType : NegMorphemeType
  /-- WALS Ch 113: symmetric/asymmetric/both -/
  symmetry : NegSymmetry
  /-- WALS Ch 114: asymmetry subtype -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Which dimensions of asymmetry are present (Appendix III C/P columns) -/
  asymmetryDimensions : List AsymmetryDimension
  /-- Negation marker form(s), derived from Fragment where available -/
  negMarkers : List String
  /-- Brief description of the asymmetry (if any) -/
  asymmetryDescription : String := ""
  deriving Repr, BEq

/-! ## Per-language data (Fragment-derived where possible)

Codings follow the book's Appendix III rows; deviations from WALS or
gaps in the book's sample are flagged in the datum docstrings. -/

/-- Finnish: constructional A/Fin/NegVerb. The negative auxiliary is the
    finite element; the lexical verb appears as a nonfinite connegative.
    Forms derived from `Finnish.Negation.negParadigm`. -/
def finnish : MiestamoDatum :=
  { language := "Finnish"
  , iso := "fin"
  , morphemeType := .auxVerb
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := Finnish.Negation.negParadigm.map (·.form)
  , asymmetryDescription := "A/Fin/NegVerb: the negative auxiliary carries " ++
      "finiteness; the lexical verb is a nonfinite connegative." }

/-- German: symmetric. Particle *nicht*.
    Form derived from `German.Negation.nicht.form`. -/
def german : MiestamoDatum :=
  { language := "German"
  , iso := "deu"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [German.Negation.nicht.form]
  , asymmetryDescription := "Symmetric: adding nicht introduces no " ++
      "structural or paradigmatic changes." }

/-- Japanese: constructional A/Fin + A/Cat. Plain *-nai* adjectivalizes
    the verb (A/Fin/Neg-LV); the polite nonpast replaces TAM material
    (A/Cat/TAM); the polite past adds a finite element. Appendix III codes
    all three constructions as constructional, with no paradigmatic row.
    Form derived from `Japanese.Negation.negSuffix.form`. -/
def japanese : MiestamoDatum :=
  { language := "Japanese"
  , iso := "jpn"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finAndCat
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Japanese.Negation.negSuffix.form]
  , asymmetryDescription := "A/Fin/Neg-LV: -nai turns the verb into an " ++
      "i-adjective; A/Cat/TAM: the polite nonpast replaces TAM material. " ++
      "All constructional in Appendix III." }

/-- Turkish: SymAsy with constructional A/Cat/TAM in the aorist only.
    The aorist suffix changes to *-z* in the 2nd/3rd persons and is
    omitted in the 1st (Appendix II ex. 260); negation is symmetric
    elsewhere. Form derived from `Turkish.Negation.negSuffix.form`. -/
def turkish : MiestamoDatum :=
  { language := "Turkish"
  , iso := "tur"
  , morphemeType := .affix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Turkish.Negation.negSuffix.form]
  , asymmetryDescription := "Constructional A/Cat/TAM: aorist -(I)r → -z " ++
      "under negation (2nd/3rd persons; omitted in the 1st). " ++
      "Most other TAM constructions are symmetric." }

/-- French: symmetric. Bipartite *ne...pas* introduces no structural change.
    Forms derived from `French.Negation`. -/
def french : MiestamoDatum :=
  { language := "French"
  , iso := "fra"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [French.Negation.neClitic,
                    French.Negation.pasReinforcer]
  , asymmetryDescription := "Symmetric: ne...pas adds negation without " ++
      "changing clause structure or paradigm. " ++
      "Jespersen cycle: ne dropping in colloquial speech." }

/-- Burmese: constructional + paradigmatic A/Cat, in one construction
    (Appendix III type B): the circumfix replaces the TAM slot and
    neutralizes the actual/potential distinction (A/Cat/TAM/Neutr).
    Forms derived from `Burmese.Negation`. -/
def burmese : MiestamoDatum :=
  { language := "Burmese"
  , iso := "mya"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional, .paradigmatic]
  , negMarkers := [Burmese.Negation.negPrefix,
                    Burmese.Negation.negSuffix]
  , asymmetryDescription := "Constructional: ma-...-bu replaces the TAM slot. " ++
      "Paradigmatic: -bu neutralizes TAM distinctions (A/Cat/TAM/Neutr)." }

/-- Italian: symmetric. Particle *non*, no structural change.
    Form derived from `Italian.Negation.non.form`. -/
def italian : MiestamoDatum :=
  { language := "Italian"
  , iso := "ita"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Italian.Negation.non.form]
  , asymmetryDescription := "Symmetric: non adds negation without " ++
      "structural or paradigmatic change." }

/-- Spanish: symmetric. Particle *no*, no structural change.
    Form derived from `Spanish.Negation.no.form`. -/
def spanish : MiestamoDatum :=
  { language := "Spanish"
  , iso := "spa"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Spanish.Negation.no.form]
  , asymmetryDescription := "Symmetric: no adds negation without " ++
      "structural or paradigmatic change. " ++
      "Position-dependent n-word concord (parallels Italian)." }

/-- Mandarin Chinese: SymAsy with constructional A/Fin.
    Non-perfectives negated by *bù* (symmetric). Perfectives negated by
    *méi(yǒu)*: the existential verb *yǒu* is introduced as the finite
    element (A/Fin/Neg-FE); when *méi* occurs without *yǒu*, it functions
    as a negative existential verb (A/Fin/NegVerb). [miestamo-2005]
    pp. 90-91, example (51). Forms derived from `Mandarin.Negation`. -/
def mandarin : MiestamoDatum :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Mandarin.Negation.bu.form,
                    Mandarin.Negation.mei.form]
  , asymmetryDescription := "Constructional: méi(yǒu) introduces the " ++
      "existential verb yǒu as the finite element (A/Fin/Neg-FE); " ++
      "méi alone is a negative existential verb (A/Fin/NegVerb). " ++
      "bù constructions are symmetric." }

/-- English: SymAsy with paradigmatic A/Emph/Neutr. Appendix III codes
    AUX+*not* as symmetric (with *do* as the finite AUX host) and locates
    the asymmetry in the paradigm: the periphrastic emphatic (*I DO eat*)
    is unavailable in negatives. WALS Ch 114A instead codes English A/Cat;
    see `english_subtype_diverges_from_wals`.
    Form derived from `English.Negation.not.form`. -/
def english : MiestamoDatum :=
  { language := "English"
  , iso := "eng"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .emphasis
  , asymmetryDimensions := [.paradigmatic]
  , negMarkers := [English.Negation.not.form]
  , asymmetryDescription := "Paradigmatic A/Emph/Neutr: the periphrastic " ++
      "emphatic is unavailable in negatives (simple tenses). " ++
      "AUX+not constructions themselves are symmetric." }

/-- Russian: symmetric. Particle *не* (*ne*), no structural change.
    Form derived from `Russian.Negation.ne.form`. -/
def russian : MiestamoDatum :=
  { language := "Russian"
  , iso := "rus"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Russian.Negation.ne.form]
  , asymmetryDescription := "Symmetric: не adds negation without " ++
      "structural or paradigmatic change. " ++
      "Obligatory negative concord (Slavic pattern)." }

/-- Czech: symmetric. Prefix *ne-*, no structural change. Not in the
    book's RS (nor the WALS Ch 113A-115A samples); coded here by applying
    the book's criteria to symmetric *ne-* prefixation.
    Form derived from `Czech.Negation.negPrefix`. -/
def czech : MiestamoDatum :=
  { language := "Czech"
  , iso := "ces"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Czech.Negation.negPrefix]
  , asymmetryDescription := "Symmetric: ne- prefix adds negation without " ++
      "structural or paradigmatic change. " ++
      "Obligatory negative concord (Slavic pattern)." }

/-- Maori: constructional A/Fin/NegVerb. *Kāhore* is the finite element
    and the lexical clause is subordinated. WALS Ch 112A codes the
    morpheme type as wordUnclear.
    Form derived from `Maori.Negation.kahore.form`. -/
def maori : MiestamoDatum :=
  { language := "Maori"
  , iso := "mri"
  , morphemeType := .wordUnclear
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Maori.Negation.kahore.form]
  , asymmetryDescription := "Constructional A/Fin/NegVerb: kāhore takes the " ++
      "TAM position, the verb appears in nominalized form." }

/-- Hixkaryana: constructional A/Fin/Neg-LV. Suffix *-hɨra* deverbalizes
    the verb; a copula becomes the finite element.
    Form derived from `Hixkaryana.Negation.hira.form`. -/
def hixkaryana : MiestamoDatum :=
  { language := "Hixkaryana"
  , iso := "hix"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Hixkaryana.Negation.hira.form]
  , asymmetryDescription := "Constructional A/Fin/Neg-LV: -hira deverbalizes " ++
      "the verb, a copula becomes the finite element." }

/-- Imbabura Quechua: SymAsy with paradigmatic A/NonReal/Displc.
    *Mana* constructions are symmetric; negatives require the validator
    enclitic *-chu*, which also marks interrogatives. Since only one
    validator may occur per sentence, the further ban on other validators
    is an asymmetry the book classifies as *derived* from this one
    (p. 158). Form derived from `Quechua.Negation.mana.form`. -/
def imbaburaQuechua : MiestamoDatum :=
  { language := "Quechua (Imbabura)"
  , iso := "qvi"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .realityStatus
  , asymmetryDimensions := [.paradigmatic]
  , negMarkers := [Quechua.Negation.mana.form]
  , asymmetryDescription := "Paradigmatic A/NonReal/Displc: negatives require " ++
      "the -chu validator, a category shared with interrogatives; other " ++
      "validators are displaced (derived asymmetry). " ++
      "Clause structure is preserved." }

def allData : List MiestamoDatum :=
  [finnish, german, japanese, turkish, french, burmese, italian, spanish,
   mandarin, english, russian, czech, maori, hixkaryana, imbaburaQuechua]

/-! ## WALS consistency

The book's codings against the (later, same-author) WALS chapter rows,
read via the `Syntax.Negation` per-ISO accessors. Languages absent from
a chapter's WALS sample (Czech throughout) pass vacuously. -/

set_option maxRecDepth 8192 in
/-- Datum morpheme types agree with WALS Ch 112A wherever coded.
    (Scoped `maxRecDepth`: kernel evaluation recurses through the
    1157-row Ch 112A table.) -/
theorem morphemeType_matches_wals :
    allData.all (fun d =>
      (morphemeTypeOfISO d.iso).all (· == d.morphemeType)) = true := by
  decide

/-- Datum symmetry codings agree with WALS Ch 113A wherever coded. -/
theorem symmetry_matches_wals :
    allData.all (fun d =>
      (symmetryOfISO d.iso).all (· == d.symmetry)) = true := by
  decide

/-- Datum subtype codings agree with WALS Ch 114A wherever coded — except
    English, where the book's A/Emph analysis diverges from WALS's A/Cat. -/
theorem subtype_matches_wals_except_english :
    allData.all (fun d =>
      d.language == "English" ||
      (asymmetrySubtypeOfISO d.iso).all (· == d.asymmetrySubtype)) = true := by
  decide

/-- The book vs WALS on English: Appendix III codes English SN as
    symmetric AUX+*not* with paradigmatic A/Emph/Neutr asymmetry; WALS
    Ch 114A codes English A/Cat. -/
theorem english_subtype_diverges_from_wals :
    english.asymmetrySubtype = .emphasis ∧
    asymmetrySubtypeOfISO english.iso = some .otherCategories :=
  ⟨rfl, by decide⟩

/-! ## Structural sanity of the coding -/

/-- Symmetric languages have no asymmetry dimensions. -/
theorem symmetric_no_dimensions :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => d.asymmetryDimensions.isEmpty) = true := by
  decide

/-- Asymmetric languages have at least one asymmetry dimension. -/
theorem asymmetric_has_dimensions :
    (allData.filter (·.symmetry == .asymmetric)).all
      (fun d => !d.asymmetryDimensions.isEmpty) = true := by
  decide

/-- SymAsy languages have at least one asymmetry dimension
    (for their asymmetric constructions). -/
theorem symasy_has_dimensions :
    (allData.filter (·.symmetry == .both)).all
      (fun d => !d.asymmetryDimensions.isEmpty) = true := by
  decide

/-- Symmetric-only (WALS) implies nonAssignable asymmetry subtype. -/
theorem symmetric_implies_nonassignable :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => d.asymmetrySubtype == .nonAssignable) = true := by
  decide

/-- A/Fin with a *verbal* negator implies constructional asymmetry:
    the negative verb takes over the finite verb slot, necessarily
    restructuring the clause. -/
theorem afin_verbal_implies_constructional :
    (allData.filter (fun d =>
      (d.asymmetrySubtype == .finiteness ||
       d.asymmetrySubtype == .finAndCat ||
       d.asymmetrySubtype == .finAndNonReal) &&
      d.morphemeType == .auxVerb)).all
      (fun d => d.asymmetryDimensions.contains .constructional) = true := by
  decide

/-- All A/Fin languages in our sample have constructional asymmetry,
    regardless of negation marker type — matching Table 5, where A/Fin
    is constructional in 44 of 45 RS languages. -/
theorem afin_always_constructional_in_sample :
    (allData.filter (fun d =>
      d.asymmetrySubtype == .finiteness ||
      d.asymmetrySubtype == .finAndCat ||
      d.asymmetrySubtype == .finAndNonReal)).all
      (fun d => d.asymmetryDimensions.contains .constructional) = true := by
  decide

/-! ## Theoretical predictions -/

/-- Particles that are symmetric-only have no asymmetry dimensions.
    Mandarin and English are SymAsy particles with asymmetry elsewhere
    (méi(yǒu) introduces A/Fin; the emphatic paradigm is neutralized). -/
theorem symmetric_particles_no_dimensions :
    (allData.filter (fun d => d.morphemeType == .particle &&
      d.symmetry == .symmetric)).all
      (fun d => d.asymmetryDimensions.isEmpty) = true := by
  decide

/-- Affixes can produce symmetric, asymmetric, or SymAsy negation. -/
theorem affixes_variable :
    (allData.filter (·.morphemeType == .affix)).map (·.symmetry) =
      [.asymmetric, .both, .symmetric, .asymmetric] := rfl

/-- Constructional asymmetry (only) implies the paradigm is maintained:
    Finnish has A/Fin constructional asymmetry but no paradigmatic gaps. -/
theorem finnish_no_paradigmatic_asymmetry :
    finnish.asymmetryDimensions = [.constructional] := rfl

/-- Burmese has both dimensions of asymmetry: the circumfix changes
    structure (constructional) and neutralizes TAM (paradigmatic). -/
theorem burmese_both_dimensions :
    burmese.asymmetryDimensions = [.constructional, .paradigmatic] := rfl

/-- Turkish has constructional-only asymmetry: the aorist marker is
    replaced (or omitted), but no distinctions are neutralized. -/
theorem turkish_constructional_only :
    turkish.asymmetryDimensions = [.constructional] := rfl

/-- Imbabura Quechua has paradigmatic-only asymmetry: the validator
    requirement changes the paradigm, not the clause structure. -/
theorem quechua_paradigmatic_only :
    imbaburaQuechua.asymmetryDimensions = [.paradigmatic] := rfl

/-! ## Fragment cross-validation -/


/-- Japanese Fragment distribution shows the tense shift from stem to
    suffix that Appendix III codes as constructional replacement
    (A/Cat/TAM) alongside the A/Fin adjectivalization. -/
theorem japanese_distribution_confirms_asymmetry :
    let dist := Japanese.Negation.japaneseNegDistribution
    dist.affirmativeOnStem.contains .tense = true ∧
    dist.negativeOnStem.contains .tense = false ∧
    dist.negativeOnSuffix.contains .tense = true ∧
    japanese.asymmetryDimensions.contains .constructional := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Turkish Fragment confirms SymAsy: the aorist is the only asymmetric
    construction in the *gelmek* paradigm. -/
theorem turkish_fragment_confirms_symasy :
    (Turkish.Negation.gelParadigm.filter (fun e => !e.symmetric)).map
      (·.formLabel) = ["aorist"] ∧
    turkish.symmetry == .both :=
  ⟨Turkish.Negation.aorist_asymmetric, rfl⟩

/-- Burmese Fragment confirms paradigmatic asymmetry: TAM neutralized
    (3 affirmative distinctions → 1 negative form). -/
theorem burmese_fragment_confirms_paradigmatic :
    Burmese.Negation.burmeseTAM.affirmativeTAM.length = 3 ∧
    Burmese.Negation.burmeseTAM.negativeTAM.length = 1 ∧
    burmese.asymmetryDimensions.contains .paradigmatic :=
  ⟨rfl, rfl, by decide⟩

/-- Mandarin Fragment confirms SymAsy: the example set contains both
    symmetric (bù) and asymmetric (méi) constructions. -/
theorem mandarin_fragment_confirms_symasy :
    Mandarin.Negation.allExamples.any (·.symmetric) = true ∧
    Mandarin.Negation.allExamples.any (fun e => !e.symmetric) = true ∧
    mandarin.symmetry == .both := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- Mandarin méi-yǒu connects to AspectComparison: the same particle is
    formalized as a cross-domain negative perfective there. -/
theorem mandarin_meiyou_cross_module :
    Mandarin.AspectComparison.meiyou.hanzi = "没有" ∧
    Mandarin.AspectComparison.meiyou.pinyin = "méi-yǒu" :=
  ⟨rfl, rfl⟩

/-- English do-support is exactly the asymmetric constructions in the
    Fragment's construction-level coding. The book instead treats AUX+not
    as symmetric and locates English asymmetry in the emphatic paradigm
    (see `english`); the fragment fact is stable under either construal. -/
theorem english_dosupport_is_asymmetry :
    English.Negation.allExamples.all
      (fun e => e.symmetric == !e.doSupport) = true := by
  decide

/-- Maori Fragment confirms asymmetric: all constructions are A/Fin. -/
theorem maori_fragment_confirms_asymmetric :
    Maori.Negation.allExamples.all (fun e => !e.symmetric) = true ∧
    maori.asymmetryDimensions.contains .constructional := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Hixkaryana Fragment confirms asymmetric A/Fin with copula finite. -/
theorem hixkaryana_fragment_confirms_asymmetric :
    Hixkaryana.Negation.allExamples.all (fun e => !e.symmetric) = true ∧
    Hixkaryana.Negation.allExamples.all (·.copulaFinite) = true ∧
    hixkaryana.asymmetryDimensions.contains .constructional := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Imbabura Quechua Fragment confirms SymAsy, with the *-chu*
    requirement marking exactly the asymmetric constructions. -/
theorem imbaburaQuechua_chu_is_asymmetry :
    Quechua.Negation.allExamples.any (·.symmetric) = true ∧
    Quechua.Negation.allExamples.all
      (fun e => e.symmetric == !e.requiresChu) = true ∧
    imbaburaQuechua.symmetry == .both := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-! ## Miestamo's 179-language survey distribution (Table 3) -/

/-- Distribution from [miestamo-2005]'s 179-language representative
    sample (RS). These are the headline empirical results of Ch 4's
    typological survey. Note: the WALS Ch 113 sample (also by Miestamo)
    covers 297 languages with different numbers; those are captured
    separately via `Data.WALS.F113A`. -/
structure SurveyDistribution where
  totalLanguages : Nat
  symmetricOnly : Nat
  asymmetricOnly : Nat
  symAsy : Nat
  /-- Proportion check: parts sum to whole. -/
  complete : symmetricOnly + asymmetricOnly + symAsy = totalLanguages
  deriving Repr

/-- The 179-language RS distribution from [miestamo-2005] Table 3
    (p. 171). Sym = 72 (40%), SymAsy = 76 (42%), Asy = 31 (17%). -/
def miestamo179 : SurveyDistribution :=
  { totalLanguages := 179
  , symmetricOnly := 72
  , asymmetricOnly := 31
  , symAsy := 76
  , complete := by omega }

/-- SymAsy is the most common type in the RS (76 > 72 > 31).
    [miestamo-2005] Table 3 (p. 171). -/
theorem symasy_plurality :
    miestamo179.symAsy > miestamo179.symmetricOnly ∧
    miestamo179.symAsy > miestamo179.asymmetricOnly := by
  exact ⟨by decide, by decide⟩

/-- Purely asymmetric negation (type Asy) is the least common type.
    [miestamo-2005] p. 171: "symmetric negation is more common in
    the world's languages than asymmetric negation." -/
theorem asymmetric_minority :
    miestamo179.asymmetricOnly < miestamo179.symmetricOnly ∧
    miestamo179.asymmetricOnly < miestamo179.symAsy := by
  exact ⟨by decide, by decide⟩

/-- Languages with any symmetric construction (S column in Table 3:
    Sym + SymAsy = 148, 83%) greatly outnumber purely asymmetric. -/
theorem symmetric_constructions_common :
    miestamo179.symmetricOnly + miestamo179.symAsy > miestamo179.asymmetricOnly := by
  decide

/-- Asymmetry subtype frequencies from [miestamo-2005] Table 5
    (p. 173). A/Cat is most common, A/Emph least common.
    Frequency order: A/Cat (59) > A/Fin (45) > A/NonReal (23) > A/Emph (4). -/
structure SubtypeDistribution where
  aFin : Nat
  aNonReal : Nat
  aEmph : Nat
  aCat : Nat
  deriving Repr

/-- Table 5 totals (across SymAsy + Asy). Languages can show
    multiple subtypes, so these sum to more than 107. -/
def subtypeDist : SubtypeDistribution :=
  { aFin := 45, aNonReal := 23, aEmph := 4, aCat := 59 }

theorem acat_most_common : subtypeDist.aCat > subtypeDist.aFin := by decide

theorem aemph_least_common :
    subtypeDist.aEmph < subtypeDist.aNonReal ∧
    subtypeDist.aEmph < subtypeDist.aFin ∧
    subtypeDist.aEmph < subtypeDist.aCat := by
  exact ⟨by decide, by decide, by decide⟩

/-! ## Implicational universals -/

/-- A/NonReal asymmetry in our sample is paradigmatic. -/
theorem anonreal_implies_paradigmatic :
    (allData.filter (fun d =>
      d.asymmetrySubtype == .realityStatus ||
      d.asymmetrySubtype == .finAndNonReal ||
      d.asymmetrySubtype == .nonRealAndCat)).all
      (fun d => d.asymmetryDimensions.contains .paradigmatic) = true := by
  decide

/-- A/NonReal asymmetry in our sample is never constructional.
    Note: this is a sample limitation (we have only 1 A/NonReal language).
    [miestamo-2005] (p. 96) reports that "both constructional and
    paradigmatic asymmetry is commonly found in type A/NonReal", with 8 of
    23 A/NonReal languages showing constructional asymmetry (Table 5). -/
theorem anonreal_never_constructional :
    (allData.filter (fun d =>
      d.asymmetrySubtype == .realityStatus)).all
      (fun d => !d.asymmetryDimensions.contains .constructional) = true := by
  decide

/-- Symmetric-only negation never has paradigmatic asymmetry.
    By definition: if the paradigm is unchanged, negation is symmetric. -/
theorem symmetric_no_paradigmatic :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => !d.asymmetryDimensions.contains .paradigmatic) = true := by
  decide

/-! ## Bridge to auxiliary verb literature -/

section NegAuxBridge

open Syntax.Negation (NegStrategy)

/-- The NegStrategy→NegMorphemeType mapping is consistent with Finnish's
    classification: the auxiliary literature's negVerb strategy and this
    study's auxVerb morpheme type refer to the same phenomenon — the
    negative element is an inflecting auxiliary verb. -/
theorem finnish_strategy_morpheme_consistent :
    NegStrategy.negVerb.toNegMorphemeType = finnish.morphemeType := rfl

/-- Verbal negation strategy implies constructional asymmetry in both
    the auxiliary literature (creates an AVC) and the negation typology
    (A/Fin). -/
theorem neg_verb_implies_avc_and_afin :
    NegStrategy.negVerb.isVerbal = true ∧
    finnish.asymmetryDimensions.contains .constructional := by
  exact ⟨rfl, by decide⟩

end NegAuxBridge

end Miestamo2005
