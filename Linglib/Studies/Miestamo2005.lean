import Linglib.Syntax.Negation
import Linglib.Data.WALS.Features.F112A
import Linglib.Data.WALS.Features.F113A
import Linglib.Data.WALS.Features.F114A
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

Negating a declarative verbal main clause may do nothing but add a marker,
or it may restructure the clause as well. [miestamo-2005] splits that
second case along two orthogonal dimensions. **Constructional** asymmetry
changes the structure of the negative clause — Finnish adds a finite
negative auxiliary and demotes the lexical verb to a nonfinite
connegative (A/Fin), Turkish replaces the aorist suffix (A/Cat).
**Paradigmatic** asymmetry changes which distinctions remain available —
Burmese collapses three TAM distinctions to one, English loses the
periphrastic emphatic (A/Emph), Imbabura Quechua forces the *-chu*
validator and thereby displaces the others (A/NonReal). The dimensions
cross: Finnish is constructional only, Imbabura Quechua paradigmatic
only, Burmese both.

Formalized here: the book's Appendix III coding for fifteen languages,
its agreement with the later WALS chapters, and the Fragment paradigms
that witness each asymmetry. In the 179-language representative sample
symmetric negation is the more common (Table 3: Sym 72, SymAsy 76, Asy
31), and among subtypes A/Cat leads and A/Emph trails (Table 5: A/Cat
59, A/Fin 45, A/NonReal 23, A/Emph 4).

A language showing several asymmetries may have one *derived* from
another rather than from negation directly — Imbabura Quechua's ban on
other validators follows from its *-chu* requirement, since only one
validator may occur per clause. Derivedness relates asymmetries to each
other, so it is noted per datum rather than carried as a field.

Codings follow Appendix III and agree with the later, same-author WALS
chapters everywhere except English, which the book analyses as symmetric
AUX+*not* with paradigmatic A/Emph where WALS Ch 114A codes A/Cat. Czech
is in neither the book's sample nor the WALS negation chapters; its row
applies the book's criteria.

## References

* [miestamo-2005], Ch 4, Tables 3 and 5, Appendix III
* [miestamo-2013], WALS Ch 113A, 114A
-/
namespace Miestamo2005

open Syntax.Negation (asymmetrySubtypeOfISO)
open Data.WALS

/-! ### Asymmetry dimensions and subtypes -/

/-- The domain an asymmetric negative construction departs in
([miestamo-2005] Table 2). WALS Ch 114A codes the same distinctions
except A/Emph, which the book separates and the atlas folds into
A/Cat. -/
inductive AsymmetrySubtype where
  | finiteness
  | realityStatus
  | emphasis
  | otherCategories
  | finAndNonReal
  | finAndEmph
  | finAndCat
  | nonRealAndCat
  | emphAndCat
  /-- The language has only symmetric negation. -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

/-- The book's subtype recorded by a WALS Ch 114A value. -/
def AsymmetrySubtype.ofWALS114A :
    F114A.AsymmetricNegationSubtype → AsymmetrySubtype
  | .aFin => .finiteness
  | .aNonreal => .realityStatus
  | .aCat => .otherCategories
  | .aFinAndANonreal => .finAndNonReal
  | .aFinAndACat => .finAndCat
  | .aNonrealAndACat => .nonRealAndCat
  | .nonAssignable => .nonAssignable

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

/-! ### The Appendix III coding -/

/-- A Miestamo-style negation datum: the WALS-chapter classification plus
    the book's constructional/paradigmatic dimension coding (Appendix III). -/
structure MiestamoDatum where
  language : String
  /-- ISO 639-3 code; the key for the WALS-consistency checks. -/
  iso : String
  /-- WALS Ch 112: morpheme type -/
  morphemeType : F112A.NegativeMorphemeType
  /-- WALS Ch 113: symmetric/asymmetric/both -/
  symmetry : F113A.NegationSymmetry
  /-- WALS Ch 114: asymmetry subtype -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Which dimensions of asymmetry are present (Appendix III C/P columns) -/
  asymmetryDimensions : List AsymmetryDimension
  /-- The negation marker forms, read off the language's Fragment. -/
  negMarkers : List String
  deriving Repr, BEq

/-! ### Per-language rows -/

/-- Finnish: constructional A/Fin/NegVerb. The negative auxiliary is the
    finite element; the lexical verb appears as a nonfinite connegative.
    Forms derived from `Finnish.Negation.negParadigm`. -/
def finnish : MiestamoDatum :=
  { language := "Finnish"
  , iso := "fin"
  , morphemeType := .negativeAuxiliaryVerb
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := Finnish.Negation.negParadigm.map (·.form) }

/-- German: symmetric. Particle *nicht*.
    Form derived from `German.Negation.nicht.form`. -/
def german : MiestamoDatum :=
  { language := "German"
  , iso := "deu"
  , morphemeType := .negativeParticle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [German.Negation.nicht.form] }

/-- Japanese: constructional A/Fin + A/Cat. Plain *-nai* adjectivalizes
    the verb (A/Fin/Neg-LV); the polite nonpast replaces TAM material
    (A/Cat/TAM); the polite past adds a finite element. Appendix III codes
    all three constructions as constructional, with no paradigmatic row.
    Form derived from `Japanese.Negation.negSuffix.form`. -/
def japanese : MiestamoDatum :=
  { language := "Japanese"
  , iso := "jpn"
  , morphemeType := .negativeAffix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finAndCat
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Japanese.Negation.negSuffix.form] }

/-- Turkish: SymAsy with constructional A/Cat/TAM in the aorist only.
    The aorist suffix changes to *-z* in the 2nd/3rd persons and is
    omitted in the 1st (Appendix II ex. 260); negation is symmetric
    elsewhere. Form derived from `Turkish.Negation.negSuffix.form`. -/
def turkish : MiestamoDatum :=
  { language := "Turkish"
  , iso := "tur"
  , morphemeType := .negativeAffix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Turkish.Negation.negSuffix.form] }

/-- French: symmetric. Bipartite *ne...pas* introduces no structural change.
    Forms derived from `French.Negation`. -/
def french : MiestamoDatum :=
  { language := "French"
  , iso := "fra"
  , morphemeType := .negativeParticle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [French.Negation.neClitic,
                    French.Negation.pasReinforcer] }

/-- Burmese: constructional + paradigmatic A/Cat, in one construction
    (Appendix III type B): the circumfix replaces the TAM slot and
    neutralizes the actual/potential distinction (A/Cat/TAM/Neutr).
    Forms derived from `Burmese.Negation`. -/
def burmese : MiestamoDatum :=
  { language := "Burmese"
  , iso := "mya"
  , morphemeType := .doubleNegation
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional, .paradigmatic]
  , negMarkers := [Burmese.Negation.negPrefix,
                    Burmese.Negation.negSuffix] }

/-- Italian: symmetric. Particle *non*, no structural change.
    Form derived from `Italian.Negation.non.form`. -/
def italian : MiestamoDatum :=
  { language := "Italian"
  , iso := "ita"
  , morphemeType := .negativeParticle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Italian.Negation.non.form] }

/-- Spanish: symmetric. Particle *no*, no structural change.
    Form derived from `Spanish.Negation.no.form`. -/
def spanish : MiestamoDatum :=
  { language := "Spanish"
  , iso := "spa"
  , morphemeType := .negativeParticle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Spanish.Negation.no.form] }

/-- Mandarin Chinese: SymAsy with constructional A/Fin.
    Non-perfectives negated by *bù* (symmetric). Perfectives negated by
    *méi(yǒu)*: the existential verb *yǒu* is introduced as the finite
    element (A/Fin/Neg-FE); when *méi* occurs without *yǒu*, it functions
    as a negative existential verb (A/Fin/NegVerb). [miestamo-2005]
    pp. 90-91, example (51). Forms derived from `Mandarin.Negation`. -/
def mandarin : MiestamoDatum :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphemeType := .negativeParticle
  , symmetry := .both
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Mandarin.Negation.bu.form,
                    Mandarin.Negation.mei.form] }

/-- English: SymAsy with paradigmatic A/Emph/Neutr. Appendix III codes
    AUX+*not* as symmetric (with *do* as the finite AUX host) and locates
    the asymmetry in the paradigm: the periphrastic emphatic (*I DO eat*)
    is unavailable in negatives. WALS Ch 114A instead codes English A/Cat;
    see `english_subtype_diverges_from_wals`.
    Form derived from `English.Negation.not.form`. -/
def english : MiestamoDatum :=
  { language := "English"
  , iso := "eng"
  , morphemeType := .negativeParticle
  , symmetry := .both
  , asymmetrySubtype := .emphasis
  , asymmetryDimensions := [.paradigmatic]
  , negMarkers := [English.Negation.not.form] }

/-- Russian: symmetric. Particle *не* (*ne*), no structural change.
    Form derived from `Russian.Negation.ne.form`. -/
def russian : MiestamoDatum :=
  { language := "Russian"
  , iso := "rus"
  , morphemeType := .negativeParticle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Russian.Negation.ne.form] }

/-- Czech: symmetric. Prefix *ne-*, no structural change. Not in the
    book's RS (nor the WALS Ch 113A-115A samples); coded here by applying
    the book's criteria to symmetric *ne-* prefixation.
    Form derived from `Czech.Negation.negPrefix`. -/
def czech : MiestamoDatum :=
  { language := "Czech"
  , iso := "ces"
  , morphemeType := .negativeAffix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , negMarkers := [Czech.Negation.negPrefix] }

/-- Maori: constructional A/Fin/NegVerb. *Kāhore* is the finite element
    and the lexical clause is subordinated. WALS Ch 112A codes the
    morpheme type as wordUnclear.
    Form derived from `Maori.Negation.kahore.form`. -/
def maori : MiestamoDatum :=
  { language := "Maori"
  , iso := "mri"
  , morphemeType := .negativeWordUnclearIfVerbOrParticle
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Maori.Negation.kahore.form] }

/-- Hixkaryana: constructional A/Fin/Neg-LV. Suffix *-hɨra* deverbalizes
    the verb; a copula becomes the finite element.
    Form derived from `Hixkaryana.Negation.hira.form`. -/
def hixkaryana : MiestamoDatum :=
  { language := "Hixkaryana"
  , iso := "hix"
  , morphemeType := .negativeAffix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , negMarkers := [Hixkaryana.Negation.hira.form] }

/-- Imbabura Quechua: SymAsy with paradigmatic A/NonReal/Displc.
    *Mana* constructions are symmetric; negatives require the validator
    enclitic *-chu*, which also marks interrogatives. Since only one
    validator may occur per sentence, the further ban on other validators
    is an asymmetry the book classifies as *derived* from this one
    (p. 158). Form derived from `Quechua.Negation.mana.form`. -/
def imbaburaQuechua : MiestamoDatum :=
  { language := "Quechua (Imbabura)"
  , iso := "qvi"
  , morphemeType := .negativeParticle
  , symmetry := .both
  , asymmetrySubtype := .realityStatus
  , asymmetryDimensions := [.paradigmatic]
  , negMarkers := [Quechua.Negation.mana.form] }

def allData : List MiestamoDatum :=
  [finnish, german, japanese, turkish, french, burmese, italian, spanish,
   mandarin, english, russian, czech, maori, hixkaryana, imbaburaQuechua]

/-! ### Agreement with WALS -/

/-- English is the sample's only book-vs-atlas disagreement: WALS Ch 114A
    is Miestamo's own chapter, so the two codings otherwise coincide. -/
theorem subtype_matches_wals_except_english :
    allData.all (fun d =>
      d.iso == "eng" ||
      ((asymmetrySubtypeOfISO d.iso).map AsymmetrySubtype.ofWALS114A).all
        (· == d.asymmetrySubtype)) = true := by
  decide

/-- The book vs WALS on English: Appendix III codes English SN as
    symmetric AUX+*not* with paradigmatic A/Emph/Neutr asymmetry; WALS
    Ch 114A codes English A/Cat. -/
theorem english_subtype_diverges_from_wals :
    english.asymmetrySubtype = .emphasis ∧
    asymmetrySubtypeOfISO english.iso = some .aCat :=
  ⟨rfl, by decide⟩

/-! ### The Fragment paradigms behind the codings -/

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

/-! ### The negative auxiliary -/

section NegAuxBridge

open Syntax.Negation (Strategy)

/-- The auxiliary literature's negative-verb strategy and this study's
    auxiliary-verb morpheme type pick out the same Finnish phenomenon: an
    inflecting negative auxiliary. -/
theorem finnish_strategy_morpheme_consistent :
    Strategy.negVerb.morphemeType = finnish.morphemeType := rfl

/-- Verbal negation strategy implies constructional asymmetry in both
    the auxiliary literature (creates an AVC) and the negation typology
    (A/Fin). -/
theorem neg_verb_implies_avc_and_afin :
    Strategy.negVerb.IsVerbal ∧
    finnish.asymmetryDimensions.contains .constructional :=
  ⟨trivial, by decide⟩

end NegAuxBridge

end Miestamo2005
