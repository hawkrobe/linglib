import Linglib.Syntax.Coordination
import Linglib.Fragments.English.Coordination
import Linglib.Fragments.Japanese.Coordination
import Linglib.Fragments.Hungarian.Coordination
import Linglib.Fragments.Georgian.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Korean.Coordination

/-!
# Mitrović & Sauerland (2016): Two conjunctions are better than one
[mitrovic-sauerland-2016] [mitrovic-sauerland-2014] [mitrovic-2021]
[haspelmath-2007]

Moreno Mitrović & Uli Sauerland. "Two conjunctions are better than one."
*Acta Linguistica Hungarica* 63 (2016) 4, 471–494.
DOI: 10.1556/064.2016.63.4.5

The paper proposes a universal **J-μ system** for DP coordination: μ is an
e-type head (combines with a single individual) and J is a t-type head
(combines two truth-value-typed arguments). Languages parametrise which
heads are overtly pronounced; the predictions are:

- **J-type coordinators** (e.g. English *and*) have propositional uses, do not
  double, and lack additive/quantificational uses.
- **μ-type coordinators** (e.g. Japanese *mo*) combine DPs, can double, and
  may have additive/quantificational uses.
- Some languages overtly realise both heads, giving triadic exponency
  (J + two μ): [mitrovic-sauerland-2016] §3.1 lists SE Macedonian,
  Hungarian, and Avar as their attested cases (with SerBo-Croatian
  approaching the pattern with adversative J).

## Main declarations

* `hasAllThreeStrategies` — propositional predicate for triadic exponency.
* `mu_additive_generalization` — every language with a μ morpheme has a μ
  morpheme that also serves as the additive particle (§3).
* `j_is_universal` — every M&S focus language has a J-only strategy (§1).
* `all_three_is_rare` — within the focus sample, only Hungarian and Georgian
  show triadic exponency; the paper's own sample uses SE Macedonian, Avar,
  Hungarian (none of SE Macedonian / Avar / SerBo-Croatian is encoded here,
  so the formalised claim is restricted to the M&S focus sub-sample).
* `mu_kind_asymmetry` — Georgian μ is bound, Hungarian μ is free; [bill-etal-2025]
  link this morphological asymmetry to acquisition difficulty.

## Implementation notes

* The language records (`english`, `japanese`, `hungarian`, `georgian`, `latin`,
  `korean`, `slovenian`) carry the J/μ classification of each language's
  conjunction morphemes; the morphemes are the Fragment entries. The
  triadic-exponency classification of Georgian and the Korean and Slovenian
  records follow [mitrovic-2021]; [mitrovic-sauerland-2016] itself
  does not include Georgian.
* The original paper's languages SE Macedonian, Avar, and SerBo-Croatian
  are not yet in the sample.
-/

namespace MitrovicSauerland2016

open Syntax.Coordination

/-! ### The language records -/

/-- English only has J ("and"). "Both...and" is sometimes analyzed as J-MU,
    but "both" is not productively used as an additive particle (*"John both
    slept") and English lacks MU-only conjunction (*"John both Mary both slept"). -/
def english : ConjunctionSystem :=
  { language := "English"
  , morphemes := [ { entry := English.Coordination.and_ } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/-- Japanese conjunction uses "to" (J) and "mo" (MU).
    "to" derives from the comitative marker. "mo" is also the additive particle. -/
def japanese : ConjunctionSystem :=
  { language := "Japanese"
  , morphemes :=
    [ { entry := Japanese.Coordination.to_
      , source := some .comitative }
    , { entry := Japanese.Coordination.mo
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "jpn" }

/-- Hungarian: "és" (J, free, prepositive), "is" (MU, free, postpositive).
    "is" is also the additive focus particle ("also"). One of the languages
    exhibiting triadic exponency, all three of two μ heads and a J head,
    [mitrovic-sauerland-2016] (28). -/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian"
  , morphemes :=
    [ { entry := Hungarian.Coordination.es }
    , { entry := Hungarian.Coordination.is_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hun" }

/-- Georgian: "da" (J, free), "-c" (MU, bound clitic).
    "-c" is also the additive/focus particle. Classified as exhibiting all
    three strategies per [mitrovic-2021]; [mitrovic-sauerland-2016]
    itself uses SE Macedonian, Hungarian, and Avar as the triadic-exponency
    languages. -/
def georgian : ConjunctionSystem :=
  { language := "Georgian"
  , morphemes :=
    [ { entry := Georgian.Coordination.da }
    , { entry := Georgian.Coordination.c_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "kat" }

/-- Latin: "et" (J, free, prepositive) and "-que" (MU, bound enclitic, postpositive).
    Three patterns: A et B, A B-que, et A B-que. -/
def latin : ConjunctionSystem :=
  { language := "Latin"
  , morphemes :=
    [ { entry := Latin.Coordination.et }
    , { entry := Latin.Coordination.que
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .co'a_b'co]
  , iso := "lat" }

/-- Korean: "-(i)rang" (J, bound, postpositive) and "-to" (MU, bound, additive);
    classification follows [mitrovic-2021]. -/
def korean : ConjunctionSystem :=
  { language := "Korean"
  , morphemes :=
    [ { entry := Korean.Coordination.irang }
    , { entry := Korean.Coordination.to_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "kor" }

/-- Slovenian: "in" (J, free, prepositive). Primarily J-only. -/
def slovenian : ConjunctionSystem :=
  { language := "Slovenian"
  , morphemes :=
    [ { entry := { form := "in", gloss := "and", role := .j, kind := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "slv" }

/-- The seven-language sample. -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

/-! ### Triadic-exponency predicate -/

/-- A language exhibits **triadic exponency** when all three M&S strategies
    (J-only, MU-only, J-MU) are attested. The paper's strongest synchronic
    typological observation (§3.1). -/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Prop :=
  sys.hasStrategy .jOnly ∧ sys.hasStrategy .muOnly ∧ sys.hasStrategy .jMu

instance (sys : ConjunctionSystem) : Decidable (hasAllThreeStrategies sys) := by
  unfold hasAllThreeStrategies; infer_instance

/-! ### M&S 2016 generalisations -/

/-- **MU is additive.** Every language with a MU conjunction particle uses
    the same morpheme as its additive ("also/too") particle ([mitrovic-sauerland-2016]
    §3). MU is a single lexical item with subset semantics that appears in
    both conjunction and additive contexts. -/
theorem mu_additive_generalization :
    ∀ sys ∈ msLanguages,
      (∃ m ∈ sys.morphemes, m.entry.role = .mu) → sys.muIsAdditive := by
  decide

/-- **J is universal in the M&S focus sample.** Every M&S-classified language
    has at least the J-only strategy ([mitrovic-sauerland-2016] §3). -/
theorem j_is_universal : ∀ sys ∈ msLanguages, sys.hasStrategy .jOnly := by
  decide

/-- **Triadic exponency is rare.** Within the seven-language sample, the only
    languages exhibiting all three M&S strategies (J, MU, J-MU) are Hungarian
    and Georgian (iso codes "hun", "kat"). The biconditional pins which
    languages have the rare pattern and which do not. -/
theorem all_three_is_rare :
    ∀ sys ∈ msLanguages,
      hasAllThreeStrategies sys ↔ sys.iso = "kat" ∨ sys.iso = "hun" := by
  decide

/-- **MU attachment asymmetry.** Georgian MU (*-c*) is a bound enclitic;
    Hungarian MU (*is*) is free. [bill-etal-2025] (with [mitrovic-2021])
    propose this morphological difference may explain the acquisition
    asymmetry: bound morphemes are harder to segment. -/
theorem mu_kind_asymmetry :
    georgian.muKind = some (.bound .after .clitic) ∧
    hungarian.muKind = some .free := by
  decide

end MitrovicSauerland2016
