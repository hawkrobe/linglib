import Linglib.Typology.Profile
import Mathlib.Tactic.DeriveFintype

/-!
# Typology.PolarityMarking
@cite{turco-braun-dimroth-2014} @cite{bluhdorn-lohnstein-2012} @cite{sudhoff-2012}
@cite{hohle-1992} @cite{holmberg-2016}

Per-language typological substrate for polarity-marking strategies
(neg → affirm switches): the form-class taxonomy + per-marker
environments + the cross-linguistic entry record. Fragment files for
Dutch, German, English, Italian, Spanish, French, Swedish populate
the schema; Phenomena/Polarity/Studies files consume it for
cross-linguistic predictions.

Moved from `Features/InformationStructure.lean` in the 0.230.493 cleanup
(commit 3/3 of the InformationStructure dump-bag dissolution; cluster B
of the multi-agent audit). The B-cluster's 12-file consumer base —
7 Fragments + 4 Studies + 1 Theory — matches the per-language-typology
shape of `Typology/Indefinite.lean`, `Typology/Possession.lean`, etc.,
not the feature-taxonomy shape `Features/` is for. Names tightened
in the 0.230.496 follow-up (`PolarityMarkingStrategy/Env/Entry` →
`Strategy/Env/Entry`) per mathlib idiom: short type name in deep
namespace (`Polynomial.Monic` not `PolynomialMonic`).

**Framework commitment** (from the original docstring; copied here as
the substrate's load-bearing self-aware note):

This taxonomy treats polarity-marking strategies as form-class properties
(a particle either *is* or *is not* `polarityReversal`), aligned with the
@cite{bluhdorn-lohnstein-2012} / @cite{sudhoff-2012} / @cite{turco-braun-dimroth-2014}
tradition that pairs polarity contrast with specific lexical or prosodic
devices. See `Phenomena/Polarity/Studies/TurcoBraunDimroth2014.lean` for
the canonical consumer.

**This framework is contested.** @cite{matic-nikolaeva-2018} (in
@cite{dimroth-sudhoff-2018}) explicitly reject the form-class encoding,
arguing that "polarity focus" is not a fixed form-meaning association
but a pragmatic interpretation arising from context — they propose
*salient polarity* as the correct construct.
@cite{garassino-jacob-2018} (same volume, fn 13) endorse the M&N view:
"PF (or salient polarity as they prefer to name this specific type of
emphasis) is not directly encoded by certain linguistic forms in a
given language but can be pragmatically conveyed by different
structures under appropriate (contextual) conditions." So the very
chapter that anchors `Fragments/Italian/PolarityMarking.lean::siChe`
disagrees with the encoding choice this enum makes.

The non-equivalence between form-class encoding and M&N's pragmatic
salient-polarity property is stated as a Lean theorem in
`Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`. The substrate
keeps the form-class enum because (a) it has 8 cross-language
consumers via TBD2014, (b) M&N's framework is one alternative among
several — alongside @cite{hohle-1992}'s verum-as-illocutionary-operator
(`Phenomena/Polarity/Studies/Hohle1992.lean`),
@cite{romero-han-2004}'s epistemic-CONJ FOR-SURE-CG
(`Phenomena/Questions/Studies/RomeroHan2004.lean`), and
@cite{gutzmann-2015}'s use-conditional sentence-mood operators
(`Theories/Semantics/Mood/Gutzmann.lean` +
`Phenomena/SentenceMood/Studies/Gutzmann2015.lean`, where verum
composes via DEONT/EPIS/HKNOW dimensions orthogonal to truth-
conditional polarity). All three sibling frameworks are in tension
with the form-class encoding for different reasons; the
incompatibilities are recorded, not silently resolved.
-/

namespace Typology.PolarityMarking

/-- How a language marks polarity switches (neg → affirm). See module
    docstring for the framework-commitment note. -/
inductive Strategy where
  /-- Sentence-internal affirmative particle (e.g., Dutch *wel*) -/
  | particle
  /-- Pitch accent on the finite verb (@cite{hohle-1992} Verum focus) -/
  | verumFocus
  /-- Polarity-reversing particle: affirms [+Pol] while contradicting a
      negative context (e.g., German *doch*, Swedish *jo*, French *si*;
      @cite{holmberg-2016}). The cross-linguistic lumping under this
      constructor records a shared functional role only — the surface
      categories vary (response particle vs. clause-initial construction
      vs. discourse particle); see @cite{garassino-jacob-2018} fn 11. -/
  | polarityReversal
  /-- Other strategy (e.g., pre-utterance particle, intonation pattern) -/
  | other
  /-- No overt polarity marking -/
  | unmarked
  deriving DecidableEq, Repr

/-- Environments / contexts a polarity-marking strategy may be available
    in. Bundles the structural-position dimension (`sentenceInternal`
    vs. pre-utterance) with the discourse-context dimensions (`contrast`,
    `correction`) so per-language entries record one set rather than
    three parallel Bools. -/
inductive Env where
  /-- Position: marker appears sentence-internally (vs. pre-utterance). -/
  | sentenceInternal
  /-- Discourse: marker is available in contrast contexts. -/
  | contrast
  /-- Discourse: marker is available in correction contexts. -/
  | correction
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A cross-linguistic polarity-marking entry.

    Unified structure for all strategies — particles (Dutch *wel*),
    prosodic (German VF), or other. Language-specific Fragment files
    instantiate this with appropriate optional fields. The
    `environments` field records the set of `Env`
    positions/contexts the marker is available in.

    See module docstring for the framework-commitment note: this schema
    records form-class properties in the Blühdorn/Sudhoff/TBD2014
    tradition, an encoding contested by @cite{matic-nikolaeva-2018}
    (formalized in `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`).
    The schema is intentionally thin — syntactic position
    (clause-initial construction vs. response particle vs.
    sentence-medial discourse marker) is *not* encoded;
    cross-linguistic entries grouped under the same `strategy`
    constructor may differ on this dimension. -/
structure Entry where
  /-- Descriptive label (e.g., "wel", "Verum focus", "doch (pre-utterance)") -/
  label : String
  /-- Surface form, if the strategy is a particle -/
  form : Option String := none
  /-- What bears prosodic prominence, if the strategy is prosodic -/
  prosodicTarget : Option String := none
  /-- Set of positions/contexts in which this marker is available. -/
  environments : Typology.Profile Env
  /-- The polarity-marking strategy category -/
  strategy : Strategy

end Typology.PolarityMarking
