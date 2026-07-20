/-!
# Evidential — lexical structure for evidential markers
[aikhenvald-2004] [de-haan-2013] [murray-2017]

The evidential as a lexical object, following the Determiner-API pattern
(`Semantics/Definiteness/Determiner.lean`). The base `Evidential` carries only what is
universal to all evidential markers — a surface `form`; each specialization
(`DirectEvidential`, `ReportativeEvidential`, `InferentialEvidential`) adds
its own structure: an `Exponent` (realization strategy) plus a fine-grained
source value ([aikhenvald-2004]'s parameter carving).

A language's evidential inventory is a `List Evidential.Entry` (heterogeneous
across the three kinds) declared in its Fragment. Typological classifications
— WALS Ch 77 system-type, Ch 78 coding strategy, [aikhenvald-2004]
paradigm system-type — are *derived* from the inventory, not stipulated:
a language's WALS cell is a theorem about its declared evidentials.

## Main declarations

* `Evidential` — the base lexical-item record (just `form`).
* `DirectEvidential`, `ReportativeEvidential`, `InferentialEvidential` —
  the three Aikhenvald-coarse specializations.
* `Evidential.Exponent` — realization-strategy enum (analysis-neutral).
* `DirectSource`, `ReportativeSource`, `InferentialBasis` — the
  [aikhenvald-2004] fine-grained source taxonomies the specializations carry.
* `Evidential.Entry` — an evidential occurrence in a language's inventory.

## Implementation notes

* The semantic side (Murray-style not-at-issue contribution, Faller-style
  illocutionary modification, Korotkova-style modal force, Cumming-style
  temporal anchoring) is deferred to `Studies/{Author}{Year}.lean` files
  which provide opt-in typeclass instances on `Entry`. This file is the
  framework-agnostic lexical and typological-derivation substrate only.
* Mirrors the `Semantics/Definiteness/Determiner.lean` pattern: structure +
  `Exponent` realization enum + `Entry` heterogeneous sum + typological
  derivations as theorems about the declared inventory.
-/

set_option autoImplicit false

namespace Semantics.Evidential

/-! ### Fine-grained source taxonomies ([aikhenvald-2004]) -/

/-- Sensory channel of a direct (firsthand) evidential. The visual vs
    non-visual contrast is grammaticalized in many languages
    (Tuyuca, Tariana, Kashaya); finer distinctions (auditory vs other
    non-visual sensory) are grammaticalized in some (Kashaya). Languages
    that don't grammaticalize the contrast use `.unspecified`. -/
inductive DirectSource where
  | unspecified
  | visual
  | auditory
  | nonvisualSensory
  deriving DecidableEq, Repr, Inhabited

/-- Source-identity of a reportative evidential. [aikhenvald-2004]
    distinguishes hearsay (original speaker not identified) from quotative
    (specifically named source). -/
inductive ReportativeSource where
  | unspecified
  | unidentified
  | identified
  deriving DecidableEq, Repr, Inhabited

/-- Basis of an inferential evidential. [aikhenvald-2004] distinguishes
    inference `fromResult` (observable consequences) from `fromAssumption`
    (general knowledge / reasoning). -/
inductive InferentialBasis where
  | unspecified
  | fromResult
  | fromAssumption
  deriving DecidableEq, Repr, Inhabited

/-- How an evidential is morphosyntactically realized. Analysis-neutral —
    distinguishes Bulgarian-style TAM-fusion from Cuzco-Quechua-style
    second-position clitic from Cheyenne-style clausal particle without
    committing to a syntactic analysis. -/
inductive Exponent where
  /-- A verbal affix or bound suffix (Kashaya `-yá`, Turkish `-mIş`). -/
  | verbalAffix
  /-- Fused into the TAM paradigm (Bulgarian indirect in the perfect). -/
  | tamFusion
  /-- A second-position (Wackernagel) clitic (Cuzco Quechua `-si`/`-chá`). -/
  | clitic2P
  /-- A clausal particle, typically clause-final (Cheyenne `=sėstse`,
      Japanese `soo da`). -/
  | clauseParticle
  /-- A parenthetical / matrix-frame construction (English "I hear"). -/
  | parenthetical
  /-- A grammaticalized lexical frame (Korean `-tay` matrix quotative). -/
  | lexicalFrame
  /-- Tonal or ablaut realization (some Akha and Tibeto-Burman cases). -/
  | toneAblaut
  deriving DecidableEq, Repr

end Semantics.Evidential

open Semantics.Evidential (DirectSource ReportativeSource InferentialBasis)

/-- The base evidential lexical item: only what is universal — a surface
    form. Specializations (`DirectEvidential`, `ReportativeEvidential`,
    `InferentialEvidential`) `extends` this. -/
structure Evidential where
  /-- Surface form (a representative morpheme or construction label). -/
  form : String
  deriving DecidableEq, Repr

/-- A direct (firsthand) evidential: signals that the speaker has direct
    sensory evidence for the prejacent. The `source` field records the
    sensory channel for languages that grammaticalize it (visual vs
    non-visual sensory, etc.). -/
structure DirectEvidential extends Evidential where
  exponent : Semantics.Evidential.Exponent
  /-- Aikhenvald-fine sensory channel (visual / auditory / …). Defaults
      to `.unspecified` for languages that don't grammaticalize the
      contrast. -/
  source : DirectSource := .unspecified
  deriving DecidableEq, Repr

/-- A reportative (hearsay / quotative) evidential: signals that the speaker
    learned the prejacent from another speaker. `sourceIdentity` records
    whether the original speaker is named (`identified` — quotative) or
    not (`unidentified` — hearsay). -/
structure ReportativeEvidential extends Evidential where
  exponent : Semantics.Evidential.Exponent
  /-- Whether the original speaker is identified. -/
  sourceIdentity : ReportativeSource := .unspecified
  deriving DecidableEq, Repr

/-- An inferential evidential: signals that the speaker reasoned to the
    prejacent from indirect evidence. `basis` records whether the
    inference is from observable results (Aikhenvald `fromResult`) or
    from general knowledge / reasoning (Aikhenvald `fromAssumption`). -/
structure InferentialEvidential extends Evidential where
  exponent : Semantics.Evidential.Exponent
  /-- The basis of inference. -/
  basis : InferentialBasis := .unspecified
  deriving DecidableEq, Repr

namespace Semantics.Evidential

/-- An evidential occurrence in a language's inventory: one of the three
    coarse kinds, carrying its typed payload. -/
inductive Entry where
  | direct      (e : DirectEvidential)
  | reportative (e : ReportativeEvidential)
  | inferential (e : InferentialEvidential)
  deriving DecidableEq, Repr

namespace Entry

/-- The occurrence is a direct evidential. -/
def IsDirect : Entry → Prop
  | .direct _ => True
  | _         => False

instance : DecidablePred IsDirect := fun e => by
  cases e <;> unfold IsDirect <;> infer_instance

/-- The occurrence is a reportative evidential. -/
def IsReportative : Entry → Prop
  | .reportative _ => True
  | _              => False

instance : DecidablePred IsReportative := fun e => by
  cases e <;> unfold IsReportative <;> infer_instance

/-- The occurrence is an inferential evidential. -/
def IsInferential : Entry → Prop
  | .inferential _ => True
  | _              => False

instance : DecidablePred IsInferential := fun e => by
  cases e <;> unfold IsInferential <;> infer_instance

/-- The realization strategy of an entry. -/
def exponent : Entry → Exponent
  | .direct e      => e.exponent
  | .reportative e => e.exponent
  | .inferential e => e.exponent

/-- The surface form of an entry. -/
def form : Entry → String
  | .direct e      => e.form
  | .reportative e => e.form
  | .inferential e => e.form

end Entry

end Semantics.Evidential
