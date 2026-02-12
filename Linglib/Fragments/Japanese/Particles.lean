import Linglib.Theories.TruthConditional.Expressives.OutlookMarker

/-!
# Japanese Particles

## Part 1: Interrogative Particles

Q-morphemes and related particles in Japanese, following Dayal (2025: §1.3).

Japanese has a three-way distinction in interrogative particles that maps
directly onto the three layers of the left periphery:

1. *ka/no*: Clause-typing particle (CP) — obligatory in subordinated interrogatives
2. *koto*: Appears in declaratives (contrast with *ka* in interrogatives)
3. *kke*: Meta question particle (MQP, SAP) — only in matrix and quotation

## Part 2: Outlook Markers

Adverbs and focus particles that express subjective evaluation and manage
discourse stances, following Kubota (2026) and Kubota & Ido (2026a,b).

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- Sauerland, U. & K. Yatsushiro (2017). Remind-me presuppositions and speech-act
  decomposition. Linguistic Inquiry 48.
- Miyagawa, S. (2012). Agreements that occur mainly in the main clause.
- Kubota, Y. (2026). Outlook Management. In *Handbook of Japanese Semantics and Pragmatics*.
- Kubota, Y. & M. Ido (2026a,b). Outlook markers / contrastive *wa*.
-/

namespace Fragments.Japanese.Particles

/-- Layer of the left periphery that a particle occupies. -/
inductive Layer where
  | cp | perspP | sap
  deriving DecidableEq, Repr, BEq

/-- A Japanese particle entry. -/
structure ParticleEntry where
  form : String
  romaji : String
  layer : Layer
  /-- Does this particle appear in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Does this particle appear in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Does this particle appear in matrix questions? -/
  inMatrix : Bool
  deriving Repr, BEq

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated interrogatives,
    optional in matrix (can be dropped). Marks CP as +WH. -/
def ka : ParticleEntry :=
  { form := "か", romaji := "ka"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := true, inMatrix := true }

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : ParticleEntry :=
  { form := "の", romaji := "no"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := true, inMatrix := true }

/-- *koto* — complementizer for declarative clauses. Contrast with *ka*:
    having *ka* in the embedded clause suffices for interrogative interpretation,
    while *koto* marks a declarative (Dayal 2025: (15)). -/
def koto : ParticleEntry :=
  { form := "こと", romaji := "koto"
  , layer := .cp
  , inSubordinated := true, inQuasiSub := false, inMatrix := false }

/-- *kke* — meta question particle (MQP). Only in matrix questions and quotations.
    Has a "remind-me" presupposition: speaker has forgotten Ans(Q) and believes
    the addressee knows it (Sauerland & Yatsushiro 2017). -/
def kke : ParticleEntry :=
  { form := "っけ", romaji := "kke"
  , layer := .sap
  , inSubordinated := false, inQuasiSub := false, inMatrix := true }

def allParticles : List ParticleEntry := [ka, no_, koto, kke]

end Fragments.Japanese.Particles


/-! ## Part 2: Outlook Markers (Kubota 2026)

Japanese adverbs and focus particles that function as "outlook markers" —
discourse markers with dual-layered secondary meaning (presuppositional +
expressive-like). They require a salient counterstance in the discourse and
express the speaker's evaluative stance toward that counterstance.

### Classification (Kubota 2026: (1)–(2))

**Adverbs:**
- (1a) *dōse* 'anyway', *shosen* 'anyway', *yahari* 'after all', *kekkyoku* 'after all'
- (1b) *masani* 'precisely', *mushiro* 'rather', *mashite* 'let alone', *semete* 'at least'
- (1c) *yoppodo* 'rather', *kaette* 'rather'

**Focus particles:**
- (2) *nanka* 'anything like', *kurai* 'at least', *koso* 'precisely'
-/

namespace Fragments.Japanese.OutlookMarkers

open TruthConditional.Expressives.OutlookMarker

/-- Syntactic category of an outlook marker. -/
inductive OutlookCat where
  /-- Adverbial (modifies VP or sentence) -/
  | adverb
  /-- Focus particle (attaches to NP or phrase) -/
  | focusParticle
  deriving DecidableEq, Repr, BEq

/-- An outlook marker lexical entry.

Encodes the form, stance type, syntactic category, and modal selectional
restrictions following Kubota (2026: §3). -/
structure OutlookEntry where
  form : String
  romaji : String
  gloss : String
  cat : OutlookCat
  stance : StanceType
  /-- Modal selectional restrictions (which modal flavors the marker is compatible with). -/
  modalCompat : ModalCompatibility
  /-- Does this marker require a salient counterstance in the discourse?
      True for all outlook markers by definition (Kubota 2026: (37)–(38)). -/
  requiresCounterstance : Bool := true
  deriving Repr, BEq

/-- All outlook markers require a counterstance. This is definitional. -/
theorem allRequireCounterstance (e : OutlookEntry) (h : e.requiresCounterstance = true) :
    e.requiresCounterstance = true := h

-- Default modal compatibility: no restrictions
private def allModals : ModalCompatibility :=
  { epistemic := true, deontic := true, circumstantial := true }

-- Deontic/bouletic only (semete's restriction)
private def deonticOnly : ModalCompatibility :=
  { epistemic := false, deontic := true, circumstantial := false }


/-! ### Adverbs (Kubota 2026: (1)) -/

/-- *dōse* 'anyway' — signals pessimistic/defeatist outlook.
    Kubota (2026: (3a)): "I can't win a gold medal anyway." -/
def dōse : OutlookEntry :=
  { form := "どうせ", romaji := "dōse", gloss := "anyway"
  , cat := .adverb, stance := .negative, modalCompat := allModals }

/-- *shosen* 'anyway/after all' — pessimistic outlook, similar to *dōse*. -/
def shosen : OutlookEntry :=
  { form := "所詮", romaji := "shosen", gloss := "anyway/after all"
  , cat := .adverb, stance := .negative, modalCompat := allModals }

/-- *yahari* 'after all/as expected' — confirms expected outcome.
    Incompatible with *igai-ni* 'unexpectedly' (Kubota 2026: (11)). -/
def yahari : OutlookEntry :=
  { form := "やはり", romaji := "yahari", gloss := "after all/as expected"
  , cat := .adverb, stance := .emphasis, modalCompat := allModals }

/-- *kekkyoku* 'after all/in the end' — confirms expected outcome. -/
def kekkyoku : OutlookEntry :=
  { form := "結局", romaji := "kekkyoku", gloss := "after all/in the end"
  , cat := .adverb, stance := .emphasis, modalCompat := allModals }

/-- *masani* 'precisely/exactly' — emphatic confirmation.
    Kubota (2026: (5a)): "It is precisely you who should go." -/
def masani : OutlookEntry :=
  { form := "まさに", romaji := "masani", gloss := "precisely"
  , cat := .adverb, stance := .emphasis, modalCompat := allModals }

/-- *mushiro* 'rather' — contrary to expected evaluation.
    Kubota (2026: (6a)): "Frankly admitting your mistake actually leaves a better impression."
    Incompatible with *igai-ni* 'unexpectedly' (Kubota 2026: (11)). -/
def mushiro : OutlookEntry :=
  { form := "むしろ", romaji := "mushiro", gloss := "rather"
  , cat := .adverb, stance := .contrary, modalCompat := allModals }

/-- *kaette* 'rather/on the contrary' — contrary to expectation.
    Kubota (2026: (1c)). -/
def kaette : OutlookEntry :=
  { form := "かえって", romaji := "kaette", gloss := "rather/on the contrary"
  , cat := .adverb, stance := .contrary, modalCompat := allModals }

/-- *yoppodo* 'much more/rather' — strong contrary evaluation.
    Kubota (2026: (6b)): "Frankly admitting your mistake leaves a far better impression." -/
def yoppodo : OutlookEntry :=
  { form := "よっぽど", romaji := "yoppodo", gloss := "much more/rather"
  , cat := .adverb, stance := .contrary, modalCompat := allModals }

/-- *semete* 'at least' — minimum standard, settling for less.
    Kubota (2026: (4a), (46)): compatible with desiderative *-tai* and deontic *-beki*
    but NOT with epistemic *hazu* or ability *-eru*. -/
def semete : OutlookEntry :=
  { form := "せめて", romaji := "semete", gloss := "at least"
  , cat := .adverb, stance := .minimum, modalCompat := deonticOnly }

/-- *mashite* 'let alone' — a fortiori minimum standard. -/
def mashite : OutlookEntry :=
  { form := "まして", romaji := "mashite", gloss := "let alone"
  , cat := .adverb, stance := .minimum, modalCompat := allModals }


/-! ### Focus Particles (Kubota 2026: (2)) -/

/-- *nanka* 'anything like' — negative evaluation focus particle.
    Kubota (2026: (3b), (9), (37)–(42)): the prototypical outlook marker.
    Requires a salient counterstance; allows perspective shift under embedding. -/
def nanka : OutlookEntry :=
  { form := "なんか", romaji := "nanka", gloss := "anything like"
  , cat := .focusParticle, stance := .negative, modalCompat := allModals }

/-- *kurai* 'at least' — minimum standard focus particle.
    Kubota (2026: (4b)): "Why don't you have something light, like some tea?" -/
def kurai : OutlookEntry :=
  { form := "くらい", romaji := "kurai", gloss := "at least"
  , cat := .focusParticle, stance := .minimum, modalCompat := allModals }

/-- *koso* 'precisely' — emphatic confirmation focus particle.
    Kubota (2026: (5b)): "It is you who should go." -/
def koso : OutlookEntry :=
  { form := "こそ", romaji := "koso", gloss := "precisely"
  , cat := .focusParticle, stance := .emphasis, modalCompat := allModals }

/-- All outlook marker entries. -/
def allOutlookMarkers : List OutlookEntry :=
  [dōse, shosen, yahari, kekkyoku, masani, mushiro, kaette, yoppodo,
   semete, mashite, nanka, kurai, koso]

/-- All outlook markers have `requiresCounterstance = true`. -/
theorem all_require_counterstance :
    allOutlookMarkers.all (·.requiresCounterstance) = true := by native_decide

/-- *semete* is the only marker with restricted modal compatibility (rejects epistemic). -/
theorem semete_unique_modal_restriction :
    (allOutlookMarkers.filter (λ e => !e.modalCompat.epistemic)).map (·.romaji) = ["semete"] := by
  native_decide


/-! ### Per-Entry Verification Theorems

Each entry has a theorem verifying its stance classification, ensuring that
changing a field in any entry breaks exactly one theorem. -/

theorem dōse_is_negative : dōse.stance = .negative := rfl
theorem shosen_is_negative : shosen.stance = .negative := rfl
theorem yahari_is_emphasis : yahari.stance = .emphasis := rfl
theorem kekkyoku_is_emphasis : kekkyoku.stance = .emphasis := rfl
theorem masani_is_emphasis : masani.stance = .emphasis := rfl
theorem mushiro_is_contrary : mushiro.stance = .contrary := rfl
theorem kaette_is_contrary : kaette.stance = .contrary := rfl
theorem yoppodo_is_contrary : yoppodo.stance = .contrary := rfl
theorem semete_is_minimum : semete.stance = .minimum := rfl
theorem mashite_is_minimum : mashite.stance = .minimum := rfl
theorem nanka_is_negative : nanka.stance = .negative := rfl
theorem kurai_is_minimum : kurai.stance = .minimum := rfl
theorem koso_is_emphasis : koso.stance = .emphasis := rfl

end Fragments.Japanese.OutlookMarkers
