import Linglib.Syntax.Category.Particle.Basic
import Linglib.Features.Expressive

/-!
# Japanese Particles
[dayal-2025] [kubota-2026] [sauerland-yatsushiro-2017]

## Part 1: Interrogative Particles

Q-morphemes and related particles in Japanese, as `Particle` values with
embedding-distribution facets. The left-peripheral layer assignments are
derived from those facets in `BhattDayal2020`.

1. *ka/no*: Clause-typing Q-morphemes — appear in subordinated interrogatives
2. *koto*: Declarative complementizer (contrast with *ka* in interrogatives)
3. *kke*: Meta question particle — only in matrix and quotation
4. *daroo*: Conjectural/epistemic copula

## Part 2: Outlook Markers

Adverbs and focus particles that express subjective evaluation and manage
discourse stances, following [kubota-2026]. The fragment carries the theory-neutral
lexical inventory (form + category); [kubota-2026]'s stance classification and modal
selectional restrictions live in `Studies/Kubota2026.lean`.
-/

namespace Japanese.Particles

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated
interrogatives, optional in matrix (can be dropped). Marks CP as +WH.
Licensed in quotation as well. -/
def ka : Particle where
  form := "ka"
  script := some "か"
  position := some .clauseFinal
  embedding := some
    { matrix := some .optional
      subordinated := some .obligatory
      quasiSubordinated := some .optional
      quotation := some .optional }

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : Particle where
  form := "no"
  script := some "の"
  position := some .clauseFinal
  embedding := some
    { matrix := some .optional
      subordinated := some .optional
      quasiSubordinated := some .optional }

/-- *koto* — complementizer for declarative clauses. Contrast with *ka*:
having *ka* in the embedded clause suffices for interrogative
interpretation, while *koto* marks a declarative ([dayal-2025]: (15)).
Subordinated clauses only. -/
def koto : Particle where
  form := "koto"
  script := some "こと"
  position := some .clauseFinal
  embedding := some
    { matrix := some .excluded
      subordinated := some .optional
      quasiSubordinated := some .excluded }

/-- *kke* — meta question particle (MQP). Only in matrix questions and
quotations ([sauerland-yatsushiro-2017]). Has a "remind-me"
presupposition: speaker has forgotten Ans(Q) and believes the addressee
knows it. -/
def kke : Particle where
  form := "kke"
  script := some "っけ"
  position := some .clauseFinal
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .excluded
      quotation := some .optional }

/-- *daroo* (だろう) — conjectural/epistemic copula.
With declarative complement: "x thinks p" (⟦daroo⟧({p})(x) = INQ_x ⊆ {p}↓).
With interrogative complement: "x wonders Q" (⟦daroo⟧(Q)(x) = INQ_x ⊆ Q).
The dual reading arises from the absence of an ignorance component,
unlike wonder ([roelofsen-uegaki-2020], [uegaki-roelofsen-2018]).
Appears in matrix and quasi-subordinated contexts but not in subordinated
interrogatives (which use *ka*). -/
def daroo : Particle where
  form := "daroo"
  script := some "だろう"
  position := some .clauseFinal
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .optional }

def allParticles : List Particle := [ka, no_, koto, kke, daroo]

end Japanese.Particles


/-! ## Part 2: Outlook Markers

Theory-neutral lexical inventory of the Japanese adverbs and focus particles that
[kubota-2026] analyses as outlook markers ([kubota-2026] (1)-(2)). The stance
classification, modal restrictions, and dual-layer denotation are paper apparatus and
live in `Studies/Kubota2026.lean`. -/

namespace Japanese.OutlookMarkers

/-- Gross syntactic category of an outlook marker ([kubota-2026] (1)-(2)): the standard
adverb vs. *toritate* focus-particle distinction. -/
inductive Category where
  | adverb
  | focusParticle
  deriving DecidableEq, Repr, Inhabited

/-- An outlook-marker lexical entry — theory-neutral surface facts only. -/
structure OutlookMarkerForm where
  form : String
  romaji : String
  gloss : String
  category : Category
  deriving DecidableEq, Repr

/-- Outlook markers are all use-conditional items of one expressive class — the consensus
metadata Fragments carry; the diagnostic fingerprint lives in `Studies/Kubota2026.lean`. -/
def expressiveKind : Features.Expressive := .outlookMarker

/-! ### Adverbs ([kubota-2026] (1)) -/

def dōse : OutlookMarkerForm := ⟨"どうせ", "dōse", "anyway", .adverb⟩
def shosen : OutlookMarkerForm := ⟨"所詮", "shosen", "anyway/after all", .adverb⟩
def yahari : OutlookMarkerForm := ⟨"やはり", "yahari", "after all/as expected", .adverb⟩
def kekkyoku : OutlookMarkerForm := ⟨"結局", "kekkyoku", "after all/in the end", .adverb⟩
def masani : OutlookMarkerForm := ⟨"まさに", "masani", "precisely", .adverb⟩
def mushiro : OutlookMarkerForm := ⟨"むしろ", "mushiro", "rather", .adverb⟩
def kaette : OutlookMarkerForm := ⟨"かえって", "kaette", "rather/on the contrary", .adverb⟩
def yoppodo : OutlookMarkerForm := ⟨"よっぽど", "yoppodo", "much more/rather", .adverb⟩
def semete : OutlookMarkerForm := ⟨"せめて", "semete", "at least", .adverb⟩
def mashite : OutlookMarkerForm := ⟨"まして", "mashite", "let alone", .adverb⟩

/-! ### Focus particles ([kubota-2026] (2)) -/

def nanka : OutlookMarkerForm := ⟨"なんか", "nanka", "anything like", .focusParticle⟩
def kurai : OutlookMarkerForm := ⟨"くらい", "kurai", "at least", .focusParticle⟩
def koso : OutlookMarkerForm := ⟨"こそ", "koso", "precisely", .focusParticle⟩

/-- The Japanese outlook-marker lexical inventory ([kubota-2026] (1)-(2)). -/
def all : List OutlookMarkerForm :=
  [dōse, shosen, yahari, kekkyoku, masani, mushiro, kaette, yoppodo, semete, mashite,
   nanka, kurai, koso]

end Japanese.OutlookMarkers
