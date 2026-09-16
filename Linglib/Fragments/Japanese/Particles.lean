import Linglib.Syntax.Category.Particle.Basic
import Linglib.Pragmatics.Expressives.Kind

/-!
# Japanese particles

The clause-final particles of Japanese questions and their distribution over matrix, embedded
and quoted clauses: the question particle *ka*, obligatory in embedded questions and optional
in matrix ones, its informal counterpart *no*, the declarative complementizer *koto*, the
meta-question particle *kke*, which asks the addressee to remind the speaker of an answer and
occurs only in matrix questions and quotations, and the conjectural *darō*, which embeds
declaratives and questions alike. The file also lists the adverbs and focus particles Kubota
analyses as outlook markers, *dōse* 'anyway', *yahari* 'after all', *koso* 'precisely' and the
rest, use-conditional items whose meaning is the matter of `Studies/Kubota2026.lean`.

## Main definitions

* `Japanese.Particles.ka`, `no_`, `koto`, `kke`, `daroo` — the clause-typing particles with
  their embedding distributions
* `Japanese.OutlookMarkers.all` — the ten adverbs and three focus particles Kubota
  analyses as outlook markers

## References

* [dayal-2025]
* [kubota-2026]
* [roelofsen-uegaki-2020]
* [sauerland-yatsushiro-2017]
* [uegaki-roelofsen-2018]
-/

namespace Japanese.Particles

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated
interrogatives, optional in matrix (can be dropped). Marks CP as +WH.
Licensed in quotation as well. -/
def ka : Particle where
  form := "ka"
  script := some "か"
  position := some .clauseFinal
  distribution := fun c e => match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .obligatory
      | .quasiSubordinated => some .optional
      | .quotation => some .optional
    | _ => none

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : Particle where
  form := "no"
  script := some "の"
  position := some .clauseFinal
  distribution := fun c e => match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .optional
      | .quasiSubordinated => some .optional
      | .quotation => none
    | _ => none

/-- *koto* — complementizer for declarative clauses. Contrast with *ka*:
having *ka* in the embedded clause suffices for interrogative
interpretation, while *koto* marks a declarative ([dayal-2025]: (15)).
Subordinated clauses only. -/
def koto : Particle where
  form := "koto"
  script := some "こと"
  position := some .clauseFinal
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .declarative, .subordinated => some .optional
    | .declarative, .quasiSubordinated => some .excluded
    | _, _ => none

/-- *kke* — meta question particle (MQP). Only in matrix questions and
quotations ([sauerland-yatsushiro-2017]). Has a "remind-me"
presupposition: speaker has forgotten Ans(Q) and believes the addressee
knows it. -/
def kke : Particle where
  form := "kke"
  script := some "っけ"
  position := some .clauseFinal
  distribution := fun c e => match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .excluded
      | .quotation => some .optional
    | _ => none

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
  distribution := fun c e => match c with
    | .declarative | .polar =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .optional
      | .quotation => none
    | _ => none

def allParticles : List Particle := [ka, no_, koto, kke, daroo]

end Japanese.Particles


/-! ### Outlook markers -/

namespace Japanese.OutlookMarkers

/-- The category of an outlook marker: an adverb or a *toritate* focus particle. -/
inductive Category where
  | adverb
  | focusParticle
  deriving DecidableEq, Repr, Inhabited

/-- An outlook marker: its form, romanization, gloss and category. -/
structure OutlookMarkerForm where
  form : String
  romaji : String
  gloss : String
  category : Category
  deriving DecidableEq, Repr

/-- Outlook markers are use-conditional items of one expressive class. -/
def expressiveKind : Pragmatics.Expressives.Kind := .outlookMarker

/-! #### Adverbs -/

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

/-! #### Focus particles -/

def nanka : OutlookMarkerForm := ⟨"なんか", "nanka", "anything like", .focusParticle⟩
def kurai : OutlookMarkerForm := ⟨"くらい", "kurai", "at least", .focusParticle⟩
def koso : OutlookMarkerForm := ⟨"こそ", "koso", "precisely", .focusParticle⟩

/-- The outlook markers. -/
def all : List OutlookMarkerForm :=
  [dōse, shosen, yahari, kekkyoku, masani, mushiro, kaette, yoppodo, semete, mashite,
   nanka, kurai, koso]

end Japanese.OutlookMarkers
