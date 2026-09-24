module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Semantics.Root.Defs
public import Linglib.Fragments.Dargwa.Locatives
public import Linglib.Fragments.Dargwa.Agreement

/-!
# Tanti Dargwa complex verbs and valency alternations

This file defines the complex verbs of Tanti Dargwa and its valency alternations as Sumbatova
describes them. A Dargwa verb is simplex, a bare root with at most a gender prefix, a preverb
verb, or a complex verb, a lexical stem followed by a light verb with any preverbs between them.
The stems are noun, adjective, numeral, verb or ideophone stems, some of them found only in the
complex verb, and a few light verbs likewise occur only there. The causative *-aq* is the only
valency-changing morphology: the causee of an intransitive base is the absolutive P of the
derived clause, that of a transitive base an oblique in the inter-elative, a locative form
without the direction marker every spatial elative carries. The antipassive is uncoded and
confined to imperfective forms, and some transitive forms are P-labile, the preterite
*če-b-asː-un* meaning 'he glued it' or 'it stuck' where the future tells the two apart by its
thematic suffix.

## Main definitions

* `Dargwa.LightVerb`, `Dargwa.lightVerbs`: the light verbs, each with the meaning of the
  homophonous simplex verb where it has one
* `Dargwa.ComplexVerb`: a lexical stem, as a `Semantics.Root`, with its word class, preverbs
  and light verb
* `Dargwa.antipassive`, `Dargwa.anticausative`, `Dargwa.causativeOfIntransitive`,
  `Dargwa.causativeOfTransitive`, `Dargwa.alternations`: the valency alternations
* `Dargwa.causeeForm`: the inter-elative of the causee of a transitive base

## Main results

* `Dargwa.isCoded_iff`: the two causatives are the alternations coded on the verb
* `Dargwa.causativeOfIntransitive_fateOfRole_S`, `Dargwa.causativeOfTransitive_valency`: the
  causee of an intransitive base stays a core term; that of a transitive base is demoted as
  the causer is introduced, so the valency is unchanged
* `Dargwa.causeeForm_wellFormed`: the causee form is the directionless elative no spatial
  form is
* `Dargwa.labile_future_thematic`: the future forms of a P-labile verb differ in their
  thematic suffix

## Implementation notes

* A light verb is cited by its stem without the gender prefix, `agrees` recording the roots
  whose shape begins with the agreement slot. Sumbatova lists *aq-* both as 'hang' and among
  the light verbs found only in complex verbs; both entries are kept.
* The demoted causee and the antipassive patient are adpositional positions of the derived
  frame, the frame vocabulary's oblique; the case each takes is stated with the voice.
* The Muira Dargwa complex predicates of Kalyakin's study, with the position he assigns
  their roots, are in `Studies/Kalyakin2026.lean`.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
* [D. Creissels, *Transitivity, Valency, and Voice* (2024)][creissels-2024]
-/

@[expose] public section

namespace Dargwa

open ArgumentFrame.Slot Morphology

/-! ### Light verbs -/

/-- A light verb is the verbal component of a complex verb. -/
structure LightVerb where
  /-- The stem, without the gender prefix. -/
  stem : String
  /-- Whether the root begins with the gender agreement slot. -/
  agrees : Bool
  /-- The meaning of the homophonous simplex verb, `none` for a light verb found only in
  complex verbs. -/
  heavy : Option String
  deriving DecidableEq, Repr

/-- *b-arq'-* 'do, make', the most common light verb. -/
def make : LightVerb := ⟨"arq'", true, some "do, make"⟩

/-- *b-iχ-* 'become'. -/
def become : LightVerb := ⟨"iχ", true, some "become"⟩

/-- *w-ik'-* 'speak'. -/
def speak : LightVerb := ⟨"ik'", true, some "speak"⟩

/-- *b-at-* 'leave'. -/
def leave : LightVerb := ⟨"at", true, some "leave"⟩

/-- *b-ič-* 'fall'. -/
def fall : LightVerb := ⟨"ič", true, some "fall"⟩

/-- *b-aˁq-* 'hit'. -/
def hit : LightVerb := ⟨"aˁq", true, some "hit"⟩

/-- *b-icː-* 'stand up'. -/
def standUp : LightVerb := ⟨"icː", true, some "stand up"⟩

/-- *b-ig-* 'sit down'. -/
def sitDown : LightVerb := ⟨"ig", true, some "sit down"⟩

/-- *aq-* 'hang'. -/
def hang : LightVerb := ⟨"aq", false, some "hang"⟩

/-- *aʁ-* 'reach'. -/
def reach : LightVerb := ⟨"aʁ", false, some "reach"⟩

/-- *b-ač'-* 'come'. -/
def come : LightVerb := ⟨"ač'", true, some "come"⟩

/-- *le-b-q'-* 'come (here)'. -/
def comeHere : LightVerb := ⟨"le-q'", true, some "come (here)"⟩

/-- *b-arʁ-* 'collect'. -/
def collect : LightVerb := ⟨"arʁ", true, some "collect"⟩

/-- *b-ixː-* 'put'. -/
def put : LightVerb := ⟨"ixː", true, some "put"⟩

/-- *it-* 'beat'. -/
def beat : LightVerb := ⟨"it", false, some "beat"⟩

/-- *ag-* 'go away'. -/
def goAway : LightVerb := ⟨"ag", false, some "go away"⟩

/-- *ʔ-* 'say'. -/
def say : LightVerb := ⟨"ʔ", false, some "say"⟩

/-- *b-erk'-* 'drive'. -/
def drive : LightVerb := ⟨"erk'", true, some "drive"⟩

/-- *arg-* 'sift'. -/
def sift : LightVerb := ⟨"arg", false, some "sift"⟩

/-- *b-ertː-* 'tear'. -/
def tear : LightVerb := ⟨"ertː", true, some "tear"⟩

/-- *b-aˁʜ-* 'struggle'. -/
def struggle : LightVerb := ⟨"aˁʜ", true, some "struggle"⟩

/-- *b-ut'-* 'cut', the light verb of *č'u-b-ut'-* 'divide by two'. -/
def cut : LightVerb := ⟨"ut'", true, some "cut"⟩

/-- *b-uq-*, found only in complex verbs. -/
def uq : LightVerb := ⟨"uq", true, none⟩

/-- *aq-*, found only in complex verbs. -/
def aq : LightVerb := ⟨"aq", false, none⟩

/-- *b-ikː-*, found only in complex verbs. -/
def ikk : LightVerb := ⟨"ikː", true, none⟩

/-- *art-*, found only in complex verbs. -/
def art : LightVerb := ⟨"art", false, none⟩

/-- The light verbs Sumbatova lists. -/
def lightVerbs : Finset LightVerb :=
  {make, become, speak, leave, fall, hit, standUp, sitDown, hang, reach, come, comeHere,
    collect, put, beat, goAway, say, drive, sift, tear, struggle, cut, uq, aq, ikk, art}

/-! ### Complex verbs -/

/-- The word class of the lexical stem of a complex verb as an independent word. -/
inductive StemClass where
  | noun
  | adjective
  | numeral
  | verb
  | ideophone
  deriving DecidableEq, Repr, Fintype

/-- A complex verb is a lexical stem, cited as the root it contributes, followed by a light
verb, with any preverbs between them. -/
structure ComplexVerb where
  /-- The lexical stem, which carries the core meaning of the complex. -/
  root : Semantics.Root
  /-- The word class of the stem, `none` for a stem restricted to the complex verb. -/
  category : Option StemClass
  /-- The preverbs between the stem and the light verb. -/
  preverbs : List Morph := []
  /-- The light verb. -/
  lightVerb : LightVerb
  /-- The meaning of the complex verb. -/
  gloss : String
  deriving DecidableEq, Repr

/-- *taman-b-arq'-* 'finish' (transitive), from *taman* 'end'. -/
def finish : ComplexVerb :=
  { root := { name := "taman" }, category := some .noun, lightVerb := make, gloss := "finish" }

/-- *ʜaˁdur-d-arq'-* 'prepare', from *ʜaˁdur-* 'ready'. -/
def prepare : ComplexVerb :=
  { root := { name := "ʜaˁdur" }, category := some .adjective, lightVerb := make,
    gloss := "prepare" }

/-- *č'u-b-ut'-* 'divide by two', from *č'u* 'two'. -/
def divideByTwo : ComplexVerb :=
  { root := { name := "č'u" }, category := some .numeral, lightVerb := cut,
    gloss := "divide by two" }

/-- *qeʜ-w-ik'-* 'cough' (imperfective), from the ideophone *qeʜ-*. -/
def cough : ComplexVerb :=
  { root := { name := "qeʜ" }, category := some .ideophone, lightVerb := speak,
    gloss := "cough" }

/-- *w-isːe-w-ig-* 'start crying', from *w-isː-* 'cry' (imperfective). -/
def startCrying : ComplexVerb :=
  { root := { name := "isːe" }, category := some .verb, lightVerb := sitDown,
    gloss := "start crying" }

/-- *tːurχ-b-arq'-* 'spin', from a stem found nowhere else. -/
def spin : ComplexVerb :=
  { root := { name := "tːurχ" }, category := none, lightVerb := make, gloss := "spin" }

/-- *t'aš-ka-b-icː-* 'stop', from a stem found nowhere else, with the preverb *ka-*
'downward' between it and the light verb. -/
def stop : ComplexVerb :=
  { root := { name := "t'aš" }, category := none, preverbs := [.pref "ka"],
    lightVerb := standUp, gloss := "stop" }

/-! ### Valency alternations -/

/-- The antipassive is uncoded and confined to imperfective forms. The A is absolutive and the
P is demoted to an ergative that controls no agreement; affective verbs have none. -/
def antipassive : Voice := .antipassive

/-- P-lability is the uncoded anticausative of a transitive form, mostly of verbs of
situations that occur with or without an agent, whose patient is then the S. -/
def anticausative : Voice := .anticausative

/-- The causative *-aq* of an intransitive verb. The causer is the ergative A and the causee,
the initial S, the absolutive P. -/
def causativeOfIntransitive : Voice := Voice.causative.marked [.suff "aq"]

/-- The causative *-aq* of a transitive verb. The causer is the ergative A and the causee, the
initial A, an oblique in the inter-elative. -/
def causativeOfTransitive : Voice :=
  { source := .np, target := ⟨some .nominal, [.nominal, .adpositional]⟩,
    correspondence := [(external, complement 1), (complement 0, complement 0)],
    marker := [.suff "aq"] }

/-- The inter-elative of the causee of a transitive base, a locative form without a direction
marker. -/
def causeeForm : Locatives.LocativeForm := ⟨.inter, .elative, none⟩

/-- The valency alternations of Tanti. -/
def alternations : Finset Voice :=
  {antipassive, anticausative, causativeOfIntransitive, causativeOfTransitive}

/-- The causative is the only alternation coded on the verb. -/
theorem isCoded_iff {v : Voice} (hv : v ∈ alternations) :
    v.IsCoded ↔ v = causativeOfIntransitive ∨ v = causativeOfTransitive := by
  simp only [alternations, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

/-- The causee of an intransitive base stays a core term, the P of the derived construction. -/
theorem causativeOfIntransitive_fateOfRole_S :
    causativeOfIntransitive.fateOfRole .S = .maintained := by decide

/-- The causative of a transitive base introduces the causer as it demotes the causee, so the
derived construction has the valency of the initial one. -/
theorem causativeOfTransitive_valency :
    causativeOfTransitive.Nucleativizes ∧
      causativeOfTransitive.fateOfRole .A = .denucleativized ∧
      causativeOfTransitive.target.valency = causativeOfTransitive.source.valency := by
  decide

/-- The causee form is an elative without a direction marker, which no spatial elative is. -/
theorem causeeForm_wellFormed : causeeForm.wellFormed = false := rfl

/-- The future forms of a P-labile verb with third-person arguments are told apart by the
thematic suffix, *-u* for *če-b-alsː-u* '(he) will glue it' and *-ar* for *če-b-alsː-ar* 'it
will stick'. -/
theorem labile_future_thematic :
    thematic ⟨.third, .third⟩ = .suff "u" ∧ .suff "ar" ∈ intransitiveThematic .third := by
  decide

end Dargwa
