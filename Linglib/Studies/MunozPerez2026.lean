import Linglib.Data.Examples.Judgment
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Person.Features
import Linglib.Fragments.Spanish.Predicates
import Linglib.Fragments.Spanish.Clitics

/-!
# Muñoz Pérez (2026): Stylistic Applicatives

This file formalizes the argument of [munoz-perez-2026] from the stylistic dative clitic
*le* of Chilean Spanish, which co-occurs with the reflexive *se* of marked anticausatives
and the ethical dative *me*, to the nature of anticausative *se*. The three clitic
patterns are synonymous, which follows if the Voice head that hosts them is semantically
vacuous (`three_way_synonymy_from_vacuity`). The stylistic clitic arises by a fission rule on
the applicative head, which applies to a participant singular bundle
(`isFissionApplicable_iff`) in an inchoative context (`fission_eq_none_iff`) and is blocked by
unmarked anticausatives (`unmarked_blocks_stylLE`). The first exponent of a fissioned head is
read off the dative series of the Spanish fragment, and since that series is syncretic with the
reflexive outside the third person, it marks the Voice projection overtly where *se* is absent
(`marksVoice_of_fission`). Acceptability follows the library's six-level taxonomy, the paper's
star mapping to the unacceptable level.

## References

* [munoz-perez-2026]
-/

open Data.Examples (Acceptability)

namespace MunozPerez2026

/-! ### Data types -/

/-- A clitic pattern in an anticausative construction. -/
inductive CliticPattern where
  /-- SE + dative clitic: *se me rompió*. -/
  | se_cl
  /-- Dative clitic + LE: *me le rompió* (stylistic applicative). -/
  | cl_le
  /-- SE + dative clitic + LE: *se me le rompió*. -/
  | se_cl_le
  deriving DecidableEq, Repr

/-- Person of the dative clitic. -/
inductive DativeCliticPerson where
  /-- *me* -/
  | first_sg
  /-- *te* -/
  | second_sg
  /-- *le* -/
  | third_sg
  /-- *nos* -/
  | first_pl
  /-- *les* -/
  | third_pl
  deriving DecidableEq, Repr

/-- A single grammaticality judgment from the paper. -/
structure Judgment where
  /-- Example number in the paper. -/
  exNumber : String
  /-- The verb in citation form. -/
  verb : String
  /-- The clitic pattern. -/
  pattern : CliticPattern
  /-- Person of the dative clitic. -/
  dativePerson : DativeCliticPerson
  /-- Acceptability per `Data.Examples.Acceptability`. -/
  acceptability : Acceptability
  deriving Repr, BEq

/-! ### Three-way synonymy data (exx. 7–12) -/

/-- *romper* "break" with 1SG dative: all three patterns OK. -/
def romper_se_me : Judgment :=
  { exNumber := "7a", verb := "romper", pattern := .se_cl,
    dativePerson := .first_sg, acceptability := .ok }
def romper_me_le : Judgment :=
  { exNumber := "7b", verb := "romper", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }
def romper_se_me_le : Judgment :=
  { exNumber := "7c", verb := "romper", pattern := .se_cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-- *hundir* "sink" with 1SG dative. -/
def hundir_se_me : Judgment :=
  { exNumber := "8a", verb := "hundir", pattern := .se_cl,
    dativePerson := .first_sg, acceptability := .ok }
def hundir_me_le : Judgment :=
  { exNumber := "8b", verb := "hundir", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-- *caer* "fall" with 1SG dative. -/
def caer_se_me : Judgment :=
  { exNumber := "9a", verb := "caer", pattern := .se_cl,
    dativePerson := .first_sg, acceptability := .ok }
def caer_me_le : Judgment :=
  { exNumber := "9b", verb := "caer", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }
def caer_se_me_le : Judgment :=
  { exNumber := "9c", verb := "caer", pattern := .se_cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-- *morir* "die" with 1SG dative. -/
def morir_se_me : Judgment :=
  { exNumber := "10a", verb := "morir", pattern := .se_cl,
    dativePerson := .first_sg, acceptability := .ok }
def morir_me_le : Judgment :=
  { exNumber := "10b", verb := "morir", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }
def morir_se_me_le : Judgment :=
  { exNumber := "10c", verb := "morir", pattern := .se_cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-! ### Negative controls (exx. 13b, 14b)

Crucially, the *me le* pattern is NOT freely available — it is rejected
with the inherently reflexive verb *quejarse* "complain" (ex. 13b) and
with impersonal SE plus an argumental dative (ex. 14b). These witnesses
keep the dataset honest: stylistic LE depends on the marked-anticausative
structure, not on phonological adjacency. -/

/-- *quejarse* "complain" rejects the *me le* pattern (ex. 13b). -/
def quejarse_me_le : Judgment :=
  { exNumber := "13b", verb := "quejarse", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .unacceptable }

/-- Impersonal SE + argumental dative rejects the *me le* pattern (ex. 14b). -/
def impersonal_me_le : Judgment :=
  { exNumber := "14b", verb := "dar", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .unacceptable }

/-- Negative-control judgments. -/
def negativeControls : List Judgment :=
  [quejarse_me_le, impersonal_me_le]

/-! ### Person restriction data (exx. 15–19, *cerrar la ventana*) -/

/-- 1SG: stylistic LE is OK (ex. 15b *Me le cerró la ventana*). -/
def person_1sg : Judgment :=
  { exNumber := "15b", verb := "cerrar", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-- 2SG: stylistic LE is OK (ex. 16b *Te le cerró la ventana*). -/
def person_2sg : Judgment :=
  { exNumber := "16b", verb := "cerrar", pattern := .cl_le,
    dativePerson := .second_sg, acceptability := .ok }

/-- 3SG: stylistic LE is BLOCKED (ex. 17b *Le le cerró la ventana*). -/
def person_3sg : Judgment :=
  { exNumber := "17b", verb := "cerrar", pattern := .cl_le,
    dativePerson := .third_sg, acceptability := .unacceptable }

/-- 1PL: stylistic LE is BLOCKED (ex. 18b *Nos le cerró la ventana*). -/
def person_1pl : Judgment :=
  { exNumber := "18b", verb := "cerrar", pattern := .cl_le,
    dativePerson := .first_pl, acceptability := .unacceptable }

/-- 2/3PL: stylistic LE is BLOCKED (ex. 19b *Les le cerró la ventana*). -/
def person_3pl : Judgment :=
  { exNumber := "19b", verb := "cerrar", pattern := .cl_le,
    dativePerson := .third_pl, acceptability := .unacceptable }

/-- Person restriction data collected. -/
def personRestrictionData : List Judgment :=
  [person_1sg, person_2sg, person_3sg, person_1pl, person_3pl]

/-! ### Marking restriction data (exx. 39–44) -/

/-- *quebrar* (marked SE) licenses stylistic LE (ex. 39b *Me le quebró el florero*). -/
def quebrar_le : Judgment :=
  { exNumber := "39b", verb := "quebrar", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-- *mejorar* (unmarked) does NOT license stylistic LE (ex. 40b *Me le mejoró el sueldo). -/
def mejorar_le : Judgment :=
  { exNumber := "40b", verb := "mejorar", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .unacceptable }

/-- *hervir* (optional SE) DOES license stylistic LE (ex. 44a *Me le hirvió el agua*). -/
def hervir_le : Judgment :=
  { exNumber := "44a", verb := "hervir", pattern := .cl_le,
    dativePerson := .first_sg, acceptability := .ok }

/-! ### Data verification -/

/-- All three-way synonymy patterns are grammatical for 1SG. -/
theorem three_way_all_grammatical :
    (romper_se_me.acceptability == .ok &&
    romper_me_le.acceptability == .ok &&
    romper_se_me_le.acceptability == .ok) = true := rfl

/-- Person restriction: exactly 1SG and 2SG are grammatical. -/
theorem person_restriction_data :
    (personRestrictionData.filter (·.acceptability == .ok)).length = 2 := by
  decide

/-- Person restriction: exactly 3SG, 1PL, 3PL are ungrammatical. -/
theorem person_restriction_blocked :
    (personRestrictionData.filter (·.acceptability == .unacceptable)).length = 3 := by
  decide

/-- The person paradigm uses *cerrar* (ex. 15), not *caer* (ex. 9). -/
theorem cerrar_anchors_person_paradigm :
    personRestrictionData.all (·.verb == "cerrar") = true := by decide

/-- Marking restriction: marked/optional → OK, unmarked → blocked. -/
theorem marking_restriction :
    (quebrar_le.acceptability == .ok &&
    hervir_le.acceptability == .ok &&
    mejorar_le.acceptability == .unacceptable) = true := rfl

/-- Negative controls are present and uniformly unacceptable. Drift sentry:
    if the *me le* pattern were ever miscoded as `.ok`, this fails. -/
theorem negative_controls_unacceptable :
    negativeControls.all (·.acceptability == .unacceptable) = true := by decide

/-! ### The fission rule -/

open Minimalist Minimalist.Voice
open Spanish.Predicates
open Person

/-- The bundle condition of the fission rule holds of an applicative head that is
[+PART, +SING]. -/
def IsFissionApplicable (c : Category) : Prop :=
  .participant ∈ c.toFeatures ∧ c.IsSingular

instance : DecidablePred IsFissionApplicable := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The bundle condition singles out the speaker and the addressee, since a third person lacks
[+PART] and a group lacks [+SING]. -/
theorem isFissionApplicable_iff (c : Category) :
    IsFissionApplicable c ↔ c = .speaker ∨ c = .addressee := by
  cases c <;> decide

/-- The two exponents of a fissioned applicative head. -/
structure FissionOutput where
  /-- The forms of the first exponent, which keeps the person and number of the head. -/
  cl1 : Finset String
  /-- The form of the second exponent, a dative without person and number. -/
  cl2 : String
  deriving DecidableEq

/-- The fission rule of Chilean Spanish splits an applicative head that is [+PART, +SING] in two
when the context is inchoative. The first exponent has the dative forms of the head's category
and the second is the inflectionless dative *le*. -/
def fission (c : Category) (heads : List VerbHead) : Option FissionOutput :=
  if isInchoative heads = true ∧ IsFissionApplicable c then
    some ⟨PersonalPronoun.paradigm Spanish.Clitics.dative c, Spanish.Clitics.le.form⟩
  else none

theorem fission_eq_none_iff {c : Category} {heads : List VerbHead} :
    fission c heads = none ↔ ¬ (isInchoative heads = true ∧ IsFissionApplicable c) := by
  simp [fission]

/-- A first person singular head fissions into *me le*. -/
theorem fission_speaker : fission .speaker [.vCAUSE, .vGO, .vBE] = some ⟨{"me"}, "le"⟩ := by
  decide +kernel

/-- A second person singular head fissions into *te le*. -/
theorem fission_addressee : fission .addressee [.vCAUSE, .vGO, .vBE] = some ⟨{"te"}, "le"⟩ := by
  decide +kernel

/-- Fission applies to the first and second person singular, whose stylistic clitic is accepted,
and not to the third, whose stylistic clitic is rejected. -/
theorem person_restriction_matches_data :
    IsFissionApplicable .speaker ∧
    person_1sg.acceptability = .ok ∧
    IsFissionApplicable .addressee ∧
    person_2sg.acceptability = .ok ∧
    ¬ IsFissionApplicable .other ∧
    person_3sg.acceptability = .unacceptable := by
  refine ⟨?_, rfl, ?_, rfl, ?_, rfl⟩ <;> decide

/-! ### Inchoative requirement (the context of rule 55) -/

/-- Stylistic *le* requires an inchoative context, so fission applies neither to an activity nor
to a causative. -/
theorem stylLE_requires_inchoative :
    fission .speaker [.vDO] = none ∧ fission .speaker [.vDO, .vCAUSE, .vGO, .vBE] = none := by
  decide +kernel

/-- Every Muñoz-Pérez verb that licenses stylistic LE has inchoative structure.
    DERIVED from the verb fragment. -/
theorem stylLE_verbs_inchoative :
    (Spanish.Predicates.munozVerbs.filter (·.licensesStylLE)).all
      (fun v ↦ isInchoative v.verbHead) = true := by decide

/-! ### Marking restriction -/

/-- Unmarked anticausatives block stylistic LE.
    DERIVED from the verb fragment: mejorar is unmarked and blocks LE. -/
theorem unmarked_blocks_stylLE :
    mejorar.anticausativeMarking = .unmarked ∧
    mejorar.licensesStylLE = false := ⟨rfl, rfl⟩

/-- Marked anticausatives license stylistic LE. -/
theorem marked_licenses_stylLE :
    quebrar.anticausativeMarking = .marked ∧
    quebrar.licensesStylLE = true := ⟨rfl, rfl⟩

/-- Optional SE-marking also licenses stylistic LE. -/
theorem optional_licenses_stylLE :
    hervir.anticausativeMarking = .optional ∧
    hervir.licensesStylLE = true := ⟨rfl, rfl⟩

/-- All Muñoz-Pérez verbs blocking stylistic LE are unmarked.
    DERIVED from the fragment data. -/
theorem blocking_verbs_all_unmarked :
    (Spanish.Predicates.munozVerbs.filter (!·.licensesStylLE)).all
      (fun v ↦ v.anticausativeMarking == .unmarked) = true := by decide

/-! ### The overt-marking condition -/

/-- A form counts as a reflexive clitic at PF when the reflexive series has it, syncretic
elements being indistinguishable there. -/
def IsReflexiveForm (f : String) : Prop := ∃ p ∈ Spanish.Clitics.reflexive, p.form = f

instance : DecidablePred IsReflexiveForm := fun _ ↦ inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The paper's PF condition on a fissioned head requires the non-thematic Voice projection to be
overtly marked by a reflexive clitic, here the first exponent. -/
def FissionOutput.MarksVoice (out : FissionOutput) : Prop := ∃ f ∈ out.cl1, IsReflexiveForm f

/-- Outside the third person every dative form is a reflexive form, by the syncretism of the two
series. -/
theorem isReflexiveForm_of_mem_dative {c : Category} (hc : c.person ≠ .third) {f : String}
    (hf : f ∈ PersonalPronoun.paradigm Spanish.Clitics.dative c) : IsReflexiveForm f := by
  rw [(Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff c).mpr hc] at hf
  obtain ⟨p, hp, -, rfl⟩ := ReflexivePronoun.mem_paradigm.mp hf
  exact ⟨p, hp, rfl⟩

/-- Whenever fission applies, its first exponent marks Voice, so *se* is optional beside a
stylistic clitic. -/
theorem marksVoice_of_fission {c : Category} {heads : List VerbHead} {out : FissionOutput}
    (h : fission c heads = some out) : out.MarksVoice := by
  unfold fission at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hne : c.person ≠ .third := by
    rcases (isFissionApplicable_iff c).mp hc.2 with rfl | rfl <;> decide
  have hdat : (PersonalPronoun.paradigm Spanish.Clitics.dative c).Nonempty := by
    rw [(Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff c).mpr hne]
    exact Spanish.Clitics.paradigm_reflexive_nonempty c
  obtain ⟨f, hf⟩ := hdat
  exact ⟨f, hf, isReflexiveForm_of_mem_dative hne hf⟩

/-- The second exponent *le* is not a reflexive form, so the marking comes from the first. -/
theorem not_isReflexiveForm_le : ¬ IsReflexiveForm Spanish.Clitics.le.form := by decide +kernel

/-- Syncretism with the reflexive does not suffice for a stylistic clitic. The first person
plural *nos* is syncretic, and fission still skips it for want of [+SING]. -/
theorem syncretic_not_isFissionApplicable :
    PersonalPronoun.paradigm Spanish.Clitics.dative .speakerOthers =
        ReflexivePronoun.paradigm Spanish.Clitics.reflexive .speakerOthers ∧
      ¬ IsFissionApplicable .speakerOthers :=
  ⟨(Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff _).mpr (by decide), by decide⟩

/-! ### Three-way synonymy -/

/-- Re-export of `Minimalist.Voice.nonThematic_no_semantics` in the Muñoz-Pérez
    frame. SE is purely a PF marker — its presence or absence is
    phonological, not semantic. -/
theorem voice_semantically_vacuous :
    ¬ Minimalist.Voice.anticausative.HasSemantics :=
  Minimalist.Voice.nonThematic_no_semantics

/-- The empirical three-way synonymy is consistent with Voice
    vacuity: the three `.ok` judgments co-hold with the proof that
    Voice has no semantics (the judgments are data, not derived). -/
theorem three_way_synonymy_from_vacuity :
    romper_se_me.acceptability = .ok ∧
    romper_me_le.acceptability = .ok ∧
    romper_se_me_le.acceptability = .ok ∧
    ¬ Minimalist.Voice.anticausative.HasSemantics := by
  refine ⟨rfl, rfl, rfl, ?_⟩; exact voice_semantically_vacuous

/-! ### Against a null-reflexive extension of [koontz-garboden-2009]

On the reflexivization analysis extended with a null reflexive
([chierchia-2004]), every alternating verb has SE in its anticausative,
cumulation of A and P being spelled out as SE. *mejorar* "improve"
alternates while remaining unmarked. The paper's footnote 7 notes that
[koontz-garboden-2009]'s own implementation restricts reflexivization
to SE-marked anticausatives, so the argument bites against the
extension. -/

/-- The verb-level prediction of the null-reflexive extension: an
    alternating verb has SE in its anticausative form. -/
def seMarkedIfAlternating (v : SpanishVerbEntry) : Prop :=
  v.causativeAlternation = true → v.anticausativeMarking ≠ .unmarked

/-- *mejorar* alternates but is unmarked, against the prediction. -/
theorem refutes_koontzgarboden : ¬ seMarkedIfAlternating mejorar := by
  unfold seMarkedIfAlternating; decide

/-! ### Cross-framework comparisons

The paper draws a second comparative argument — narrower than
[martin-schaefer-kastner-2025]'s two-flavor Voice — that is not
yet stated as a Lean theorem.

## Todo

* **MSK comparison as a real bridge theorem.** Analogously,
  `MartinSchaeferKastner2025.seVoiceOptions : List Flavor` is a
  list literal `[.nonThematic, .reflexive]`. A subset claim against any
  hand-written Muñoz list of flavors is decided by `decide` over list
  literals — no real Voice-flavor mechanism is engaged. A genuine
  comparison requires deriving each paper's *predicted* flavor set from
  its analytical commitments (Voice-flavor licensing rules in MSK;
  Fission + Voice-vacuity in MunozPerez), then proving inclusion of
  the derived sets.

* **vGO ⌒ vBE adjacency in `isInchoative` (Phase D — substrate).**
  Muñoz Pérez's Fission rule has the explicit context `/vGO __ vBE`,
  but `Syntax/Minimalist/VerbalDecomposition.lean`'s
  `isInchoative` checks only set-membership (`heads.contains .vGO`),
  not adjacency. Deferred because the refactor touches 8 downstream
  consumer files. A focused session should add an `applPos` field (or
  similar adjacency witness) to the decomposition and audit each
  consumer site.

* **Derive `licensesStylLE` from structure
  (Phase D — `Fragments/Spanish/Predicates.lean`).** The Fragment
  currently stipulates `licensesStylLE : Bool` per verb; per
  CLAUDE.md's "derive, don't stipulate" rule it should be computed
  from existing structural fields, plausibly
  `isInchoative v.verbHead && v.anticausativeMarking ∈ [.marked, .optional]`.
  Deferred pending Phase D's `isInchoative` refactor (the derivation
  needs adjacency-aware inchoativity to be empirically tight).

* **Newman 2024 Feature Failure (Phase D — Minimalist substrate).**
  Paper rule 60 grounds why the stylistic *le*'s unchecked features
  do not crash the derivation. The Minimalist substrate currently
  has no `Derivation` or `crashes` predicates to formalise
  Feature Failure against; deferred pending those primitives.
-/

end MunozPerez2026
