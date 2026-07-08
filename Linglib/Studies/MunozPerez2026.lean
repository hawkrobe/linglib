import Linglib.Features.Acceptability
import Linglib.Morphology.DM.Fission
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Fragments.Spanish.PersonFeatures
import Linglib.Fragments.Spanish.Predicates
import Linglib.Fragments.Spanish.Clitics
import Linglib.Studies.KoontzGarboden2009

/-!
# Muñoz Pérez (2026) — Stylistic Applicatives in Chilean Spanish
[munoz-perez-2026]

Grammaticality judgments from [munoz-perez-2026] "Stylistic applicatives:
A lens into the nature of anticausative SE" (*Glossa* 11(1)).

## Main declarations

* `Judgment`, `CliticPattern`, `DativeCliticPerson` — empirical data types
* `spanishFissionRule` — instantiation of the generic
  `Morphology.DM.FissionRule` with Chilean-Spanish-specific data
* `voice_semantically_vacuous` — re-export of
  `Minimalist.Voice.nonThematic_no_semantics`
* `three_way_synonymy_from_vacuity`,
  `fission_person_restriction`, `stylLE_requires_inchoative`,
  `unmarked_blocks_stylLE` — bridge theorems for the empirical
  properties of stylistic LE the Fission analysis accounts for

## Implementation notes

Acceptability follows the project-canonical `Features.Acceptability`
six-level taxonomy. Paper-internal `*` maps to `.unacceptable` and the
unmarked judgment maps to `.ok`.

## Key data points

1. **Three-way synonymy** (exx. 7–12): For marked anticausatives with
   1SG/2SG dative, three clitic patterns are interchangeable:
   - SE + CL_dat: *se me rompió* "it broke on me"
   - CL_dat + LE: *me le rompió*
   - SE + CL_dat + LE: *se me le rompió*

2. **Person restriction** (exx. 15–19, *cerrar la ventana*): Stylistic
   LE is available only with 1SG (*me*) and 2SG (*te*), not 3SG (*le*),
   1PL (*nos*), 2/3PL (*les*).

3. **Marking restriction** (exx. 39–44): Stylistic LE requires SE-marked
   (or optionally SE-marked) anticausatives. Unmarked anticausatives
   (*mejorar*) block it.

4. **Negative controls** (exx. 13b, 14b): *quejarse* and impersonal SE
   reject the *me le* pattern; the stylistic *le* is not a free dative.
-/

open Features (Acceptability)

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
  /-- Acceptability per `Features.Acceptability`. -/
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

/-! ### Spanish Fission instantiation -/

open Minimalist
open Morphology.DM
open Spanish.PersonFeatures
open Spanish.Predicates
open Spanish.Clitics
open Person

/-- The Spanish-specific realization output of Fission: two clitic
    positions. Cl₁ surfaces person features (`me`/`te`), Cl₂ is
    invariably `le`. -/
structure FissionOutput where
  /-- Cl₁: bears person features. -/
  cl1Form : String
  /-- Cl₂: bears case features. -/
  cl2Form : String
  deriving Repr, DecidableEq

/-- The stylistic applicative Fission rule for Chilean Spanish
    ([munoz-perez-2026] rule 55).

    Instantiates the generic `Morphology.DM.FissionRule` with
    Spanish-specific data:
    - Context: inchoative verbal-head sequence (vGO ⌒ vBE)
    - Bundle: [+PART, +SING] person (1SG or 2SG)
    - Realization: Cl₁ = me/te (from [±AUTHOR]), Cl₂ = le (invariable) -/
def spanishFissionRule : FissionRule Category (List VerbHead) FissionOutput where
  contextOk := fun heads => isInchoative heads = true
  decContext := fun heads => inferInstanceAs (Decidable (isInchoative heads = true))
  bundleOk := IsFissionApplicable
  decBundle := inferInstance
  realize := fun p => {
    cl1Form := if p.toFeatures.hasAuthor then "me" else "te"
    cl2Form := "le"
  }

/-- [munoz-perez-2026]'s PF condition (rule 58): the non-thematic
    VoiceP projection must be overtly marked on the verb by a
    *reflexive clitic*. `se` is the directly-merged reflexive; `me`/`te`
    count because they are DAT-REFL syncretic (the paper's table 59)
    and syncretic elements are indistinguishable for PF purposes.
    (1PL `nos` is also syncretic but is filtered upstream: Fission
    requires [+SING], so `nos le` is never generated.) -/
def AnticausativePF (out : FissionOutput) : Prop :=
  out.cl1Form = "me" ∨ out.cl1Form = "te" ∨ out.cl1Form = "se"

instance : DecidablePred AnticausativePF := fun out =>
  inferInstanceAs
    (Decidable (out.cl1Form = "me" ∨ out.cl1Form = "te" ∨ out.cl1Form = "se"))

/-- Apply the Spanish stylistic applicative Fission rule. -/
def applySpanishFission (p : Category) (heads : List VerbHead) :
    Option FissionOutput :=
  spanishFissionRule.apply p heads

/-! ### Person restriction (paper §3.1) -/

/-- Fission applies only to 1SG and 2SG.
    DERIVED from [+PARTICIPANT, +SINGULAR] feature condition. -/
theorem fission_person_restriction :
    IsFissionApplicable .s1 ∧
    IsFissionApplicable .s2 ∧
    ¬ IsFissionApplicable .s3 ∧
    ¬ IsFissionApplicable .minIncl ∧
    ¬ IsFissionApplicable .augIncl ∧
    ¬ IsFissionApplicable .excl ∧
    ¬ IsFissionApplicable .secondGrp ∧
    ¬ IsFissionApplicable .thirdGrp := by decide

/-- The person restriction matches the empirical data:
    Fission applies ↔ stylistic LE is grammatical. -/
theorem person_restriction_matches_data :
    IsFissionApplicable .s1 ∧
    person_1sg.acceptability = .ok ∧
    IsFissionApplicable .s2 ∧
    person_2sg.acceptability = .ok ∧
    ¬ IsFissionApplicable .s3 ∧
    person_3sg.acceptability = .unacceptable := by
  refine ⟨?_, rfl, ?_, rfl, ?_, rfl⟩ <;> decide

/-! ### Inchoative requirement (the context of rule 55) -/

/-- Stylistic LE requires inchoative context (vGO ∧ vBE).
    DERIVED from Fission's structural context condition. -/
theorem stylLE_requires_inchoative :
    (applySpanishFission .s1 [.vCAUSE, .vGO, .vBE]).isSome = true ∧
    (applySpanishFission .s1 [.vDO]).isSome = false ∧
    (applySpanishFission .s1 [.vDO, .vCAUSE, .vGO, .vBE]).isSome = false := by
  decide

/-- Every Muñoz-Pérez verb that licenses stylistic LE has inchoative structure.
    DERIVED from the verb fragment. -/
theorem stylLE_verbs_inchoative :
    (Spanish.Predicates.munozVerbs.filter (·.licensesStylLE)).all
      (fun v => isInchoative v.verbHead) = true := by decide

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
      (fun v => v.anticausativeMarking == .unmarked) = true := by decide

/-! ### SE-optionality (the PF condition, rule 58) -/

/-- When Fission applies, the output clitic satisfies the PF
    marking condition (syncretic with reflexive), making SE optional. -/
theorem se_optional_1sg :
    ∃ out, applySpanishFission .s1 [.vCAUSE, .vGO, .vBE] = some out ∧
      AnticausativePF out :=
  ⟨{ cl1Form := "me", cl2Form := "le" }, by decide, by decide⟩

theorem se_optional_2sg :
    ∃ out, applySpanishFission .s2 [.vCAUSE, .vGO, .vBE] = some out ∧
      AnticausativePF out :=
  ⟨{ cl1Form := "te", cl2Form := "le" }, by decide, by decide⟩

/-- The DAT-REFL syncretism that enables SE-optionality is present
    for exactly the persons where Fission applies. -/
theorem syncretism_aligns_with_fission :
    datReflSyncretic .first .Sing = true ∧
    datReflSyncretic .second .Sing = true ∧
    datReflSyncretic .third .Sing = false := ⟨rfl, rfl, rfl⟩

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

/-! ### Fission verification -/

/-- Fission applies to 1SG in inchoative context. -/
theorem fission_1sg_inchoative :
    applySpanishFission .s1 [.vCAUSE, .vGO, .vBE] =
      some { cl1Form := "me", cl2Form := "le" } := by decide

/-- Fission applies to 2SG in inchoative context. -/
theorem fission_2sg_inchoative :
    applySpanishFission .s2 [.vCAUSE, .vGO, .vBE] =
      some { cl1Form := "te", cl2Form := "le" } := by decide

/-- Fission does NOT apply to 3SG (not [+PART]). -/
theorem fission_blocked_3sg :
    applySpanishFission .s3 [.vCAUSE, .vGO, .vBE] = none := by decide

/-- Fission does NOT apply in non-inchoative context (activity). -/
theorem fission_blocked_activity :
    applySpanishFission .s1 [.vDO] = none := by decide

/-- Fission does NOT apply in causative context (has vDO). -/
theorem fission_blocked_causative :
    applySpanishFission .s1 [.vDO, .vCAUSE, .vGO, .vBE] = none := by decide

/-- 1SG Cl₁ is "me" (reflects [+AUTHOR]). -/
theorem cl1_1sg_is_me :
    (applySpanishFission .s1 [.vCAUSE, .vGO, .vBE]).map (·.cl1Form) = some "me" := by decide

/-- 2SG Cl₁ is "te" (reflects [-AUTHOR]). -/
theorem cl1_2sg_is_te :
    (applySpanishFission .s2 [.vCAUSE, .vGO, .vBE]).map (·.cl1Form) = some "te" := by decide

/-- Cl₂ is always invariable "le". -/
theorem cl2_invariable :
    (applySpanishFission .s1 [.vCAUSE, .vGO, .vBE]).map (·.cl2Form) = some "le" ∧
    (applySpanishFission .s2 [.vCAUSE, .vGO, .vBE]).map (·.cl2Form) = some "le" := by decide

/-! ### Refutation of [koontz-garboden-2009]

K-G's reflexivization analysis predicts that every alternating verb
has SE in its anticausative form (cumulation of A and P spelled out as
SE). The verb-level predicate `KoontzGarboden2009.kgPredictsSEMarked`
formalises this chain. *mejorar* "improve" alternates while remaining
unmarked, falsifying the prediction. The paper's footnote 7 notes that
[koontz-garboden-2009]'s own implementation restricts reflexivization
to SE-marked anticausatives, so the *mejorar* argument bites most
directly against the null-reflexive extension ([chierchia-2004]). -/

/-- Refutation of [koontz-garboden-2009]: *mejorar* alternates but
    is unmarked (no SE), against K-G's prediction that reflexivization
    requires SE-spell-out. Closes the bridge from K-G's
    `reflexivization.involvesCumulation = true` to a falsifying
    Spanish verb. -/
theorem refutes_koontzgarboden :
    ¬ KoontzGarboden2009.kgPredictsSEMarked mejorar := by
  unfold KoontzGarboden2009.kgPredictsSEMarked KoontzGarboden2009.hasSEMarking
  intro h
  rcases h rfl with h | h
  all_goals exact absurd h (by decide)

/-! ### Cross-framework comparisons

The paper draws a second comparative argument — narrower than
[martin-schaefer-kastner-2025]'s two-flavor Voice — that is not
yet stated as a Lean theorem.

## Todo

* **MSK comparison as a real bridge theorem.** Analogously,
  `MartinSchaeferKastner2025.seVoiceOptions : List Voice.Flavor` is a
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
