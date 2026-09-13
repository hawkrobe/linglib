import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Syntax.Control.Head
import Linglib.Studies.Landau2013
import Linglib.Data.Examples.Allotey2021

/-!
# Allotey (2021): overt pronouns of infinitival predicates of Gã

This file formalizes [allotey-2021]. Obligatory control into Gã irrealis
`ni`-clauses requires an overt subject proclitic: null PRO is ungrammatical, a
lexical subject is ungrammatical, and the proclitic shows the whole OC signature
(Table 2). The controlled clause is non-finite and irrealis rather than
subjunctive — it bars tense and aspect, focus fronting and free reference,
licenses NPIs across its boundary, negates preverbally, and carries the irrealis
marker only as a high tone on its subject (Table 4). The pronoun is overt
because that tone needs a segmental host.

Everything is read off the paper's example rows and the Fragment. The control
profile of a clause type is [landau-2013]'s signature as the rows attest it
(`Control.ofAttested`): no row attests a criterial configuration of the
`ni`-clause, so it is obligatory control, while the finite `akɛ`-clause attests
free reference. Complementizer selection is `Verb.takes` over the Fragment's
frames; every finiteness diagnostic is a row theorem conditioned on the
complementizer's finiteness alone, the paper's convergence argument; Table 4 is
the exponents the rows show in each irrealis context, and the tone-hosting
requirement then derives the overt pronoun from the minimal-pronoun inventory.

## Implementation notes

The bound-variable row of Table 2 rests on the *de se* example (53); the paper
has no *only* test, so `Control.Diagnostic.strictUnderOnly` is never attested
and the bound-variable clause of the signature holds unrefuted rather than
tested. The paper tests reference only in the `ni`- and `akɛ`-clauses, so the
comparison with [landau-2004]'s scale is stated for those two.

## References

* [allotey-2021]
* [landau-2013]
* [landau-2004]
* [szabolcsi-2009]
* [hornstein-1999]
* [satik-2019]
* [karttunen-1971]
* [noonan-2007]
* [rizzi-1997]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

namespace Allotey2021

open Minimalist.MinimalPronoun Control Ga Data.Examples

/-! ### Pronouns (Table 3) -/

/-- Only second and third person singular have a dedicated objective form. -/
theorem objective_form_iff (p : Person) (n : Number) :
    (∃ q ∈ pronouns, q.person = some p ∧ q.number = some n ∧ q.case_ = some .acc) ↔
      n = .singular ∧ (p = .second ∨ p = .third) := by
  cases p <;> cases n <;> decide

/-- No dedicated possessive form: the possessive column of Table 3 is the
    elsewhere form. -/
theorem no_possessive_form : ∀ q ∈ pronouns, q.case_ ≠ some .gen := by
  decide

/-! ### Complementizer selection (§5.5.1) -/

/-- The three-way clause typology is the selection relation: each clause type's
    frame takes exactly its own complementizer. -/
theorem frame_takes_iff (c d : EmbeddedClauseType) :
    c.frame.Takes d.complementizer ↔ c = d := by
  cases c <;> cases d <;> decide

/-- A verb takes `ni` exactly when some frame of it is controlled. -/
theorem takes_ni_iff_control :
    ∀ v ∈ verbs, v.takes ni ↔ ∃ r ∈ v.readings, r.control.isSome := by
  decide

/-- [wurmbrand-lohninger-2023]'s hierarchy at Gã's granularity: a proposition
    complement is exactly one whose frame takes a finite complementizer;
    situations and events share the infinitival `ni`-frame. -/
theorem proposition_iff_finite :
    ∀ v ∈ verbs, ∀ r ∈ v.readings, ∀ s ∈ r.size,
      (s = .proposition ↔ ∃ z ∈ complementizers, r.frame.Takes z ∧ z.IsFinite) := by
  decide

/-- Subject and object control are both in the inventory (Table 2). -/
theorem control_rows :
    (∃ v ∈ verbs, ∃ r ∈ v.readings, r.control = some .subjectControl) ∧
      ∃ v ∈ verbs, ∃ r ∈ v.readings, r.control = some .objectControl := by
  decide

/-! ### Rows -/

/-- Gã vocabulary items for minimal pronouns: no context-specific item, so the
    elsewhere pronoun realizes every context. -/
def gaInventory : MinPronInventory PronForm where
  items := []
  elsewhere := .pronoun

/-- The Fragment entry for a row's matrix verb. -/
def verbOf (row : LinguisticExample) : Option Verb :=
  (row.feature? "verb").bind (lookupSense verbs ·)

/-- The clause type a complementizer feature names. -/
def clauseOf : String → Option EmbeddedClauseType
  | "ni" => some .ni
  | "ake" => some .ake
  | "keji" => some .keji
  | _ => none

/-- The clause type of a row: its complement's, or the finite type for a
    matrix clause the paper labels finite. -/
def clauseTypeOf (row : LinguisticExample) : Option EmbeddedClauseType :=
  match row.feature? "complementizer", row.feature? "clauseType" with
  | some c, _ => clauseOf c
  | none, some "finite" => some .ake
  | _, _ => none

/-- A row records reading `r` with judgment `j`. -/
def reads (row : LinguisticExample) (r : String) (j : Judgment) : Prop :=
  ∃ x ∈ row.readings, x = (r, j)

instance (row : LinguisticExample) (r : String) (j : Judgment) : Decidable (reads row r j) :=
  inferInstanceAs (Decidable (∃ x ∈ row.readings, _))

/-- The realized form of a row's embedded subject. -/
def formOf (row : LinguisticExample) : Option PronForm :=
  match row.feature? "embeddedSubject" with
  | some "pronoun" => some .pronoun
  | some "null" => some .null
  | _ => none

/-- Rows whose only point is the shape of the controlled subject: the
    control frame is grammatical exactly with the inventory's control form
    (exx 2–3, 34–44, 54–59 vs 40–41). -/
theorem controlled_subject_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" ∈ [none, some "nullSubject"] →
      ∀ f ∈ formOf row, (row.judgment = .acceptable ↔ f = gaInventory.controlForm) := by
  decide +kernel

/-- A lexical subject in the control frame is out (exx 42b–c, 64) — the copy the
    Movement Theory of Control ([hornstein-1999]) would pronounce. -/
theorem lexical_subject_rows :
    ∀ row ∈ Examples.all, row.feature? "embeddedSubject" = some "lexical" →
      row.feature? "clauseContext" = none → row.judgment = .ungrammatical := by
  decide +kernel

/-- Complementizer selection (exx 104–106): grammatical exactly when the verb
    takes the complementizer. -/
theorem c_selection_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "cSelection" →
      ∀ v ∈ verbOf row, ∀ c ∈ clauseTypeOf row,
        (row.judgment = .acceptable ↔ v.takes c.complementizer) := by
  decide +kernel

/-- Overt tense or aspect in the complement is grammatical exactly in the finite
    clause types (exx 101, 111). -/
theorem tam_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ t ∈ row.feature? "embeddedTAM",
      t ≠ "none" → (row.judgment = .acceptable ↔ c.complementizer.IsFinite) := by
  decide +kernel

/-- Focus fronting, [rizzi-1997]'s strong-CP diagnostic, is available exactly in
    the finite clauses (exx 107–108); matrix negation licenses an embedded NPI
    exactly across the non-finite one (exx 116–117). -/
theorem focus_npi_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row,
      (row.feature? "diagnostic" = some "focus" →
        (row.judgment = .acceptable ↔ c.complementizer.IsFinite)) ∧
      (row.feature? "diagnostic" = some "npi" → row.feature? "negation" = some "matrix" →
        (row.judgment = .acceptable ↔ ¬ c.complementizer.IsFinite)) := by
  decide +kernel

/-- Negation precedes the verb exactly in the non-finite clause (exx 121–122,
    124). -/
theorem negation_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ p ∈ row.feature? "negationPosition",
      (p = "preverbal" ↔ ¬ c.complementizer.IsFinite) := by
  decide +kernel

/-- The embedded subject bears the irrealis high tone exactly in the `ni`-clause
    (exx 110–112, 118). -/
theorem subject_tone_rows :
    ∀ row ∈ Examples.all, row.judgment = .acceptable → ∀ c ∈ clauseTypeOf row,
      ∀ t ∈ row.feature? "subjectTone", (t = "high") = (c = .ni) := by
  decide +kernel

/-! ### The irrealis marker -/

/-- The marker appears on the subject of the control frame and nowhere else in
    the complement data (exx 34, 88–89, 92, 100–103, 106, 109, 112, 117–119,
    122); it tracks the frame, not the verb — *kai* 'remember' takes it in its
    `ni`-frame (exx 43, 117a) and lacks it in its realis `akɛ`-frame (ex 89a). -/
theorem marker_rows :
    ∀ row ∈ Examples.all, row.feature? "clauseContext" ∈ [none, some "control"] →
      ∀ m ∈ row.feature? "irrealisMarker",
        (m = "present" ↔ (row.feature? "control").isSome) := by
  decide +kernel

/-- The paper's implicative contrast (ex 89): the marker is absent exactly under
    the positive implicatives of the Fragment, whose complements are entailed
    realized ([karttunen-1971]). -/
theorem implicative_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "implicative" →
      ∀ v ∈ verbOf row,
        (row.feature? "irrealisMarker" = some "absent" ↔ v.implicative = some .positive) := by
  decide +kernel

/-! ### The OC signature (Table 2) -/

/-- The antecedent must c-command the controlled pronoun (exx 45–46):
    grammatical exactly under the paper's c-commanding coindexation. -/
theorem cCommand_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "cCommand" →
      (row.judgment = .acceptable ↔ row.feature? "antecedent" = some "cCommanding") := by
  decide +kernel

/-- No long-distance antecedent (exx 47–49): grammatical exactly under the local
    coindexation. -/
theorem longDistance_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "longDistance" →
      (row.judgment = .acceptable ↔ row.feature? "antecedent" = some "local") := by
  decide +kernel

/-- Under ellipsis the controlled pronoun has the sloppy reading only (ex 52). -/
theorem sloppy_only :
    ∃ row ∈ Examples.all, row.feature? "diagnostic" = some "ellipsis" ∧
      reads row "sloppy" .acceptable ∧ reads row "strict" .unacceptable := by
  decide +kernel

/-- A free reading of the embedded subject is available exactly in the finite
    complement (exx 110–111 vs 92, 112). -/
theorem free_reading_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ j, reads row "free" j →
      (j = .acceptable ↔ c.complementizer.IsFinite) := by
  decide +kernel

/-- Ex 53 witnesses the *de se* row: infelicitous in its context. -/
theorem deSe_witness :
    ∃ row ∈ Examples.all, row.feature? "diagnostic" = some "deSe" ∧
      row.judgment = .unacceptable ∧ row.context ≠ "" := by
  decide +kernel

/-- The controlled form φ-covaries with its controller (exx 37–39), unlike
    [satik-2019]'s form-invariant Ewe *yè*. -/
theorem controlled_form_covaries :
    subjectProclitic? .second .singular ≠ subjectProclitic? .second .plural := by
  decide

/-- The control diagnostic a row attests when acceptable: a non-c-commanding or
    long-distance antecedent by the paper's coindexation, a free reading of the
    embedded subject, or a strict reading under ellipsis. -/
def attests (row : LinguisticExample) : Diagnostic → Prop
  | .nonCCommandingControl =>
    row.feature? "antecedent" = some "nonCCommanding" ∧ row.judgment = .acceptable
  | .longDistanceControl =>
    row.feature? "antecedent" = some "longDistance" ∧ row.judgment = .acceptable
  | .arbitraryControl => reads row "free" .acceptable
  | .strictEllipsis => reads row "strict" .acceptable
  | .strictUnderOnly => False

instance (row : LinguisticExample) : DecidablePred (attests row) := fun d => by
  cases d <;> unfold attests <;> infer_instance

/-- The diagnostics the rows attest for a clause type. -/
def attested (c : EmbeddedClauseType) : Set Diagnostic :=
  {d | ∃ row ∈ Examples.all, clauseTypeOf row = some c ∧ attests row d}

instance (c : EmbeddedClauseType) : DecidablePred (· ∈ attested c) := fun d => by
  unfold attested; infer_instance

/-- The control profile of a clause type in [landau-2013]'s signature: the
    clauses no attested diagnostic refutes. -/
def gaProfile (c : EmbeddedClauseType) : Set Landau2013.Clause74 :=
  ofAttested (attested c)

/-- No row attests a criterial configuration of the `ni`-clause. -/
theorem attested_ni : attested .ni = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]; decide +kernel

/-- The `ni`-clause is obligatory control: every clause of the signature holds,
    so it admits no criterial configuration. [szabolcsi-2009]'s long-distance
    Agree reaches the embedded subject across this weak CP. -/
theorem ni_obligatory : gaProfile .ni = Set.univ :=
  ofAttested_eq_univ_iff.2 attested_ni

theorem admits_ni : admits (gaProfile .ni) = ∅ := admits_eq_empty_iff.2 ni_obligatory

/-- The finite `akɛ`-clause attests a free reading (exx 110–111). -/
theorem arbitrary_mem_attested_ake : .arbitraryControl ∈ attested .ake := by
  decide +kernel

/-- So it is not obligatory control. -/
theorem ake_not_obligatory : gaProfile .ake ≠ Set.univ := fun h =>
  Set.notMem_empty _ (ofAttested_eq_univ_iff.1 h ▸ arbitrary_mem_attested_ake)

/-! ### Landau's scale -/

/-- Gã clause types on [landau-2004]'s finiteness scale — a scale position, not
    a mood claim. Unrestricted TAM and independent tense both coincide with the
    complementizer's finiteness (exx 109–111, 118–119). -/
def gaToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (decide c.complementizer.IsFinite) (decide c.complementizer.IsFinite)

/-- No Gã clause type is a tensed-but-controlled F-subjunctive. -/
theorem ga_no_fSubjunctive (c : EmbeddedClauseType) : gaToLandau c ≠ .fSubjunctive := by
  cases c <;> decide

/-- The scale agrees with the rows where the paper tests reference: OC exactly on
    the C-subjunctive, at any Agr value — Gã has no φ-agreement (exx 79–81,
    123). -/
theorem landau_predicts_control (c : EmbeddedClauseType) (hc : c ≠ .keji) (agr : Bool) :
    gaProfile c = Set.univ ↔ (gaToLandau c).HasOC agr := by
  cases c with
  | keji => exact absurd rfl hc
  | ni => exact iff_of_true ni_obligatory (by cases agr <;> decide)
  | ake => exact iff_of_false ake_not_obligatory (by cases agr <;> decide)

/-- In [noonan-2007]'s typology the non-finite clause is the reduced one:
    `.infinitive`, the paper's own term for the bare-root `ni`-complement. -/
theorem reduced_iff_not_finite (c : EmbeddedClauseType) :
    (∀ cd ∈ c.frame.codings, cd.isReduced = true) ↔ ¬ c.complementizer.IsFinite := by
  cases c <;> decide

/-! ### Table 4 -/

/-- The five irrealis contexts of Table 4. -/
inductive IrrealisContext where
  | subjunctive
  | imperative
  | conditional
  | future
  | embeddedControl
  deriving DecidableEq, Repr

/-- The context a row's `clauseContext` names. -/
def contextOf : String → Option IrrealisContext
  | "subjunctive" => some .subjunctive
  | "imperative" => some .imperative
  | "conditional" => some .conditional
  | "future" => some .future
  | "control" => some .embeddedControl
  | _ => none

/-- The exponents of the irrealis marker: high tone on the subject, high tone on
    the verb, the vowel segment *a*. -/
inductive Exponent where
  | subjectTone
  | verbTone
  | vowel
  deriving DecidableEq, Repr, Fintype

/-- A row shows an exponent. -/
def shows (row : LinguisticExample) : Exponent → Prop
  | .subjectTone => row.feature? "subjectTone" = some "high"
  | .verbTone => row.feature? "verbTone" = some "high"
  | .vowel => row.feature? "irrealisVowel" = some "present"

instance (row : LinguisticExample) : DecidablePred (shows row) := fun e => by
  cases e <;> unfold shows <;> infer_instance

/-- The rows in an irrealis context with judgment `j`. -/
def rowsIn (ctx : IrrealisContext) (j : Judgment) : List LinguisticExample :=
  Examples.all.filter fun row =>
    decide ((row.feature? "clauseContext").bind contextOf = some ctx ∧ row.judgment = j)

/-- Table 4 from the rows: the exponents some grammatical row shows in the
    context (exx 85–86, 93–97, 100–103). -/
def realization (ctx : IrrealisContext) : Finset Exponent :=
  Finset.univ.filter fun e => ∃ row ∈ rowsIn ctx .acceptable, shows row e

/-- Embedded control realizes the marker as the subject's high tone alone. -/
theorem realization_control : realization .embeddedControl = {.subjectTone} := by
  decide +kernel

/-- The embedded-control realization is unique among the five contexts; in
    particular it lacks the subjunctive's doubled high tone (ex 88). -/
theorem control_realization_unique (c : IrrealisContext) :
    realization c = realization .embeddedControl → c = .embeddedControl := by
  cases c <;> decide +kernel

/-- The realizations are exact: adding the verb's tone to the control clause
    (ex 88) or the subject's to the future (ex 96), or dropping the verb's from
    the subjunctive (ex 87), is ungrammatical. -/
theorem realization_exact :
    (∃ row ∈ rowsIn .embeddedControl .ungrammatical, shows row .verbTone) ∧
    (∃ row ∈ rowsIn .future .ungrammatical, shows row .subjectTone) ∧
    ∃ row ∈ rowsIn .subjunctive .ungrammatical, ¬ shows row .verbTone := by
  decide +kernel

/-! ### Deriving the overt pronoun -/

/-- A tonal exponent needs a segmental host; the null form has none. -/
def HostsTone (f : PronForm) : Prop := f ≠ .null

/-- The controlled-subject form must host the irrealis tone Table 4 places on
    the embedded-control subject. -/
def HostsControlTone (inv : MinPronInventory PronForm) : Prop :=
  .subjectTone ∈ realization .embeddedControl → HostsTone inv.controlForm

/-- Null PRO is impossible in Gã: a null controlled-subject form cannot host
    the irrealis tone. -/
theorem null_pro_impossible (inv : MinPronInventory PronForm) (h : inv.controlForm = .null) :
    ¬ HostsControlTone inv := fun hc =>
  hc (realization_control ▸ Finset.mem_singleton_self _) h

/-- The Gã inventory meets the tone-hosting requirement. -/
theorem ga_hostsControlTone : HostsControlTone gaInventory := fun _ h => nomatch h

/-- Controlled subjects surface as overt proclitics. -/
theorem ga_overt_pro : gaInventory.controlForm = .pronoun := rfl

/-- Overt PRO and no *pro*-drop: Gã instantiates the implicational universal. -/
theorem ga_satisfies_universal :
    gaInventory.OvertPROUniversal Ga.allowsProDrop := λ _ ↦ rfl

end Allotey2021
