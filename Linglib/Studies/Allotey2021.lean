import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Syntax.Control.Head
import Linglib.Studies.Landau2013
import Linglib.Data.Examples.Allotey2021

/-!
# Allotey (2021): overt pronouns of infinitival predicates of Gã

Obligatory control into Gã irrealis `ni`-clauses requires an overt subject
proclitic: null PRO is ungrammatical, a lexical subject is ungrammatical, and
the proclitic shows the whole OC signature (Table 2). The controlled clause is
non-finite and irrealis rather than subjunctive — it bars tense and aspect,
focus fronting and obviation, licenses NPIs across its boundary, negates
preverbally, and carries the irrealis marker only as a high tone on its
subject (Table 4). The pronoun is overt because that tone needs a segmental
host.

The OC signature is read off the Fragment's clause typology through
[landau-2013]'s profile, the complement frames off the Fragment's verb
inventory, and the finiteness diagnostics off the Fragment's clause
properties; the example rows check each claim, including the implicative
contrast of (89) against the verbs' Karttunen classes. The Movement Theory of
Control is refuted by the lexical-subject rows, and the tone-hosting
requirement derives the overt pronoun from the minimal-pronoun inventory.

## References

* [allotey-2021]
* [landau-2013]
* [landau-2004]
* [szabolcsi-2009]
* [hornstein-1999]
* [satik-2019]
* [karttunen-1971]
* [noonan-2007]
-/

namespace Allotey2021

open Minimalist.MinimalPronoun Control Ga Data.Examples

/-! ### Pronouns (Table 3) -/

/-- Only second and third person singular distinguish a subjective from an
    objective form. -/
theorem objective_distinct_iff (p : Person) (n : Number) :
    pronoun p n .objective ≠ pronoun p n .subjective ↔
      n = .singular ∧ (p = .second ∨ p = .third) := by
  cases p <;> cases n <;> decide

/-- The possessive always matches the subjective form. -/
theorem possessive_eq_subjective (p : Person) (n : Number) :
    pronoun p n .possessive = pronoun p n .subjective := by
  cases p <;> cases n <;> rfl

/-! ### OC by clause type -/

/-- The control profile of a Gã clause type, from its noncoreference flag. -/
def gaProfile (c : EmbeddedClauseType) : Profile Landau2013.Clause74 :=
  Landau2013.ofNoncoreferential (clauseProperties c).noncoreferentialSubject

/-- OC status is read off the complementizer's finiteness. -/
theorem obligatory_iff_not_isFinite (c : EmbeddedClauseType) :
    (gaProfile c).IsObligatory ↔ (clauseComplementizer c).isFinite = false := by
  cases c <;> decide

/-- A verb has a `ni`-frame exactly when it is a control verb. -/
theorem control_iff_selects_ni :
    ∀ v ∈ gaCTPs, .irrealisNi ∈ v.selects ↔ v.control ≠ .none := by
  decide

/-! ### Table 2 -/

/-- The rows of Table 2: [landau-2013]'s OC criteria and the paper's further
    properties of the overt pronoun. -/
inductive Table2Row where
  | cCommandedByAntecedent
  | longDistanceAntecedent
  | sloppyOnly
  | boundVariable
  | hasPhiFeatures
  | obligatoryDeSe
  | subjectControl
  | objectControl
  deriving DecidableEq, Repr

/-- Table 2's overt-pronoun column, identical to its PRO column. -/
def overtPronoun (r : Table2Row) : Bool := r != .longDistanceAntecedent

/-- The antecedence and reading rows are what the `ni`-clause profile admits
    under [landau-2013]'s signature: nothing. -/
theorem signature_rows :
    (overtPronoun .cCommandedByAntecedent ↔
      Diagnostic.nonCCommandingControl ∉ (gaProfile .irrealisNi).admits) ∧
    (overtPronoun .longDistanceAntecedent ↔
      Diagnostic.longDistanceControl ∈ (gaProfile .irrealisNi).admits) ∧
    (overtPronoun .sloppyOnly ↔ Diagnostic.strictEllipsis ∉ (gaProfile .irrealisNi).admits) ∧
    (overtPronoun .boundVariable ↔
      Diagnostic.strictUnderOnly ∉ (gaProfile .irrealisNi).admits) := by
  decide

/-- The two control rows are the verb inventory. -/
theorem control_rows :
    (overtPronoun .subjectControl ↔ ∃ v ∈ gaCTPs, v.control = .subjectControl) ∧
    (overtPronoun .objectControl ↔ ∃ v ∈ gaCTPs, v.control = .objectControl) := by
  decide

/-- The controlled form φ-covaries with its controller (exx 37–39), unlike
    [satik-2019]'s form-invariant Ewe *yè*. -/
theorem controlled_form_covaries :
    overtPronoun .hasPhiFeatures ↔
      subjectProclitic .second .singular ≠ subjectProclitic .second .plural := by
  decide

/-! ### Minimal-pronoun inventory -/

/-- Gã vocabulary items for minimal pronouns: no context-specific item, so the
    elsewhere pronoun realizes every context. -/
def gaInventory : MinPronInventory PronForm where
  items := []
  elsewhere := .pronoun

/-! ### Rows -/

/-- The Fragment entry for a row's matrix verb. -/
def ctpOf (row : LinguisticExample) : Option CTP :=
  (row.feature? "verb").bind λ v ↦ gaCTPs.find? (·.form = v)

/-- The clause type a complementizer feature names. -/
def clauseOf : String → Option EmbeddedClauseType
  | "ni" => some .irrealisNi
  | "ake" => some .finiteAke
  | "keji" => some .finiteKeji
  | _ => none

/-- The clause type of a row: its complement's, or the finite type for a
    matrix clause the paper labels finite. -/
def clauseTypeOf (row : LinguisticExample) : Option EmbeddedClauseType :=
  match row.feature? "complementizer", row.feature? "clauseType" with
  | some c, _ => clauseOf c
  | none, some "finite" => some .finiteAke
  | _, _ => none

/-- The complementizer inside an alternative form. -/
def clauseOfForm (s : String) : Option EmbeddedClauseType :=
  if " ni ".toList <:+: s.toList then some .irrealisNi
  else if " akɛ ".toList <:+: s.toList then some .finiteAke
  else if " kɛji ".toList <:+: s.toList then some .finiteKeji
  else none

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
      row.feature? "clauseContext" = none → row.judgment = .unacceptable := by
  decide +kernel

/-- Complementizer selection (exx 104–106), over each row and its alternatives:
    grammatical exactly when the Fragment records the frame for the verb. -/
theorem c_selection_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "cSelection" →
      ∀ v ∈ ctpOf row,
        (∀ c ∈ clauseTypeOf row, (row.judgment = .acceptable ↔ c ∈ v.selects)) ∧
        ∀ alt ∈ row.alternatives, ∀ c ∈ clauseOfForm alt.1,
          (alt.2 = .acceptable ↔ c ∈ v.selects) := by
  decide +kernel

/-- Overt tense or aspect in the complement is grammatical exactly in the
    clause types with unrestricted TAM (exx 101, 111). -/
theorem tam_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ t ∈ row.feature? "embeddedTAM",
      t ≠ "none" → (row.judgment = .acceptable ↔ (clauseProperties c).unrestrictedTAM) := by
  decide +kernel

/-- Focus fronting (exx 107–108) and NPI licensing by matrix negation (exx
    116–117) follow the clause properties. -/
theorem focus_npi_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row,
      (row.feature? "diagnostic" = some "focus" →
        (row.judgment = .acceptable ↔ (clauseProperties c).focusFronting)) ∧
      (row.feature? "diagnostic" = some "npi" → row.feature? "negation" = some "matrix" →
        (row.judgment = .acceptable ↔ (clauseProperties c).npiTransparent)) := by
  decide +kernel

/-- Negation precedes the verb exactly in the irrealis clause (exx 121–122,
    124). -/
theorem negation_rows :
    ∀ row ∈ Examples.all, ∀ c ∈ clauseTypeOf row, ∀ p ∈ row.feature? "negationPosition",
      (p = "preverbal") = (clauseProperties c).preverbalNegation := by
  decide +kernel

/-- The embedded subject bears the irrealis high tone exactly in the `ni`-clause
    (exx 110–112, 118). -/
theorem subject_tone_rows :
    ∀ row ∈ Examples.all, row.judgment = .acceptable → ∀ c ∈ clauseTypeOf row,
      ∀ t ∈ row.feature? "subjectTone", (t = "high") = (c = .irrealisNi) := by
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
      ∀ v ∈ ctpOf row,
        (row.feature? "irrealisMarker" = some "absent" ↔ v.implicative = some .positive) := by
  decide +kernel

/-! ### Landau's scale -/

/-- Gã clause types on [landau-2004]'s finiteness scale — a scale position, not
    a mood claim. -/
def gaToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (clauseProperties c).unrestrictedTAM (clauseProperties c).independentTense

/-- No Gã clause type is a tensed-but-controlled F-subjunctive. -/
theorem ga_no_fSubjunctive (c : EmbeddedClauseType) : gaToLandau c ≠ .fSubjunctive := by
  cases c <;> decide

/-- The scale predicts the control facts at any Agr value: Gã has no
    φ-agreement (exx 79–81, 123) and lacks the one position that reads Agr. -/
theorem landau_predicts_control (c : EmbeddedClauseType) (agr : Bool) :
    (gaProfile c).IsObligatory ↔ (gaToLandau c).HasOC agr := by
  cases c <;> cases agr <;> decide

/-! ### CP strength -/

/-- A strong CP in [rizzi-1997]'s sense: focus features and independent tense. -/
def StrongCP (c : EmbeddedClauseType) : Prop :=
  (clauseProperties c).focusFronting ∧ (clauseProperties c).independentTense

instance : DecidablePred StrongCP :=
  λ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- `akɛ` and `kɛji` head strong CPs, `ni` a weak one. -/
theorem strongCP_iff_isFinite (c : EmbeddedClauseType) :
    StrongCP c ↔ (clauseComplementizer c).isFinite := by
  cases c <;> decide

/-- Long-distance Agree ([szabolcsi-2009]) reaches the embedded subject across
    the weak CP only: the controlled clauses are the weak ones, and they are
    the NPI-transparent ones. -/
theorem weakCP_iff_obligatory (c : EmbeddedClauseType) :
    ¬ StrongCP c ↔ (gaProfile c).IsObligatory ∧ (clauseProperties c).npiTransparent := by
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

/-- Where the irrealis marker is realized: high tone on the subject, high tone
    on the verb, the vowel segment *a*. -/
structure IrrealisRealization where
  subjectTone : Bool
  verbTone : Bool
  vowelSegment : Bool
  deriving DecidableEq, Repr

/-- Table 4. -/
def irrealisRealization : IrrealisContext → IrrealisRealization
  | .subjunctive => ⟨true, true, true⟩
  | .imperative => ⟨true, true, true⟩
  | .conditional => ⟨false, false, true⟩
  | .future => ⟨false, false, true⟩
  | .embeddedControl => ⟨true, false, false⟩

/-- The context a row's `clauseContext` names. -/
def contextOf : String → Option IrrealisContext
  | "subjunctive" => some .subjunctive
  | "imperative" => some .imperative
  | "conditional" => some .conditional
  | "future" => some .future
  | "control" => some .embeddedControl
  | _ => none

/-- Each tone or segment a grammatical row reports is the table's value for its
    context (exx 85–86, 93–94, 96–97, 100–103). -/
theorem table4_rows :
    ∀ row ∈ Examples.all, row.judgment = .acceptable →
      ∀ ctx ∈ (row.feature? "clauseContext").bind contextOf,
        (∀ t ∈ row.feature? "subjectTone", t ≠ "none" →
          (t = "high") = (irrealisRealization ctx).subjectTone) ∧
        (∀ t ∈ row.feature? "verbTone", (t = "high") = (irrealisRealization ctx).verbTone) ∧
        ∀ v ∈ row.feature? "irrealisVowel",
          (v = "present") = (irrealisRealization ctx).vowelSegment := by
  decide +kernel

/-- The embedded-control realization is unique among the five contexts; in
    particular it lacks the subjunctive's doubled high tone (ex 88). -/
theorem control_realization_unique (c : IrrealisContext) :
    irrealisRealization c = irrealisRealization .embeddedControl → c = .embeddedControl := by
  cases c <;> decide

/-! ### Deriving the overt pronoun -/

/-- A tonal exponent needs a segmental host; the null form has none. -/
def hostsTone : PronForm → Bool
  | .null => false
  | .pronoun => true
  | .reflexive => true

/-- The controlled-subject form must host the obligatory irrealis tone of
    Table 4's embedded-control row. -/
def HostsControlTone (inv : MinPronInventory PronForm) : Prop :=
  (irrealisRealization .embeddedControl).subjectTone = true → hostsTone inv.controlForm = true

/-- Null PRO is impossible in Gã: a null controlled-subject form cannot host
    the irrealis tone. -/
theorem null_pro_impossible (inv : MinPronInventory PronForm) (h : inv.controlForm = .null) :
    ¬ HostsControlTone inv :=
  λ hc ↦ by simpa [hostsTone, h] using hc rfl

/-- The Gã inventory meets the tone-hosting requirement. -/
theorem ga_hostsControlTone : HostsControlTone gaInventory := λ _ ↦ rfl

/-- Controlled subjects surface as overt proclitics. -/
theorem ga_overt_pro : gaInventory.controlForm = .pronoun := rfl

/-- Overt PRO and no *pro*-drop: Gã instantiates the implicational universal. -/
theorem ga_satisfies_universal : gaInventory.OvertPROUniversal Ga.allowsProDrop := λ _ ↦ rfl

/-- Ex 53 witnesses the *de se* row of Table 2: infelicitous in its context. -/
theorem deSe_witness :
    ∃ row ∈ Examples.all, row.feature? "diagnostic" = some "deSe" ∧
      row.judgment = .questionable := by
  decide +kernel

/-! ### Typological placement -/

/-- Gã complements in [noonan-2007]'s typology; `.infinitive` is the paper's
    own term for the bare-root `ni`-complement. -/
def gaToNoonan : EmbeddedClauseType → Complement.Coding
  | .finiteAke => .indicative
  | .finiteKeji => .indicative
  | .irrealisNi => .infinitive

/-- The control complement is reduced in Noonan's terms. -/
theorem ni_complement_reduced : (gaToNoonan .irrealisNi).isReduced = true := rfl

end Allotey2021
