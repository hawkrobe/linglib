/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Syntax.Control.Tier
import Linglib.Syntax.Control.Clause
import Linglib.Syntax.Control.Dependency
import Linglib.Syntax.Control.Signature
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Features.Complementation

/-!
# Allotey (2021): Overt Pronouns of Infinitival Predicates of Gã

Formalizes [allotey-2021]: obligatory control into Gã irrealis
`ni`-clauses requires an overt subject proclitic — null PRO is
ungrammatical. The controlled clause is non-finite irrealis, not
subjunctive (against [dakubu-2004], [campbell-2017], [korsah-2017]);
the pronoun is a Spec-TP subject valued by Long Distance Agree across
the weak C head `ni` ([szabolcsi-2009], [rizzi-1997]) and pronounced to
host the obligatory irrealis high tone. The Movement Theory of Control
([hornstein-1999]) does not extend to Gã, and [satik-2019]'s
left-periphery-bound pronoun only partly does. The
verb-movement/negation diagnostics (§§5.5.5, 6.2, after [pollock-1989])
need phrase-structure substrate and are not formalized.

## References

* [D. Allotey, *Overt Pronouns of Infinitival Predicates of Gã*][allotey-2021]
-/

namespace Allotey2021

open Minimalist Minimalist.MinimalPronoun Control Ga

/-! ### OC by clause type -/

/-- The control signature of a Gã clause type, from its noncoreference
    flag (the derivation `Ostrove2026.smpmSignature` also uses). -/
def gaSignature (c : EmbeddedClauseType) : Signature :=
  .ofNoncoreferential (clauseProperties c).noncoreferentialSubject

/-- OC status is read off the complementizer's finiteness. -/
theorem obligatory_iff_not_isFinite (c : EmbeddedClauseType) :
    (gaSignature c).Obligatory ↔ (clauseComplementizer c).isFinite = false := by
  cases c <;> decide

/-- A verb has a `ni`-frame exactly when it is a control verb (§§3.4–3.5,
    5.5.1). -/
theorem control_iff_selects_ni :
    ∀ v ∈ gaCTPs, .irrealisNi ∈ v.selects ↔ v.control ≠ .none := by
  decide

/-! ### Table 2: the overt pronoun has the OC signature -/

/-- The eight rows of [allotey-2021]'s Table 2 ([landau-2013]'s OC
    criteria, §§3.3–3.4). -/
inductive Table2Row where
  /-- Must be c-commanded by its antecedent (exx 45–46) -/
  | cCommandedByAntecedent
  /-- Allows a long-distance antecedent (exx 47–49) -/
  | longDistanceAntecedent
  /-- Sloppy reading only under ellipsis (exx 50–52) -/
  | sloppyOnly
  /-- Interpreted as a bound variable -/
  | boundVariable
  /-- Bears φ-features -/
  | hasPhiFeatures
  /-- Must be read *de se* (ex 53; [chierchia-1990]'s diagnostic) -/
  | obligatoryDeSe
  /-- Occurs under subject control (exx 34–43) -/
  | subjectControl
  /-- Occurs under object control (exx 54–59) -/
  | objectControl
  deriving DecidableEq, Repr

/-- The Table 2 column predicted by a control signature, a tier, and a
    control-verb inventory: the antecedence and reading rows are the
    criteria the signature excludes (`Signature.admits`); *de se* is a
    tier property, not signature content ([landau-2013] §1.3;
    [chierchia-1990]) — the attitude-tier reading in the paper's
    subject-control test configuration (ex 53; communicative object
    control would give *de te* instead); φ-covariance is feature
    transmission under binding; the two control rows read the
    inventory. -/
def predictedColumn (sig : Signature) (tier : Tier) (verbs : List CTP) :
    Table2Row → Bool
  | .cCommandedByAntecedent =>
      !decide (Signature.Criterion.nonCCommandingControl ∈ sig.admits)
  | .longDistanceAntecedent =>
      decide (Signature.Criterion.longDistanceControl ∈ sig.admits)
  | .sloppyOnly => !decide (Signature.Criterion.strictEllipsis ∈ sig.admits)
  | .boundVariable => !decide (Signature.Criterion.strictUnderOnly ∈ sig.admits)
  | .hasPhiFeatures         => sig.boundVariable
  | .obligatoryDeSe         => tier.isAttitude
  | .subjectControl         => verbs.any (·.control == .subjectControl)
  | .objectControl          => verbs.any (·.control == .objectControl)

/-- Table 2's observed overt-pronoun column (§§3.3.1–3.3.7, 3.4). -/
def overtPronoun (d : Table2Row) : Bool :=
  d != .longDistanceAntecedent

/-- The observed column is what the `ni`-clause signature predicts over
    the attested inventory, on the logophoric tier of the attitude
    verbs the *de se* test uses (ex 53 'expect'). -/
theorem overt_pronoun_matches_pro :
    overtPronoun = predictedColumn (gaSignature .irrealisNi) .logophoric gaCTPs := by
  funext d; cases d <;> decide

/-! ### The irrealis marker across complement frames

Within the `ni`-frame the subject's irrealis tone is constant (exx 43,
89c–d, 100–103, 117a). Implicativity governs frame choice: an
affirmative positive implicative entails its complement realized and
alternates into a realis frame (exx 89a–b), where the marker is
impossible (§§5.2.3, 5.3.5). -/

/-- An attested complement configuration: matrix verb, complementizer
    (`none` for the bare frame of ex 89b), matrix polarity, marker. -/
structure MarkerDatum where
  verb : CTP
  comp : Option Complementizer
  matrixAffirmative : Bool
  markerPresent : Bool
  deriving DecidableEq, Repr

/-- Whether the datum's frame is the irrealis `ni`-clause. -/
def MarkerDatum.irrealisFrame (d : MarkerDatum) : Bool :=
  d.comp == some .ni

/-- The attested marker data (exx 89a–d, 100, 102–103, 117a). -/
def irrealisMarkerData : List MarkerDatum :=
  [ ⟨kai,      some .ake, true,  false⟩   -- 89a  realis 'remember that'
  , ⟨nye,      none,      true,  false⟩   -- 89b  bare realis complement
  , ⟨kpleno,   some .ni,  true,  true⟩    -- 89c  *mi/má
  , ⟨kpang,    some .ni,  true,  true⟩    -- 89d  *mi/má
  , ⟨tao,      some .ni,  true,  true⟩    -- 100  má (also exx 34, 88)
  , ⟨hiekpano, some .ni,  true,  true⟩    -- 102–103  ó, é
  , ⟨kai,      some .ni,  false, true⟩ ]  -- 117a é under matrix negation

/-- The marker tracks the clause frame, not the verb. -/
theorem marker_iff_irrealis_frame :
    ∀ d ∈ irrealisMarkerData, d.markerPresent = d.irrealisFrame := by
  decide

/-- A realis frame occurs only where the complement is entailed
    realized: under an affirmative positive implicative (§5.2.3). -/
theorem realis_frame_only_under_realization :
    ∀ d ∈ irrealisMarkerData, d.irrealisFrame = false →
      d.verb.implicative = some .positive ∧ d.matrixAffirmative = true := by
  decide

/-! ### Landau bridge -/

/-- Gã clause types on [landau-2004]'s finiteness scale, via
    `ClauseClass.ofFiniteness` — a scale position, not a mood claim:
    §5.2 argues these clauses are not subjunctives. -/
def gaToLandau (c : EmbeddedClauseType) : Control.ClauseClass :=
  .ofFiniteness (clauseProperties c).unrestrictedTAM
    (clauseProperties c).independentTense

/-- No Gã clause type is a tensed-but-controlled F-subjunctive
    (contrast `Studies/Ostrove2026.lean`). -/
theorem ga_no_fSubjunctive (c : EmbeddedClauseType) :
    gaToLandau c ≠ .fSubjunctive := by
  cases c <;> decide

/-- The scale predicts the control facts for any Agr value: Gã lacks
    the one position that reads Agr, and has no φ-agreement anyway
    (§4.4, exx 79–81; §6.1). -/
theorem landau_predicts_control (c : EmbeddedClauseType) (agr : Bool) :
    (gaSignature c).Obligatory ↔ (gaToLandau c).HasOC agr := by
  cases c <;> cases agr <;> decide

/-! ### Long-Distance Agree and CP strength

`akɛ`/`kɛji` head strong CPs, `ni` a weak CP ([rizzi-1997], §5.5.1).
Blocking is a [keine-2020]-style horizon at the strong C head — clause
size, not intervention (contrast `Studies/Halpert2019.lean`, whose
blocking CP is a φ-goal). -/

/-- Projected heads of a `c`-headed complement: strong CPs project the
    full C-domain, the weak CP `ni` only Fin. -/
def clauseSpine (c : Complementizer) : List Cat :=
  if c.isFinite then [.V, .v, .T, .Fin, .Foc, .C] else [.V, .v, .T, .Fin]

/-- The matrix φ-probe: a T-probe whose horizon is the strong C head. -/
def ldaProbe : Probe.Profile := ⟨.T, some .C⟩

/-- LDA reaches into a `c`-headed complement. -/
def ldaReaches (c : Complementizer) : Bool :=
  ldaProbe.transparentToLabel (clauseSpine c)

/-- LDA crosses `ni` and is blocked by `akɛ`/`kɛji`. -/
theorem ldaReaches_eq_not_isFinite (c : Complementizer) :
    ldaReaches c = !c.isFinite := by
  cases c <;> rfl

/-- The probe reaches the embedded subject in exactly the OC clause types. -/
theorem ldaReaches_iff_obligatory (c : EmbeddedClauseType) :
    ldaReaches (clauseComplementizer c) = true ↔ (gaSignature c).Obligatory := by
  cases c <;> decide

/-- `ni` projects no focus field; the finite complementizers do
    (exx 107–108). -/
theorem ni_projects_no_focus :
    Cat.Foc ∉ clauseSpine .ni ∧ Cat.Foc ∈ clauseSpine .ake := by
  decide

/-- NPI licensing patterns with LDA (§5.5.3, exx 115–117). -/
theorem npi_patterns_with_lda (c : EmbeddedClauseType) :
    (clauseProperties c).npiTransparent = ldaReaches (clauseComplementizer c) := by
  cases c <;> rfl

/-! ### Against the rival derivations -/

/-- Gã forbids embedded lexical-DP copies (exx 42b, 64). -/
def gaEmbeddedLexicalCopyAvailable : Bool := false

/-- The occupants of ex 42b's two positions. -/
inductive Ex42Item where
  /-- the lexical matrix subject *Ameele* -/
  | ameele
  /-- the obligatory embedded proclitic -/
  | pronoun
  deriving DecidableEq, Repr

/-- Ex 42b's control dependency: matrix controller position `0` to
    embedded subject position `1`. -/
def ex42Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The attested occupants: lexical *Ameele* controls the obligatory
    proclitic — never a lexical copy (exx 42b, 64). -/
def ex42Occupant : Fin 2 → Ex42Item :=
  fun p => if p = 0 then .ameele else .pronoun

/-- Movement is token identity, and ex 42b's occupants differ across
    the dependency — the Movement Theory of Control ([hornstein-1999])
    is refuted on the Gã configuration (§3.6.2): control is
    base-generated. -/
theorem ga_refutes_movement : ¬ Shares ex42Occupant ex42Dependency :=
  not_shares_of_mismatch (P := (· = .ameele)) rfl rfl (by decide)

/-- The lexical-copy ban is what [landau-2024]'s (72) predicts: the
    ex 42b/64 matrix verb *kai* is an implicative — nonattitude,
    predicative tier — so its complement is property-denoting and a
    lexical subject is a type mismatch. (The attitude verbs' `ni`-frame
    aligns too: *kplɛnɔ* 'agree' takes the lexical-subject subjunctive
    of ex 105.) -/
theorem lexical_copy_ban_predicted :
    gaEmbeddedLexicalCopyAvailable
      = decide (LicensesLexicalSubject Tier.predicative.complementDenotation) := rfl

/-- The controlled form φ-covaries with its controller (exx 37–39),
    unlike [satik-2019]'s form-invariant Ewe *yè* (§3.6.3). -/
theorem controlled_form_covaries :
    subjectProclitic .first .singular ≠ subjectProclitic .second .singular := by
  decide

/-! ### Table 4: the irrealis marker's realization sites -/

/-- The five `[−REALIS]` contexts of Table 4. -/
inductive IrrealisContext where
  | subjunctive
  | imperative
  | conditional
  | future
  | embeddedControl
  deriving DecidableEq, Repr

/-- Realization sites of the irrealis marker: high tone on the subject,
    high tone on the verb, the vowel segment `a`. -/
structure IrrealisRealization where
  subjectTone : Bool
  verbTone : Bool
  vowelSegment : Bool
  deriving DecidableEq, Repr

/-- Table 4 (exx 85–87 subjunctive; 93–94 imperative; 97 conditional;
    95–96 future; 100–103 embedded control). -/
def irrealisRealization : IrrealisContext → IrrealisRealization
  | .subjunctive     => ⟨true,  true,  true⟩
  | .imperative      => ⟨true,  true,  true⟩
  | .conditional     => ⟨false, false, true⟩
  | .future          => ⟨false, false, true⟩
  | .embeddedControl => ⟨true,  false, false⟩

/-- The embedded-control realization profile is unique among the five
    irrealis contexts. -/
theorem control_realization_unique (c : IrrealisContext) :
    irrealisRealization c = irrealisRealization .embeddedControl →
      c = .embeddedControl := by
  cases c <;> decide

/-- The control clause lacks the subjunctive's doubled realization
    (§5.2.2, ex 88: *ná). -/
theorem control_not_subjunctive :
    irrealisRealization .embeddedControl ≠ irrealisRealization .subjunctive := by
  decide

/-! ### Deriving overt PRO

The control clause obligatorily realizes the irrealis tone on its
subject, and a tone needs a segmental host (pp. 28, 45) — so the
controlled subject cannot be silent. -/

/-- A tonal exponent needs a segmental host; the null form has none. -/
def _root_.Minimalist.MinimalPronoun.PronForm.hostsTone : PronForm → Bool
  | .null      => false
  | .pronoun   => true
  | .reflexive => true

/-- The controlled-subject form must host the obligatory irrealis tone
    (Table 4's embedded-control row). -/
def HostsControlTone (inv : MinPronInventory PronForm) : Prop :=
  (irrealisRealization .embeddedControl).subjectTone = true →
    inv.controlForm.hostsTone = true

/-- Null PRO is impossible in Gã: a null controlled-subject form cannot
    host the irrealis tone. -/
theorem null_pro_impossible (inv : MinPronInventory PronForm)
    (h : inv.controlForm = .null) : ¬ HostsControlTone inv :=
  fun hc => by simpa [PronForm.hostsTone, h] using hc rfl

/-! ### Minimal pronoun inventory -/

/-- Gã vocabulary items: reflexive when locally bound, pronoun
    elsewhere; no null item. (The reflexive item is required by
    [ostrove-2026]'s syncretism row for Gã; UNVERIFIED — [allotey-2021]
    never discusses Gã reflexives, check [campbell-2017].) -/
def gaInventory : MinPronInventory PronForm where
  items := [⟨.locallyBound, .reflexive⟩]
  elsewhere := .pronoun

/-- The Gã inventory meets the tone-hosting requirement. -/
theorem ga_hostsControlTone : HostsControlTone gaInventory :=
  fun _ => rfl

/-- Controlled subjects surface as overt proclitics: no null item
    exists, so the elsewhere pronoun applies. -/
theorem ga_overt_pro : gaInventory.controlForm = .pronoun := rfl

/-- The locally-bound context realizes the reflexive item. -/
theorem ga_has_reflexive :
    gaInventory.realize .locallyBound = .reflexive := rfl

/-! ### Typological placement -/

/-- Gã complements in [noonan-2007]'s typology; `.infinitive` is §5.6's
    own term for the bare-root `ni`-complement. -/
def gaToNoonan : EmbeddedClauseType → NoonanCompType
  | .finiteAke  => .indicative
  | .finiteKeji => .indicative
  | .irrealisNi => .infinitive

/-- The control complement is reduced (deranked) in Noonan's terms. -/
theorem ni_complement_reduced :
    (gaToNoonan .irrealisNi).isReduced = true := rfl

/-- Gã instantiates [ostrove-2026]'s universal: overt PRO and no
    *pro*-drop. -/
theorem ga_satisfies_universal :
    gaInventory.OvertPROUniversal Ga.allowsProDrop :=
  fun _ => rfl

end Allotey2021
