import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.NullSubject
import Linglib.Syntax.Control.Basic
import Linglib.Syntax.Control.CopyControl
import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Allotey (2021): Overt Pronouns of Infinitival Predicates of Gã

This file formalizes [allotey-2021]. Gã (Kwa; ISO gaa) shows obligatory
control over the embedded subject of irrealis `ni`-clauses, and the
controlled subject must be an overt subject proclitic — null PRO is
ungrammatical. Allotey argues that `ni`-clauses are non-finite and
irrealis-marked rather than subjunctive (against the descriptive
tradition of [dakubu-2004] and [campbell-2017]), that the overt pronoun
is a subject in Spec TP valued by Long Distance Agree from the matrix
controller ([szabolcsi-2009]) and lexicalized to host the obligatory
irrealis high tone, and that both the Movement Theory of Control
([hornstein-1999]) and [satik-2019]'s left-periphery-bound-pronoun
analysis fail on the Gã data.

Everything is derived from the fragment's clause typology:
`gaOCSignature` reads the noncoreference flag (OC in exactly the
`ni`-clause type), [landau-2004]'s finiteness scale predicts the
control facts (`landau_predicts_control`), the LDA mechanism is a
`Minimalist.Probe` search that crosses the weak C head `ni` and is
blocked by finite `akɛ`/`kɛji` (`lda_reaches_iff_oc`), the embedded
irrealis marker is suppressed under positive implicatives
(`irrealis_marker_iff_not_positive_implicative`), and the controlled
subject surfaces as the elsewhere form of a minimal-pronoun inventory
with no null vocabulary item (`ga_overt_pro`). The
verb-movement/negation-placement diagnostic (Allotey's fifth
non-finiteness argument, after [pollock-1989]) is not formalized: the
raising argument needs phrase-structure substrate, and the finiteness
split it diagnoses is already carried by the clause typology.

## References

* [D. Allotey, *Overt Pronouns of Infinitival Predicates of Gã*][allotey-2021]
-/

namespace Allotey2021

open Minimalist.MinimalPronoun
open Control
open NullSubject (ProDropProfile)
open Ga

/-! ### OC diagnostics

The OC signature is derived from the fragment's
`clauseProperties.noncoreferentialSubject` via
`OCSignature.ofNoncoreferential` (the same derivation as
`Ostrove2026.smpmOCSignature`): a clause type that bars
noncoreferential embedded subjects forces the full [landau-2013]
signature, and only `irrealisNi` does. -/

/-- The OC signature of a Gã clause type, from its noncoreference flag. -/
def gaOCSignature (c : EmbeddedClauseType) : OCSignature :=
  .ofNoncoreferential (clauseProperties c).noncoreferentialSubject

/-- The clause type determines OC, regardless of the verb's own control
    type. -/
theorem oc_determined_by_clause_type (c : CTP) :
    (gaOCSignature c.selects).isOC = !(clauseComplementizer c.selects).isFinite := by
  cases h : c.selects <;> rfl

/-! ### The irrealis marker under implicative verbs

§5.2.3: the embedded irrealis marker `á` is suppressed under positive
implicatives ([karttunen-1971]) — their complements are entailed
realized — and present otherwise, including under negative-implicative
`hiɛ-kpa-nɔ` 'forget', whose complement is entailed unrealized. -/

/-- Attested presence of the embedded irrealis marker per verb
    (exx 89a–d, 102–103). -/
def irrealisMarkerData : List (CTP × Bool) :=
  [(kai, false), (nye, false), (kpleno, true), (kpang, true), (hiekpano, true)]

/-- The marker appears exactly on the complements of
    non-positive-implicative verbs. -/
theorem irrealis_marker_iff_not_positive_implicative :
    ∀ p ∈ irrealisMarkerData, p.2 = !p.1.positiveImplicative := by decide

/-! ### Landau bridge

`ni`-clauses are C-subjunctives on [landau-2004]'s finiteness scale;
`akɛ`/`kɛji`-clauses are fully finite. Gã has no F-subjunctive — no
tensed-but-controlled clause class — so the entire control system rides
on the single finiteness bit: OC status, LDA reachability, and Agr are
each `isFinite` up to negation. Contrast SMPM
(`Studies/Ostrove2026.lean`), whose tensed subjunctives pull TAM
restriction and noncoreference apart. -/

def gaToLandau : EmbeddedClauseType → Control.ClauseClass
  | .irrealisNi => .cSubjunctive
  | .finiteAke  => .finite
  | .finiteKeji => .finite

/-- Gã Agr status: `irrealisNi` is `[−Agr]` — its proclitic realizes a
    minimal pronoun, not independent agreement ([landau-2015]). -/
def gaAgr (c : EmbeddedClauseType) : Bool :=
  (clauseProperties c).finiteComplementizer

/-- The Landau classification predicts the Gã control facts. -/
theorem landau_predicts_control (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = (gaToLandau c).hasOCWithAgr (gaAgr c) := by
  cases c <;> rfl

/-! ### Long-Distance Agree

The matrix φ-probe values the embedded minimal pronoun across the weak
C head `ni` ([szabolcsi-2009]); the finite complementizers head strong
CPs (exx 107–109) and block the search. Run on the `Minimalist.Probe`
kernel: a blocking C is a visible-but-inactive goal
(`Probe.agree_eq_none_of_inactive`), as in `Studies/Halpert2019.lean`. -/

/-- Whether a complementizer blocks LDA: the strong-CP (finite) ones do. -/
def _root_.Ga.Complementizer.blocksLDA (c : Complementizer) : Bool :=
  c.isFinite

/-- The matrix probe's search space, in structural order: the C head,
    then the embedded subject pronoun. -/
inductive LDAGoal where
  | complementizer
  | embeddedSubject
  deriving DecidableEq, Repr

/-- The matrix φ-probe into a `c`-headed embedded clause. -/
def ldaProbe (c : Complementizer) : Minimalist.Probe LDAGoal where
  vis
    | .complementizer => c.blocksLDA
    | .embeddedSubject => true
  act
    | .complementizer => false
    | .embeddedSubject => true

/-- LDA reaches the embedded subject of a `c`-headed clause. -/
def ldaReaches (c : Complementizer) : Bool :=
  (ldaProbe c).agree [.complementizer, .embeddedSubject]
    == some .embeddedSubject

/-- LDA crosses `ni` and is blocked by `akɛ`/`kɛji`. -/
theorem ldaReaches_eq_not_isFinite (c : Complementizer) :
    ldaReaches c = !c.isFinite := by
  cases c <;> rfl

/-- The probe reaches the embedded subject in exactly the OC clause
    types. -/
theorem lda_reaches_iff_oc (c : EmbeddedClauseType) :
    ldaReaches (clauseComplementizer c) = (gaOCSignature c).isOC := by
  cases c <;> rfl

/-! ### Against the Movement Theory of Control

§3.6.2: under movement ([hornstein-1999]) the pronounced embedded
element is a copy of the matrix DP, predicting an embedded lexical DP
where Gã allows only a pronoun (exx 42b, 64) — so control is
base-generated (refuting movement is free:
`Derivation.eq_supportedBy_of_predicts` says the supported derivation
is unique). The pole `Ostrove2026.smpm_supports_basegeneration`
reaches via exempt anaphors. -/

/-- Gã forbids embedded lexical-DP copies (exx 42b, 64). -/
def gaEmbeddedLexicalCopyAvailable : Bool := false

/-- The derivation the lexical-copy observation supports. -/
def gaControlDerivation : Derivation :=
  Derivation.supportedBy .embeddedLexicalCopy gaEmbeddedLexicalCopyAvailable

theorem ga_supports_basegeneration :
    gaControlDerivation = .baseGeneration := rfl

/-! ### Minimal pronoun inventory

Gã lacks a null vocabulary item for controlled subjects, so the
elsewhere (pronoun) item applies: PRO surfaces as the ordinary subject
proclitic. -/

open PronForm

/-- Gã vocabulary items: reflexive when locally bound, pronoun
    elsewhere. -/
def gaInventory : MinPronInventory PronForm where
  items := [ ⟨.locallyBound, .reflexive⟩ ]
  elsewhere := .pronoun

/-- Controlled subjects surface as overt proclitics — the central
    empirical observation. -/
theorem ga_overt_pro :
    gaInventory.controlForm = .pronoun := rfl

theorem ga_has_reflexive :
    gaInventory.realize .locallyBound = .reflexive := rfl

/-! ### Pro-drop / overt-PRO universal -/

/-- Gã profile: non-*pro*-drop with overt PRO. -/
def gaProfile : ProDropProfile :=
  { allowsProDrop := Ga.allowsProDrop
  , hasOvertPRO   := decide gaInventory.hasOvertPRO }

theorem ga_satisfies_universal : gaProfile.Satisfies := by decide

end Allotey2021
