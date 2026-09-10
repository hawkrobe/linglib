import Linglib.Data.Examples.Erlewine2016
import Linglib.Features.Person.Basic
import Linglib.Fragments.Mayan.Params
import Linglib.Phonology.OptimalityTheory.Tableau
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erlewine (2016): Anti-locality and Optimality in Kaqchikel Agent Focus

This file formalizes [erlewine-2016]'s account of Kaqchikel Agent Focus (AF), the verb form with
an AF suffix and no Set A agreement that a transitive subject takes under Ā-extraction. The
trigger is not subject extraction but movement that is too short: AF disappears when a preverbal
adverb (§3.1) or another preverbal operator (§3.2) intervenes, and long-distance extraction puts
it on the embedded verb alone. Spec-to-Spec Anti-Locality (§4) bans Ā-movement from the
specifier of XP that crosses no maximal projection but XP, crossing being dominance of the origin
but not of the landing site. Kaqchikel T carries an obligatory Set B probe and an optional Set A
probe with the EPP property (§4.1); a constraint that every argument be cross-referenced makes
the transitive subject move to Spec,TP, from where its next step to Spec,CP is too short, while
an intransitive subject stays in situ, which derives the ergative alignment of agreement (§4.2).
Among the competing derivations of one numeration (§5.1) the AF derivation skips Spec,TP at the
cost of a cross-referencing violation, so anti-locality outranks cross-referencing, and the AF
suffix realizes an argument left un-cross-referenced (§4.1). Set B on an AF verb targets the
participant argument ([stiebels-2006], [preminger-2011]), and when both arguments are
participants the full-agreement transitive returns even under subject extraction (§5.2), which a
top-ranked constraint cross-referencing participants derives and a last-resort account, such as
[coon-mateo-pedro-preminger-2014]'s for Q'anjob'al, cannot (§5.3); evaluation must see the whole
clause, since at TP the anti-locality violation is not yet visible. Rerankings give the typology
of §6.1: Popti', whose Set B targets only the object, keeps the full form whenever the subject is
a participant; Akatek ranks anti-locality highest and uses AF regardless of person; Ch'ol ranks
cross-referencing highest and has no AF.

## Implementation notes

* A clause is the spine VP, vP, TP and the layers above TP, an adverb's projection
  ([cinque-1999]), the CPs of a split periphery ([rizzi-1997]) and the topic projection (§4.4),
  indexed from the bottom. A position lies within the projection of its index, so the crossing
  set of a step is the interval of projections from the origin's up to but excluding the landing
  site's. Long-distance extraction is the embedded clause's competition, since movement stops at
  the embedded Spec,CP (§4.3).
* A candidate is a choice of the optional Set A probe and of the Set B probe's target; the two
  probes cannot share a goal, and the Set A probe, which moves its goal, sees only the subject at
  the vP edge. Popti' and Akatek restrict Set B to the object.
* The grammars are the rankings of §6.1 over the three constraints of §5; the constraint
  preferring plural targets that the paper mentions in a footnote is not modelled.
* Example numbers follow the lingbuzz preprint, the version consulted.
* The examples are `Data.Examples.Erlewine2016`.

## References

* [erlewine-2016]
* [abels-2003]
* [cinque-1999]
* [rizzi-1997]
* [stiebels-2006]
* [preminger-2011]
* [coon-mateo-pedro-preminger-2014]
* [prince-smolensky-1993]
-/

namespace Erlewine2016

open Constraints OptimalityTheory Data.Examples Erlewine2016.Examples

/-- The arguments of a verb. -/
inductive Arg
  | subj
  | obj
  deriving DecidableEq, Repr

/-- A layer of the clause above TP: an adverb's projection, a CP of the periphery, or the topic
projection. -/
inductive Layer
  | advP
  | cP
  | topP
  deriving DecidableEq, Repr

/-- A clause and its extraction: whether it is transitive, the layers above TP from the bottom,
the extracted argument with the index of the layer it lands in, and the person of each
argument. -/
structure Input where
  transitive : Bool
  layers : List Layer
  extracted : Option (Arg × ℕ)
  subj : Person
  obj : Person
  deriving DecidableEq, Repr

/-- The arguments of a transitive or intransitive clause. -/
def argsOf (transitive : Bool) : List Arg := if transitive then [.subj, .obj] else [.subj]

/-- The arguments of the clause. -/
def Input.args (i : Input) : List Arg := argsOf i.transitive

/-- The person of an argument. -/
def Input.person (i : Input) : Arg → Person
  | .subj => i.subj
  | .obj => i.obj

/-! ### The spine and anti-locality -/

/-- The index of TP in the spine VP, vP, TP, layers. -/
def tP : ℕ := 2

/-- The index of the `k`th layer above TP. -/
def layerIndex (k : ℕ) : ℕ := 3 + k

/-- The base position of an argument: Spec,vP for the subject, the complement of V for the
object (§4.1). -/
def Arg.base : Arg → ℕ
  | .subj => 1
  | .obj => 0

/-- The projections a step crosses, (43): those dominating the origin, which lies within
projection `α`, but not the landing site, the specifier of projection `β`. -/
def crosses (α β : ℕ) : Finset ℕ := Finset.Ico α β

/-- Spec-to-Spec Anti-Locality, (42): a step is too close when it crosses no maximal projection
other than the one it leaves. -/
def TooClose (α β : ℕ) : Prop := ∀ γ ∈ crosses α β, γ = α

instance (α β : ℕ) : Decidable (TooClose α β) := by unfold TooClose; infer_instance

/-- An upward step is too close exactly when its landing site immediately dominates its
origin, the configuration of (44). -/
theorem tooClose_iff {α β : ℕ} (h : α < β) : TooClose α β ↔ β = α + 1 := by
  constructor
  · intro H
    by_contra hne
    have := H (α + 1) (by simp only [crosses, Finset.mem_Ico]; omega)
    omega
  · intro hβ γ hγ
    simp only [crosses, Finset.mem_Ico] at hγ
    omega

/-! ### Derivations and constraints -/

/-- A derivation of the clause (§5.1): whether T's optional Set A probe is used, moving the
subject to Spec,TP, and the argument its Set B probe targets. -/
structure Candidate where
  aProbe : Bool
  bTarget : Arg
  deriving DecidableEq, Repr

/-- The candidates of a numeration: the Set B target is an argument, the two probes cannot share
a goal, and where Set B is restricted to the object it targets the object. -/
def candidatesOf (transitive objectOnly : Bool) : List Candidate :=
  ([true, false].flatMap λ a => (argsOf transitive).map (⟨a, ·⟩)).filter λ c =>
    (c.aProbe → c.bTarget ≠ .subj) ∧ (objectOnly → transitive → c.bTarget = .obj)

/-- The candidates of a clause. -/
def candidates (i : Input) (objectOnly : Bool) : List Candidate :=
  candidatesOf i.transitive objectOnly

theorem candidates_ne_nil (i : Input) (o : Bool) : candidates i o ≠ [] := by
  unfold candidates; cases i.transitive <;> cases o <;> decide

/-- An argument is cross-referenced when the Set A probe targets it, the subject having moved to
Spec,TP, or the Set B probe does, (46). -/
def CrossRef (c : Candidate) (a : Arg) : Prop := (c.aProbe ∧ a = .subj) ∨ c.bTarget = a

instance (c : Candidate) (a : Arg) : Decidable (CrossRef c a) := by unfold CrossRef; infer_instance

/-- The position an extracted argument moves from: Spec,TP for a subject the Set A probe has
attracted, its base position otherwise. -/
def Candidate.origin (c : Candidate) : Arg → ℕ
  | .subj => if c.aProbe then tP else Arg.subj.base
  | .obj => Arg.obj.base

/-- Spec-to-Spec Anti-Locality as a violable constraint: one violation per step that is too
close. -/
def ssal (i : Input) : Constraint Candidate := λ c =>
  match i.extracted with
  | none => 0
  | some (a, k) => if TooClose (c.origin a) (layerIndex k) then 1 else 0

/-- XRef: one violation per argument not cross-referenced. -/
def xref (i : Input) : Constraint Candidate := λ c => (i.args.filter (¬ CrossRef c ·)).length

/-- XRef-Participant: one violation per participant argument not cross-referenced (§5.2). -/
def xrefP (i : Input) : Constraint Candidate := λ c =>
  (i.args.filter λ a => (i.person a).IsSAP ∧ ¬ CrossRef c a).length

/-- A grammar of §6.1: a ranking of the constraints and whether Set B is restricted to the
object. -/
structure Grammar where
  ranking : List (Input → Constraint Candidate)
  objectOnly : Bool

/-- The competition of a clause under a grammar. -/
def Grammar.tableau (g : Grammar) (i : Input) :=
  Tableau.ofRanking (candidates i g.objectOnly) (g.ranking.map (· i)) (candidates_ne_nil i _)

/-- Kaqchikel: XRef-Participant ≫ SSAL ≫ XRef, Set B free to target either argument. -/
def kaqchikel : Grammar := ⟨[xrefP, ssal, xref], false⟩

/-- Popti': the Kaqchikel ranking with Set B restricted to the object. -/
def popti : Grammar := ⟨[xrefP, ssal, xref], true⟩

/-- Akatek: SSAL above both cross-referencing constraints, Set B restricted to the object. -/
def akatek : Grammar := ⟨[ssal, xrefP, xref], true⟩

/-- A Mayan language without AF, Ch'ol: XRef ≫ SSAL. -/
def chol : Grammar := ⟨[xref, ssal], false⟩

/-! ### Realization -/

/-- (48): the AF suffix is realized when some argument is not cross-referenced. -/
def Candidate.AFSuffix (args : List Arg) (c : Candidate) : Prop := ∃ a ∈ args, ¬ CrossRef c a

instance (args : List Arg) (c : Candidate) : Decidable (c.AFSuffix args) := by
  unfold Candidate.AFSuffix; infer_instance

/-- The AF suffix marks a violation of XRef. -/
theorem afSuffix_iff_xref_pos (i : Input) (c : Candidate) :
    c.AFSuffix i.args ↔ 0 < xref i c := by
  simp [Candidate.AFSuffix, xref, List.length_pos_iff_exists_mem, List.mem_filter]

/-- The verb form of a derivation, Set A being realized only when the subject moved to
Spec,TP. -/
def Candidate.form (args : List Arg) (c : Candidate) : Mayan.VerbForm :=
  if c.AFSuffix args then .agentFocus else .transitive

/-- Among the candidates of a transitive clause, the AF form is exactly the absence of the Set
A probe: the derivation that skips Spec,TP loses Set A and gains the suffix. -/
theorem form_hasSetA (o : Bool) :
    ∀ c ∈ candidatesOf true o, (c.form (argsOf true)).hasSetA = c.aProbe := by
  cases o <;> decide

/-! ### The rows -/

/-- The clause types as named in the rows. -/
def clauseTable : List (String × Bool) := [("transitive", true), ("intransitive", false)]

/-- The layers above TP as named in the rows. -/
def layerTable : List (String × List Layer) :=
  [("CP", [.cP]), ("AdvP,CP", [.advP, .cP]), ("CP,CP", [.cP, .cP]), ("CP,TopP", [.cP, .topP])]

/-- The extracted argument as named in the rows. -/
def extractedTable : List (String × Option Arg) :=
  [("none", none), ("subject", some .subj), ("object", some .obj)]

/-- The persons as named in the rows. -/
def personTable : List (String × Person) := [("1", .first), ("2", .second), ("3", .third)]

/-- The verb forms as named in the rows: whether the AF suffix appears. -/
def verbTable : List (String × Bool) := [("AF", true), ("full", false)]

/-- The grammars by glottocode. -/
def grammarTable : List (String × Grammar) :=
  [("kaqc1270", kaqchikel), ("popt1235", popti), ("akat1248", akatek), ("chol1282", chol)]

/-- A row: the clause, its language's grammar, whether the attested form bears the AF suffix,
and the judgment. -/
structure Row where
  input : Input
  grammar : Grammar
  af : Bool
  judgment : Judgment

/-- A row from an example; landing layers count from one in the rows. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let transitive ← ex.parse? "clause" clauseTable
  let layers ← ex.parse? "layers" layerTable
  let extracted ← match ← ex.parse? "extracted" extractedTable with
    | none => pure none
    | some a => do pure (some (a, (← ex.nat? "landing") - 1))
  let subj ← ex.parse? "subject" personTable
  let grammar ← List.lookup ex.language grammarTable
  let af ← ex.parse? "verb" verbTable
  pure ⟨⟨transitive, layers, extracted, subj, (ex.parse? "object" personTable).getD .third⟩,
    grammar, af, ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The rows of all four languages. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The Kaqchikel rows. -/
def kaqchikelRows : List Row :=
  (Examples.all.filter (·.language = "kaqc1270")).filterMap Row.ofExample

/-- Every row: the attested form is grammatical exactly when an optimal derivation realizes
it. -/
theorem rows_optimal :
    ∀ r ∈ rows, r.judgment = .acceptable ↔
      ∃ c ∈ (r.grammar.tableau r.input).optimal, (c.AFSuffix r.input.args ↔ r.af = true) := by
  decide

/-- The generalization of §3: with at most one participant argument, AF is optimal in Kaqchikel
exactly when the subject moves to the layer immediately above TP. -/
theorem af_iff_immediately_preverbal :
    ∀ r ∈ kaqchikelRows, ¬ (r.input.subj.IsSAP ∧ r.input.obj.IsSAP) →
      ((∃ c ∈ (kaqchikel.tableau r.input).optimal, c.AFSuffix r.input.args) ↔
        r.input.extracted = some (.subj, 0)) := by
  decide

/-! ### The competitions of §5 and §6 -/

/-- Subject extraction to Spec,CP in a simple transitive clause. -/
def subjectExtraction (s o : Person) : Input := ⟨true, [.cP], some (.subj, 0), s, o⟩

/-- §5.1: without extraction, cross-referencing selects the derivation that moves the subject to
Spec,TP; this is also what an evaluation at TP would select before the anti-locality violation
of a later extraction is visible, the argument of §5.3 for evaluation at the clause. -/
theorem no_extraction_full (s o : Person) :
    (kaqchikel.tableau ⟨true, [.cP], none, s, o⟩).optimal = {⟨true, .obj⟩} := by
  cases s <;> cases o <;> decide

/-- §5.1: under subject extraction with two third-person arguments, both AF derivations beat
the derivation through Spec,TP, and the two constraints do not decide the Set B target. -/
theorem subject_extraction_af :
    (kaqchikel.tableau (subjectExtraction .third .third)).optimal =
      {⟨false, .subj⟩, ⟨false, .obj⟩} := by
  decide

/-- §5.2: a participant argument breaks the tie, Set B cross-referencing it. -/
theorem participant_breaks_tie :
    (kaqchikel.tableau (subjectExtraction .second .third)).optimal = {⟨false, .subj⟩} ∧
      (kaqchikel.tableau (subjectExtraction .third .second)).optimal = {⟨false, .obj⟩} := by
  decide

/-- §5.2: with two participant arguments the full-agreement transitive is optimal, the
anti-locality violation notwithstanding. -/
theorem participant_exception :
    (kaqchikel.tableau (subjectExtraction .first .second)).optimal = {⟨true, .obj⟩} := by
  decide

/-- §4.2: object extraction and intransitive subject extraction cross enough structure, and no
optimal derivation bears the AF suffix. -/
theorem no_af_without_short_step :
    (kaqchikel.tableau ⟨true, [.cP], some (.obj, 0), .third, .third⟩).optimal =
        {⟨true, .obj⟩} ∧
      ∀ c ∈ (kaqchikel.tableau ⟨false, [.cP], some (.subj, 0), .third, .third⟩).optimal,
        ¬ c.AFSuffix (argsOf false) := by
  decide

/-- §6.1: the typology of rerankings. Popti' keeps the full form when the subject is a
participant and uses AF when it is not; Akatek uses AF for a participant subject; Ch'ol keeps
the full form throughout. -/
theorem typology :
    (popti.tableau (subjectExtraction .second .third)).optimal = {⟨true, .obj⟩} ∧
      (popti.tableau (subjectExtraction .third .second)).optimal = {⟨false, .obj⟩} ∧
      (akatek.tableau (subjectExtraction .first .third)).optimal = {⟨false, .obj⟩} ∧
      (chol.tableau (subjectExtraction .third .second)).optimal = {⟨true, .obj⟩} := by
  decide

end Erlewine2016
