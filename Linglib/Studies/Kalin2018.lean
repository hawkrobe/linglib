module

public import Linglib.Data.Examples.Kalin2018
public import Linglib.Syntax.Case.Assigner

/-!
# Kalin (2018): Licensing and Differential Object Marking

This file formalizes [kalin-2018], which derives differential object marking from nominal
licensing rather than from object visibility, raising or differentiation. Two parameters
interact: which nominals require licensing, in Senaya only the specific ones, and where the
licensers are, every clause carrying one obligatory primary licenser that licenses the closest
nominal and secondary licensers that merge only when the derivation would otherwise crash, the
Licensing Economy Principle, (36); differential marking is the visible signature of a secondary
licenser activating. In Senaya the marking is verbal agreement rather than case: imperfective
Asp is a licenser and agrees with the subject as an S-suffix, leaving T to license a specific
object as an L-suffix, (39), while perfective Asp is not, so T agrees with the subject and a
specific object cannot be licensed at all, (37), the ban of (12). The substrate's licensing
algorithm reproduces the agreement data (8) to (12) and (38) row by row (`rows_agree`). The
perfective ban is the paper's argument against a no-licensing theory of case: a total
configurational assignment in the manner of [marantz-1991] still gives the perfective object an
accusative where licensing leaves it unlicensed
(`dependentCase_vs_licensing_diverge_on_perfective_object`). Licensing subsumes the Case Filter: a
nominal is licensed exactly when it bears a case (`isLicensed_iff_assignedCase_isSome`).

## Implementation notes

* `Licenser.assignedCase` is a case, so the two agreement suffixes are carried by the licensing
  heads: the S-suffix is agreement with `Asp`, the L-suffix agreement with `T`, and a licenser's
  case value is not read. Nominals carry only labels; word order and the position of agreement
  within the verbal complex are not modelled.

## References

* [kalin-2018]
* [marantz-1991]
* [preminger-2014]
-/

@[expose] public section

namespace Kalin2018

open Data.Examples Case Case.Licensing

/-! ### Senaya's licensers

Imperfective Asp licenses, agreeing as an S-suffix, and T licenses the next nominal as an
L-suffix; perfective Asp does not, so T is the only licenser, (37) and (39). -/

/-- In the imperfective, Asp is the primary licenser and T the secondary. -/
def imperfective : ClauseLicensers where
  primary := { kind := .primary, head := "Asp", assignedCase := .nom }
  secondaries := [{ kind := .secondary, head := "T", assignedCase := .nom }]

/-- In the perfective, T is the only licenser. -/
def perfective : ClauseLicensers where
  primary := { kind := .primary, head := "T", assignedCase := .nom }
  secondaries := []

/-- The agreement suffix a licensing head yields, an S-suffix from Asp and an L-suffix from T. -/
inductive Suffix
  | S
  | L
  deriving DecidableEq, Repr

/-- The suffix of a licensing outcome, none for an unlicensed nominal. -/
def outcomeSuffix : LicensingOutcome → Option Suffix
  | .byPrimary h _ | .bySecondary h _ => some (if h = "Asp" then .S else .L)
  | .byLexical _ | .unlicensed => none

/-- A transitive clause's nominals are the subject and an object that needs licensing exactly
when specific, (40) to (42). -/
def transitive (specific : Bool) : List LicensedNP :=
  [{ label := "subj", needsLicensing := true }, { label := "obj", needsLicensing := specific }]

/-! ### The agreement data (Section 2.1) -/

/-- A row carries the aspect's licensers, the object if any, the subject's and the object's
suffix, and the judgment. -/
structure Row where
  clause : ClauseLicensers
  object : Option Bool
  subjectSuffix : Suffix
  objectSuffix : Option Suffix
  grammatical : Bool

def suffixOf : String → Option (Option Suffix)
  | "S" => some (some .S)
  | "L" => some (some .L)
  | "none" => some none
  | _ => none

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let cl ← match e.feature? "aspect" with
    | some "imperfective" => some imperfective
    | some "perfective" => some perfective
    | _ => none
  let obj ← match e.feature? "object" with
    | some "specific" => some (some true)
    | some "nonspecific" => some (some false)
    | some "none" => some none
    | _ => none
  let s ← (e.feature? "subject_suffix").bind suffixOf
  let s ← s
  let o ← (e.feature? "object_suffix").bind suffixOf
  some ⟨cl, obj, s, o, e.judgment = .acceptable⟩

/-- The Senaya data, (8) to (12) and (38). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The nominals of a row are the subject alone, or the subject and its object. -/
def Row.nominals (r : Row) : List LicensedNP :=
  match r.object with
  | none => [{ label := "subj", needsLicensing := true }]
  | some specific => transitive specific

/-- Licensing reproduces the data: a sentence is grammatical exactly when every nominal is
licensed, so that a specific object in the perfective crashes; the subject's suffix is that of the
primary licenser, the S-suffix under imperfective Asp and the L-suffix under perfective T; and the
object carries the L-suffix exactly when the secondary licenser T licensed it, the marking a
nonspecific object never triggers. -/
theorem rows_agree :
    ∀ r ∈ rows,
      (r.grammatical = true ↔ ∀ x ∈ licenseNPs r.clause r.nominals, x.outcome.IsLicensed) ∧
      (getOutcomeOf "subj" (licenseNPs r.clause r.nominals)).bind outcomeSuffix =
        some r.subjectSuffix ∧
      (r.objectSuffix = some .L ↔
        getOutcomeOf "obj" (licenseNPs r.clause r.nominals) = some (.bySecondary "T" .nom)) := by
  decide

/-! ### Licensing against total case assignment -/

/-- On the perfective object the two accounts disagree: a total configurational assignment gives
it a structural accusative, licensing gives it nothing. -/
theorem perfective_object_verdicts :
    dependentAssigner .accusative (transitive true) "obj" = some (.assigned .acc .structural) ∧
      kalinAssigner perfective (transitive true) "obj" = some .unassigned :=
  ⟨by decide, by decide⟩

/-- Licensing diverges from total configurational case assignment ([marantz-1991],
[preminger-2014]) exactly on the perfective object: dependent case never crashes, so a
no-licensing theory leaves the ban of (12) unexplained, whereas licensing derives it. -/
theorem dependentCase_vs_licensing_diverge_on_perfective_object :
    ¬ AgreesOnCase (dependentAssigner .accusative) (kalinAssigner perfective)
      (transitive true) := by
  decide

/-! ### The Case Filter as a theorem of licensing -/

/-- Licensing subsumes the Case Filter: a nominal converges exactly when some licenser has valued
its [Case] feature, so that it bears a case, and the filter need not be stipulated alongside
licensing. -/
theorem isLicensed_iff_assignedCase_isSome (o : LicensingOutcome) :
    o.IsLicensed ↔ o.assignedCase.isSome := by
  cases o <;> simp [LicensingOutcome.assignedCase]

/-- A derivation converges under licensing iff every one of its nominals bears a case. -/
theorem all_isLicensed_iff_all_assignedCase_isSome (results : List LicensedResult) :
    (∀ r ∈ results, r.outcome.IsLicensed) ↔ ∀ r ∈ results, r.outcome.assignedCase.isSome := by
  simp only [isLicensed_iff_assignedCase_isSome]

end Kalin2018
