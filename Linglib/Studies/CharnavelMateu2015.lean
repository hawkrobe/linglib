import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Logophoricity
import Linglib.Features.Empathy
import Linglib.Features.Person.Decomposition
import Linglib.Fragments.Spanish.Clitics

/-!
# Charnavel and Mateu 2015: the clitic logophoric restriction

This file formalizes the reanalysis of the Romance clitic-cluster restriction in
[charnavel-mateu-2015]. Earlier work took the restriction on accusative clitics to be a binding
condition; a grammaticality experiment with French and Spanish speakers finds instead that what
degrades a cluster is the accusative clitic corefering with a logophoric center, whether or not
the antecedent c-commands it.

The account gives three logophoric centers — discourse participant, empathy locus, attitude
holder ([sells-1987], [kuno-1987]) — each a subset of a three-feature space, arranged so that
neighbours on the hierarchy share a feature and the two ends do not. Two centers in one domain
clash exactly when they share a feature, which makes the Person Case Constraint and the clitic
logophoric restriction one mechanism at two places on the hierarchy: a discourse participant with
an empathy locus, and an empathy locus with an attitude holder. A discourse participant with an
attitude holder is the one licit pair.

## Main definitions

* `LogoCenter`, `LogoFeature`, `LogoCenter.features` — the hierarchy and its feature subsets
* `Clash`, `Antilogophoric` — two centers sharing a feature, and a domain containing such a pair
* `dativeCenter`, `accusativeCenter` — the center a Spanish clitic realizes, from its person
* `Condition`, `predictsUngrammatical` — the experiment's crossed factors and the prediction

## Main results

* `not_clash_iff` — the only licit pair is the two ends of the hierarchy, which is what unifies
  the Person Case Constraint with the clitic logophoric restriction
* `c_command_irrelevant` — the prediction does not read c-command
* `spanish_le_lo_de_se_clash`, `spanish_le_me_clash`, `spanish_me_lo_de_se_licit` — the Spanish
  clusters, with each clitic's center read off its person feature

## References

* [charnavel-mateu-2015]
* [sells-1987]
* [kuno-1987]
-/

namespace CharnavelMateu2015

/-! ### The logophoric centers -/

/-- Three types of logophoric center, ordered by degree of perspective
    integration in the discourse (paper eq. 54: discourse participant >
    empathy locus > attitude holder). -/
inductive LogoCenter : Type where
  /-- Speaker / addressee — directly defining the discourse. -/
  | discourseParticipant
  /-- Event participant the speaker empathizes with (Kuno's empathy locus).
      In Romance, typically the 3rd-person dative clitic. -/
  | empathyLocus
  /-- Attitude holder whose thoughts/discourse are reported.
      In Romance, typically a 3rd-person accusative clitic read *de se*. -/
  | attitudeHolder
  deriving DecidableEq, Repr, Fintype

/-! ### The feature system -/

/-- The three abstract logophoric features. `B` expresses the
    speaker-component (shared by discourse participants and empathy loci);
    `C` expresses perspectival distance from the speaker (shared by empathy
    loci and attitude holders). -/
inductive LogoFeature : Type
  | A | B | C
  deriving DecidableEq, Repr, Fintype

/-- Feature decomposition (paper eq. 63). -/
def LogoCenter.features : LogoCenter → Finset LogoFeature
  | .discourseParticipant => {.A, .B}
  | .empathyLocus         => {.B, .C}
  | .attitudeHolder       => {.C}

/-! ### Antilogophoric clash -/

/-- Two centers clash iff their feature sets share at least one feature.
    Equivalent to "identical or adjacent on the hierarchy" (paper eq. 54). -/
def Clash (x y : LogoCenter) : Prop := (x.features ∩ y.features).Nonempty

instance (x y : LogoCenter) : Decidable (Clash x y) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- C&M's antilogophoric intervention (paper §3.5.2, generalising eq. 64):
    a configuration of logophoric centers in a single domain is
    antilogophoric iff some pair of distinct centers clash.

    Note: a single center never clashes with itself in this formulation —
    the "identical centers" case of (54) corresponds to multiple *positions*
    bearing the same center type, not the abstract type clashing with
    itself. We model the multi-position case with a `List`. -/
def Antilogophoric (centers : List LogoCenter) : Prop :=
  ∃ i j : Fin centers.length, i ≠ j ∧ Clash centers[i] centers[j]

instance (centers : List LogoCenter) : Decidable (Antilogophoric centers) :=
  inferInstanceAs (Decidable (∃ _ : Fin _, _))

/-- Two centers clash unless they are the two ends of the hierarchy: a discourse participant and
an attitude holder share no feature, and every other pair does. The Person Case Constraint (a
discourse participant with an empathy locus) and the clitic logophoric restriction (an empathy
locus with an attitude holder) are the two clashing neighbour pairs. -/
theorem not_clash_iff (x y : LogoCenter) :
    ¬ Clash x y ↔
      ((x = .discourseParticipant ∧ y = .attitudeHolder) ∨
        (x = .attitudeHolder ∧ y = .discourseParticipant)) := by
  cases x <;> cases y <;> decide

/-! ### The experiment's conditions -/

/-- A test condition in C&M's grammaticality experiment, parameterised by
    the three crossed factors (paper Table 1). The 9 conditions enumerate
    {c-command, no c-command} × {logophoric centre as antecedent, not} ×
    {3.dat dative clitic, 1/2.dat dative clitic}, dropping the "bound 3"
    sub-case (their condition 3) for which they collapse the same
    prediction as condition 1. -/
structure Condition where
  /-- Does the antecedent c-command the accusative clitic? -/
  cCommandingAntecedent : Bool
  /-- Is the antecedent a logophoric centre (attitude holder)? -/
  logoCenterAntecedent : Bool
  /-- Is the dative clitic a 3rd-person form (an empathy locus)? -/
  dative3rdPerson : Bool
  deriving DecidableEq, Repr

/-- C&M's hypothesis (paper §2.1): a sentence is ungrammatical iff the
    antecedent of the accusative clitic is a logophoric centre AND the
    dative clitic is 3rd person. C-command is **not** the relevant factor
    (contra Bhatt & Šimík). -/
def predictsUngrammatical (c : Condition) : Prop :=
  c.logoCenterAntecedent = true ∧ c.dative3rdPerson = true

instance (c : Condition) : Decidable (predictsUngrammatical c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The hypothesis does not read c-command, which is the experiment's finding: the conditions
that degraded were exactly those with a logophoric-center antecedent and a third-person dative,
whether or not the antecedent c-commanded the accusative clitic. -/
theorem c_command_irrelevant
    (logoCenter dative3rd : Bool) :
    predictsUngrammatical ⟨true, logoCenter, dative3rd⟩ ↔
    predictsUngrammatical ⟨false, logoCenter, dative3rd⟩ := by
  cases logoCenter <;> cases dative3rd <;> decide

/-! ### The Spanish clusters

Each clitic's logophoric center is read off its person feature: a dative is a discourse
participant when it is first or second person and an empathy locus when it is third; an
accusative is a discourse participant when it is first or second person, and a third-person one
is an attitude holder exactly on its *de se* reading. -/

/-- The center a dative clitic realizes. -/
def dativeCenter : UD.Person → LogoCenter
  | .third => .empathyLocus
  | _ => .discourseParticipant

/-- The center an accusative clitic realizes, given whether it is read *de se*. -/
def accusativeCenter : UD.Person → Bool → LogoCenter
  | .third, true => .attitudeHolder
  | .third, false => .empathyLocus
  | _, _ => .discourseParticipant

/-- *Se lo* (underlyingly *le lo*), a third-person dative with a *de se* third-person accusative,
is the clitic logophoric restriction's configuration: empathy locus with attitude holder. -/
theorem spanish_le_lo_de_se_clash :
    Clash (dativeCenter Spanish.Clitics.le_dat.person)
      (accusativeCenter Spanish.Clitics.lo.person true) := by decide

/-- *Le me*, a third-person dative with a first-person accusative, is the Person Case Constraint's
configuration: empathy locus with discourse participant. -/
theorem spanish_le_me_clash :
    Clash (dativeCenter Spanish.Clitics.le_dat.person)
      (accusativeCenter Spanish.Clitics.me_acc.person false) := by decide

/-- *Me lo* is licit even on the *de se* reading: a first-person dative is a discourse
participant, and that is the one center an attitude holder does not clash with. -/
theorem spanish_me_lo_de_se_licit :
    ¬ Clash (dativeCenter Spanish.Clitics.me_dat.person)
      (accusativeCenter Spanish.Clitics.lo.person true) := by decide

end CharnavelMateu2015
