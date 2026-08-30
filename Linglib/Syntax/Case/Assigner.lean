import Linglib.Features.Case.Source
import Linglib.Syntax.Case.Dependent
import Linglib.Syntax.Case.Licensing

/-!
# Case assigners — one signature for comparing rival theories
[marantz-1991] [kalin-2018]

The rival accounts of case assignment (`Dependent.lean`, `Licensing.lean`)
each run on their own input type and produce their own result type, so they
cannot be applied to a *common* stimulus — which is exactly what comparing
them requires. This file gives them one shared signature.

* The shared stimulus is `List LicensedNP` — the richest of the rivals'
  inputs (`LicensedNP extends Case.NP`), so a configural account reads its
  `Case.NP` projection and ignores `needsLicensing`, while a licensing
  account reads the whole thing.
* An `Assigner` maps that stimulus to a per-label `Verdict` (a surface case
  plus its neutral `Case.Source` provenance). This is the `Predict`-style
  function signature, *not* a typeclass: rivals are ordinary `def`s, so two
  accounts with the same input/output types coexist (which a typeclass could
  not host).
* `AgreesOnCase` / `AgreesOnSource` compare two accounts per projection.
  Divergence is the negation, witnessed by a stimulus — generalizing the
  `agree_on_…`/`diverge_on_…` pattern of `Studies/Woolford1997.lean` and
  `Studies/Baker2015.lean`.

The Chomskyan Case Filter (`Syntax/Minimalist/Case.lean`) is a *checker*, not an
assigner, and is bridged separately. The paper-anchored dependent-case ⟺
licensing DOM divergence belongs in the later paper's study file
(`Studies/Kalin2018.lean`); the `example`s here only validate that the harness
is non-vacuous.
-/

namespace Syntax.Case

open Licensing (LicensedNP ClauseLicensers Licenser licenseNPs LicensingOutcome)

/-- What a case account assigns one nominal: a case together with its neutral
    provenance, or nothing at all. An account that cannot fail simply never
    produces `unassigned`. -/
inductive Assignment where
  | assigned (case : _root_.Case) (source : _root_.Case.Source)
  | unassigned
  deriving DecidableEq, Repr

/-- The surface case, absent exactly when nothing was assigned. -/
def Assignment.surfaceCase : Assignment → Option _root_.Case
  | .assigned c _ => some c
  | .unassigned => none

/-- The provenance, absent exactly when nothing was assigned. -/
def Assignment.provenance : Assignment → Option _root_.Case.Source
  | .assigned _ s => some s
  | .unassigned => none

/-- A case-assignment account as a function from the shared stimulus to a
    per-label assignment (`none` = no nominal with that label). The signature
    that makes rival theories runnable on one input. -/
abbrev Assigner := List LicensedNP → String → Option Assignment

/-- Marantz dependent case as an `Assigner`: it reads the configural
    projection (`needsLicensing` ignored) and is total, so it never produces
    `unassigned`. -/
def dependentAssigner (a : Alignment.AlignmentType) : Assigner := fun nps label =>
  ((_root_.Case.assignCases a (nps.map (·.toNP))).find? (·.1.label == label)).map fun r =>
    match r.2 with
    | some (c, m) => .assigned c m.toSource
    | none => .unassigned

/-- A licensing outcome as a neutral assignment: primary and secondary
    licensing are structural, lexical pre-licensing inherent, and the crash
    assigns nothing. -/
def Licensing.LicensingOutcome.toAssignment : LicensingOutcome → Assignment
  | .byPrimary _ c   => .assigned c .structural
  | .bySecondary _ c => .assigned c .structural
  | .byLexical c     => .assigned c .inherent
  | .unlicensed      => .unassigned

/-- Kalin hybrid licensing as an `Assigner`: an unlicensed nominal is
    `unassigned`. -/
def kalinAssigner (cl : ClauseLicensers) : Assigner := fun nps label =>
  ((licenseNPs cl nps).find? (·.label == label)).map (·.outcome.toAssignment)

/-- Two accounts agree on the **surface case** of every nominal in the
    stimulus. -/
def AgreesOnCase (a b : Assigner) (nps : List LicensedNP) : Prop :=
  ∀ np ∈ nps, (a nps np.label).map Assignment.surfaceCase
            = (b nps np.label).map Assignment.surfaceCase

/-- Two accounts agree on the **provenance** of every nominal in the
    stimulus. Two accounts can agree on case yet diverge here. -/
def AgreesOnSource (a b : Assigner) (nps : List LicensedNP) : Prop :=
  ∀ np ∈ nps, (a nps np.label).map Assignment.provenance
            = (b nps np.label).map Assignment.provenance

instance (a b : Assigner) (nps : List LicensedNP) : Decidable (AgreesOnCase a b nps) := by
  unfold AgreesOnCase; infer_instance

instance (a b : Assigner) (nps : List LicensedNP) : Decidable (AgreesOnSource a b nps) := by
  unfold AgreesOnSource; infer_instance

/-! ### Non-vacuity: the harness on a transitive clause

A `[subj, obj]` transitive (both nominals active, no lexical case) in an
accusative language with a Turkish-style primary-T / secondary-AGRO clause.
Dependent case and hybrid licensing **agree on the surface case** (subj NOM,
obj ACC) but **diverge on the provenance** of the subject — dependent case
calls it `default` (unmarked last resort), licensing calls it `structural`
(valued by primary T). The shape of the eventual `Studies/Kalin2018.lean`
divergence, here only to confirm the harness is not vacuous. -/

private def transitiveStimulus : List LicensedNP :=
  [ { label := "subj", lexicalCase := none, needsLicensing := true }
  , { label := "obj",  lexicalCase := none, needsLicensing := true } ]

private def turkishLikeClause : ClauseLicensers :=
  { primary := { kind := .primary, head := "T", assignedCase := .nom }
  , secondaries := [{ kind := .secondary, head := "AGRO", assignedCase := .acc }] }

example : dependentAssigner .accusative transitiveStimulus "obj"
    = some (.assigned .acc .structural) := by decide

example : kalinAssigner turkishLikeClause transitiveStimulus "obj"
    = some (.assigned .acc .structural) := by decide

example : AgreesOnCase (dependentAssigner .accusative)
    (kalinAssigner turkishLikeClause) transitiveStimulus := by decide

example : ¬ AgreesOnSource (dependentAssigner .accusative)
    (kalinAssigner turkishLikeClause) transitiveStimulus := by decide

end Syntax.Case
