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
  inputs (`LicensedNP extends NPInDomain`), so a configural account reads its
  `NPInDomain` projection and ignores `needsLicensing`, while a licensing
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

The Chomskyan Case Filter (`Syntax/Case/Filter.lean`) is a *checker*, not an
assigner, and is bridged separately. The paper-anchored dependent-case ⟺
licensing DOM divergence belongs in the later paper's study file
(`Studies/Kalin2018.lean`); the `example`s here only validate that the harness
is non-vacuous.
-/

namespace Syntax.Case

open Licensing (LicensedNP ClauseLicensers Licenser licenseNPs LicensingOutcome)

/-- What a case account predicts for one nominal: its surface case (`none`
    exactly when the provenance is the crash `uncased`) and its neutral
    `Case.Source` provenance. -/
structure Verdict where
  source : _root_.Case.Source
  surfaceCase : Option _root_.Case
  deriving DecidableEq, Repr

/-- A case-assignment account as a function from the shared stimulus to a
    per-label verdict (`none` = no nominal with that label). The signature
    that makes rival theories runnable on one input. -/
abbrev Assigner := List LicensedNP → String → Option Verdict

/-- Marantz dependent case as an `Assigner`: it reads the configural
    projection (`needsLicensing` ignored) and is total, so it never produces
    the crash `uncased`. -/
def dependentAssigner (lang : CaseLanguageType) : Assigner := fun nps label =>
  ((assignCases lang (nps.map (·.toNPInDomain))).find? (·.label == label)).map
    fun r => ⟨r.source.toNeutral, some r.case⟩

/-- Kalin hybrid licensing as an `Assigner`: an unlicensed nominal crashes to
    `⟨uncased, none⟩`. -/
def kalinAssigner (cl : ClauseLicensers) : Assigner := fun nps label =>
  ((licenseNPs cl nps).find? (·.label == label)).map
    fun r => ⟨r.outcome.toNeutral, r.outcome.assignedCase⟩

/-- Two accounts agree on the **surface case** of every nominal in the
    stimulus. -/
def AgreesOnCase (a b : Assigner) (nps : List LicensedNP) : Prop :=
  ∀ np ∈ nps, (a nps np.label).map Verdict.surfaceCase
            = (b nps np.label).map Verdict.surfaceCase

/-- Two accounts agree on the **provenance** of every nominal in the
    stimulus. Two accounts can agree on case yet diverge here. -/
def AgreesOnSource (a b : Assigner) (nps : List LicensedNP) : Prop :=
  ∀ np ∈ nps, (a nps np.label).map Verdict.source
            = (b nps np.label).map Verdict.source

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
    = some ⟨.structural, some .acc⟩ := by decide

example : kalinAssigner turkishLikeClause transitiveStimulus "obj"
    = some ⟨.structural, some .acc⟩ := by decide

example : AgreesOnCase (dependentAssigner .accusative)
    (kalinAssigner turkishLikeClause) transitiveStimulus := by decide

example : ¬ AgreesOnSource (dependentAssigner .accusative)
    (kalinAssigner turkishLikeClause) transitiveStimulus := by decide

end Syntax.Case
