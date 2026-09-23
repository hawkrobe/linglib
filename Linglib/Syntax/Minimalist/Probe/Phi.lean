module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Minimalist.Phi.Geometry
public import Linglib.Syntax.Case.Licensing

/-!
# φ-probes: the φ-feature specialization of `Probe`
[preminger-2014] [bejar-rezac-2003]

The φ-instantiation of the general `Probe` core (`Probe/Basic.lean`):
probes over `Agreement.Bundle`s, relativized by the sought feature
(`Probe.Target`, `Phi/Geometry.lean`). This is [preminger-2014]'s
participant-relativized person probe and the Person Licensing
Condition built on it.

## Main declarations

- `Agreement.Bundle.visibleTo` — a cell bears the feature a target seeks.
- `Agreement.Bundle.IsParticipant` — a cell bears an interpretable 1st/2nd person feature.
- `Probe.Target.toProbe` — a target's denotation as a `Probe` over φ-cells.
- `PhiGoal` — a nominal as a φ-goal: its Case-licensing state with its φ-cell.
- `PLC` — the Person Licensing Condition over φ-bearing goal tokens.
-/

@[expose] public section

namespace Minimalist

/-- Visibility of a φ-cell to a relativized probe: the cell bears the
    feature the probe seeks (`probeVisible`, `Phi/Geometry.lean`). -/
def _root_.Agreement.Bundle.visibleTo (c : Agreement.Bundle) (t : Probe.Target) : Bool :=
  probeVisible t c.person (decide c.IsPlural)

/-- A cell bears an interpretable 1st/2nd person feature: it is visible to the
participant probe, by the person geometry of [harley-ritter-2002]. -/
def _root_.Agreement.Bundle.IsParticipant (c : Agreement.Bundle) : Prop :=
  c.visibleTo .participant = true

instance : DecidablePred Agreement.Bundle.IsParticipant := fun c =>
  inferInstanceAs (Decidable (c.visibleTo .participant = true))

/-- The `Probe` a `Probe.Target` denotes: relativized to the sought
    feature, over φ-cells (π⁰ = `Probe.Target.participant.toProbe`). -/
def Probe.Target.toProbe (t : Probe.Target) : Probe Agreement.Bundle :=
  .relativized (·.visibleTo t)

/-- A nominal as the goal of a φ-probe: its Case-licensing state (`LicensedNP`) together
with its φ-cell. A relativized probe reads the cell for visibility; Agree reads the Case
state for activity (`LicensedNP.isActive`, the Active Goal Hypothesis of [chomsky-2000]). -/
structure PhiGoal extends Case.Licensing.LicensedNP where
  cell : Agreement.Bundle
  deriving DecidableEq, Repr

/-- A nominal whose Case `c` a head of its own has already valued: inactive for Agree. -/
def PhiGoal.valued (c : Case) (cell : Agreement.Bundle) : PhiGoal :=
  { label := "", lexicalCase := some c, needsLicensing := true, cell := cell }

/-- A nominal with unvalued Case: active for Agree. -/
def PhiGoal.unvalued (cell : Agreement.Bundle) : PhiGoal :=
  { label := "", lexicalCase := none, needsLicensing := true, cell := cell }

@[simp] theorem PhiGoal.cell_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).cell = cell := rfl

@[simp] theorem PhiGoal.lexicalCase_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).lexicalCase = some c := rfl

@[simp] theorem PhiGoal.needsLicensing_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).needsLicensing = true := rfl

@[simp] theorem PhiGoal.cell_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).cell = cell := rfl

@[simp] theorem PhiGoal.lexicalCase_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).lexicalCase = none := rfl

@[simp] theorem PhiGoal.needsLicensing_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).needsLicensing = true := rfl

theorem PhiGoal.isActive_valued (c : Case) (cell : Agreement.Bundle) :
    (PhiGoal.valued c cell).isActive = false := rfl

theorem PhiGoal.isActive_unvalued (cell : Agreement.Bundle) :
    (PhiGoal.unvalued cell).isActive = true := rfl

@[simp] theorem PhiGoal.valued_ne_unvalued (c : Case) (cell cell' : Agreement.Bundle) :
    PhiGoal.valued c cell ≠ PhiGoal.unvalued cell' := by
  simp [PhiGoal.valued, PhiGoal.unvalued]

@[simp] theorem PhiGoal.unvalued_ne_valued (c : Case) (cell cell' : Agreement.Bundle) :
    PhiGoal.unvalued cell' ≠ PhiGoal.valued c cell :=
  (PhiGoal.valued_ne_unvalued c cell cell').symm

/-- The Person Licensing Condition ([bejar-rezac-2003], [preminger-2014]):
    every [participant]-bearing goal is licensed by the person probe's
    search. This single-cycle, search-only rendering omits
    [bejar-rezac-2003]'s F-licensing route and multi-cycle repairs (see
    `BejarRezac2003.PLCOk`). -/
def PLC {α : Type*} (cellOf : α → Agreement.Bundle) (goals : List α) : Prop :=
  (Probe.relativized fun a => (cellOf a).visibleTo .participant).AllLicensed
    (fun a => (cellOf a).visibleTo .participant) goals

instance {α : Type*} [DecidableEq α] (cellOf : α → Agreement.Bundle) (goals : List α) :
    Decidable (PLC cellOf goals) :=
  inferInstanceAs (Decidable (Probe.AllLicensed _ _ goals))

end Minimalist
