import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Minimalist.Phi.Geometry

/-!
# φ-probes: the φ-feature specialization of `Probe`
[preminger-2014] [bejar-rezac-2003]

The φ-instantiation of the general `Probe` core (`Probe/Basic.lean`):
probes over `Agreement.Cell`s, relativized by the sought feature
(`Probe.Target`, `Phi/Geometry.lean`). This is [preminger-2014]'s
participant-relativized person probe and the Person Licensing
Condition built on it.

## Main declarations

- `Agreement.Cell.visibleTo` — a cell bears the feature a target seeks.
- `Probe.Target.toProbe` — a target's denotation as a `Probe` over φ-cells.
- `PLC` — the Person Licensing Condition over φ-bearing goal tokens.
-/

namespace Minimalist

/-- Visibility of a φ-cell to a relativized probe: the cell bears the
    feature the probe seeks (`probeVisible`, `Phi/Geometry.lean`). -/
def _root_.Agreement.Cell.visibleTo (c : Agreement.Cell) (t : Probe.Target) : Bool :=
  probeVisible t c.toPerson c.isPlural

/-- The `Probe` a `Probe.Target` denotes: relativized to the sought
    feature, over φ-cells (π⁰ = `Probe.Target.participant.toProbe`). -/
def Probe.Target.toProbe (t : Probe.Target) : Probe Agreement.Cell :=
  .ofVis (·.visibleTo t)

/-- The Person Licensing Condition ([bejar-rezac-2003], [preminger-2014]):
    every [participant]-bearing goal is licensed by the person probe's
    search. This single-cycle, search-only rendering omits
    [bejar-rezac-2003]'s F-licensing route and multi-cycle repairs (see
    `BejarRezac2003.PLCOk`). -/
def PLC {α : Type*} (cellOf : α → Agreement.Cell) (goals : List α) : Prop :=
  (Probe.ofVis fun a => (cellOf a).visibleTo .participant).AllLicensed
    (fun a => (cellOf a).visibleTo .participant) goals

instance {α : Type*} [DecidableEq α] (cellOf : α → Agreement.Cell) (goals : List α) :
    Decidable (PLC cellOf goals) :=
  inferInstanceAs (Decidable (Probe.AllLicensed _ _ goals))

end Minimalist
