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
- `Probe.Target.toProbe` — the canonical specification-to-`Probe` map:
  π⁰ is `Probe.Target.participant.toProbe`, #⁰ is `.plural.toProbe`.
- `PLC` — the Person Licensing Condition over φ-bearing goal tokens.
-/

namespace Minimalist

/-- Visibility of a φ-cell to a relativized probe: the cell bears the
    feature the probe seeks (`probeVisible`, `Phi/Geometry.lean`). -/
def _root_.Agreement.Cell.visibleTo (c : Agreement.Cell) (t : Probe.Target) : Bool :=
  probeVisible t c.toPerson c.isPlural

/-- The probe a `Probe.Target` specification denotes: relativized to
    the sought feature, over φ-cells. The canonical
    specification-to-`Probe` map for the substrate's probe enum —
    [preminger-2014]'s π⁰ is `Probe.Target.participant.toProbe`, his
    #⁰ is `Probe.Target.plural.toProbe`. -/
def Probe.Target.toProbe (t : Probe.Target) : Probe Agreement.Cell :=
  .ofVis (·.visibleTo t)

/-- The Person Licensing Condition ([bejar-rezac-2003];
    [preminger-2014] (40)/(75)): every [participant]-bearing goal
    token must be licensed by the person probe's search. Goal tokens
    have type `α` with a φ-cell projection, so two arguments with
    identical φ remain distinct licensees.

    This is [preminger-2014]'s single-cycle, search-only, diagonal
    rendering of the condition: it omits [bejar-rezac-2003]'s
    F-licensing route (a nominal's own φ-bearing P/dative/focus head
    counts as a licensing Agree relation) and multi-cycle repairs —
    for the paper's own condition see `BejarRezac2003.PLCOk`. -/
def PLC {α : Type*} (cellOf : α → Agreement.Cell) (goals : List α) : Prop :=
  (Probe.ofVis fun a => (cellOf a).visibleTo .participant).AllLicensed
    (fun a => (cellOf a).visibleTo .participant) goals

instance {α : Type*} [DecidableEq α] (cellOf : α → Agreement.Cell) (goals : List α) :
    Decidable (PLC cellOf goals) :=
  inferInstanceAs (Decidable (Probe.AllLicensed _ _ goals))

end Minimalist
