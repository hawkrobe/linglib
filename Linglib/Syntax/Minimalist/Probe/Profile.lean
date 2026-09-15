import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Syntax.Minimalist.Probe.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Probe profiles

This file defines a probe's locality profile, the head that hosts it together with the category
that terminates its search, its horizon ([keine-2019], [keine-2020]). Labels are bilateral within
an extended projection, so a clause's label is the list of heads it projects, and a clause is
transparent to a probe exactly when its label does not contain the horizon. Transparency is then
antitone in the extension order of clause spines, which is Upward Entailment, and a probe whose
horizon lies in the label of its own sister is vacuous, the premise of the Height–Locality
Theorem. A profile denotes a `Probe` over any goal type that exposes a label; the tree-native
counterpart of a horizon is `SyntacticObject.behindHorizonIn`.

## Main definitions

* `Minimalist.Probe.Profile`, `Minimalist.Probe.Profile.transparentToLabel`
* `Minimalist.Probe.Profile.isVacuousFor`, `Minimalist.Probe.Profile.isVacuous`
* `Minimalist.Probe.Profile.toProbe`

## Main results

* `Minimalist.Probe.Profile.transparentToLabel_antitone`, Upward Entailment.

## References

* [keine-2019]
* [keine-2020]
-/

namespace Minimalist

/-- A probe's profile is the head that hosts it and the category that terminates its search, its
horizon; a probe without horizon searches into any domain ([keine-2020]). -/
structure Probe.Profile where
  /-- The head that hosts the probe. -/
  probeHead : Cat
  /-- The category that terminates the probe's search, if any. -/
  horizon : Option Cat
  deriving DecidableEq, Repr

namespace Probe.Profile

variable (p : Probe.Profile)

/-! ### Transparency -/

/-- A domain with bilateral label `label` is transparent to `p` when `p` has no horizon or the
label does not contain it. -/
def transparentToLabel (label : List Cat) : Bool :=
  match p.horizon with
  | none => true
  | some h => !(label.any (· == h))

/-- Upward Entailment. A label containing every head of a label opaque to `p` is opaque to `p`. -/
theorem transparentToLabel_eq_false_of_subset {L₁ L₂ : List Cat} (h_sub : ∀ c ∈ L₁, c ∈ L₂)
    (h_opaque : p.transparentToLabel L₁ = false) : p.transparentToLabel L₂ = false := by
  simp only [transparentToLabel] at *
  cases h_hz : p.horizon with
  | none => simp_all
  | some h =>
    simp_all only [Bool.not_eq_false']
    rw [List.any_eq_true] at h_opaque ⊢
    obtain ⟨x, hx_mem, hx_eq⟩ := h_opaque
    exact ⟨x, h_sub x hx_mem, hx_eq⟩

/-- Upward Entailment. Transparency is antitone in the extension order of clause spines, since a
spine's label contains the horizon whenever a spine below it does. -/
theorem transparentToLabel_antitone :
    Antitone λ s : ClauseSpine => p.transparentToLabel s.projectedHeads :=
  λ s _ h => Bool.le_iff_imp.mpr λ ht => by
    cases hs : p.transparentToLabel s.projectedHeads
    · exact absurd (p.transparentToLabel_eq_false_of_subset h hs) (by simp [ht])
    · exact hs

/-! ### Vacuity -/

/-- `p` is vacuous for a sister with label `sisterLabel` when its horizon lies in that label, so
that its search terminates at its sister and no domain remains ([keine-2020]). -/
def isVacuousFor (sisterLabel : List Cat) : Bool :=
  match p.horizon with
  | none => false
  | some _ => p.transparentToLabel sisterLabel = false

/-- `p` is vacuous in the standard verbal spine, where the sister of C⁰ is TP, of T⁰ is vP and of
Force⁰ is CP ([keine-2020]). Vacuous probes trigger no dependency and are undetectable, which
is what makes the Height–Locality Theorem emerge. -/
def isVacuous : Bool :=
  match p.horizon with
  | none => false
  | some _ =>
    let sisterLabel := match p.probeHead with
      | .C     => ClauseSpine.tP.projectedHeads
      | .Force => ClauseSpine.cP.projectedHeads
      | .T     => ClauseSpine.vP.projectedHeads
      | _      => []
    p.transparentToLabel sisterLabel = false

/-- A probe without horizon is never vacuous. -/
theorem isVacuous_mk_none (head : Cat) : (Probe.Profile.mk head none).isVacuous = false := by
  simp [isVacuous]

/-! ### Denotation into the canonical `Probe` -/

/-- The probe a profile denotes over goals exposing a label, which sees a goal iff the goal's
label is transparent to it. -/
def toProbe {α : Type*} (labelOf : α → List Cat) : Probe α :=
  .ofVis λ a => p.transparentToLabel (labelOf a)

end Probe.Profile

end Minimalist
