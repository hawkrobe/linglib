import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-!
# Keine (2019): Selective Opacity

This file formalizes the horizons account of selective opacity of [keine-2019]: a syntactic
domain may be opaque to some operations and transparent to others (their (1)), and the constraint
is on the searches of probes, each terminated by a category of its own, its horizon ((38)),
rather than on domains or on the moving element. With category inheritance within an extended
projection ((43)) a clause's label collects the categories it projects, so a clause is opaque to a
probe exactly when its label contains the horizon, and Upward Entailment ((40)), that larger
clauses are at least as opaque, is the Horizon Inheritance Theorem ((45), (46)), transparency
antitone in the extension order of clause sizes (`sizes_le`). The Hindi probes of (48) and (57),
φ-agreement and A-movement on T⁰ with
horizon T, wh-licensing on C⁰ with horizon C and Ā-movement on C⁰ without one, derive the
transparency table (58) with its three locality types (`transparency_table`) and with it the
generalizations (21) and (23) on long-distance agreement; English hyperraising is A-movement
with horizon C (Section 4.2.3), and its availability elsewhere is the absence of that horizon
(`hyperraising_iff`).

The Height-Locality Connection ((33), (62)), that higher probes search into more kinds of
structure, is derived rather than stipulated: a probe whose horizon lies below its position finds
it in its sister and is vacuous ((63)), so for a nonvacuous probe the position bounds the horizon
and the horizon bounds the position, the Height-Locality Theorem ((65)) instantiated for Hindi in
(66) and (67).

## Implementation notes

Labels are the projected heads of the substrate's `ClauseSpine`s and transparency is
`Probe.Profile.transparentToLabel`; the article's probes are the substrate's `keinePhiProbe`,
`keineAProbe`, `keineWhLicensing` and `keineĀProbe`, and vacuity is `Probe.Profile.isVacuous`,
which takes the sister of a probe on C⁰ to be TP and of one on T⁰ to be vP.

## References

* [keine-2019]
-/

namespace Keine2019

open Minimalist

/-- The label of a finite clause, the categories inherited up its extended projection ((44)). -/
def cpLabel : List Cat := ClauseSpine.cP.projectedHeads

/-- The label of a large nonfinite clause. -/
def tpLabel : List Cat := ClauseSpine.tP.projectedHeads

/-- The label of a small nonfinite clause. -/
def vpLabel : List Cat := ClauseSpine.vP.projectedHeads

/-! ### Horizons and Upward Entailment (Section 4.1) -/

/-- (45), (46): Upward Entailment follows from category inheritance. The three clause sizes
stand in the extension order, TP extending vP and CP extending TP, and transparency is antitone
in that order for every probe (`Probe.Profile.transparentToLabel_antitone`), so a probe blocked
by a clause is blocked by every larger one. -/
theorem sizes_le : ClauseSpine.vP ≤ .tP ∧ ClauseSpine.tP ≤ .cP := by decide

/-! ### The Hindi probes (Section 4.2) -/

/-- A probe's row of the transparency table: finite, large nonfinite, small nonfinite. -/
def row (p : Probe.Profile) : List Bool := [cpLabel, tpLabel, vpLabel].map p.transparentToLabel

/-- (58): φ-agreement and A-movement search only into vP clauses, wh-licensing into TP and vP
clauses, Ā-movement into all three. -/
theorem transparency_table :
    row keinePhiProbe = [false, false, true] ∧ row keineAProbe = [false, false, true] ∧
      row keineWhLicensing = [false, true, true] ∧ row keineĀProbe = [true, true, true] := by
  decide

/-- Selective opacity is not binary: the table has three locality types. -/
theorem three_locality_types :
    row keinePhiProbe ≠ row keineWhLicensing ∧ row keineWhLicensing ≠ row keineĀProbe ∧
      row keinePhiProbe ≠ row keineĀProbe := by
  decide

/-- (23), the finite clause embedding (49): finite clauses, edge included, are opaque to
A-movement and φ-agreement but not to Ā-movement. -/
theorem finite_clauses_selectively_opaque :
    keineAProbe.transparentToLabel cpLabel = false ∧
      keinePhiProbe.transparentToLabel cpLabel = false ∧
      keineĀProbe.transparentToLabel cpLabel = true := by
  decide

/-- (21), the nonfinite embeddings (50) and (51): the two probes on T⁰ share their horizon, so a
nonfinite clause small enough for A-extraction is the vP structure and is transparent to
φ-agreement, which makes long-distance agreement obligatory; Ā-movement enters the TP structure
too and has no such effect. -/
theorem a_extraction_forces_lda :
    (∀ L ∈ [tpLabel, vpLabel], keineAProbe.transparentToLabel L = true →
        L = vpLabel ∧ keinePhiProbe.transparentToLabel L = true) ∧
      keineĀProbe.transparentToLabel tpLabel = true ∧
      keinePhiProbe.transparentToLabel tpLabel = false := by
  decide

/-! ### Hyperraising (Section 4.2.3) -/

/-- The English A-probe, on T⁰ with horizon C. -/
def englishAProbe : Probe.Profile := ⟨.T, some .C⟩

/-- The English extraposition probe, on T⁰ with horizon T. -/
def extrapositionProbe : Probe.Profile := ⟨.T, some .T⟩

/-- (59): no A-probe search enters a finite clause in English, while Ā-extraction is unaffected;
extraposition, with horizon T, cannot leave even a nonfinite clause. -/
theorem hyperraising_blocked :
    englishAProbe.transparentToLabel cpLabel = false ∧
      keineĀProbe.transparentToLabel cpLabel = true ∧
      extrapositionProbe.transparentToLabel tpLabel = false := by
  decide

/-- Hyperraising is a horizon parameter: an A-probe on T⁰ enters finite clauses exactly when its
horizon is none of the categories a finite clause inherits, as in the languages that allow it. -/
theorem hyperraising_iff (h : Option Cat) :
    (⟨.T, h⟩ : Probe.Profile).transparentToLabel cpLabel = true ↔ ∀ c ∈ cpLabel, h ≠ some c := by
  cases h with
  | none => simp [Probe.Profile.transparentToLabel]
  | some x =>
    simp only [Probe.Profile.transparentToLabel, Bool.not_eq_true', List.any_eq_false, beq_iff_eq,
      ne_eq, Option.some.injEq]
    exact ⟨λ h c hc hx => h c hc hx.symm, λ h c hc hx => h c hc hx.symm⟩

/-! ### The Height-Locality Connection (Section 5) -/

/-- (63): a probe on C⁰ with horizon T finds its horizon in its sister and has no search space. -/
theorem vacuous_example : (⟨.C, some .T⟩ : Probe.Profile).isVacuous = true := by decide

/-- (65a), height to locality: a nonvacuous probe on C⁰ has no horizon among the categories of
its sister TP, and one on T⁰ none among those of vP, so those clauses are necessarily transparent
to it. -/
theorem height_to_locality (h : Cat) :
    ((⟨.C, some h⟩ : Probe.Profile).isVacuous = false → h ∉ tpLabel) ∧
      ((⟨.T, some h⟩ : Probe.Profile).isVacuous = false → h ∉ vpLabel) := by
  simp [Probe.Profile.isVacuous, Probe.Profile.transparentToLabel, tpLabel, vpLabel]

/-- (65b), locality to height: a probe with horizon T is vacuous on C⁰, and one with horizon v on
T⁰ and C⁰; a nonvacuous probe's horizon bounds its position from below. -/
theorem locality_to_height :
    (⟨.C, some .T⟩ : Probe.Profile).isVacuous = true ∧
      (⟨.T, some .v⟩ : Probe.Profile).isVacuous = true ∧
      (⟨.C, some .v⟩ : Probe.Profile).isVacuous = true := by
  decide

/-- A nonvacuous probe on C⁰ searches into TP and vP clauses, and one on T⁰ into vP clauses,
whatever their horizons: the Height-Locality Connection for the two positions. -/
theorem nonvacuous_transparent (h : Option Cat) :
    ((⟨.C, h⟩ : Probe.Profile).isVacuous = false →
        (⟨.C, h⟩ : Probe.Profile).transparentToLabel tpLabel = true ∧
          (⟨.C, h⟩ : Probe.Profile).transparentToLabel vpLabel = true) ∧
      ((⟨.T, h⟩ : Probe.Profile).isVacuous = false →
        (⟨.T, h⟩ : Probe.Profile).transparentToLabel vpLabel = true) := by
  cases h with
  | none => simp [Probe.Profile.isVacuous, Probe.Profile.transparentToLabel]
  | some x =>
    have hsub : ∀ c ∈ vpLabel, c ∈ tpLabel := by decide
    simp only [Probe.Profile.isVacuous, Probe.Profile.transparentToLabel, Bool.not_eq_true',
      Bool.not_eq_false', List.any_eq_false, List.any_eq_true, beq_iff_eq,
      decide_eq_false_iff_not, not_exists, not_and, tpLabel, vpLabel]
    exact ⟨λ h => ⟨h, λ c hc => h c (hsub c hc)⟩, λ h => h⟩

/-- (66) and (67) for Hindi: the four probes are nonvacuous, so the two on C⁰ search into TP and
vP clauses and the two on T⁰ into vP clauses, which is why nonfinite clauses are no islands for
Ā-movement or wh-licensing and why only these interact with long-distance agreement as (21)
says; and the A-probe's horizon T would make it vacuous on C⁰, so A-movement lands inside
nonfinite clauses. -/
theorem hindi_consequences :
    (∀ p ∈ [keinePhiProbe, keineAProbe, keineWhLicensing, keineĀProbe], p.isVacuous = false) ∧
      (∀ p ∈ [keineWhLicensing, keineĀProbe],
        p.transparentToLabel tpLabel = true ∧ p.transparentToLabel vpLabel = true) ∧
      (∀ p ∈ [keinePhiProbe, keineAProbe], p.transparentToLabel vpLabel = true) ∧
      (⟨.C, keineAProbe.horizon⟩ : Probe.Profile).isVacuous = true := by
  decide

end Keine2019
