import Mathlib.Order.Minimal
import Linglib.Core.Order.OfCriteria
import Linglib.Core.Order.PreorderLattice

/-!
# Normality orderings

This file develops default reasoning over a preorder on worlds. A *normality ordering* is a
`Preorder` on worlds, where `p.le w v` means that `w` is at least as normal as `v`, and the
operations of default reasoning are defined on it directly.

The most normal worlds of a domain are its minimal elements, in the sense of mathlib's `Minimal`.
The order under which all worlds are equally normal is the top of the lattice of preorders.
Veltman's update of an ordering by a default `φ`, which promotes the `φ`-worlds, is the meet of
the ordering with the preorder that ranks `φ`-worlds below the others, so the laws of refinement
(commutativity, idempotence, the all-equal order as unit) are the laws of a meet-semilattice.
Kratzer's ordering induced by an ordering source ranks `w` below `v` when `w` satisfies every
proposition of the source that `v` satisfies. Under a well-founded ordering every world of a
domain has a most normal world of the domain below it, which is the limit assumption and the
smoothness condition of Kraus, Lehmann and Magidor.

## Main declarations

* `Core.Order.Normality.optimal`: the most normal worlds of a domain.
* `Core.Order.Normality.connected`: any two worlds are comparable.
* `Core.Order.Normality.total`: the ordering under which all worlds are equally normal.
* `Core.Order.Normality.crit`, `Core.Order.Normality.refine`: the preorder of a single criterion,
  and the refinement of an ordering by a criterion.
* `Core.Order.Normality.respects`: an ordering already promotes the worlds of a proposition.
* `Core.Order.Normality.fromProps`: the ordering induced by a list of propositions.
* `Core.Order.Normality.exists_le_mem_optimal`: below every world of a domain lies an optimal
  world, when the strict order is well-founded.

## References

* [S. Kraus, D. Lehmann and M. Magidor, *Nonmonotonic Reasoning, Preferential Models and
  Cumulative Logics* (1990)][kraus-magidor-1990]
* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [D. Rudin, *Asserting epistemic modals* (2025)][rudin-2025a]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
-/

namespace Core.Order
namespace Normality

variable {W : Type*}

/-! ### Optimality, totality, the total order -/

/-- The optimal worlds of a domain `d` are its most normal worlds, the minimal elements of `d`
under the preorder `p`. -/
def optimal (p : Preorder W) (d : Set W) : Set W := {w | @Minimal W p.toLE (· ∈ d) w}

theorem mem_optimal {p : Preorder W} {d : Set W} {w : W} :
    w ∈ optimal p d ↔ w ∈ d ∧ ∀ ⦃v⦄, v ∈ d → p.le v w → p.le w v := Iff.rfl

theorem optimal_subset (p : Preorder W) (d : Set W) : optimal p d ⊆ d := fun _ h ↦ h.1

/-- A world optimal in a domain is optimal in any subdomain it belongs to. -/
theorem mem_optimal_of_subset {p : Preorder W} {d e : Set W} {w : W} (h : d ⊆ e)
    (hw : w ∈ optimal p e) (hd : w ∈ d) : w ∈ optimal p d :=
  Minimal.mono hw (fun _ hv ↦ h hv) hd

/-- Under a criteria-derived order, when some world of the domain satisfies every criterion,
the optimal worlds are exactly those. -/
theorem optimal_ofCriteria_eq {C : Type*} {sat : W → C → Prop} {criteria : Set C} {d : Set W}
    (hex : ∃ w ∈ d, ∀ c ∈ criteria, sat w c) :
    optimal (Preorder.ofCriteria sat criteria) d = {w ∈ d | ∀ c ∈ criteria, sat w c} :=
  let ⟨_, hv, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨hw, hopt⟩ ↦ ⟨hw, fun c hc ↦ hopt hv (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨hw, hall⟩ ↦ ⟨hw, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

/-- Under a well-founded order every world of a domain has an optimal world of the domain below
it. -/
theorem exists_le_mem_optimal {p : Preorder W} (hp : WellFounded p.lt) {d : Set W} {w : W}
    (hw : w ∈ d) : ∃ v ∈ optimal p d, p.le v w :=
  letI := p
  haveI : WellFoundedLT W := hp
  let ⟨v, hvw, hv⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ d) w hw
  ⟨v, hv, hvw⟩

/-- A preorder is connected if every two worlds are comparable. -/
def connected (p : Preorder W) : Prop := ∀ w v, p.le w v ∨ p.le v w

/-- The total normality order makes all worlds equally normal. It is the top of the lattice of
preorders. -/
abbrev total : Preorder W := ⊤

theorem total_connected : connected (total : Preorder W) := fun _ _ ↦ Or.inl trivial

theorem total_all_optimal (d : Set W) : optimal (total : Preorder W) d = d := by
  ext w
  rw [mem_optimal]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ _ ↦ trivial⟩⟩

/-! ### Refinement as meet with a criterion preorder -/

/-- The criterion preorder of a property `φ` ranks `w` below `v` when `φ v` implies `φ w`. It is
defined directly rather than through `Preorder.ofCriteria`, so that `(refine p φ).le` reduces
definitionally to a conjunction. -/
@[reducible] def crit (φ : W → Prop) : Preorder W :=
  Preorder.ofLE (fun w v ↦ φ v → φ w) (fun _ ↦ id)
    (fun _ _ _ hab hbc h ↦ hab (hbc h))

theorem crit_le {φ : W → Prop} {w v : W} : (crit φ).le w v ↔ (φ v → φ w) := Iff.rfl

/-- The refinement of `p` by `φ` promotes the `φ`-worlds. It is the meet of `p` with the
criterion preorder of `φ`. -/
@[reducible] def refine (p : Preorder W) (φ : W → Prop) : Preorder W := p ⊓ crit φ

theorem refine_le {p : Preorder W} {φ : W → Prop} {w v : W} :
    (refine p φ).le w v ↔ p.le w v ∧ (φ v → φ w) := and_congr Iff.rfl crit_le

theorem refine_le_imp {p : Preorder W} {φ : W → Prop} {w v : W}
    (h : (refine p φ).le w v) : p.le w v := (refine_le.mp h).1

/-- After refinement by φ, a non-φ-world cannot be as normal as a φ-world. -/
theorem refine_separates (p : Preorder W) (φ : W → Prop)
    {w v : W} (hv : φ v) (hw : ¬φ w) : ¬(refine p φ).le w v :=
  fun h ↦ hw ((refine_le.mp h).2 hv)

/-! ### Respect and persistence -/

/-- An ordering respects `φ` if it already promotes the `φ`-worlds. -/
def respects (p : Preorder W) (φ : W → Prop) : Prop :=
  ∀ w v, p.le w v → φ v → φ w

theorem refine_respects (p : Preorder W) (φ : W → Prop) : respects (refine p φ) φ :=
  fun _ _ h hv ↦ (refine_le.mp h).2 hv

/-- Respecting `φ` survives further refinement. -/
theorem refine_preserves_respects (p : Preorder W) (φ ψ : W → Prop)
    (h : respects p φ) : respects (refine p ψ) φ :=
  fun w v hle ↦ h w v (refine_le_imp hle)

theorem respects_refine_iff (p : Preorder W) (φ : W → Prop)
    (h : respects p φ) {w v : W} : (refine p φ).le w v ↔ p.le w v :=
  ⟨fun hle ↦ (refine_le.mp hle).1, fun hle ↦ refine_le.mpr ⟨hle, fun hv ↦ h w v hle hv⟩⟩

/-- Refining by `φ` twice is refining once. -/
theorem refine_idempotent (p : Preorder W) (φ : W → Prop) :
    refine (refine p φ) φ = refine p φ := inf_right_idem _ _

/-- The order of two refinements is immaterial. -/
theorem refine_comm (p : Preorder W) (φ ψ : W → Prop) :
    refine (refine p φ) ψ = refine (refine p ψ) φ := inf_right_comm _ _ _

theorem crit_const_top (b : Prop) : crit (W := W) (fun _ ↦ b) = ⊤ :=
  le_antisymm le_top (fun _ _ _ ↦ crit_le.mpr id)

/-- Refining by the universal property is the identity (`inf_top_eq`). -/
theorem refine_univ (p : Preorder W) : refine p (fun _ ↦ True) = p := by
  show p ⊓ crit (fun _ ↦ True) = p
  rw [crit_const_top True, inf_top_eq]

theorem refine_empty (p : Preorder W) : refine p (fun _ ↦ False) = p := by
  show p ⊓ crit (fun _ ↦ False) = p
  rw [crit_const_top False, inf_top_eq]

/-- If an ordering respects φ, refining by φ changes nothing. -/
theorem refine_of_respects (p : Preorder W) (φ : W → Prop)
    (h : respects p φ) : refine p φ = p :=
  le_antisymm inf_le_left (fun w v hle ↦ refine_le.mpr ⟨hle, fun hv ↦ h w v hle hv⟩)

theorem respects_no_domination (p : Preorder W) (φ : W → Prop)
    (hresp : respects p φ) {w v : W} (hv : φ v) (hw : ¬φ w) : ¬p.le w v :=
  fun hle ↦ hw (hresp w v hle hv)

/-! ### Connectedness and optimality -/

theorem optimal_of_respects_connected (p : Preorder W)
    (φ : W → Prop) (d : Set W) (hresp : respects p φ)
    (hconn : connected p) (hex : ∃ w ∈ d, φ w) :
    optimal p d ⊆ { w ∈ d | φ w } := by
  intro w hw
  rw [mem_optimal] at hw
  obtain ⟨hwd, hopt⟩ := hw
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hwd, ?_⟩
  rcases hconn w v with hwv | hvw
  · exact hresp w v hwv hφv
  · exact hresp w v (hopt hvd hvw) hφv

/-- Refining the total order by `φ` makes the optimal worlds of `d` exactly the `φ`-worlds of
`d`. -/
theorem refine_total_optimal (φ : W → Prop) (d : Set W) (hex : ∃ w ∈ d, φ w) :
    optimal (refine total φ) d = { w ∈ d | φ w } := by
  ext w
  rw [mem_optimal, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hwd, hopt⟩
    obtain ⟨v, hvd, hφv⟩ := hex
    refine ⟨hwd, ?_⟩
    by_contra hnφw
    have hle : (refine total φ).le v w := refine_le.mpr ⟨trivial, fun h ↦ absurd h hnφw⟩
    exact hnφw ((refine_le.mp (hopt hvd hle)).2 hφv)
  · rintro ⟨hwd, hφw⟩
    exact ⟨hwd, fun _ _ _ ↦ refine_le.mpr ⟨trivial, fun _ ↦ hφw⟩⟩

theorem optimal_refine_of_mem (p : Preorder W) (φ : W → Prop)
    (d : Set W) {w : W} (hopt : w ∈ optimal p d) (hφ : φ w) :
    w ∈ optimal (refine p φ) d := by
  rw [mem_optimal] at hopt ⊢
  exact ⟨hopt.1, fun v hv hle ↦
    refine_le.mpr ⟨hopt.2 hv (refine_le.mp hle).1, fun _ ↦ hφ⟩⟩

theorem optimal_refine_nonempty (p : Preorder W) (φ : W → Prop)
    (d : Set W) (hex : ∃ w ∈ optimal p d, φ w) :
    (optimal (refine p φ) d).Nonempty := by
  obtain ⟨w, hopt, hφ⟩ := hex
  exact ⟨w, optimal_refine_of_mem p φ d hopt hφ⟩

/-! ### Construction from propositions -/

/-- The normality ordering induced by a list of propositions ranks `w` below `v` when every
proposition satisfied by `v` is satisfied by `w`. -/
@[reducible] def fromProps (props : List (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p ↦ p w) {p | p ∈ props}

theorem fromProps_nil {w v : W} : (fromProps ([] : List (W → Prop))).le w v :=
  fun _ h ↦ nomatch h

theorem fromProps_cons_le (p : W → Prop) (ps : List (W → Prop))
    {w v : W} (h : (fromProps (p :: ps)).le w v) : (fromProps ps).le w v :=
  fun q hq ↦ h q (List.mem_cons_of_mem p hq)

theorem refine_total_connected (φ : W → Prop) :
    connected (refine total φ : Preorder W) := by
  intro w v
  by_cases hφw : φ w
  · exact Or.inl (refine_le.mpr ⟨trivial, fun _ ↦ hφw⟩)
  · by_cases hφv : φ v
    · exact Or.inr (refine_le.mpr ⟨trivial, fun h ↦ absurd h hφw⟩)
    · exact Or.inl (refine_le.mpr ⟨trivial, fun h ↦ absurd h hφv⟩)

end Normality
end Core.Order
