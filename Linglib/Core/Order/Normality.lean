import Mathlib.Order.Minimal
import Linglib.Core.Order.OfCriteria
import Linglib.Core.Order.PreorderLattice

/-!
# Normality orderings (default reasoning over preorders)

[kraus-magidor-1990] [veltman-1996] [rudin-2025a] [kratzer-1981]

A *normality ordering* is just a `Preorder` on worlds: `p.le w v` means
`w` is at least as normal as `v`. There is **no bespoke structure** here —
the order is mathlib's `Preorder`, so the entire order API (`<`, `Minimal`,
order-duals, monotone maps) is available, and the default-reasoning
operations are thin definitions over it:

* `optimal p d` — the most-normal worlds in `d` — is mathlib's `Minimal`.
* `connected p` — totality — is `∀ w v, p.le w v ∨ p.le v w`.
* `total = ⊤` — the all-equal order — is the top of `CompleteLattice (Preorder W)`.
* `refine p φ = p ⊓ crit φ` — [veltman-1996]'s promote-φ update — is **meet**
  with the criterion preorder `crit φ` (`w ≤ v ↔ (φ v → φ w)`). The whole
  refinement calculus (commutativity, idempotence, the total order as unit)
  is therefore the meet-semilattice laws (`inf_right_comm`, `inf_right_idem`,
  `inf_top_eq`).
* `fromProps` — [kratzer-1981]'s ordering-source order — is `Preorder.ofCriteria`.

This replaces the former hand-rolled `NormalityOrder` structure (a
field-for-field reimplementation of `Preorder`).
-/

namespace Core.Order
namespace Normality

variable {W : Type*}

/-! ### Optimality, totality, the total order -/

/-- The **optimal** (most normal) worlds in a domain `d`: mathlib's
    `Minimal` for the membership predicate, under the preorder `p`. -/
def optimal (p : Preorder W) (d : Set W) : Set W := {w | @Minimal W p.toLE (· ∈ d) w}

theorem mem_optimal {p : Preorder W} {d : Set W} {w : W} :
    w ∈ optimal p d ↔ w ∈ d ∧ ∀ ⦃v⦄, v ∈ d → p.le v w → p.le w v := Iff.rfl

theorem optimal_subset (p : Preorder W) (d : Set W) : optimal p d ⊆ d := fun _ h => h.1

/-- A preorder is **connected** (total) if every two worlds are comparable. -/
def connected (p : Preorder W) : Prop := ∀ w v, p.le w v ∨ p.le v w

/-- The **total** normality order: all worlds equally normal — the top of
    the lattice of preorders. -/
abbrev total : Preorder W := ⊤

theorem total_connected : connected (total : Preorder W) := fun _ _ => Or.inl trivial

theorem total_all_optimal (d : Set W) : optimal (total : Preorder W) d = d := by
  ext w
  rw [mem_optimal]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ => trivial⟩⟩

/-! ### Refinement as meet with a criterion preorder -/

/-- The **criterion preorder** for a property `φ`: `w ≤ v ↔ (φ v → φ w)`.
    Defined directly (not via `Preorder.ofCriteria {φ}`) so that
    `(refine p φ).le` reduces definitionally to `p.le … ∧ (φ … → φ …)`. -/
@[reducible] def crit (φ : W → Prop) : Preorder W :=
  Preorder.ofLE (fun w v => φ v → φ w) (fun _ => id)
    (fun _ _ _ hab hbc h => hab (hbc h))

theorem crit_le {φ : W → Prop} {w v : W} : (crit φ).le w v ↔ (φ v → φ w) := Iff.rfl

/-- **Refinement** ([veltman-1996]): promote φ-worlds. `refine p φ` is the
    meet of `p` with the criterion preorder for `φ`, so
    `(refine p φ).le w v ↔ p.le w v ∧ (φ v → φ w)`. -/
@[reducible] def refine (p : Preorder W) (φ : W → Prop) : Preorder W := p ⊓ crit φ

theorem refine_le {p : Preorder W} {φ : W → Prop} {w v : W} :
    (refine p φ).le w v ↔ p.le w v ∧ (φ v → φ w) := and_congr Iff.rfl crit_le

theorem refine_le_imp {p : Preorder W} {φ : W → Prop} {w v : W}
    (h : (refine p φ).le w v) : p.le w v := (refine_le.mp h).1

/-- After refinement by φ, a non-φ-world cannot be as normal as a φ-world. -/
theorem refine_separates (p : Preorder W) (φ : W → Prop)
    {w v : W} (hv : φ v) (hw : ¬φ w) : ¬(refine p φ).le w v :=
  fun h => hw ((refine_le.mp h).2 hv)

/-! ### Respect and persistence -/

/-- An ordering **respects** φ if it already promotes φ-worlds. -/
def respects (p : Preorder W) (φ : W → Prop) : Prop :=
  ∀ w v, p.le w v → φ v → φ w

theorem refine_respects (p : Preorder W) (φ : W → Prop) : respects (refine p φ) φ :=
  fun _ _ h hv => (refine_le.mp h).2 hv

/-- **Persistence**: respecting φ survives further refinement. -/
theorem refine_preserves_respects (p : Preorder W) (φ ψ : W → Prop)
    (h : respects p φ) : respects (refine p ψ) φ :=
  fun w v hle => h w v (refine_le_imp hle)

theorem respects_refine_iff (p : Preorder W) (φ : W → Prop)
    (h : respects p φ) {w v : W} : (refine p φ).le w v ↔ p.le w v :=
  ⟨fun hle => (refine_le.mp hle).1, fun hle => refine_le.mpr ⟨hle, fun hv => h w v hle hv⟩⟩

/-- **Idempotency**: refining by φ twice is refining once (`inf_right_idem`). -/
theorem refine_idempotent (p : Preorder W) (φ : W → Prop) :
    refine (refine p φ) φ = refine p φ := inf_right_idem _ _

/-- **Commutativity**: refinement order is immaterial (`inf_right_comm`). -/
theorem refine_comm (p : Preorder W) (φ ψ : W → Prop) :
    refine (refine p φ) ψ = refine (refine p ψ) φ := inf_right_comm _ _ _

theorem crit_const_top (b : Prop) : crit (W := W) (fun _ => b) = ⊤ :=
  le_antisymm le_top (fun _ _ _ => crit_le.mpr id)

/-- Refining by the universal property is the identity (`inf_top_eq`). -/
theorem refine_univ (p : Preorder W) : refine p (fun _ => True) = p := by
  show p ⊓ crit (fun _ => True) = p
  rw [crit_const_top True, inf_top_eq]

theorem refine_empty (p : Preorder W) : refine p (fun _ => False) = p := by
  show p ⊓ crit (fun _ => False) = p
  rw [crit_const_top False, inf_top_eq]

/-- If an ordering respects φ, refining by φ changes nothing. -/
theorem refine_of_respects (p : Preorder W) (φ : W → Prop)
    (h : respects p φ) : refine p φ = p :=
  le_antisymm inf_le_left (fun w v hle => refine_le.mpr ⟨hle, fun hv => h w v hle hv⟩)

theorem respects_no_domination (p : Preorder W) (φ : W → Prop)
    (hresp : respects p φ) {w v : W} (hv : φ v) (hw : ¬φ w) : ¬p.le w v :=
  fun hle => hw (hresp w v hle hv)

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

/-- **Refinement makes φ-worlds optimal**: from the total order, refining by
    φ makes the optimal worlds in `d` exactly the φ-worlds in `d`. -/
theorem refine_total_optimal (φ : W → Prop) (d : Set W) (hex : ∃ w ∈ d, φ w) :
    optimal (refine total φ) d = { w ∈ d | φ w } := by
  ext w
  rw [mem_optimal, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hwd, hopt⟩
    obtain ⟨v, hvd, hφv⟩ := hex
    refine ⟨hwd, ?_⟩
    by_contra hnφw
    have hle : (refine total φ).le v w := refine_le.mpr ⟨trivial, fun h => absurd h hnφw⟩
    exact hnφw ((refine_le.mp (hopt hvd hle)).2 hφv)
  · rintro ⟨hwd, hφw⟩
    exact ⟨hwd, fun _ _ _ => refine_le.mpr ⟨trivial, fun _ => hφw⟩⟩

theorem optimal_refine_of_mem (p : Preorder W) (φ : W → Prop)
    (d : Set W) {w : W} (hopt : w ∈ optimal p d) (hφ : φ w) :
    w ∈ optimal (refine p φ) d := by
  rw [mem_optimal] at hopt ⊢
  exact ⟨hopt.1, fun v hv hle =>
    refine_le.mpr ⟨hopt.2 hv (refine_le.mp hle).1, fun _ => hφ⟩⟩

theorem optimal_refine_nonempty (p : Preorder W) (φ : W → Prop)
    (d : Set W) (hex : ∃ w ∈ optimal p d, φ w) :
    (optimal (refine p φ) d).Nonempty := by
  obtain ⟨w, hopt, hφ⟩ := hex
  exact ⟨w, optimal_refine_of_mem p φ d hopt hφ⟩

/-! ### Construction from propositions ([kratzer-1981]) -/

/-- Construct a normality ordering from a list of propositions:
    `w ≤ v` iff every proposition satisfied by `v` is satisfied by `w`.
    This is `Preorder.ofCriteria` with the ordering source as criteria. -/
@[reducible] def fromProps (props : List (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p => p w) {p | p ∈ props}

theorem fromProps_nil {w v : W} : (fromProps ([] : List (W → Prop))).le w v :=
  fun _ h => nomatch h

theorem fromProps_cons_le (p : W → Prop) (ps : List (W → Prop))
    {w v : W} (h : (fromProps (p :: ps)).le w v) : (fromProps ps).le w v :=
  fun q hq => h q (List.mem_cons_of_mem p hq)

theorem refine_total_connected (φ : W → Prop) :
    connected (refine total φ : Preorder W) := by
  intro w v
  by_cases hφw : φ w
  · exact Or.inl (refine_le.mpr ⟨trivial, fun _ => hφw⟩)
  · by_cases hφv : φ v
    · exact Or.inr (refine_le.mpr ⟨trivial, fun h => absurd h hφw⟩)
    · exact Or.inl (refine_le.mpr ⟨trivial, fun h => absurd h hφv⟩)

/-! ### Darwiche-Pearl representation conditions

[darwiche-pearl-1997]: conditions on how a total preorder may change under
revision by `μ`. `prior`/`post` are the orderings before/after revision. -/

/-- CR1: the ordering among μ-worlds is preserved. -/
@[reducible] def satisfies_CR1 (prior post : Preorder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = true → (prior.le w v ↔ post.le w v)

/-- CR2: the ordering among ¬μ-worlds is preserved. -/
@[reducible] def satisfies_CR2 (prior post : Preorder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = false → μ v = false → (prior.le w v ↔ post.le w v)

/-- CR3: a μ-world strictly below a ¬μ-world stays strictly below. The strict
    order is spelled `le … ∧ ¬ le …` (definitionally `<`) so the relation is
    decidable on finite world sets. -/
@[reducible] def satisfies_CR3 (prior post : Preorder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = false →
    (prior.le w v ∧ ¬ prior.le v w) → (post.le w v ∧ ¬ post.le v w)

/-- CR4: a μ-world ≤ a ¬μ-world stays ≤. -/
@[reducible] def satisfies_CR4 (prior post : Preorder W) (μ : W → Bool) : Prop :=
  ∀ w v, μ w = true → μ v = false → prior.le w v → post.le w v

end Normality
end Core.Order
