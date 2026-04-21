import Linglib.Theories.Semantics.Exhaustification.Excluder

/-!
# Tolerant Exhaustification (Chierchia 2013)
@cite{chierchia-2013}

A second `Excluder`: negate **every** alternative not entailed by the
prejacent, even if the result is contradictory.

An alternative `a` is *non-weaker* than `φ` iff `φ ⊄ a` (some `φ`-world
is outside `a`). Innocent exclusion further requires that the negation
of `a` be jointly compatible with the negations of other choices; the
tolerant operator drops that requirement and excludes every non-weaker
alternative unconditionally. The result `tolerant.exh` may therefore be
empty (a contradiction).

Tolerance is empirically motivated by EFCIs (@cite{alonso-ovalle-moghiseh-2025}):
applying `tolerant` to an unembedded existential free-choice item produces
the contradiction that drives modal insertion or partial exhaustification.

## Relationship to `innocent`

Tolerance always excludes at least as much as innocent exclusion (every
innocently-excludable alternative is non-weaker), so
`tolerant.exh ⊆ innocent.exh`. The converse can fail when symmetric
alternatives leave both choices outside `IE` while still being non-weaker.
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Chierchia 2013's contradiction-tolerating excluder: pick every
    alternative not entailed by the prejacent. -/
def tolerant : Excluder W where
  excluded ALT φ := ALT.filter (fun a => ¬ φ ⊆ a)
  excluded_subset _ _ := Finset.filter_subset _ _

@[simp] theorem tolerant_excluded (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.excluded ALT φ = ALT.filter (fun a => ¬ φ ⊆ a) := rfl

theorem mem_tolerant_excluded {ALT : Finset (Finset W)} {φ a : Finset W} :
    a ∈ tolerant.excluded ALT φ ↔ a ∈ ALT ∧ ¬ φ ⊆ a := by
  simp [tolerant_excluded, Finset.mem_filter]

/-- A world `w` survives `tolerant.exh` iff it satisfies the prejacent
    and falsifies every non-entailed alternative. -/
theorem mem_tolerant_exh_iff (ALT : Finset (Finset W)) (φ : Finset W) {w : W} :
    w ∈ tolerant.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ ALT, ¬ φ ⊆ a → w ∉ a := by
  rw [Excluder.mem_exh_iff]
  refine and_congr_right (fun _ => ?_)
  simp [tolerant_excluded, Finset.mem_filter, and_imp]

/-- Alternatives entailed by the prejacent are kept, never negated. -/
theorem entailed_not_excluded {ALT : Finset (Finset W)} {φ a : Finset W}
    (h : φ ⊆ a) : a ∉ tolerant.excluded ALT φ := by
  simp [h]

end Exhaustification
