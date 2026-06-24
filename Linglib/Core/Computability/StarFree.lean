/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Algebra.Group.Aperiodic

/-!
# Star-free languages

A language is **star-free** when its syntactic monoid is finite and aperiodic
([schutzenberger-1965]) — the algebraic characterization of the star-free regular
expressions (built from finite sets by `∪`, `·`, complement, *no* Kleene star),
equivalently the counter-free / `FO[<]`-definable stringsets ([mcnaughton-papert-1971]).
Taking the syntactic-monoid characterization as the definition mirrors the project's
treatment of regularity (`Language.isRegular_iff_finite_syntacticMonoid`).

## Main definitions

* `Language.IsStarFree` — regular with an aperiodic syntactic monoid.

## Main results

* `Language.IsStarFree.compl` — star-free languages are closed under complement.
-/

namespace Language

variable {α : Type*} {L : Language α}

/-- A language is **star-free** when it is regular and its syntactic monoid is aperiodic
([schutzenberger-1965]). Star-free = `FO[<]`-definable = counter-free
([mcnaughton-papert-1971]). -/
def IsStarFree (L : Language α) : Prop :=
  L.IsRegular ∧ Monoid.IsAperiodic L.syntacticMonoid

theorem IsStarFree.isRegular (h : L.IsStarFree) : L.IsRegular := h.1

theorem IsStarFree.isAperiodic (h : L.IsStarFree) :
    Monoid.IsAperiodic L.syntacticMonoid := h.2

/-- The syntactic congruence is complement-invariant: a two-sided context distinguishes
`u` from `v` for `L` exactly when it does for `Lᶜ`. -/
theorem syntacticCon_compl (L : Language α) : Lᶜ.syntacticCon = L.syntacticCon :=
  Con.ext fun u v => by
    rw [syntacticCon_iff, syntacticCon_iff]
    exact forall_congr' fun _ => forall_congr' fun _ => not_iff_not

/-- The syntactic monoid is complement-invariant. -/
theorem syntacticMonoid_compl (L : Language α) : Lᶜ.syntacticMonoid = L.syntacticMonoid := by
  unfold syntacticMonoid; rw [syntacticCon_compl]

/-- **Star-free languages are closed under complement** — immediate from the
complement-invariance of the syntactic monoid (`syntacticMonoid_compl`) and of regularity
(`Language.IsRegular.compl`). -/
theorem IsStarFree.compl (h : L.IsStarFree) : Lᶜ.IsStarFree := by
  refine ⟨h.1.compl, ?_⟩
  show Monoid.IsAperiodic (syntacticCon Lᶜ).Quotient
  rw [syntacticCon_compl]
  exact h.2

end Language
