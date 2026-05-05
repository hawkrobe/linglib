import Linglib.Theories.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Theories.Semantics.Plurality.Cumulativity

/-!
# PPCDRT — Cumulativity Bridge
@cite{langendoen-1978} @cite{haug-dalrymple-2020}

@cite{langendoen-1978} first observed that reciprocity is a species of
cumulativity: in *the women pointed at each other*, every woman points at
some other woman and every woman is pointed at by some other woman.
@cite{haug-dalrymple-2020} §1 reaffirms this. The link is structural: the
PPCDRT condition `groupIdentityCond u_anaph u_ant`
(`Plurality.Cumulativity` is the bidirectional-coverage version of equality
on the value-sets `∪u_anaph(S) = ∪u_ant(S)`) collapses to
`cumulativeOp (· = ·)` on the Finset of value pairs.

The `Plurality/Cumulativity.lean` substrate types are `Bool`-valued over
`Finset × Finset`, while PPCDRT is `Prop`-valued over `PluralAssign`. The
bridge theorem under `[DecidableEq E]` and finiteness assumptions on the
value-sets establishes the structural identity that the original
`Reference/Reciprocals.lean` docstring asserted as prose.
-/

namespace Theories.Semantics.Dynamic.PPCDRT

open Core
open Semantics.Plurality.Cumulativity

universe u

variable {E : Type}

-- ════════════════════════════════════════════════════════════════
-- § 1: Cumulative Operator Reduces to Set Equality on Equality
-- ════════════════════════════════════════════════════════════════

/-- The cumulative operator `**` of @cite{krifka-1989}/Beck-Sauerland on
    the equality relation reduces to `Finset` equality.

    This is the structural identity behind the Langendoen reciprocity-as-
    cumulativity claim: bidirectional value-coverage IS the equality of
    value sets.

    ⊆ direction: if `cumulativeOp (· = ·) x y = true`, then for every
    `a ∈ x` there is `b ∈ y` with `a = b`, so `a ∈ y`; and symmetrically.
    ⊇ direction: if `x = y`, every element witnesses itself. -/
theorem cumulativeOp_eq_iff_finset_eq [DecidableEq E] (x y : Finset E) :
    cumulativeOp (fun a b => decide (a = b)) x y = true ↔ x = y := by
  constructor
  · intro h
    rw [cumulativeOp, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
    obtain ⟨hLR, hRL⟩ := h
    apply Finset.ext
    intro a
    constructor
    · intro hax
      obtain ⟨b, hby, hab⟩ := hLR a hax
      have : a = b := of_decide_eq_true hab
      rw [this]; exact hby
    · intro hay
      obtain ⟨b, hbx, hba⟩ := hRL a hay
      have : b = a := of_decide_eq_true hba
      rw [← this]; exact hbx
  · intro h
    rw [cumulativeOp, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    refine ⟨?_, ?_⟩
    · intro a hax
      exact ⟨a, h ▸ hax, by simp⟩
    · intro b hby
      exact ⟨b, h ▸ hby, by simp⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Bridge: groupIdentityCond ↔ cumulativeOp
-- (resolves audit finding: prose claim → theorem)
-- ════════════════════════════════════════════════════════════════

/-- Bridge: when the value-sets of the two drefs across the plural state
    are *given* as Finsets matching `sumDref`, group identity holds iff
    those Finsets are equal — iff `cumulativeOp (· = ·)` returns `true`.

    The hypothesis is stated as `Set` membership on `sumDref` because
    `Set E → Finset E` requires `Set.Finite`, which is downstream of the
    consumer's choice of value domain. Concrete H&D examples (Phase 4)
    instantiate this with `[Fintype]` toy domains where the value-sets are
    automatically finite.

    This theorem is the formal realisation of @cite{langendoen-1978}'s
    reciprocity-as-cumulativity claim within PPCDRT. -/
theorem groupIdentityCond_iff_cumulativeOp_eq [DecidableEq E]
    (uAnaph uAnt : Nat) (S : PluralAssign E) (xa xb : Finset E)
    (hxa : ∀ d, d ∈ xa ↔ d ∈ Core.PluralAssign.sumDref S uAnaph)
    (hxb : ∀ d, d ∈ xb ↔ d ∈ Core.PluralAssign.sumDref S uAnt) :
    groupIdentityCond uAnaph uAnt S ∅ ↔
    cumulativeOp (fun a b => decide (a = b)) xa xb = true := by
  rw [cumulativeOp_eq_iff_finset_eq]
  unfold groupIdentityCond
  constructor
  · intro h
    apply Finset.ext
    intro d
    rw [hxa d, hxb d, h]
  · intro h
    apply Set.ext
    intro d
    rw [← hxa d, ← hxb d, h]

end Theories.Semantics.Dynamic.PPCDRT
