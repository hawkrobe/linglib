import Linglib.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Semantics.Plurality.Cumulativity

/-!
# PPCDRT — Cumulativity Bridge
[langendoen-1978] [haug-dalrymple-2020]

[langendoen-1978] first observed that reciprocity is a species of
cumulativity: in *the women pointed at each other*, every woman points at
some other woman and every woman is pointed at by some other woman.
[haug-dalrymple-2020] §1 reaffirms this. The link is structural: the
PPCDRT condition `groupIdentityCond u_anaph u_ant`
(`Plurality.Cumulativity` is the bidirectional-coverage version of equality
on the value-sets `∪u_anaph(S) = ∪u_ant(S)`) collapses to
`Cumulative (· = ·)` on the Finset of value pairs.

The `Plurality/Cumulativity.lean` substrate is `Prop`-valued over
`Finset × Finset` (with a `Decidable` instance), while PPCDRT is also
`Prop`-valued over `PluralAssign`. The bridge theorem under
`[DecidableEq E]` and finiteness assumptions on the value-sets establishes
the structural identity that the original `Reference/Reciprocals.lean`
docstring asserted as prose.
-/

namespace PPCDRT

open Core
open Semantics.Plurality.Cumulativity

-- Note: monomorphic `Type` (universe 0) here — `Plurality.Cumulativity.Cumulative`
-- now lives at `Type*` so this could be lifted; lifted as needed by future
-- consumers.
variable {E : Type}

-- ════════════════════════════════════════════════════════════════
-- § 1: Cumulative Operator Reduces to Set Equality on Equality
-- ════════════════════════════════════════════════════════════════

/-- The cumulative operator `**` of [krifka-1989]/Beck-Sauerland on
    the equality relation reduces to `Finset` equality.

    This is the structural identity behind the Langendoen reciprocity-as-
    cumulativity claim: bidirectional value-coverage IS the equality of
    value sets.

    ⊆ direction: if `Cumulative (· = ·) x y`, then for every `a ∈ x`
    there is `b ∈ y` with `a = b`, so `a ∈ y`; and symmetrically.
    ⊇ direction: if `x = y`, every element witnesses itself. -/
theorem cumulative_eq_iff_finset_eq [DecidableEq E] (x y : Finset E) :
    Cumulative (fun a b : E => a = b) x y ↔ x = y := by
  constructor
  · rintro ⟨hLR, hRL⟩
    apply Finset.ext
    intro a
    refine ⟨fun hax => ?_, fun hay => ?_⟩
    · obtain ⟨b, hby, hab⟩ := hLR a hax
      rw [hab]; exact hby
    · obtain ⟨b, hbx, hba⟩ := hRL a hay
      rw [← hba]; exact hbx
  · intro h
    refine ⟨?_, ?_⟩
    · intro a hax
      exact ⟨a, h ▸ hax, rfl⟩
    · intro b hby
      exact ⟨b, h ▸ hby, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Bridge: groupIdentityCond ↔ Cumulative
-- (resolves audit finding: prose claim → theorem)
-- ════════════════════════════════════════════════════════════════

/-- Bridge: when the value-sets of the two drefs across the plural state
    are *given* as Finsets matching `sumDref`, group identity holds iff
    those Finsets are equal — iff `Cumulative (· = ·)` returns `true`.

    The hypothesis is stated as `Set` membership on `sumDref` because
    `Set E → Finset E` requires `Set.Finite`, which is downstream of the
    consumer's choice of value domain. Concrete H&D examples (Phase 4)
    instantiate this with `[Fintype]` toy domains where the value-sets are
    automatically finite.

    This theorem is the formal realisation of [langendoen-1978]'s
    reciprocity-as-cumulativity claim within PPCDRT. -/
theorem groupIdentityCond_iff_cumulative_eq [DecidableEq E]
    (uAnaph uAnt : Nat) (S : PluralAssign E) (xa xb : Finset E)
    (hxa : ∀ d, d ∈ xa ↔ d ∈ Core.PluralAssign.sumDref S uAnaph)
    (hxb : ∀ d, d ∈ xb ↔ d ∈ Core.PluralAssign.sumDref S uAnt) :
    groupIdentityCond uAnaph uAnt S ∅ ↔
    Cumulative (fun a b : E => a = b) xa xb := by
  rw [cumulative_eq_iff_finset_eq]
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

end PPCDRT
