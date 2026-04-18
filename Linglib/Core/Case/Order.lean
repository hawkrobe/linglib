import Mathlib.Order.Basic
import Linglib.Core.Case.Basic
/-!
# Caha Containment Order on Case
@cite{caha-2009} @cite{mcfadden-2018}

The canonical order on `Core.Case`: state-of-the-art syntax
(configurational case + nanosyntactic spellout) assumes Caha's
containment as the default. Each case on the hierarchy literally
*contains* the representations of all cases below it:

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

Cases without a `containmentRank` (ERG, ABS, INST, COM, …) are silent —
incomparable with on-hierarchy cases under `≤`, except for reflexivity.
That silence is the theoretical content: Caha's hierarchy is silent on
those cases, and the `PartialOrder` structure preserves the silence.

Other orders (Blake's typological frequency in `Core/Case/Hierarchy.lean`,
per-language syncretism graphs) live as named `def`s used locally via
`letI` rather than as competing instances on `Case`.
-/

namespace Core
namespace Case

/-- Caha's containment rank (@cite{caha-2009}). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established). -/
def containmentRank : Case → Option Nat
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4
  | _ => none

/-- Strict containment on Caha-rank Cases: both must have a rank, and the
    first's must be strictly smaller. False whenever either side is
    off-hierarchy. -/
def cahaLT (c₁ c₂ : Case) : Prop :=
  match containmentRank c₁, containmentRank c₂ with
  | some n, some m => n < m
  | _, _ => False

instance instDecidableCahaLT : DecidableRel cahaLT := fun c₁ c₂ => by
  unfold cahaLT; split <;> infer_instance

/-- The Caha containment order. `c₁ ≤ c₂` iff either they are equal, or
    `cahaLT c₁ c₂`. Off-hierarchy cases are reflexively `≤` themselves and
    incomparable with everything else. -/
def cahaLE (c₁ c₂ : Case) : Prop := c₁ = c₂ ∨ cahaLT c₁ c₂

instance : DecidableRel cahaLE := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

instance : LE Case := ⟨cahaLE⟩

instance (c₁ c₂ : Case) : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (cahaLE c₁ c₂))

theorem cahaLE_refl (c : Case) : c ≤ c := Or.inl rfl

theorem cahaLT_trans {a b c : Case} : cahaLT a b → cahaLT b c → cahaLT a c := by
  unfold cahaLT
  cases ha : containmentRank a <;> cases hb : containmentRank b <;>
    cases hc : containmentRank c <;> simp_all
  exact lt_trans

theorem cahaLE_trans (a b c : Case) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  exact Or.inr (cahaLT_trans hab hbc)

theorem cahaLE_antisymm (a b : Case) : a ≤ b → b ≤ a → a = b := by
  intro hab hba
  rcases hab with rfl | hab
  · rfl
  rcases hba with rfl | hba
  · rfl
  exfalso
  exact absurd (cahaLT_trans hab hba) (by
    unfold cahaLT
    cases ha : containmentRank a <;> simp_all)

instance : Preorder Case where
  le_refl := cahaLE_refl
  le_trans _ _ _ := cahaLE_trans _ _ _

instance : PartialOrder Case where
  le_antisymm _ _ := cahaLE_antisymm _ _

/-- A case is **nonnominative** iff its representation contains ACC's, i.e.
    `Case.acc ≤ c` in the Caha order. @cite{mcfadden-2018} argues this is
    the key natural class for stem allomorphy: a VI rule conditioned on
    `[ACC]` captures the NOM-vs-oblique split found cross-linguistically. -/
def IsNonnominative (c : Case) : Prop := Case.acc ≤ c

instance (c : Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable (Case.acc ≤ c))

-- ============================================================================
-- § Sanity Chain: NOM < ACC < GEN < DAT < LOC
-- ============================================================================

theorem nom_le_acc : (Case.nom : Case) ≤ Case.acc :=
  Or.inr (show (0 : Nat) < 1 from Nat.lt_succ_self 0)
theorem acc_le_gen : (Case.acc : Case) ≤ Case.gen :=
  Or.inr (show (1 : Nat) < 2 from Nat.lt_succ_self 1)
theorem gen_le_dat : (Case.gen : Case) ≤ Case.dat :=
  Or.inr (show (2 : Nat) < 3 from Nat.lt_succ_self 2)
theorem dat_le_loc : (Case.dat : Case) ≤ Case.loc :=
  Or.inr (show (3 : Nat) < 4 from Nat.lt_succ_self 3)

/-- Off-hierarchy cases (ERG) are incomparable with on-hierarchy cases. -/
theorem erg_incomparable_nom : ¬ ((Case.erg : Case) ≤ Case.nom) := by
  rintro (h | h)
  · exact UD.Case.noConfusion h
  · exact (show False from h)

theorem nom_incomparable_erg : ¬ ((Case.nom : Case) ≤ Case.erg) := by
  rintro (h | h)
  · exact UD.Case.noConfusion h
  · exact (show False from h)

end Case
end Core
