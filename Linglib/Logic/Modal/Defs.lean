import Mathlib.Logic.Basic
import Mathlib.Logic.Relator
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.PropInstances

/-!
# Frame conditions and modal operators

This file defines the frame conditions of modal correspondence theory for
accessibility relations `W → W → Prop`, and the relational `box`/`diamond`
of Kripke semantics ([kripke-1963]).
-/

namespace ModalLogic

/-! ### Frame conditions -/

/-- `R` is **serial** if every world accesses at least one world. -/
class IsSerial {W : Type*} (R : W → W → Prop) : Prop where
  serial : Relator.LeftTotal R

/-- `R` is **Euclidean** if from any pair of `R`-successors of `w`, each is
    an `R`-successor of the other. -/
class IsEuclidean {W : Type*} (R : W → W → Prop) : Prop where
  eucl : ∀ w v u, R w v → R w u → R v u

/-! ### Frame implications and instances -/

variable {W : Type*}

instance : Std.Refl (⊤ : W → W → Prop) := ⟨fun _ => trivial⟩
instance : IsSerial (⊤ : W → W → Prop) := ⟨fun w => ⟨w, trivial⟩⟩
instance : IsTrans W (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩
instance : Std.Symm (⊤ : W → W → Prop) := ⟨fun _ _ _ => trivial⟩
instance : IsEuclidean (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩

-- The derived instances get lowered priority: the Refl+Euclidean and
-- Symm+Trans derivations are mutually productive, and direct instances
-- should always be preferred.

/-- Reflexive relations are serial. -/
instance (priority := 100) {R : W → W → Prop} [h : Std.Refl R] :
    IsSerial R := ⟨fun w => ⟨w, h.refl w⟩⟩

/-- Reflexive + Euclidean implies symmetric. -/
instance (priority := 100) {R : W → W → Prop} [hR : Std.Refl R] [hE : IsEuclidean R] :
    Std.Symm R :=
  ⟨fun w v hwv => hE.eucl w v w hwv (hR.refl w)⟩

/-- Reflexive + Euclidean implies transitive. -/
instance (priority := 100) {R : W → W → Prop} [hR : Std.Refl R] [hE : IsEuclidean R] :
    IsTrans W R :=
  ⟨fun w v u hwv hvu => hE.eucl v w u (hE.eucl w v w hwv (hR.refl w)) hvu⟩

/-- Symmetric + transitive implies euclidean. -/
instance (priority := 100) {R : W → W → Prop} [hS : Std.Symm R] [hT : IsTrans W R] :
    IsEuclidean R :=
  ⟨fun w v u hwv hwu => hT.trans v w u (hS.symm w v hwv) hwu⟩

/-! ### Box and diamond -/

/-- Restricted necessity: `□_R p` at world `w` holds iff `p v` for all
    `v` accessible from `w`.

    `⟦□_R φ⟧^w = 1` iff `⟦φ⟧^v = 1` for all `v` with `R(w,v)` — the Kripke
    generalization of the S5 necessity of [dowty-wall-peters-1981]'s IL,
    whose `Intensional.box` is the universal-accessibility special case.
    The `Set`-valued mathlib counterpart is `Rel.core`. -/
def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `◇_R p` at world `w` holds iff `p v` for some
    `v` accessible from `w`. Dual of `box`; the `Set`-valued mathlib
    counterpart is `Rel.preimage`. -/
def diamond (R : W → W → Prop) (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

/-! ### Duality -/

/-- Restricted modal duality: `□_R p ↔ ¬◇_R ¬p`. -/
theorem box_neg_diamond (R : W → W → Prop) (p : W → Prop) (w : W) :
    box R p w ↔ ¬ diamond R (fun v => ¬ p v) w :=
  ⟨fun hb ⟨v, hwv, hnp⟩ => hnp (hb v hwv),
   fun h v hwv => Classical.byContradiction fun hnp => h ⟨v, hwv, hnp⟩⟩

/-- Dual form: `◇_R p ↔ ¬□_R ¬p`. -/
theorem diamond_neg_box (R : W → W → Prop) (p : W → Prop) (w : W) :
    diamond R p w ↔ ¬ box R (fun v => ¬ p v) w :=
  ⟨fun ⟨v, hwv, hpv⟩ h => h v hwv hpv,
   fun h => Classical.byContradiction fun hne =>
     h fun v hwv hpv => hne ⟨v, hwv, hpv⟩⟩

end ModalLogic
