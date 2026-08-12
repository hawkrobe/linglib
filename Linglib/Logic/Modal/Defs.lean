import Mathlib.Logic.Basic
import Mathlib.Logic.Relator
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.PropInstances

/-!
# Modal operators and frame conditions

This file defines the relational `box`/`diamond` of Kripke semantics,
the frame conditions of modal correspondence theory for accessibility
relations `W → W → Prop`, and the per-axiom correspondences (K, T, D, 4,
B, 5) connecting them; the `Set`-valued mathlib counterparts of the
operators are `Rel.core` and `Rel.preimage`.

## References

* [kripke-1963] — relational semantics
* [blackburn-derijke-venema-2001] — Chapter 3, frame definability
-/

namespace ModalLogic

variable {W : Type*} (R : W → W → Prop)

/-! ### Box and diamond -/

/-- Restricted necessity: `box R p w` holds iff `p v` for all `v`
    accessible from `w`. -/
def box (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `diamond R p w` holds iff `p v` for some `v`
    accessible from `w`. Dual of `box`. -/
def diamond (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

@[inherit_doc] scoped notation:max "□[" R "]" => box R
@[inherit_doc] scoped notation:max "◇[" R "]" => diamond R

/-! ### Duality -/

@[simp] theorem not_box (p : W → Prop) (w : W) :
    ¬ □[R] p w ↔ ◇[R] (fun v => ¬ p v) w := by
  simp [box, diamond, not_forall]

@[simp] theorem not_diamond (p : W → Prop) (w : W) :
    ¬ ◇[R] p w ↔ □[R] (fun v => ¬ p v) w := by
  simp [box, diamond, not_and]

/-! ### Frame conditions -/

/-- `R` is **serial** if every world accesses at least one world. -/
class IsSerial : Prop where
  serial : Relator.LeftTotal R

/-- `R` is **Euclidean** if from any pair of `R`-successors of `w`, each is
    an `R`-successor of the other. -/
class IsEuclidean : Prop where
  eucl : ∀ w v u, R w v → R w u → R v u

/-! ### Frame implications and instances -/

variable {R}

-- Seriality, symmetry, and transitivity of `⊤` follow from the two
-- instances below via the derivations that follow.
instance : Std.Refl (⊤ : W → W → Prop) := ⟨fun _ => trivial⟩
instance : IsEuclidean (⊤ : W → W → Prop) := ⟨fun _ _ _ _ _ => trivial⟩

/-- Reflexive relations are serial. -/
instance [hR : Std.Refl R] : IsSerial R where serial w := ⟨w, hR.refl w⟩

/-- Reflexive + Euclidean implies symmetric. -/
instance [hR : Std.Refl R] [hE : IsEuclidean R] : Std.Symm R where
  symm w v hwv := hE.eucl w v w hwv (hR.refl w)

/-- Reflexive + Euclidean implies transitive. -/
instance [hR : Std.Refl R] [hE : IsEuclidean R] : IsTrans W R where
  trans w v u hwv hvu := hE.eucl v w u (hE.eucl w v w hwv (hR.refl w)) hvu

/-- Symmetric + transitive implies euclidean. -/
instance [hS : Std.Symm R] [hT : IsTrans W R] : IsEuclidean R where
  eucl w v u hwv hwu := hT.trans v w u (hS.symm w v hwv) hwu

variable {p q : W → Prop} {w : W}

/-! ### Axiom correspondence -/

/-- **K**: `□(p → q) → □p → □q`, over any relation. -/
theorem box_K (hpq : □[R] (fun v => p v → q v) w) (hp : □[R] p w) : □[R] q w :=
  fun v hwv => hpq v hwv (hp v hwv)

/-- **T** defines reflexivity: `□p ≤ p` for all `p` iff `R` is reflexive. -/
theorem box_T_iff : (∀ p : W → Prop, □[R] p ≤ p) ↔ Std.Refl R :=
  ⟨fun h => ⟨fun w => h (R w) w fun _ hv => hv⟩,
   fun hR _ w h => h w (hR.refl w)⟩

/-- **T**: over a reflexive relation, `□p → p`. -/
theorem box_T [hR : Std.Refl R] (h : □[R] p w) : p w :=
  box_T_iff.mpr hR _ _ h

/-- **D** defines seriality: `□p ≤ ◇p` for all `p` iff `R` is serial. -/
theorem box_D_iff : (∀ p : W → Prop, □[R] p ≤ ◇[R] p) ↔ IsSerial R :=
  ⟨fun h => ⟨fun w =>
     let ⟨v, hv, _⟩ := h (fun _ => True) w fun _ _ => trivial; ⟨v, hv⟩⟩,
   fun hS _ w h => let ⟨v, hwv⟩ := hS.serial w; ⟨v, hwv, h v hwv⟩⟩

/-- **D**: over a serial relation, `□p → ◇p`. -/
theorem box_D [hS : IsSerial R] (h : □[R] p w) : ◇[R] p w :=
  box_D_iff.mpr hS _ _ h

/-- **B** defines symmetry: `p ≤ □◇p` for all `p` iff `R` is symmetric. -/
theorem box_B_iff : (∀ p : W → Prop, p ≤ □[R] (◇[R] p)) ↔ Std.Symm R :=
  ⟨fun h => ⟨fun w v hwv =>
     match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩,
   fun hS _ w h v hwv => ⟨w, hS.symm w v hwv, h⟩⟩

/-- **B**: over a symmetric relation, `p → □◇p`. -/
theorem box_B [hS : Std.Symm R] (h : p w) : □[R] (◇[R] p) w :=
  box_B_iff.mpr hS _ _ h

/-- **4** defines transitivity: `□p ≤ □□p` for all `p` iff `R` is transitive. -/
theorem box_four_iff : (∀ p : W → Prop, □[R] p ≤ □[R] (□[R] p)) ↔ IsTrans W R :=
  ⟨fun h => ⟨fun w v u hwv hvu => h (R w) w (fun _ hv => hv) v hwv u hvu⟩,
   fun hT _ w h v hwv u hvu => h u (hT.trans w v u hwv hvu)⟩

/-- **4**: over a transitive relation, `□p → □□p`. -/
theorem box_four [hT : IsTrans W R] (h : □[R] p w) : □[R] (□[R] p) w :=
  box_four_iff.mpr hT _ _ h

/-- **5** defines the Euclidean property: `◇p ≤ □◇p` for all `p` iff `R` is
    Euclidean. -/
theorem box_five_iff : (∀ p : W → Prop, ◇[R] p ≤ □[R] (◇[R] p)) ↔ IsEuclidean R :=
  ⟨fun h => ⟨fun w v u hwv hwu =>
     match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩,
   fun hE _ w h v hwv => let ⟨u, hwu, hpu⟩ := h; ⟨u, hE.eucl w v u hwv hwu, hpu⟩⟩

/-- **5**: over a Euclidean relation, `◇p → □◇p`. -/
theorem box_five [hE : IsEuclidean R] (h : ◇[R] p w) : □[R] (◇[R] p) w :=
  box_five_iff.mpr hE _ _ h

end ModalLogic
