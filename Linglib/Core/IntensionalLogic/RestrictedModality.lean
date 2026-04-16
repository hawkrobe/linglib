import Linglib.Core.IntensionalLogic.Quantification
import Linglib.Core.IntensionalLogic.Algebra

/-!
# Restricted Modality: Accessibility-Parameterized Box and Diamond

@cite{dowty-wall-peters-1981} @cite{kratzer-1981} @cite{kripke-1963}

Montague's IL defines `box`/`diamond` as S5 operators — quantifying over
**all** indices. This is Semantic Rule B.13 in DWP. But natural language
modality requires restricting quantification to **accessible** indices,
determined by an accessibility relation `R : F.Index → F.Index → Prop`.

This module defines the restricted operators `boxR` and `diamondR` and
establishes the key results:

1. **Specialization**: S5 `box`/`diamond` are `boxR`/`diamondR` with
   universal accessibility (`R = ⊤`)
2. **Modal axiom correspondence**: frame conditions on `R` (reflexivity,
   transitivity, symmetry, euclideanness) correspond to modal axioms
   (T, 4, B, 5) — the Kripke correspondence in the IL setting
3. **Lattice connection**: `boxR` is a restricted infimum (`⨅`) and
   `diamondR` is a restricted supremum (`⨆`) over accessible indices

The `Prop`-valued formulation here is the IL-native version. The `Bool`-valued
Kripke semantics in `Core/Logic/ModalLogic.lean` and the Kratzer infrastructure
in `Theories/Semantics/Modality/Kratzer/` are computational specializations
for finite domains.

## Connection to Kratzer semantics

Kratzer's conversational backgrounds derive accessibility from a modal base:
`R_f(w, w') ≡ w' ∈ ⋂f(w)`. The ordering source further restricts to "best"
worlds. In IL terms:

- Simple Kratzer necessity = `boxR R_f` (no ordering source)
- Full Kratzer necessity = `boxR R_{f,g}` where `R_{f,g}` restricts to best worlds
- S5 necessity = `boxR (fun _ _ => True)` = `box`
-/

namespace Core.IntensionalLogic.RestrictedModality

open Core.IntensionalLogic

variable {F : Frame}

-- ════════════════════════════════════════════════════════════════
-- § Accessibility Relations
-- ════════════════════════════════════════════════════════════════

/-- An accessibility relation on indices. `R i j` means index `j` is
    accessible from index `i`. -/
abbrev AccessRel (F : Frame) := F.Index → F.Index → Prop

/-- Universal accessibility: every index is accessible from every index. -/
def universalR : AccessRel F := fun _ _ => True

/-- Empty accessibility: no index is accessible from any index. -/
def emptyR : AccessRel F := fun _ _ => False

/-- Reflexive (identity) accessibility: each index accesses only itself. -/
def identityR : AccessRel F := fun i j => i = j

-- ════════════════════════════════════════════════════════════════
-- § Frame Conditions
-- ════════════════════════════════════════════════════════════════

/-- Reflexivity: every index accesses itself. -/
def Refl (R : AccessRel F) : Prop := ∀ i, R i i

/-- Seriality: every index accesses at least one index. -/
def Serial (R : AccessRel F) : Prop := ∀ i, ∃ j, R i j

/-- Transitivity. -/
def Trans (R : AccessRel F) : Prop := ∀ i j k, R i j → R j k → R i k

/-- Symmetry. -/
def Symm (R : AccessRel F) : Prop := ∀ i j, R i j → R j i

/-- Euclideanness. -/
def Eucl (R : AccessRel F) : Prop := ∀ i j k, R i j → R i k → R j k

-- ════════════════════════════════════════════════════════════════
-- § Frame Condition Relationships
-- ════════════════════════════════════════════════════════════════

theorem universalR_refl : Refl (universalR (F := F)) := fun _ => trivial
theorem universalR_serial : Serial (universalR (F := F)) := fun i => ⟨i, trivial⟩
theorem universalR_trans : Trans (universalR (F := F)) := fun _ _ _ _ _ => trivial
theorem universalR_symm : Symm (universalR (F := F)) := fun _ _ _ => trivial
theorem universalR_eucl : Eucl (universalR (F := F)) := fun _ _ _ _ _ => trivial

theorem refl_serial {R : AccessRel F} (h : Refl R) : Serial R :=
  fun i => ⟨i, h i⟩

theorem refl_eucl_symm {R : AccessRel F} (hR : Refl R) (hE : Eucl R) : Symm R :=
  fun i j hij => hE i j i hij (hR i)

theorem refl_eucl_trans {R : AccessRel F} (hR : Refl R) (hE : Eucl R) : Trans R :=
  fun i j k hij hjk => hE j i k (refl_eucl_symm hR hE i j hij) hjk

-- ════════════════════════════════════════════════════════════════
-- § Restricted Box and Diamond
-- ════════════════════════════════════════════════════════════════

/-- Restricted necessity: `□_R p` at index `i` holds iff `p j` for all
    `j` accessible from `i`.

    `⟦□_R φ⟧^i = 1` iff `⟦φ⟧^j = 1` for all `j` with `R(i,j)`.

    This is the Kripke generalization of DWP's Rule B.13 (`box`). -/
def boxR (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) : F.Denot .t :=
  ∀ j, R i j → p j

/-- Restricted possibility: `◇_R p` at index `i` holds iff `p j` for some
    `j` accessible from `i`. Dual of `boxR`. -/
def diamondR (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) : F.Denot .t :=
  ∃ j, R i j ∧ p j

-- ════════════════════════════════════════════════════════════════
-- § Specialization: S5 as Universal Accessibility
-- ════════════════════════════════════════════════════════════════

/-- S5 necessity (`box`) is restricted necessity with universal accessibility. -/
theorem boxR_universal (p : F.Denot .prop) :
    (fun i => boxR universalR p i) = (fun _ => box (F := F) p) := by
  ext i
  simp only [boxR, universalR, box, forall_true_left]

/-- S5 possibility (`diamond`) is restricted possibility with universal accessibility. -/
theorem diamondR_universal (p : F.Denot .prop) :
    (fun i => diamondR universalR p i) = (fun _ => diamond (F := F) p) := by
  ext i
  simp only [diamondR, universalR, diamond, true_and]

-- ════════════════════════════════════════════════════════════════
-- § Duality
-- ════════════════════════════════════════════════════════════════

/-- `□_R p ↔ ¬◇_R ¬p` — restricted modal duality. -/
theorem boxR_neg_diamondR (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) :
    boxR R p i = neg (diamondR R (fun j => neg (p j)) i) := by
  simp only [boxR, diamondR, neg, not_exists, not_and, not_not]

/-- `◇_R p ↔ ¬□_R ¬p` — dual form. -/
theorem diamondR_neg_boxR (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) :
    diamondR R p i = neg (boxR R (fun j => neg (p j)) i) := by
  simp only [diamondR, boxR, neg]
  exact propext ⟨
    fun ⟨j, hij, hpj⟩ h => h j hij hpj,
    fun h => Classical.byContradiction fun hne => by
      simp only [not_exists, not_and] at hne
      exact h (fun j hij => hne j hij)⟩

-- ════════════════════════════════════════════════════════════════
-- § Modal Axiom Correspondence
-- ════════════════════════════════════════════════════════════════

/-- **K axiom**: `□_R(p → q) → (□_R p → □_R q)`.
    Holds for any accessibility relation — the fundamental distribution axiom. -/
theorem boxR_K (R : AccessRel F) (p q : F.Denot .prop) (i : F.Index) :
    impl (boxR R (fun j => impl (p j) (q j)) i)
         (impl (boxR R p i) (boxR R q i)) :=
  fun hpq hp j hij => hpq j hij (hp j hij)

/-- **T axiom**: reflexive `R` gives `□_R p i → p i`.
    What is necessary is actual. -/
theorem boxR_T (R : AccessRel F) (hR : Refl R) (p : F.Denot .prop) (i : F.Index)
    (h : boxR R p i) : p i :=
  h i (hR i)

/-- **D axiom**: serial `R` gives `□_R p i → ◇_R p i`.
    What is necessary is possible. -/
theorem boxR_D (R : AccessRel F) (hS : Serial R) (p : F.Denot .prop) (i : F.Index)
    (h : boxR R p i) : diamondR R p i :=
  let ⟨j, hij⟩ := hS i; ⟨j, hij, h j hij⟩

/-- **4 axiom**: transitive `R` gives `□_R p → □_R □_R p`.
    Positive introspection. -/
theorem boxR_four (R : AccessRel F) (hT : Trans R) (p : F.Denot .prop) (i : F.Index)
    (h : boxR R p i) : boxR R (boxR R p) i :=
  fun j hij k hjk => h k (hT i j k hij hjk)

/-- **B axiom**: symmetric `R` gives `p i → □_R ◇_R p i`.
    What is actual is necessarily possible. -/
theorem boxR_B (R : AccessRel F) (hS : Symm R) (p : F.Denot .prop) (i : F.Index)
    (h : p i) : boxR R (diamondR R p) i :=
  fun j hij => ⟨i, hS i j hij, h⟩

/-- **5 axiom**: euclidean `R` gives `◇_R p i → □_R ◇_R p i`.
    Positive possibility introspection. -/
theorem boxR_five (R : AccessRel F) (hE : Eucl R) (p : F.Denot .prop) (i : F.Index)
    (h : diamondR R p i) : boxR R (diamondR R p) i :=
  let ⟨k, hik, hpk⟩ := h
  fun j hij => ⟨k, hE i j k hij hik, hpk⟩

-- ════════════════════════════════════════════════════════════════
-- § Monotonicity
-- ════════════════════════════════════════════════════════════════

/-- `boxR R` is monotone: if `p ≤ q` pointwise, then `□_R p ≤ □_R q`. -/
theorem boxR_mono (R : AccessRel F) {p q : F.Denot .prop}
    (h : ∀ j, p j → q j) (i : F.Index)
    (hb : boxR R p i) : boxR R q i :=
  fun j hij => h j (hb j hij)

/-- `diamondR R` is monotone. -/
theorem diamondR_mono (R : AccessRel F) {p q : F.Denot .prop}
    (h : ∀ j, p j → q j) (i : F.Index)
    (hd : diamondR R p i) : diamondR R q i :=
  let ⟨j, hij, hpj⟩ := hd; ⟨j, hij, h j hpj⟩

-- ════════════════════════════════════════════════════════════════
-- § Distribution over Connectives
-- ════════════════════════════════════════════════════════════════

/-- `□_R` distributes over `∧`. -/
theorem boxR_conj (R : AccessRel F) (p q : F.Denot .prop) (i : F.Index) :
    boxR R (fun j => conj (p j) (q j)) i =
    conj (boxR R p i) (boxR R q i) := by
  simp only [boxR, conj]
  exact propext ⟨fun h => ⟨fun j hij => (h j hij).1, fun j hij => (h j hij).2⟩,
                  fun ⟨hp, hq⟩ j hij => ⟨hp j hij, hq j hij⟩⟩

/-- `◇_R` distributes over `∨`. -/
theorem diamondR_disj (R : AccessRel F) (p q : F.Denot .prop) (i : F.Index) :
    diamondR R (fun j => disj (p j) (q j)) i =
    disj (diamondR R p i) (diamondR R q i) := by
  simp only [diamondR, disj]
  exact propext ⟨
    fun ⟨j, hij, h⟩ => h.elim (fun hp => .inl ⟨j, hij, hp⟩) (fun hq => .inr ⟨j, hij, hq⟩),
    fun h => h.elim (fun ⟨j, hij, hp⟩ => ⟨j, hij, .inl hp⟩)
                     (fun ⟨j, hij, hq⟩ => ⟨j, hij, .inr hq⟩)⟩

/-- Necessitation: if `p` holds at every index, then `□_R p` holds everywhere. -/
theorem boxR_necessitation (R : AccessRel F) (p : F.Denot .prop)
    (h : ∀ j, p j) (i : F.Index) : boxR R p i :=
  fun j _ => h j

-- ════════════════════════════════════════════════════════════════
-- § Accessibility Restriction (Kratzer's Insight)
-- ════════════════════════════════════════════════════════════════

/-- Restricting accessibility strengthens necessity:
    if `R₂ ⊆ R₁`, then `□_{R₁} p → □_{R₂} p`. -/
theorem boxR_restrict {R₁ R₂ : AccessRel F}
    (h : ∀ i j, R₂ i j → R₁ i j) (p : F.Denot .prop) (i : F.Index)
    (hb : boxR R₁ p i) : boxR R₂ p i :=
  fun j hij => hb j (h i j hij)

/-- Restricting accessibility weakens possibility:
    if `R₂ ⊆ R₁`, then `◇_{R₂} p → ◇_{R₁} p`. -/
theorem diamondR_restrict {R₁ R₂ : AccessRel F}
    (h : ∀ i j, R₂ i j → R₁ i j) (p : F.Denot .prop) (i : F.Index)
    (hd : diamondR R₂ p i) : diamondR R₁ p i :=
  let ⟨j, hij, hpj⟩ := hd; ⟨j, h i j hij, hpj⟩

/-- S5 box implies any restricted box (since universal R is the weakest
    restriction — everything is accessible). -/
theorem box_implies_boxR (R : AccessRel F) (p : F.Denot .prop)
    (h : box (F := F) p) (i : F.Index) : boxR R p i :=
  fun j _ => h j

/-- Any restricted diamond implies S5 diamond (some world is accessible
    and satisfies p, so certainly some world satisfies p). -/
theorem diamondR_implies_diamond (R : AccessRel F) (p : F.Denot .prop) (i : F.Index)
    (h : diamondR R p i) : diamond (F := F) p :=
  let ⟨j, _, hpj⟩ := h; ⟨j, hpj⟩

-- ════════════════════════════════════════════════════════════════
-- § Lattice-Theoretic Formulation
-- ════════════════════════════════════════════════════════════════

/-! `boxR` and `diamondR` are restricted infima and suprema over the
accessible index set, connecting to the lattice bridge in `Algebra.lean`.

In contrast to the unrestricted `box_eq_iInf` / `diamond_eq_iSup` from
`Algebra.lean`, the restricted versions quantify over the subtype of
accessible indices. -/

/-- `boxR R p i` is the infimum of `p j` over indices `j` accessible from `i`. -/
theorem boxR_eq_forall (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) :
    boxR R p i = (∀ j, R i j → p j) := rfl

/-- `diamondR R p i` is the supremum of `p j` over indices `j` accessible from `i`. -/
theorem diamondR_eq_exists (R : AccessRel F) (p : F.Denot .prop) (i : F.Index) :
    diamondR R p i = (∃ j, R i j ∧ p j) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Entailment with Restricted Modality
-- ════════════════════════════════════════════════════════════════

open Core.IntensionalLogic.Algebra (valid entails trueAt)

/-- A valid proposition is R-necessary at every index (for any R). -/
theorem valid_boxR (R : AccessRel F) (p : F.Denot .prop)
    (hv : valid (F := F) p) (i : F.Index) : boxR R p i :=
  fun j _ => hv j

/-- Semantic entailment lifts to restricted modality:
    if `p ⊨ q` then `□_R p ⊨ □_R q`. -/
theorem boxR_entailment_lift (R : AccessRel F)
    (p q : F.Denot .prop)
    (h : ∀ j, p j → q j)
    (i : F.Index) (hb : boxR R p i) : boxR R q i :=
  boxR_mono R h i hb

-- ════════════════════════════════════════════════════════════════
-- § S5 Recovery Theorems
-- ════════════════════════════════════════════════════════════════

/-- With reflexive + euclidean accessibility (= S5 frame conditions),
    `boxR` validates all of T, D, 4, B, 5. -/
theorem S5_frame_all_axioms (R : AccessRel F)
    (hR : Refl R) (hE : Eucl R) :
    (∀ p i, boxR R p i → p i) ∧                          -- T
    (∀ p i, boxR R p i → diamondR R p i) ∧               -- D
    (∀ p i, boxR R p i → boxR R (boxR R p) i) ∧          -- 4
    (∀ p i, p i → boxR R (diamondR R p) i) ∧             -- B
    (∀ p i, diamondR R p i → boxR R (diamondR R p) i) := -- 5
  ⟨fun p i => boxR_T R hR p i,
   fun p i => boxR_D R (refl_serial hR) p i,
   fun p i => boxR_four R (refl_eucl_trans hR hE) p i,
   fun p i => boxR_B R (refl_eucl_symm hR hE) p i,
   fun p i => boxR_five R hE p i⟩

end Core.IntensionalLogic.RestrictedModality
