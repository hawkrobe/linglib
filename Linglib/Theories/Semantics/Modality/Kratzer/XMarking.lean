import Linglib.Theories.Semantics.Modality.Directive

/-!
# X-Marking on Necessity Modals
@cite{ferreira-2023} @cite{von-fintel-iatridou-2023}

X-marking is a morphological operation (realized as past imperfect in Portuguese,
covert ambiguity in English) that shifts the modal parameters of necessity modals
without changing their quantificational force (both remain ∀ over best worlds).

Two independent X-marking operations target the two Kratzerian parameters:

- **Xf** (modal base revision): widens the domain ∩f_w by suspending presupposed
  evidence against the prejacent, adding p-worlds similar to currently accessible
  worlds.

- **Xg** (ordering source revision): refines the ordering by favoring p-worlds
  among those previously ranked as best.

Applied to strong necessity (SN), these generate the **square of necessities**:

```
    SN ────Xf────→ SN_Xf
    │                │
    Xg               Xg
    │                │
    SN_Xg ──Xf────→ SN_{Xf,g}
```

The central equation: **WN ≡ SN_Xg** — weak necessity IS strong necessity with
X-marked ordering source.
-/

namespace Semantics.Modality.Kratzer.XMarking

open Semantics.Modality.Kratzer
open Semantics.Modality.Directive

variable {W : Type*} [DecidableEq W] [Fintype W]

/-! ## Star-revision: X-marking on modal bases (Xf) -/

/-- Property: f' is a **∗-revision** of f for p (@cite{ferreira-2023}, §3).

    A ∗-revision widens the modal domain by adding p-worlds:
    (1) every world accessible under f remains accessible under f',
    (2) every newly accessible world satisfies p. -/
structure IsStarRevision (f f' : ModalBase W) (p : W → Bool) : Prop where
  widens : ∀ w w', w' ∈ accessibleWorlds f w → w' ∈ accessibleWorlds f' w
  new_satisfy_p : ∀ w w', w' ∈ accessibleWorlds f' w →
    w' ∉ accessibleWorlds f w → p w' = true

theorem starRevision_widens {f f' : ModalBase W} {p : W → Bool}
    (h : IsStarRevision f f' p) (w w' : W)
    (hw : w' ∈ accessibleWorlds f w) :
    w' ∈ accessibleWorlds f' w :=
  h.widens w w' hw

theorem starRevision_new_satisfy_p {f f' : ModalBase W} {p : W → Bool}
    (h : IsStarRevision f f' p) (w w' : W)
    (hw' : w' ∈ accessibleWorlds f' w) (hnew : w' ∉ accessibleWorlds f w) :
    p w' = true :=
  h.new_satisfy_p w w' hw' hnew

/-! ## Double-star-revision: X-marking on ordering sources (Xg) -/

/-- **Xg**: X-marking targeting the ordering source (∗∗-revision).
    Adds a secondary ordering that favors p-worlds among the best worlds. -/
def xMarkOrdering (g : OrderingSource W) (p : W → Bool) : OrderingSource W :=
  combineOrdering g (λ _ => [p])

/-! ## The four vertices of the square -/

abbrev sn (f : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) : Prop :=
  necessity f g p w

@[reducible] def snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) : Prop :=
  necessity f (xMarkOrdering g p) p w

@[reducible] def snXf (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) : Prop :=
  necessity f' g p w

@[reducible] def snXfg (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) : Prop :=
  necessity f' (xMarkOrdering g p) p w

/-! ## Key equation: WN ≡ SN_Xg -/

theorem wn_equiv_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) :
    weakNecessity f g (λ _ => [p]) p w ↔ snXg f g p w := Iff.rfl

/-! ## Entailment: SN → SN_Xg (must → ought) -/

theorem sn_entails_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W)
    (h : sn f g p w) :
    snXg f g p w :=
  strong_entails_weak f g (λ _ => [p]) p w h

/-- The converse fails: SN_Xg ⊭ SN. -/
theorem snXg_not_entails_sn :
    ¬(∀ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
        (f : ModalBase W) (g : OrderingSource W) (p : W → Bool) (w : W),
        snXg f g p w → sn f g p w) := by
  intro h
  have := h Bool instDecidableEqBool inferInstance
    (fun _ => [fun w => w == true || w == false])
    (emptyBackground (W := Bool))
    (fun w => w == true)
    true
  exact absurd (this (by decide)) (by decide)

/-! ## Forward entailment: SN → SN_Xf under star-revision -/

theorem sn_entails_snXf (f f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W)
    (hRev : IsStarRevision f f' p)
    (hSN : sn f g p w) :
    snXf f' g p w := by
  rw [snXf, necessity_iff_all]
  rw [sn, necessity_iff_all] at hSN
  intro w' hw'
  have hw'_acc : w' ∈ accessibleWorlds f' w := bestAmong_sub _ _ w' hw'
  by_cases hmem : w' ∈ accessibleWorlds f w
  · have hBest : w' ∈ bestAmong (accessibleWorlds f w) (g w) :=
      bestAmong_superset (hRev.widens w) hw' hmem
    exact hSN w' hBest
  · exact hRev.new_satisfy_p w w' hw'_acc hmem

/-! ## Forward entailments along square edges -/

theorem snXg_entails_snXfg (f f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W)
    (hRev : IsStarRevision f f' p)
    (h : snXg f g p w) :
    snXfg f' g p w :=
  sn_entails_snXf f f' (xMarkOrdering g p) p w hRev h

theorem snXf_entails_snXfg (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W)
    (h : snXf f' g p w) :
    snXfg f' g p w :=
  sn_entails_snXg f' g p w h

theorem xMarking_parameter_independence (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) :
    snXfg f' g p w =
    necessity f' (xMarkOrdering g p) p w := rfl

/-! ## Non-entailment: reverse arrows fail -/

theorem xMarked_unmarked_independent :
    ¬(∀ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
        (f f' : ModalBase W) (g : OrderingSource W) (p : W → Bool) (w : W),
        IsStarRevision f f' p →
        snXfg f' g p w → snXg f g p w) := by
  intro h
  have hRev : IsStarRevision (W := Bool)
      (fun _ => [fun w => w == false])
      (fun _ => [fun w => w == true || w == false])
      (fun w => w == true) := by
    constructor
    · intro w w' hw'
      simp only [accessibleWorlds, propIntersection, Finset.mem_filter, Finset.mem_univ,
                  true_and, List.all_cons, List.all_nil, Bool.and_true] at hw' ⊢
      cases w' <;> simp_all
    · intro w w' hw' hnew
      simp only [accessibleWorlds, propIntersection, Finset.mem_filter, Finset.mem_univ,
                  true_and, List.all_cons, List.all_nil, Bool.and_true] at hw' hnew
      cases w' <;> simp_all
  exact absurd
    (h Bool instDecidableEqBool inferInstance _ _
      (fun _ => [fun w => w == false]) _ true hRev (by decide))
    (by decide)

theorem snXfg_not_entails_snXf :
    ¬(∀ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
        (f' : ModalBase W) (g : OrderingSource W) (p : W → Bool) (w : W),
        snXfg f' g p w → snXf f' g p w) := by
  intro h
  have := h Bool instDecidableEqBool inferInstance
    (fun _ => [fun w => w == true || w == false])
    (emptyBackground (W := Bool))
    (fun w => w == true)
    true
  exact absurd (this (by decide)) (by decide)

/-- Xf preserves the quantifier: SN_Xf is still ∀ over best worlds. -/
theorem xf_is_universal (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Bool) (w : W) :
    snXf f' g p w ↔ ∀ w' ∈ bestWorlds f' g w, p w' = true :=
  necessity_iff_all f' g p w

end Semantics.Modality.Kratzer.XMarking
