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

variable {W : Type*}

/-! ## Star-revision: X-marking on modal bases (Xf) -/

/-- Property: f' is a **∗-revision** of f for p (@cite{ferreira-2023}, §3).

    A ∗-revision widens the modal domain by adding p-worlds:
    (1) every world accessible under f remains accessible under f',
    (2) every newly accessible world satisfies p. -/
structure IsStarRevision (f f' : ModalBase W) (p : W → Prop) : Prop where
  widens : ∀ w w', w' ∈ accessibleWorlds f w → w' ∈ accessibleWorlds f' w
  new_satisfy_p : ∀ w w', w' ∈ accessibleWorlds f' w →
    w' ∉ accessibleWorlds f w → p w'

theorem starRevision_widens {f f' : ModalBase W} {p : W → Prop}
    (h : IsStarRevision f f' p) (w w' : W)
    (hw : w' ∈ accessibleWorlds f w) :
    w' ∈ accessibleWorlds f' w :=
  h.widens w w' hw

theorem starRevision_new_satisfy_p {f f' : ModalBase W} {p : W → Prop}
    (h : IsStarRevision f f' p) (w w' : W)
    (hw' : w' ∈ accessibleWorlds f' w) (hnew : w' ∉ accessibleWorlds f w) :
    p w' :=
  h.new_satisfy_p w w' hw' hnew

/-! ## Double-star-revision: X-marking on ordering sources (Xg) -/

/-- **Xg**: X-marking targeting the ordering source (∗∗-revision).
    Adds a secondary ordering that favors p-worlds among the best worlds. -/
def xMarkOrdering (g : OrderingSource W) (p : W → Prop) : OrderingSource W :=
  combineOrdering g (λ _ => [p])

/-! ## The four vertices of the square -/

abbrev sn (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f g p w

@[reducible] def snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f (xMarkOrdering g p) p w

@[reducible] def snXf (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f' g p w

@[reducible] def snXfg (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f' (xMarkOrdering g p) p w

/-! ## Key equation: WN ≡ SN_Xg -/

theorem wn_equiv_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    weakNecessity f g (λ _ => [p]) p w ↔ snXg f g p w := Iff.rfl

/-! ## Entailment: SN → SN_Xg (must → ought) -/

theorem sn_entails_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : sn f g p w) :
    snXg f g p w :=
  strong_entails_weak f g (λ _ => [p]) p w h

/-- The converse fails: SN_Xg ⊭ SN.

    Counterexample: W = Bool, f = universal access, g = trivial ordering,
    p = (· = true). Then snXg holds (xMarkOrdering favors `true` so best = {true}),
    but sn fails (all accessible worlds best under empty ordering, p false is false). -/
theorem snXg_not_entails_sn :
    ¬(∀ (W : Type)
        (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W),
        snXg f g p w → sn f g p w) := by
  intro h
  let f : ModalBase Bool := emptyBackground
  let g : OrderingSource Bool := emptyBackground
  let p : Bool → Prop := fun w => w = true
  have hAcc : ∀ w' : Bool, w' ∈ accessibleWorlds f true := by
    intro w' q hq; cases hq
  have hSnXg : snXg f g p true := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    exact hBest true (hAcc true) (fun w => w = true) hIdent rfl
  have hNotSn : ¬ sn f g p true := by
    intro hSn
    have hFalseBest : false ∈ bestWorlds f g true := by
      refine ⟨hAcc false, fun w'' _ q hq _ => ?_⟩
      simp [g, emptyBackground] at hq
    exact Bool.false_ne_true (hSn false hFalseBest)
  exact hNotSn (h Bool f g p true hSnXg)

/-! ## Forward entailment: SN → SN_Xf under star-revision -/

theorem sn_entails_snXf (f f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (hRev : IsStarRevision f f' p)
    (hSN : sn f g p w) :
    snXf f' g p w := by
  rw [snXf, necessity_iff_all]
  rw [sn, necessity_iff_all] at hSN
  intro w' hw'
  have hw'_acc : w' ∈ accessibleWorlds f' w := bestAmong_sub _ _ hw'
  by_cases hmem : w' ∈ accessibleWorlds f w
  · have hBest : w' ∈ bestAmong (accessibleWorlds f w) (g w) :=
      bestAmong_superset (hRev.widens w) hw' hmem
    exact hSN w' hBest
  · exact hRev.new_satisfy_p w w' hw'_acc hmem

/-! ## Forward entailments along square edges -/

theorem snXg_entails_snXfg (f f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (hRev : IsStarRevision f f' p)
    (h : snXg f g p w) :
    snXfg f' g p w :=
  sn_entails_snXf f f' (xMarkOrdering g p) p w hRev h

theorem snXf_entails_snXfg (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : snXf f' g p w) :
    snXfg f' g p w :=
  sn_entails_snXg f' g p w h

theorem xMarking_parameter_independence (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    snXfg f' g p w =
    necessity f' (xMarkOrdering g p) p w := rfl

/-! ## Non-entailment: reverse arrows fail -/

theorem xMarked_unmarked_independent :
    ¬(∀ (W : Type)
        (f f' : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W),
        IsStarRevision f f' p →
        snXfg f' g p w → snXg f g p w) := by
  intro h
  -- W = Bool. f restricts to {false}; f' is universal. g is empty.
  -- p = (· = true). Then f-best = {false}, snXg fails (p false is false).
  -- f'-best with xMarkOrdering = {true}, snXfg holds.
  let f : ModalBase Bool := fun _ => [fun w => w = false]
  let f' : ModalBase Bool := emptyBackground
  let g : OrderingSource Bool := emptyBackground
  let p : Bool → Prop := fun w => w = true
  have hAccF' : ∀ w' : Bool, w' ∈ accessibleWorlds f' true := by
    intro w' q hq; cases hq
  have hRev : IsStarRevision f f' p := by
    refine ⟨?_, ?_⟩
    · intro w w' _
      exact hAccF' w'
    · intro w w' _ hnew
      -- w' is not accessible under f, so ¬ (w' = false), so w' = true
      have : ¬ (w' = false) := by
        intro h
        apply hnew
        intro q hq
        simp [f] at hq
        exact hq ▸ h
      cases w'
      · exact (this rfl).elim
      · rfl
  have hSnXfg : snXfg f' g p true := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    exact hBest true (hAccF' true) (fun w => w = true) hIdent rfl
  have hNotSnXg : ¬ snXg f g p true := by
    intro hSnXg
    -- false is accessible under f (satisfies the only proposition: w = false)
    have hAccFalse : false ∈ accessibleWorlds f true := by
      intro q hq
      rcases List.mem_singleton.mp hq with rfl
      rfl
    -- false is best under xMarkOrdering: it satisfies the trivial g and beats
    -- everything because g is empty. But it doesn't satisfy p.
    have hFalseBest : false ∈ bestWorlds f (xMarkOrdering g p) true := by
      refine ⟨hAccFalse, fun w'' hw'' q _ hqw'' => ?_⟩
      have hw : w'' = false :=
        hw'' (fun w => w = false) (List.mem_singleton.mpr rfl)
      subst hw
      exact hqw''
    exact Bool.false_ne_true (hSnXg false hFalseBest)
  exact hNotSnXg (h Bool f f' g p true hRev hSnXfg)

theorem snXfg_not_entails_snXf :
    ¬(∀ (W : Type)
        (f' : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W),
        snXfg f' g p w → snXf f' g p w) := by
  intro h
  let f' : ModalBase Bool := emptyBackground
  let g : OrderingSource Bool := emptyBackground
  let p : Bool → Prop := fun w => w = true
  have hAcc : ∀ w' : Bool, w' ∈ accessibleWorlds f' true := by
    intro w' q hq; cases hq
  have hSnXfg : snXfg f' g p true := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    exact hBest true (hAcc true) (fun w => w = true) hIdent rfl
  have hNotSnXf : ¬ snXf f' g p true := by
    intro hSnXf
    have hFalseBest : false ∈ bestWorlds f' g true := by
      refine ⟨hAcc false, fun w'' _ q hq _ => ?_⟩
      simp [g, emptyBackground] at hq
    exact Bool.false_ne_true (hSnXf false hFalseBest)
  exact hNotSnXf (h Bool f' g p true hSnXfg)

/-- Xf preserves the quantifier: SN_Xf is still ∀ over best worlds. -/
theorem xf_is_universal (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    snXf f' g p w ↔ ∀ w' ∈ bestWorlds f' g w, p w' :=
  necessity_iff_all f' g p w

end Semantics.Modality.Kratzer.XMarking
