import Linglib.Semantics.Modality.Directive
import Linglib.Fragments.Portuguese.Modals
import Linglib.Fragments.English.Auxiliaries
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic

/-!
# Ferreira (2023): A square of necessities
[ferreira-2023]

A square of necessities: X-marking weak and strong necessity modals.
*Semantics and Pragmatics* 16, Article 8: 1–54.

## Core Contributions

1. Portuguese has a tripartite modal system (*poder* < *dever* < *ter que*)
   where weak necessity is lexicalized as a distinct root, unlike Spanish
   (*deber* = strong necessity) or English (*ought* = ambiguous).

2. Both weak and strong necessity modals can be X-marked via past imperfect
   morphology (*devia*, *tinha que*), but X-marking does NOT weaken modal
   force — it shifts modal parameters (modal base or ordering source).

3. Two independent X-marking operations generate a 2×2 **square of
   necessities**: Xf (modal base revision) and Xg (ordering source revision).
   Portuguese instantiates all four vertices.

4. **WN ≡ SN_Xg**: weak necessity is strong necessity with X-marked ordering
   source — the secondary ordering favors the prejacent among best worlds.

## Square Instantiation & Entailment Diamond

```
    tem que ──Xf──→ tinha que
       │                │
       Xg               Xg
       │                │
     deve ────Xf──→ devia
```

Entailment flows downward through both paths (SN → SN_Xf → SN_Xfg and
SN → SN_Xg → SN_Xfg), forming a diamond. No reverse entailments hold.
-/

namespace Ferreira2023

open Semantics.Modality.Kratzer
open Semantics.Modality.Directive
open Semantics.Modality

variable {W : Type*}

/-! ## X-marking substrate -/

/-! ### Star-revision: X-marking on modal bases (Xf) -/

/-- Property: `f'` is a **∗-revision** of `f` for `p` ([ferreira-2023]).
    A ∗-revision widens the modal domain by adding p-worlds:
    (1) every world accessible under `f` remains accessible under `f'`;
    (2) every newly accessible world satisfies `p`. -/
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

/-! ### Double-star-revision: X-marking on ordering sources (Xg) -/

/-- **Xg**: X-marking targeting the ordering source (∗∗-revision).
    Adds a secondary ordering that favors p-worlds among the best worlds. -/
def xMarkOrdering (g : OrderingSource W) (p : W → Prop) : OrderingSource W :=
  combineOrdering g (λ _ => [p])

/-! ### The four vertices of the square -/

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

/-! ### Key equation: WN ≡ SN_Xg -/

theorem wn_equiv_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (hconn : Core.Order.Normality.connected (kratzerNormality (g w))) :
    weakNecessity f g (λ _ => [p]) p w ↔ snXg f g p w := by
  constructor
  · intro hweak
    rintro w' ⟨hacc, hmin⟩
    by_cases hp : p w'
    · exact hp
    have hminG : w' ∈ bestWorlds f g w := by
      refine ⟨hacc, ?_⟩
      intro v hv hvle
      have hvle' : atLeastAsGoodAs (xMarkOrdering g p w) v w' := by
        intro q hq hqw'
        rcases List.mem_append.mp hq with hq | hq
        · exact hvle q hq hqw'
        · rcases List.mem_singleton.mp hq with rfl
          exact absurd hqw' hp
      intro q hq hqw'
      exact hmin hv hvle' q (List.mem_append_left _ hq) hqw'
    have hnop : ∀ v ∈ bestWorlds f g w, ¬ p v := by
      intro v hv hpv
      have hvle : atLeastAsGoodAs (xMarkOrdering g p w) v w' := by
        intro q hq hqw'
        rcases List.mem_append.mp hq with hq | hq
        · rcases hconn v w' with h | h
          · exact h q hq hqw'
          · exact hv.2 hminG.1 h q hq hqw'
        · rcases List.mem_singleton.mp hq with rfl
          exact absurd hqw' hp
      exact hp (hmin hv.1 hvle p
        (List.mem_append_right _ (List.mem_singleton.mpr rfl)) hpv)
    have hwmem : w' ∈ bestAmong (bestWorlds f g w) ((fun _ => [p]) w) := by
      refine ⟨hminG, ?_⟩
      intro v hv _ q hq hqv
      rcases List.mem_singleton.mp hq with rfl
      exact absurd hqv (hnop v hv)
    exact absurd (hweak w' hwmem) hp
  · intro hsnxg
    rintro w' ⟨hwB, hmin⟩
    by_cases hp : p w'
    · exact hp
    refine hsnxg w' ⟨hwB.1, ?_⟩
    intro v hv hvle
    have hvleG : atLeastAsGoodAs (g w) v w' := fun q hq hqw' =>
      hvle q (List.mem_append_left _ hq) hqw'
    have hwlev : atLeastAsGoodAs (g w) w' v := hwB.2 hv hvleG
    have hvB : v ∈ bestWorlds f g w := by
      refine ⟨hv, ?_⟩
      intro u hu hule
      have huw' : atLeastAsGoodAs (g w) u w' :=
        ordering_transitive _ u v w' hule hvleG
      exact ordering_transitive _ v w' u hvleG (hwB.2 hu huw')
    have hnopv : ¬ p v := by
      intro hpv
      have hvlp : atLeastAsGoodAs [p] v w' := by
        intro q hq hqw'
        rcases List.mem_singleton.mp hq with rfl
        exact absurd hqw' hp
      exact hp (hmin v hvB hvlp p (List.mem_singleton.mpr rfl) hpv)
    intro q hq hqv
    rcases List.mem_append.mp hq with hq | hq
    · exact hwlev q hq hqv
    · rcases List.mem_singleton.mp hq with rfl
      exact absurd hqv hnopv

/-! ### Entailment: SN → SN_Xg (must → ought) -/

theorem sn_entails_snXg (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : sn f g p w) :
    snXg f g p w := by
  rintro w' ⟨hacc, hmin⟩
  by_cases hp : p w'
  · exact hp
  · refine h w' ⟨hacc, ?_⟩
    intro v hv hvle
    have hvle' : atLeastAsGoodAs (xMarkOrdering g p w) v w' := by
      intro q hq hqw'
      rcases List.mem_append.mp hq with hq | hq
      · exact hvle q hq hqw'
      · rcases List.mem_singleton.mp hq with rfl
        exact absurd hqw' hp
    intro q hq hqw'
    exact hmin hv hvle' q (List.mem_append_left _ hq) hqw'

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
    rintro w' ⟨_, hmin⟩
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    have hTop : atLeastAsGoodAs (xMarkOrdering g p true) true w' := by
      intro q hq _
      have hq' : q = fun w => w = true := by
        simpa [xMarkOrdering, combineOrdering, g, p, emptyBackground] using hq
      subst hq'; rfl
    exact hmin (hAcc true) hTop _ hIdent rfl
  have hNotSn : ¬ sn f g p true := by
    intro hSn
    have hFalseBest : false ∈ bestWorlds f g true := by
      show false ∈ bestWorlds f emptyBackground true
      rw [empty_ordering_emptyBackground]
      exact hAcc false
    exact Bool.false_ne_true (hSn false hFalseBest)
  exact hNotSn (h Bool f g p true hSnXg)

/-! ### Forward entailment: SN → SN_Xf under star-revision -/

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

/-! ### Forward entailments along square edges -/

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

/-! ### Non-entailment: reverse arrows fail -/

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
    rintro w' ⟨_, hmin⟩
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    have hTop : atLeastAsGoodAs (xMarkOrdering g p true) true w' := by
      intro q hq _
      have hq' : q = fun w => w = true := by
        simpa [xMarkOrdering, combineOrdering, g, p, emptyBackground] using hq
      subst hq'; rfl
    exact hmin (hAccF' true) hTop _ hIdent rfl
  have hNotSnXg : ¬ snXg f g p true := by
    intro hSnXg
    have hAccFalse : false ∈ accessibleWorlds f true := by
      intro q hq
      rcases List.mem_singleton.mp hq with rfl
      rfl
    have hFalseBest : false ∈ bestWorlds f (xMarkOrdering g p) true := by
      refine ⟨hAccFalse, ?_⟩
      intro v hv _
      have hv' : v = false := hv (fun w => w = false) (List.mem_singleton.mpr rfl)
      subst hv'
      exact ordering_reflexive _ _
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
    rintro w' ⟨_, hmin⟩
    have hIdent : (fun w : Bool => w = true) ∈ xMarkOrdering g p true := by
      simp [xMarkOrdering, combineOrdering, g, p, emptyBackground]
    have hTop : atLeastAsGoodAs (xMarkOrdering g p true) true w' := by
      intro q hq _
      have hq' : q = fun w => w = true := by
        simpa [xMarkOrdering, combineOrdering, g, p, emptyBackground] using hq
      subst hq'; rfl
    exact hmin (hAcc true) hTop _ hIdent rfl
  have hNotSnXf : ¬ snXf f' g p true := by
    intro hSnXf
    have hFalseBest : false ∈ bestWorlds f' g true := by
      show false ∈ bestWorlds f' emptyBackground true
      rw [empty_ordering_emptyBackground]
      exact hAcc false
    exact Bool.false_ne_true (hSnXf false hFalseBest)
  exact hNotSnXf (h Bool f' g p true hSnXfg)

/-- Xf preserves the quantifier: SN_Xf is still ∀ over best worlds. -/
theorem xf_is_universal (f' : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    snXf f' g p w ↔ ∀ w' ∈ bestWorlds f' g w, p w' :=
  necessity_iff_all f' g p w

abbrev World := Fin 4

/-! ## Portuguese modal typology -/

/-- The six Portuguese modal forms: three roots × two tense markings. -/
inductive PortugueseModal where
  | poder    -- 'can/may' (possibility, present)
  | dever    -- 'ought' (weak necessity, present)
  | terQue   -- 'must/have to' (strong necessity, present)
  | podia    -- 'could/might' (possibility, past imperfect)
  | devia    -- 'ought-PST.IMP' (weak necessity, X-marked)
  | tinhaQue -- 'had to' (strong necessity, X-marked)
  deriving DecidableEq, Repr

/-- Modal force of each form. -/
def PortugueseModal.force : PortugueseModal → ModalForce
  | .poder | .podia       => .possibility
  | .dever | .devia       => .weakNecessity
  | .terQue | .tinhaQue   => .necessity

/-- Whether a form is X-marked (past imperfect morphology). -/
def PortugueseModal.isXMarked : PortugueseModal → Bool
  | .podia | .devia | .tinhaQue => true
  | .poder | .dever | .terQue   => false

/-- The unmarked counterpart of each form. -/
def PortugueseModal.unmarked : PortugueseModal → PortugueseModal
  | .podia    => .poder
  | .devia    => .dever
  | .tinhaQue => .terQue
  | m         => m

/-! ## Ascending scale of modal force (§2) -/

/-- *poder* p < *dever* p < *ter que* p -/
theorem ascending_force :
    ModalForce.necessity.atLeastAsStrong .weakNecessity = true ∧
    ModalForce.weakNecessity.atLeastAsStrong .possibility = true ∧
    ModalForce.possibility.atLeastAsStrong .weakNecessity = false := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## X-marking preserves force (§3) -/

/-- X-marking does not change modal force: each pair shares force. -/
theorem xMarking_preserves_force (m : PortugueseModal) :
    m.force = m.unmarked.force := by
  cases m <;> rfl

/-! ## Entailment judgments (§2) -/

/-- *ter que* p ⊨ *dever* p: strong necessity entails weak.
    Follows from `Directive.strong_entails_weak` — the Xg-refined best worlds
    are a subset of the unrefined best worlds. -/
theorem terQue_entails_dever (f : ModalBase World) (g : OrderingSource World)
    (p : (World → Prop)) (w : World)
    (h : sn f g p w) :
    snXg f g p w :=
  sn_entails_snXg f g p w h

/-- *dever* p ⊭ *ter que* p: weak necessity does not entail strong. -/
theorem dever_not_entails_terQue :
    ¬(∀ (f : ModalBase World) (g : OrderingSource World) (p : (World → Prop)) (w : World),
        snXg f g p w → sn f g p w) := by
  intro h
  -- Counterexample: f is universal access (emptyBackground), p = (· = (0 : World)).
  -- xMarkOrdering favors p-worlds, so best = {(0 : World)}; snXg holds (p (0 : World) = True).
  -- But sn fails: (1 : World) is best under empty ordering, p (1 : World) = False.
  have hCE := h
    (emptyBackground (W := World))
    (emptyBackground (W := World))
    (fun w : World => w = (0 : World))
    (0 : World)
  -- Establish snXg
  have hAcc : ∀ w' : World, w' ∈ accessibleWorlds (emptyBackground (W := World)) (0 : World) := by
    intro w'; rw [empty_base_universal_access]; exact Set.mem_univ _
  have hSnXg : snXg (emptyBackground (W := World)) (emptyBackground (W := World))
                 (fun w : World => w = (0 : World)) (0 : World) := by
    rintro w' ⟨_, hmin⟩
    have hIdent : (fun w : World => w = (0 : World)) ∈
        xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = (0 : World)) (0 : World) := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    have hTop : atLeastAsGoodAs
        (xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = (0 : World)) (0 : World))
        (0 : World) w' := by
      intro q hq _
      have hq' : q = fun w : World => w = (0 : World) := by
        simpa [xMarkOrdering, combineOrdering, emptyBackground] using hq
      subst hq'; rfl
    exact hmin (hAcc (0 : World)) hTop _ hIdent rfl
  -- snXg → sn would force w1 = w0, contradiction
  have hSn := hCE hSnXg
  rw [sn, necessity_iff_all] at hSn
  have hW1Best : ((1 : World) : World) ∈
      bestWorlds (emptyBackground (W := World)) (emptyBackground (W := World)) (0 : World) := by
    rw [empty_ordering_emptyBackground]
    exact hAcc (1 : World)
  have : ((1 : World) : World) = (0 : World) := hSn (1 : World) hW1Best
  exact absurd this (by decide)

/-- *dever* p ⊨ *poder* p: weak necessity entails possibility, completing
    the ascending scale *poder* p < *dever* p < *ter que* p.
    Requires seriality (nonempty best worlds) — the D axiom. -/
theorem dever_entails_poder (f : ModalBase World) (g : OrderingSource World)
    (p : (World → Prop)) (w : World)
    (hSerial : (bestWorlds f (xMarkOrdering g p) w).Nonempty)
    (h : snXg f g p w) :
    possibility f (xMarkOrdering g p) p w := by
  unfold snXg at h
  rw [necessity_iff_all] at h
  rw [possibility_iff_any]
  obtain ⟨w', hw'⟩ := hSerial
  exact ⟨w', hw', h w' hw'⟩

/-! ## Consistency judgments (§2) -/

/-- *dever* p ∧ ¬p is consistent: weak necessity is compatible with
    the prejacent being false ("Este homem deve ter sido assassinado,
    mas ele pode não ter sido"). -/
theorem dever_consistent_with_not_p :
    ∃ (f : ModalBase World) (g : OrderingSource World) (p : (World → Prop)) (w : World),
      snXg f g p w ∧ ¬ p w := by
  -- Model: f = universal access, g = empty, p = (· = (1 : World)).
  -- xMarkOrdering favors p-worlds, so best = {(1 : World)}; snXg holds.
  -- p (0 : World) = False, so the conjunction is satisfiable.
  refine ⟨emptyBackground,
         emptyBackground,
         (fun w : World => w = (1 : World)),
         (0 : World),
         ?_, ?_⟩
  · -- snXg: every best world satisfies p
    rintro w' ⟨_, hmin⟩
    have hAcc1 : ((1 : World) : World) ∈ accessibleWorlds (emptyBackground (W := World)) (0 : World) := by
      rw [empty_base_universal_access]; exact Set.mem_univ _
    have hIdent : (fun w : World => w = (1 : World)) ∈
        xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = (1 : World)) (0 : World) := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    have hTop : atLeastAsGoodAs
        (xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = (1 : World)) (0 : World))
        (1 : World) w' := by
      intro q hq _
      have hq' : q = fun w : World => w = (1 : World) := by
        simpa [xMarkOrdering, combineOrdering, emptyBackground] using hq
      subst hq'; rfl
    exact hmin hAcc1 hTop _ hIdent rfl
  · -- ¬ p (0 : World)
    intro h; exact absurd h (by decide)

/-- *ter que* p ∧ ¬p is contradictory when the base is realistic:
    if w ∈ ∩f(w) and all best worlds satisfy p, then w satisfies p
    (by the T axiom). -/
theorem terQue_inconsistent_with_not_p_realistic
    (f : ModalBase World) (g : OrderingSource World) (p : (World → Prop)) (w : World)
    (hReal : ∀ w, (accessibleWorlds f w) = {w})
    (hSN : sn f g p w) :
    p w :=
  totally_realistic_gives_T f g hReal p w hSN

/-! ## Non-entailment between present and past forms (§3) -/

/-- *devia* p ⊬ *deve* p: X-marking the modal base (via Xf) widens the
    domain, and the new p-worlds can change the best set under the refined
    ordering.

    Note: the reverse direction (*deve* p ⊨ *devia* p) DOES hold — see
    `PortugueseSquare.deve_entails_devia`. This follows from `sn_entails_snXf`
    applied to the refined ordering: ∗-revision only adds p-worlds, which
    cannot worsen the truth of the prejacent among best worlds. -/
theorem devia_not_entails_deve :
    ¬(∀ (f f' : ModalBase World) (g : OrderingSource World) (p : (World → Prop)) (w : World),
        IsStarRevision f f' p →
        snXfg f' g p w → snXg f g p w) := by
  intro h
  -- Counterexample: f narrow = {(1 : World)}, f' wide = {(0 : World), (1 : World)}, p = (· = (0 : World)).
  -- Under f' (wide), best worlds favor p, so snXfg holds.
  -- Under f (narrow), only (1 : World) is accessible, p (1 : World) = False, so snXg fails.
  let fNarrow : ModalBase World := fun _ => [fun w => w = (1 : World)]
  let fWide : ModalBase World := fun _ => [fun w => w = (0 : World) ∨ w = (1 : World)]
  let p : World → Prop := fun w => w = (0 : World)
  have hNarrowAcc : ∀ w' : World, w' ∈ accessibleWorlds fNarrow (0 : World) ↔ w' = (1 : World) := by
    intro w'
    refine ⟨fun hw' => hw' (fun z => z = (1 : World)) (by simp [fNarrow]), ?_⟩
    intro heq q hq; simp [fNarrow] at hq; subst hq; exact heq
  have hWideAcc : ∀ w' : World, w' ∈ accessibleWorlds fWide (0 : World) ↔ (w' = (0 : World) ∨ w' = (1 : World)) := by
    intro w'
    refine ⟨fun hw' => hw' (fun z => z = (0 : World) ∨ z = (1 : World)) (by simp [fWide]), ?_⟩
    intro heq q hq; simp [fWide] at hq; subst hq; exact heq
  have hRev : IsStarRevision fNarrow fWide p := by
    refine ⟨?_, ?_⟩
    · intro w w' hw' q hq
      have hw'1 : w' = (1 : World) := hw' (fun z => z = (1 : World)) (by simp [fNarrow])
      simp [fWide] at hq; subst hq; exact Or.inr hw'1
    · intro w w' hw' hnew
      have hWide' : w' = (0 : World) ∨ w' = (1 : World) := hw' (fun z => z = (0 : World) ∨ z = (1 : World)) (by simp [fWide])
      have hNotW1 : w' ≠ (1 : World) := by
        intro heq; apply hnew
        intro q hq; simp [fNarrow] at hq; subst hq; exact heq
      rcases hWide' with hw0 | hw1
      · exact hw0
      · exact absurd hw1 hNotW1
  have hSnXfg : snXfg fWide (emptyBackground (W := World)) p (0 : World) := by
    rintro w' ⟨_, hmin⟩
    have hAcc0 : ((0 : World) : World) ∈ accessibleWorlds fWide (0 : World) := (hWideAcc (0 : World)).mpr (Or.inl rfl)
    have hPMem : p ∈ xMarkOrdering (emptyBackground (W := World)) p (0 : World) := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    have hTop : atLeastAsGoodAs
        (xMarkOrdering (emptyBackground (W := World)) p (0 : World)) (0 : World) w' := by
      intro q hq _
      have hq' : q = p := by
        simpa [xMarkOrdering, combineOrdering, emptyBackground] using hq
      subst hq'; rfl
    exact hmin hAcc0 hTop p hPMem rfl
  have hNotSnXg : ¬ snXg fNarrow (emptyBackground (W := World)) p (0 : World) := by
    intro hSn
    have hAcc1 : ((1 : World) : World) ∈ accessibleWorlds fNarrow (0 : World) := (hNarrowAcc (1 : World)).mpr rfl
    have hBest1 : ((1 : World) : World) ∈
        bestWorlds fNarrow (xMarkOrdering (emptyBackground (W := World)) p) (0 : World) := by
      refine ⟨hAcc1, ?_⟩
      intro w'' hw'' _
      have hw''1 : w'' = (1 : World) := (hNarrowAcc w'').mp hw''
      subst hw''1
      exact ordering_reflexive _ ((1 : World) : World)
    have hPw1 : p (1 : World) := hSn (1 : World) hBest1
    exact absurd hPw1 (by decide)
  exact hNotSnXg (h fNarrow fWide (emptyBackground (W := World)) p (0 : World) hRev hSnXfg)

/-! ## Square instantiation: Portuguese occupies all four vertices -/

/-- The square of necessities applied to Portuguese modal verbs.

    Each field maps to a vertex of the square:
    - `sn` = *tem que* (strong necessity, unmarked)
    - `snXf` = *tinha que* (strong necessity, X-marked modal base)
    - `snXg` = *deve* (= weak necessity, X-marked ordering source)
    - `snXfg` = *devia* (weak necessity, X-marked modal base) -/
structure PortugueseSquare where
  /-- Modal base (epistemic/circumstantial) -/
  f : ModalBase World
  /-- ∗-revised modal base -/
  fStar : ModalBase World
  /-- Ordering source -/
  g : OrderingSource World
  /-- Prejacent -/
  p : (World → Prop)
  /-- fStar is a valid ∗-revision of f for p -/
  hRev : IsStarRevision f fStar p

/-- *tem que*: top-left vertex (SN). -/
def PortugueseSquare.temQue (sq : PortugueseSquare) (w : World) : Prop :=
  sn sq.f sq.g sq.p w

/-- *deve*: bottom-left vertex (SN_Xg = WN). -/
def PortugueseSquare.deve (sq : PortugueseSquare) (w : World) : Prop :=
  snXg sq.f sq.g sq.p w

/-- *tinha que*: top-right vertex (SN_Xf). -/
def PortugueseSquare.tinhaQue (sq : PortugueseSquare) (w : World) : Prop :=
  snXf sq.fStar sq.g sq.p w

/-- *devia*: bottom-right vertex (SN_{Xf,g}). -/
def PortugueseSquare.devia (sq : PortugueseSquare) (w : World) : Prop :=
  snXfg sq.fStar sq.g sq.p w

/-- tem que ⊨ deve: top-left entails bottom-left (SN → SN_Xg). -/
theorem PortugueseSquare.temQue_entails_deve (sq : PortugueseSquare) (w : World)
    (h : sq.temQue w) :
    sq.deve w :=
  sn_entails_snXg sq.f sq.g sq.p w h

/-! ## Forward entailment under star-revision (§3) -/

/-- tem que ⊨ tinha que: SN entails SN_Xf under ∗-revision.
    Follows from `sn_entails_snXf`: best worlds in the wider domain either
    (a) were already best in the narrower domain, or (b) are new p-worlds. -/
theorem PortugueseSquare.temQue_entails_tinhaQue (sq : PortugueseSquare) (w : World)
    (h : sq.temQue w) :
    sq.tinhaQue w :=
  sn_entails_snXf sq.f sq.fStar sq.g sq.p w sq.hRev h

/-- deve ⊨ devia: SN_Xg entails SN_{Xf,g} under ∗-revision (bottom-left → bottom-right).
    Follows from `snXg_entails_snXfg`. -/
theorem PortugueseSquare.deve_entails_devia (sq : PortugueseSquare) (w : World)
    (h : sq.deve w) :
    sq.devia w :=
  snXg_entails_snXfg sq.f sq.fStar sq.g sq.p w sq.hRev h

/-- tinha que ⊨ devia: SN_Xf entails SN_{Xf,g} (top-right → bottom-right).
    Follows from `snXf_entails_snXfg`. -/
theorem PortugueseSquare.tinhaQue_entails_devia (sq : PortugueseSquare) (w : World)
    (h : sq.tinhaQue w) :
    sq.devia w :=
  snXf_entails_snXfg sq.fStar sq.g sq.p w h

/-! ## Entailment diamond

The four vertices form a Hasse diagram — entailment flows from SN
downward to SN_Xfg through both intermediate vertices:

```
       tem que (SN)
        ╱        ╲
  tinha que     deve
    (SN_Xf)    (SN_Xg)
        ╲        ╱
       devia (SN_Xfg)
```
-/

/-! ## English ambiguity (§3) -/

/-- English *ought*/*should* is ambiguous between two square vertices:
    non-X-marked WN (SN_Xg) and X-marked WN (SN_{Xf,g}).

    Portuguese disambiguates overtly: *deve* vs *devia*.
    English collapses them into one form. -/
theorem english_ought_ambiguous_between_vertices :
    PortugueseModal.dever.force = PortugueseModal.devia.force ∧
    PortugueseModal.dever.isXMarked = false ∧
    PortugueseModal.devia.isXMarked = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## English fragment bridge (§3)

English *should* and *ought* (from `FunctionWords`) are both classified as
`.weakNecessity` — the SN_Xg vertex of the square. But unlike Portuguese,
English lacks overt X-marking morphology (*deve* vs *devia*), so the
SN_Xfg reading (counterfactual *should*) is available but not distinguished.

Note: *should* carries `tense := .Past` (morphological past = X-marking),
while *ought* carries no tense marking. Both are semantically present-tense
weak necessity in their default readings. -/

open English.Auxiliaries in
/-- English *should* and *ought* share Portuguese *dever*'s modal force
    (`.weakNecessity`), placing them at the SN_Xg vertex. -/
theorem english_portuguese_weakNecessity_correspondence :
    English.Auxiliaries.should.modalMeaning.all
        (·.force == .weakNecessity) = true ∧
    English.Auxiliaries.ought.modalMeaning.all
        (·.force == .weakNecessity) = true ∧
    PortugueseModal.dever.force = .weakNecessity := by
  exact ⟨by decide, by decide, rfl⟩

open English.Auxiliaries in
/-- English *should* has morphological past tense (X-marking), but *ought* does not.
    This reflects Iatridou's generalization: X-marking in English is realized as
    past morphology. Portuguese makes this overt: *deve* (unmarked) vs *devia*
    (past imperfect = X-marked). -/
theorem english_should_has_xmarking_morphology :
    English.Auxiliaries.should.tense = some UD.Tense.Past ∧
    English.Auxiliaries.ought.tense = none := by
  exact ⟨rfl, rfl⟩

end Ferreira2023
