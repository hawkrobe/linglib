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
  worlds. This is the same operation underlying subjunctive conditionals
  (@cite{von-fintel-iatridou-2023}).

- **Xg** (ordering source revision): refines the ordering by favoring p-worlds
  among those previously ranked as best, adding a secondary ordering criterion.
  This is exactly `Directive.combineOrdering g (λ _ => [p])`.

Applied to strong necessity (SN), these generate the **square of necessities**:

```
    SN ────Xf────→ SN_Xf
    │                │
    Xg               Xg
    │                │
    SN_Xg ──Xf────→ SN_{Xf,g}
```

Portuguese instantiates all four vertices: *tem que* (SN), *tinha que* (SN_Xf),
*deve* (SN_Xg = WN), *devia* (SN_{Xf,g}).

The central equation: **WN ≡ SN_Xg** — weak necessity IS strong necessity with
X-marked ordering source. This connects to `Directive.weakNecessity` by `rfl`.
-/

namespace Semantics.Modality.Kratzer.XMarking

open Semantics.Modality.Kratzer
open Semantics.Modality.Directive
open Semantics.Attitudes.Intensional
open Core.Proposition

/-! ## Star-revision: X-marking on modal bases (Xf) -/

/-- Property: f' is a **∗-revision** of f for p (@cite{ferreira-2023}, §3).

    A ∗-revision widens the modal domain by adding p-worlds:
    (1) every world accessible under f remains accessible under f',
    (2) every newly accessible world satisfies p.

    **Morphosyntactic trigger**: In @cite{von-fintel-iatridou-2023}'s context-tower
    framework, ∗-revision is triggered by modal ExclF (exclusion feature),
    realized as past morphology. See `Conditionals.Iatridou.xMarking_produces_modal_exclF`
    for the context-level formalization. -/
structure IsStarRevision (f f' : ModalBase) (p : BProp World) : Prop where
  /-- Domain widening: ∩f_w ⊆ ∩f'_w -/
  widens : ∀ w w', w' ∈ accessibleWorlds f w → w' ∈ accessibleWorlds f' w
  /-- New worlds satisfy p -/
  new_satisfy_p : ∀ w w', w' ∈ accessibleWorlds f' w →
    w' ∉ accessibleWorlds f w → p w' = true

/-- A ∗-revision widens the accessible world set. -/
theorem starRevision_widens {f f' : ModalBase} {p : BProp World}
    (h : IsStarRevision f f' p) (w w' : World)
    (hw : w' ∈ accessibleWorlds f w) :
    w' ∈ accessibleWorlds f' w :=
  h.widens w w' hw

/-- Worlds added by a ∗-revision all satisfy p. -/
theorem starRevision_new_satisfy_p {f f' : ModalBase} {p : BProp World}
    (h : IsStarRevision f f' p) (w w' : World)
    (hw' : w' ∈ accessibleWorlds f' w) (hnew : w' ∉ accessibleWorlds f w) :
    p w' = true :=
  h.new_satisfy_p w w' hw' hnew

/-! ## Double-star-revision: X-marking on ordering sources (Xg) -/

/-- **Xg**: X-marking targeting the ordering source (∗∗-revision).

    Adds a secondary ordering that favors p-worlds among the best worlds.
    This is precisely `combineOrdering g (λ _ => [p])` from `Directive.lean`:
    the combined ordering g ∪ [p] ranks w₁ above w₂ when w₁ satisfies all
    the g-ideals that w₂ does AND w₁ satisfies p whenever w₂ does.

    The net effect: among g-equivalent worlds, p-worlds are ranked higher.

    **Formulation note**: @cite{ferreira-2023} defines ∗∗-revision via
    better-than-triples (BTT, definition (131)). We follow the equivalent
    @cite{von-fintel-iatridou-2008} formulation using `combineOrdering`,
    which integrates directly with the existing Kratzer infrastructure.
    The equivalence holds because BTT adds a secondary p-ordering to the
    existing ordering source, which is exactly what `combineOrdering g [p]` does. -/
def xMarkOrdering (g : OrderingSource) (p : BProp World) : OrderingSource :=
  combineOrdering g (λ _ => [p])

/-! ## The four vertices of the square -/

/-- **SN**: unmarked strong necessity.
    Portuguese *tem que*, English *must*/*have to*. -/
abbrev sn (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f g p w

/-- **SN_Xg**: strong necessity with X-marked ordering source = weak necessity.
    Portuguese *deve*, English *ought*/*should* (non-X-marked reading). -/
def snXg (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f (xMarkOrdering g p) p w

/-- **SN_Xf**: strong necessity with X-marked modal base.
    Portuguese *tinha que*. Domain is widened to include p-worlds. -/
def snXf (f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f' g p w

/-- **SN_{Xf,g}**: both X-markings applied.
    Portuguese *devia*, English *ought*/*should* (X-marked reading). -/
def snXfg (f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f' (xMarkOrdering g p) p w

/-! ## Key equation: WN ≡ SN_Xg -/

/-- **WN ≡ SN_Xg**: weak necessity (from `Directive.lean`) with secondary
    ordering [p] is definitionally equal to strong necessity with X-marked
    ordering source.

    This is the central structural result: Ferreira's Xg IS the von Fintel &
    Iatridou (2008) secondary ordering source, when that source ranks worlds
    by the prejacent. -/
theorem wn_equiv_snXg (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    weakNecessity f g (λ _ => [p]) p w = snXg f g p w := rfl

/-! ## Entailment: SN → SN_Xg (must → ought) -/

/-- Strong necessity entails its Xg-marked counterpart.
    Direct corollary of `Directive.strong_entails_weak`. -/
theorem sn_entails_snXg (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (h : sn f g p w = true) :
    snXg f g p w = true :=
  strong_entails_weak f g (λ _ => [p]) p w h

/-- The converse fails: SN_Xg ⊭ SN.

    Counterexample: f accessible = {w0, w1}, g empty, p = w0.
    Under g, all worlds are tied → best = {w0, w1} → sn = false (w1 fails p).
    Under g∪[p], w0 outranks w1 → best = {w0} → snXg = true. -/
theorem snXg_not_entails_sn :
    ¬(∀ (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
        snXg f g p w = true → sn f g p w = true) := by
  intro h
  let f : ModalBase := λ _ => [λ w => w == .w0 || w == .w1]
  let g : OrderingSource := emptyBackground
  let p : BProp World := λ w => w == .w0
  exact absurd (h f g p .w0 (by decide)) (by decide)

/-! ## Xf does not change entailment direction -/

/-- Xf preserves the quantifier: SN_Xf is still ∀ over best worlds.
    The only difference is the domain — the universal quantification
    ranges over bestWorlds of the widened modal base. -/
theorem xf_is_universal (f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    snXf f' g p w = (bestWorlds f' g w).all p := rfl

/-- SN_Xf does not entail SN: the wider domain can promote new worlds
    that change which worlds are best, breaking SN even when SN_Xf holds.

    Counterexample: f accessible = {w0, w1}, f' adds w2 (∗-revision, p-world).
    g ranks w2 highest. best(f) = {w0, w1} (tied), but p(w1) = false → sn = false.
    best(f') = {w2}, p(w2) = true → snXf = true. -/
theorem xf_no_entailment :
    ¬(∀ (f f' : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
        IsStarRevision f f' p →
        snXf f' g p w = true → sn f g p w = true) := by
  intro h
  have hRev : IsStarRevision
      (λ _ => [λ w => w == .w0 || w == .w1])
      (λ _ => [λ w => w == .w0 || w == .w1 || w == .w2])
      (λ w => w == .w0 || w == .w2) := by
    constructor
    · intro w w' hw'
      unfold accessibleWorlds propIntersection at hw' ⊢
      simp only [List.mem_filter] at hw' ⊢
      exact ⟨hw'.1, by cases w' <;> simp_all⟩
    · intro w w' hw' hnew
      unfold accessibleWorlds propIntersection at hw'
      simp only [List.mem_filter] at hw'
      cases w' <;> simp_all [accessibleWorlds, propIntersection, allWorlds]
  exact absurd
    (h _ _ (λ _ => [λ w => w == .w2]) _ .w0 hRev (by decide))
    (by decide)

/-! ## Forward entailment: SN → SN_Xf under star-revision -/

/-- **SN → SN_Xf**: strong necessity under f entails strong necessity under
    any ∗-revision f' of f.

    Proof: Take any w' ∈ bestWorlds(f', g, w). Either:
    (a) w' ∈ accessibleWorlds(f, w): then w' is best in the wider domain, hence
        best in the narrower domain (`bestAmong_superset`), so p w' = true by hSN.
    (b) w' ∉ accessibleWorlds(f, w): then w' was added by the ∗-revision,
        so p w' = true by `IsStarRevision.new_satisfy_p`. -/
theorem sn_entails_snXf (f f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (hRev : IsStarRevision f f' p)
    (hSN : sn f g p w = true) :
    snXf f' g p w = true := by
  show (bestAmong (accessibleWorlds f' w) (g w)).all p = true
  rw [List.all_eq_true]
  intro w' hw'
  have hw'_acc : w' ∈ accessibleWorlds f' w := bestAmong_sub _ _ w' hw'
  by_cases hmem : w' ∈ accessibleWorlds f w
  · have hBest : w' ∈ bestAmong (accessibleWorlds f w) (g w) :=
      bestAmong_superset (hRev.widens w) hw' hmem
    exact List.all_eq_true.mp hSN w' hBest
  · exact hRev.new_satisfy_p w w' hw'_acc hmem

/-! ## Parameter independence: Xf and Xg target independent parameters -/

/-- Xf and Xg target independent parameters (modal base vs ordering source),
    so `snXfg` is well-defined regardless of the conceptual order of application.
    This is a definitional observation: `snXfg` is `necessity f' (xMarkOrdering g p) p w`
    by construction. -/
theorem xMarking_parameter_independence (f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    snXfg f' g p w =
    necessity f' (xMarkOrdering g p) p w := rfl

/-! ## Forward entailments along square edges -/

/-- **SN_Xg → SN_Xfg**: weak necessity entails X-marked weak necessity under
    ∗-revision. Follows from `sn_entails_snXf` by substituting the refined
    ordering `xMarkOrdering g p` for `g`. -/
theorem snXg_entails_snXfg (f f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (hRev : IsStarRevision f f' p)
    (h : snXg f g p w = true) :
    snXfg f' g p w = true :=
  sn_entails_snXf f f' (xMarkOrdering g p) p w hRev h

/-- **SN_Xf → SN_Xfg**: X-marked strong necessity entails doubly X-marked
    necessity. Follows from `sn_entails_snXg` since `snXf f' g p w = sn f' g p w`
    by definition. -/
theorem snXf_entails_snXfg (f' : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (h : snXf f' g p w = true) :
    snXfg f' g p w = true :=
  sn_entails_snXg f' g p w h

/-! ## Entailment diamond

The four vertices form a Hasse diagram under entailment:

```
         SN
        ╱  ╲
      Xf    Xg
        ╲  ╱
        Xfg
```

All arrows point downward: SN entails both SN_Xf and SN_Xg, and both entail
SN_Xfg. No reverse entailments hold (proved below). -/

/-! ## Non-entailment: reverse arrows all fail -/

/-- SN_Xfg does not entail SN_Xg: the wider domain from Xf can promote
    new p-worlds that change the best set under the refined ordering.

    Portuguese: devia p ⊬ deve p (@cite{ferreira-2023}).
    Counterexample: f accessible = {w1} (no p-worlds), f' adds w0 (p-world).
    Under refined ordering [g, p], best(f) = {w1} with p(w1) = false → snXg = false.
    best(f') = {w0} with p(w0) = true → snXfg = true. -/
theorem xMarked_unmarked_independent :
    ¬(∀ (f f' : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
        IsStarRevision f f' p →
        snXfg f' g p w = true → snXg f g p w = true) := by
  intro h
  have hRev : IsStarRevision
      (λ _ => [λ w => w == .w1])
      (λ _ => [λ w => w == .w0 || w == .w1])
      (λ w => w == .w0) := by
    constructor
    · intro w w' hw'
      unfold accessibleWorlds propIntersection at hw' ⊢
      simp only [List.mem_filter] at hw' ⊢
      exact ⟨hw'.1, by cases w' <;> simp_all⟩
    · intro w w' hw' hnew
      unfold accessibleWorlds propIntersection at hw'
      simp only [List.mem_filter] at hw'
      cases w' <;> simp_all [accessibleWorlds, propIntersection, allWorlds]
  exact absurd
    (h _ _ (λ _ => [λ w => w == .w3]) _ .w0 hRev (by decide))
    (by decide)

/-- SN_Xfg does not entail SN_Xf: the refined ordering (Xg) can narrow the
    best set to only p-worlds, making SN_Xfg true while SN_Xf is false.

    Counterexample: same as `snXg_not_entails_sn` — adding p to the ordering
    narrows best worlds to p-satisfiers, but without p in the ordering, non-p
    worlds can be best. -/
theorem snXfg_not_entails_snXf :
    ¬(∀ (f' : ModalBase) (g : OrderingSource) (p : BProp World) (w : World),
        snXfg f' g p w = true → snXf f' g p w = true) := by
  intro h
  let f' : ModalBase := λ _ => [λ w => w == .w0 || w == .w1]
  let g : OrderingSource := emptyBackground
  let p : BProp World := λ w => w == .w0
  exact absurd (h f' g p .w0 (by decide)) (by decide)

end Semantics.Modality.Kratzer.XMarking
