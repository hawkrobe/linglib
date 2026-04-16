import Linglib.Theories.Semantics.Modality.Kratzer.XMarking
import Linglib.Fragments.Portuguese.Modals
import Linglib.Fragments.English.FunctionWords

/-!
# Ferreira (2023): A square of necessities
@cite{ferreira-2023}

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
open Semantics.Modality.Kratzer.XMarking
open Semantics.Modality.Directive
open Semantics.Attitudes.Intensional
open Core.Modality
open Core.Proposition

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
    (p : BProp World) (w : World)
    (h : sn f g p w) :
    snXg f g p w :=
  sn_entails_snXg f g p w h

/-- *dever* p ⊭ *ter que* p: weak necessity does not entail strong. -/
theorem dever_not_entails_terQue :
    ¬(∀ (f : ModalBase World) (g : OrderingSource World) (p : BProp World) (w : World),
        snXg f g p w → sn f g p w) := by
  intro h
  have := h
    (fun _ => [fun w => w == .w0 || w == .w1])
    (emptyBackground (W := World))
    (fun w => w == .w0)
    .w0
  exact absurd (this (by decide)) (by decide)

/-- *dever* p ⊨ *poder* p: weak necessity entails possibility, completing
    the ascending scale *poder* p < *dever* p < *ter que* p.
    Requires seriality (nonempty best worlds) — the D axiom. -/
theorem dever_entails_poder (f : ModalBase World) (g : OrderingSource World)
    (p : BProp World) (w : World)
    (hSerial : (bestWorlds f (xMarkOrdering g p) w).card > 0)
    (h : snXg f g p w) :
    possibility f (xMarkOrdering g p) p w := by
  unfold snXg at h
  rw [necessity_iff_all] at h
  rw [possibility_iff_any]
  obtain ⟨w', hw'⟩ := Finset.card_pos.mp hSerial
  exact ⟨w', hw', h w' hw'⟩

/-! ## Consistency judgments (§2) -/

/-- *dever* p ∧ ¬p is consistent: weak necessity is compatible with
    the prejacent being false ("Este homem deve ter sido assassinado,
    mas ele pode não ter sido"). -/
theorem dever_consistent_with_not_p :
    ∃ (f : ModalBase World) (g : OrderingSource World) (p : BProp World) (w : World),
      snXg f g p w ∧ p w = false := by
  -- Model: w0 is actual, p false at w0. Best worlds under refined ordering
  -- satisfy p, so weak necessity holds even though p is false at w0.
  refine ⟨emptyBackground,
         λ _ => [λ w => w == .w0 || w == .w1],
         λ w => w == .w1,
         .w0,
         ?_, by decide⟩
  unfold snXg
  rw [necessity_iff_all]
  decide

/-- *ter que* p ∧ ¬p is contradictory when the base is realistic:
    if w ∈ ∩f(w) and all best worlds satisfy p, then w satisfies p
    (by the T axiom). -/
theorem terQue_inconsistent_with_not_p_realistic
    (f : ModalBase World) (g : OrderingSource World) (p : BProp World) (w : World)
    (hReal : ∀ w, (accessibleWorlds f w) = {w})
    (hSN : sn f g p w) :
    p w = true :=
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
    ¬(∀ (f f' : ModalBase World) (g : OrderingSource World) (p : BProp World) (w : World),
        IsStarRevision f f' p →
        snXfg f' g p w → snXg f g p w) := by
  intro h
  have hRev : IsStarRevision (W := World)
      (fun _ => [fun w => w == .w1])
      (fun _ => [fun w => w == .w0 || w == .w1])
      (fun w => w == .w0) := by
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
    (h _ _
      (fun _ => [fun w => w == .w1]) _ .w0 hRev (by decide))
    (by decide)

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
  p : BProp World
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

open Fragments.English in
/-- English *should* and *ought* share Portuguese *dever*'s modal force
    (`.weakNecessity`), placing them at the SN_Xg vertex. -/
theorem english_portuguese_weakNecessity_correspondence :
    FunctionWords.should.modalMeaning.all (·.force == .weakNecessity) = true ∧
    FunctionWords.ought.modalMeaning.all (·.force == .weakNecessity) = true ∧
    PortugueseModal.dever.force = .weakNecessity := by
  exact ⟨by decide, by decide, rfl⟩

open Fragments.English in
/-- English *should* has morphological past tense (X-marking), but *ought* does not.
    This reflects Iatridou's generalization: X-marking in English is realized as
    past morphology. Portuguese makes this overt: *deve* (unmarked) vs *devia*
    (past imperfect = X-marked). -/
theorem english_should_has_xmarking_morphology :
    FunctionWords.should.tense = some .Past ∧
    FunctionWords.ought.tense = none := by
  exact ⟨rfl, rfl⟩

end Ferreira2023
