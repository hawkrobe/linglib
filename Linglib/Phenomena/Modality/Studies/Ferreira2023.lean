import Linglib.Theories.Semantics.Modality.Kratzer.XMarking
import Linglib.Fragments.Portuguese.Modals
import Linglib.Fragments.English.Auxiliaries
import Linglib.Theories.Semantics.Attitudes.Intensional
import Mathlib.Data.Set.Basic

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
  -- Counterexample: f is universal access (emptyBackground), p = (· = .w0).
  -- xMarkOrdering favors p-worlds, so best = {.w0}; snXg holds (p .w0 = True).
  -- But sn fails: .w1 is best under empty ordering, p .w1 = False.
  have hCE := h
    (emptyBackground (W := World))
    (emptyBackground (W := World))
    (fun w : World => w = .w0)
    .w0
  -- Establish snXg
  have hAcc : ∀ w' : World, w' ∈ accessibleWorlds (emptyBackground (W := World)) .w0 := by
    intro w'; rw [empty_base_universal_access]; exact Set.mem_univ _
  have hSnXg : snXg (emptyBackground (W := World)) (emptyBackground (W := World))
                 (fun w : World => w = .w0) .w0 := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hIdent : (fun w : World => w = .w0) ∈
        xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = .w0) .w0 := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    exact hBest .w0 (hAcc .w0) (fun w : World => w = .w0) hIdent rfl
  -- snXg → sn would force w1 = w0, contradiction
  have hSn := hCE hSnXg
  rw [sn, necessity_iff_all] at hSn
  have hW1Best : (.w1 : World) ∈
      bestWorlds (emptyBackground (W := World)) (emptyBackground (W := World)) .w0 := by
    refine ⟨hAcc .w1, ?_⟩
    intro w'' _ q hq _
    simp [emptyBackground] at hq
  have : (.w1 : World) = .w0 := hSn .w1 hW1Best
  exact World.noConfusion this

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
  -- Model: f = universal access, g = empty, p = (· = .w1).
  -- xMarkOrdering favors p-worlds, so best = {.w1}; snXg holds.
  -- p .w0 = False, so the conjunction is satisfiable.
  refine ⟨emptyBackground,
         emptyBackground,
         (fun w : World => w = .w1),
         .w0,
         ?_, ?_⟩
  · -- snXg: every best world satisfies p
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hAcc1 : (.w1 : World) ∈ accessibleWorlds (emptyBackground (W := World)) .w0 := by
      rw [empty_base_universal_access]; exact Set.mem_univ _
    have hIdent : (fun w : World => w = .w1) ∈
        xMarkOrdering (emptyBackground (W := World)) (fun w : World => w = .w1) .w0 := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    exact hBest .w1 hAcc1 (fun w : World => w = .w1) hIdent rfl
  · -- ¬ p .w0
    intro h; exact World.noConfusion h

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
  -- Counterexample: f narrow = {.w1}, f' wide = {.w0, .w1}, p = (· = .w0).
  -- Under f' (wide), best worlds favor p, so snXfg holds.
  -- Under f (narrow), only .w1 is accessible, p .w1 = False, so snXg fails.
  let fNarrow : ModalBase World := fun _ => [fun w => w = .w1]
  let fWide : ModalBase World := fun _ => [fun w => w = .w0 ∨ w = .w1]
  let p : World → Prop := fun w => w = .w0
  have hNarrowAcc : ∀ w' : World, w' ∈ accessibleWorlds fNarrow .w0 ↔ w' = .w1 := by
    intro w'
    refine ⟨fun hw' => hw' (fun z => z = .w1) (by simp [fNarrow]), ?_⟩
    intro heq q hq; simp [fNarrow] at hq; subst hq; exact heq
  have hWideAcc : ∀ w' : World, w' ∈ accessibleWorlds fWide .w0 ↔ (w' = .w0 ∨ w' = .w1) := by
    intro w'
    refine ⟨fun hw' => hw' (fun z => z = .w0 ∨ z = .w1) (by simp [fWide]), ?_⟩
    intro heq q hq; simp [fWide] at hq; subst hq; exact heq
  have hRev : IsStarRevision fNarrow fWide p := by
    refine ⟨?_, ?_⟩
    · intro w w' hw' q hq
      have hw'1 : w' = .w1 := hw' (fun z => z = .w1) (by simp [fNarrow])
      simp [fWide] at hq; subst hq; exact Or.inr hw'1
    · intro w w' hw' hnew
      have hWide' : w' = .w0 ∨ w' = .w1 := hw' (fun z => z = .w0 ∨ z = .w1) (by simp [fWide])
      have hNotW1 : w' ≠ .w1 := by
        intro heq; apply hnew
        intro q hq; simp [fNarrow] at hq; subst hq; exact heq
      rcases hWide' with hw0 | hw1
      · exact hw0
      · exact absurd hw1 hNotW1
  have hSnXfg : snXfg fWide (emptyBackground (W := World)) p .w0 := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hAcc0 : (.w0 : World) ∈ accessibleWorlds fWide .w0 := (hWideAcc .w0).mpr (Or.inl rfl)
    have hPMem : p ∈ xMarkOrdering (emptyBackground (W := World)) p .w0 := by
      simp [xMarkOrdering, combineOrdering, emptyBackground]
    exact hBest .w0 hAcc0 p hPMem rfl
  have hNotSnXg : ¬ snXg fNarrow (emptyBackground (W := World)) p .w0 := by
    intro hSn
    have hAcc1 : (.w1 : World) ∈ accessibleWorlds fNarrow .w0 := (hNarrowAcc .w1).mpr rfl
    have hBest1 : (.w1 : World) ∈
        bestWorlds fNarrow (xMarkOrdering (emptyBackground (W := World)) p) .w0 := by
      refine ⟨hAcc1, ?_⟩
      intro w'' hw''
      have hw''1 : w'' = .w1 := (hNarrowAcc w'').mp hw''
      subst hw''1
      exact ordering_reflexive _ (.w1 : World)
    have hPw1 : p .w1 := hSn .w1 hBest1
    exact World.noConfusion hPw1
  exact hNotSnXg (h fNarrow fWide (emptyBackground (W := World)) p .w0 hRev hSnXfg)

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

open Fragments.English.Auxiliaries in
/-- English *should* and *ought* share Portuguese *dever*'s modal force
    (`.weakNecessity`), placing them at the SN_Xg vertex. -/
theorem english_portuguese_weakNecessity_correspondence :
    Fragments.English.Auxiliaries.should.modalMeaning.all
        (·.force == .weakNecessity) = true ∧
    Fragments.English.Auxiliaries.ought.modalMeaning.all
        (·.force == .weakNecessity) = true ∧
    PortugueseModal.dever.force = .weakNecessity := by
  exact ⟨by decide, by decide, rfl⟩

open Fragments.English.Auxiliaries in
/-- English *should* has morphological past tense (X-marking), but *ought* does not.
    This reflects Iatridou's generalization: X-marking in English is realized as
    past morphology. Portuguese makes this overt: *deve* (unmarked) vs *devia*
    (past imperfect = X-marked). -/
theorem english_should_has_xmarking_morphology :
    Fragments.English.Auxiliaries.should.tense = some UD.Tense.Past ∧
    Fragments.English.Auxiliaries.ought.tense = none := by
  exact ⟨rfl, rfl⟩

end Ferreira2023
