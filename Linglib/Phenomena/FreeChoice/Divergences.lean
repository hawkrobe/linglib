import Linglib.Studies.Aloni2022
import Linglib.Studies.HollidayMandelkern2024

/-!
# Cross-framework divergence theorems for free choice

A catalog of cross-framework divergence theorems for free-choice (FC) inference.
This is the file form of Aloni 2022 §8 Table 8 — but populated only with the
divergences that are CONCRETELY STATABLE given the current substrate, and with
explicit notes about which ones are structurally blocked.

Each theorem is a concrete proposition of the form
`framework_A.predict_X ∧ ¬framework_B.predict_X` (or compatible),
discharged via the existing per-framework theorems each Studies file proves.

## Catalog state (2026-05)

| # | Divergence | Status |
|---|---|---|
| 1 | Aloni 2022 (BSML+) vs Holliday & Mandelkern 2024 (orthologic): FC permission vs FC epistemic | **Proved** below |
| 2 | BSML+ (deontic, indisputable R) vs BSML+ (deontic, loose R): WS FC requires indisputability | **Proved** below (intra-framework) |
| 3 | BSML+ vs Fox 2007 (recursive EXH) on Dual Prohibition | **Blocked**: structural — see §3 below |
| 4 | BSML+ vs BSML* on Negative FC | **Blocked**: incomplete substrate — see §3 below |
| 5 | BSML+ vs Fox 2007 on Modal Disjunction | **Blocked**: structural — see §3 below |

Promotes the prose sketch at `HollidayMandelkern2024.lean:469-490` (which had been
the **only** explicit cross-framework FC comparison anywhere in linglib) to a
proper Lean theorem.
-/

namespace Phenomena.FreeChoice.Divergences

open Core.Logic.Modal.BSML
open Semantics.Modality.Orthologic
open Aloni2022
open HollidayMandelkern2024

-- ============================================================================
-- §1 Aloni 2022 (BSML+ deontic) vs Holliday & Mandelkern 2024 (orthologic epistemic)
-- ============================================================================

/-! **The two frameworks make opposite predictions, but for different modal flavors.**

    Aloni 2022's BSML+ (`Studies/Aloni2022.lean`) derives FC
    for permission-flavored ◇ via pragmatic enrichment + state-based / indisputable
    accessibility. Holliday & Mandelkern 2024's orthologic
    (`Studies/HollidayMandelkern2024.lean`) is designed for
    epistemic ◇, where the orthologic move predicts that FC FAILS at world states
    that aren't fully uncertain.

    The contrast is "modal-flavor-dependent" rather than directly contradictory:
    each framework targets a different modal force, and predictions cohere with
    the empirical observation that deontic FC is more robust than epistemic FC
    (Cremers et al. 2017, Marty et al. 2021). But within Aloni's own §6.1
    framing (epistemic = state-based R = indisputability automatically; deontic
    only with explicit knowledgeability), BSML+ would also predict epistemic FC,
    putting it in tension with HM 2024's orthologic prediction at non-x₃ states.
-/

/-- BSML+ derives FC for deontic permission on `freeChoiceTeam`; HM 2024's
    orthologic predicts FC failure for epistemic ◇ at `x₁` (the "knows p" state).

    BSML+ side: the FC consequence (`mayCoffee` and `mayTea` supported on the
    team) is a Lean theorem given the FC enriched premise — proved by
    `aloni2022_fact4_NS_FC` invoking the universal `Core.Logic.Modal.BSML.narrowScopeFC`.

    HM 2024 side: at `x₁`, `◇(p ∨ ¬p)` is true (tautologously) but
    `◇p ∧ ◇¬p` is false (since `x₁` knows `p`, only `p`-worlds are accessible) —
    proved by `HollidayMandelkern2024.free_choice_fails_at_x1`. -/
theorem aloni_predicts_FC_deontic_but_HM_orthologic_predicts_FC_failure_epistemic :
    /- BSML+ side: FC consequences supported on team -/
    (support deonticModel mayCoffee freeChoiceTeam ∧
     support deonticModel mayTea    freeChoiceTeam) ∧
    /- HM 2024 side: FC fails at epistemic x₁ -/
    (diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x1 ∧
     ¬ conj (diamond epistemicScale propP)
            (diamond epistemicScale (orthoNeg pathFrame propP)) .x1) :=
  ⟨aloni2022_fact4_NS_FC aloni2022_fact4_premise_supported,
   free_choice_fails_at_x1⟩

-- ============================================================================
-- §2 Intra-BSML+ divergence: WS FC sensitivity to indisputability
-- ============================================================================

/-- Within BSML+, WS FC depends on indisputability of the accessibility relation.
    Aloni 2022 §6.1 uses this to predict that wide-scope FC is robust for
    epistemic modals (R is state-based, hence indisputable) but conditional for
    deontic modals (indisputable only when the speaker is fully knowledgeable
    about what is permitted).

    Captured concretely: on `deonticModel` (universal R, trivially indisputable),
    WS FC's consequence holds; on `looseDeonticModel` (R varies across the team),
    WS FC's consequence FAILS even though the same enriched premise might hold. -/
theorem bsml_plus_WS_FC_sensitive_to_indisputability
    (h : support deonticModel (enrich wideScopeDisj) freeChoiceTeam) :
    /- Indisputable R: FC consequence supported -/
    (support deonticModel mayCoffee freeChoiceTeam ∧
     support deonticModel mayTea    freeChoiceTeam) ∧
    /- Loose R: FC consequence fails -/
    (¬ support looseDeonticModel mayCoffee freeChoiceTeam) :=
  ⟨aloni2022_fact5_WS_FC h, aloni2022_fact5_WS_FC_fails_loose⟩

-- ============================================================================
-- §3 Documented gaps — divergences blocked by substrate state
-- ============================================================================

/-! ### #3 BSML+ vs Fox 2007 on Dual Prohibition (BLOCKED — structural)

    Aloni 2022 §8 Table 8 contrasts BSML+ and Fox 2007 (recursive EXH) on Dual
    Prohibition: BSML+ proves it (substrate's `Core.Logic.Modal.BSML.dualProhibition`),
    Fox 2007's recursive-EXH derivation famously fails it without modification
    (the paper's central argument for moving beyond grammatical exhaustification).

    **Why this is structurally blocked at the Lean level**: Fox 2007's substrate
    in linglib (`Studies/Fox2007.lean`) operates over `Set
    World`-style predicates and an `innocent.exh` operator that takes Sauerland
    alternatives. BSML+ operates over teams (`Finset W`) with bilateral
    `support`/`antiSupport`. Negation is set complement in Fox; bilateral
    polarity flip in BSML+. The two universes don't share a formula type, a
    truth value, or a canonical translation — so a Lean theorem of shape
    `BSML.dualProhibition_holds ∧ ¬Fox.dual_prohibition_holds` would have
    incomparable types on the two sides.

    **What WOULD be needed**: a bridge module
    (`Core/Logic/Modal/BSML/FoxBridge.lean` or similar) translating BSML
    formulas to Fox-style alternative sets, OR a pointwise/set semantics for
    BSML formulas. Either is real engineering, deferred.
-/

/-! ### #4 BSML+ vs BSML* on Negative FC (BLOCKED — incomplete substrate)

    Aloni 2022 Table 4 / §6.3.1 distinguishes BSML+ (where Negative FC ◇¬(α∧β)
    ⤳ ◇¬α ∧ ◇¬β fails) from BSML* (where it holds). The substrate proves the
    BSML+ failure side as `negativeFC_poss_fails_bsmlPlus` (in
    `Studies/Aloni2022/FreeChoice.lean`). The BSML* prediction is not yet
    statable.

    **Why this is blocked at the substrate level**: the substrate's `supportStar`
    (`Core/Logic/Modal/BSML/Defs.lean:242`) has `| .neg _, _ => True` —
    negation is treated as vacuously supported, which is not Aloni's actual
    BSML* semantics. Aloni's BSML* uses bilateral polarity, mirroring BSML
    proper. Stating "BSML* validates Negative FC" against the current
    placeholder would be vacuously true (anything is supported under negation),
    not a genuine prediction.

    **What WOULD be needed**: complete the bilateral semantics in `supportStar`
    (mirror of BSML's `eval` polarity-swap structure, but with the BSML*
    nonempty-substate constraint on disjunction). Substrate fix; deferred.
-/

/-! ### #5 BSML+ vs Fox 2007 on Modal Disjunction (BLOCKED — structural)

    Aloni 2022 §8 Table 8: BSML+ predicts Modal Disjunction (`α ∨ β ⤳ ◇α ∧ ◇β`
    when R is state-based — see `Core.Logic.Modal.BSML.modalDisjunction`); Fox 2007's
    alternative-based account does not address plain (non-modal) disjunction
    deriving modal force at all.

    **Why this is blocked**: same structural blocker as #3 — the two frameworks
    don't share types. Additionally, Fox's substrate doesn't define a "modal
    disjunction" derivation as a theorem at all, so the negation side
    (`¬Fox.modal_disjunction_holds`) has no native Lean predicate to refer to.

    **What WOULD be needed**: same bridge module as #3, plus a Fox-side
    formalization of "what does plain disjunction predict, modally" — which
    is genuinely vacuous in Fox's framework, but stating that vacuity in Lean
    requires the bridge.
-/

end Phenomena.FreeChoice.Divergences
