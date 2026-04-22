import Linglib.Core.Modality.ModalBaseKind
import Linglib.Theories.Semantics.Modality.TemporalConstraint
import Linglib.Fragments.Gitksan.Modals
import Linglib.Phenomena.Modality.Studies.Matthewson2013

/-!
# @cite{matthewson-2013} ⇄ @cite{klecha-2016}: future orientation of modals

Two competing accounts of where the temporal-orientation flexibility of
modals comes from:

- **@cite{klecha-2016}** (formalized in `Klecha2016.lean`,
  `Core.Modality.ModalBaseKind`): future orientation is a property of
  the **modal base kind**. CIR (circumstantial) modal bases project to
  future histories and permit future orientation; DOX (doxastic) modal
  bases end at the eval time and strictly block it. A cross-linguistic
  universal: epistemic modals → DOX → no future.

- **@cite{matthewson-2013}** (formalized in `Matthewson2013.lean`,
  `Fragments/Gitksan/Modals.lean`): future orientation is supplied by a
  **separate prospective marker** (Gitksan `dim`), independent of the
  modal lexical entry's flavor. Epistemic modals + `dim` → future is
  felicitous (Fig. 4, ex. 42 and 44).

Both accounts agree that the prospective component is *separable* from
the modal lexical entry. They disagree on the locus: Klecha puts it in
the modal base; Matthewson puts it in a syntactically distinct aspect
marker.

This file makes the disagreement visible as a typed theorem. The
practical upshot for linglib's architecture: a unified
`ProspectiveMarkerPolicy` keyed on `ModalFlavor` (a tempting refactor
out of `Fragments/Gitksan/Modals.requiresDim`) would commit linglib to
one of these incompatible analyses. The two-instance abstraction does
not exist — Klecha and Matthewson are not two views of one invariant.
-/

namespace MatthewsonKlechaBridge

open Core.Modality (ModalFlavor ModalBaseKind ForceFlavor)
open Semantics.Modality.TemporalConstraint (ModalFlavor.toModalBaseKind)
open Fragments.Gitksan.Modals (imaa requiresDim)

-- ============================================================================
-- §1. Klecha's prediction for Gitksan epistemic modals
-- ============================================================================

/-- @cite{klecha-2016} Table 1: epistemic modals are DOX, and DOX strictly
    blocks future orientation. The combination is a definitional impossibility,
    not just an empirical generalization. -/
theorem klecha_epistemic_blocks_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future = false := rfl

/-- Gitksan `imaa` carries epistemic flavor in both of its meaning cells. -/
theorem imaa_meaning_is_epistemic :
    imaa.meaning.all (fun ff => ff.flavor == .epistemic) = true := by decide

/-- Klecha's universal applied to imaa: the flavor on its meaning is
    epistemic, so its modal base is DOX, so future orientation is
    blocked — for *every* meaning cell. -/
theorem klecha_predicts_imaa_no_future :
    imaa.meaning.all (fun ff =>
      ModalBaseKind.permitsOrientation
        (ModalFlavor.toModalBaseKind ff.flavor) .future = false) = true := by
  decide

-- ============================================================================
-- §2. Matthewson's data: imaa + dim IS future-oriented
-- ============================================================================

/-- @cite{matthewson-2013} Fig. 4 records two future-orientation cells
    for `imaa`: TP=PRESENT × TO=FUTURE (ex. 42) and TP=PAST × TO=FUTURE
    (ex. 44). Both require `dim`. The empirical claim of the paper is
    that these configurations are felicitous (with `dim`), not blocked. -/
theorem matthewson_imaa_future_attested :
    Matthewson2013.fig4Cells.any (fun c =>
      c.orientation == .future) = true := by decide

/-- The two future-orientation cells (ex. 42, 44) require `dim`. The
    cells exist in the paradigm as *attested felicitous configurations*
    of imaa with future orientation; `dim` is the obligatory marker. -/
theorem matthewson_imaa_future_with_dim :
    requiresDim imaa .future = true ∧
    Matthewson2013.fig4Cells.filter (fun c => c.orientation == .future)
      = [⟨.present, .future, 42⟩, ⟨.past, .future, 44⟩] := ⟨rfl, rfl⟩

-- ============================================================================
-- §3. The disagreement
-- ============================================================================

/-- Klecha's framework predicts no felicitous future-oriented imaa
    configurations exist (because epistemic flavor blocks future). -/
def klechaPredictsImaaFutureExists : Bool :=
  imaa.meaning.any (fun ff =>
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind ff.flavor) .future = true)

/-- Matthewson's data shows two felicitous future-oriented imaa
    configurations exist. -/
def matthewsonAttestedImaaFutureCount : Nat :=
  (Matthewson2013.fig4Cells.filter (fun c => c.orientation == .future)).length

/-- Klecha and Matthewson disagree on the felicity of imaa-future
    configurations. The disagreement is concrete: Klecha predicts none
    (Bool false), Matthewson reports two (cells ex. 42 and 44). -/
theorem klecha_matthewson_disagree :
    klechaPredictsImaaFutureExists = false ∧
    matthewsonAttestedImaaFutureCount = 2 := ⟨by decide, by decide⟩

-- ============================================================================
-- §4. Architectural consequence for linglib
-- ============================================================================

/-! The disagreement is not reconcilable by a flavor-keyed predicate
    `ProspectiveMarkerPolicy : ModalFlavor → TemporalOrientation → Bool`,
    because the two frameworks return *different Bool values* for the
    `(epistemic, future)` cell:

    - Klecha's policy: `(epistemic, future) ↦ false` (DOX cannot extend forward).
    - Matthewson's policy (= `Fragments.Gitksan.Modals.requiresDim` for
      epistemic modals): `(epistemic, future) ↦ true` (future orientation
      is felicitous, with `dim` required).

    A unified Theories-level policy would have to pick one. The honest
    architectural conclusion: the prospective-marker question is not a
    `ModalFlavor → ...` function — it is a *language-specific*
    factorization choice between modal-base content and aspect
    morphology. Until other modal-system Fragments motivate a shared
    abstraction (Korean `-keyss`, Mandarin `huì`, etc., would each need
    similar predicate data), the per-Fragment `requiresDim` should stay
    in `Fragments/`. Promotion to Theories would impose a false
    universal. -/

/-- The flavor-keyed policy disagreement on the (epistemic, future)
    cell. If a `ProspectiveMarkerPolicy` were promoted to Theories, it
    would have to pick one of these two values — and the choice is a
    cross-linguistic theoretical commitment, not a structural
    primitive. -/
theorem policy_disagrees_on_epistemic_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future ≠
    requiresDim imaa .future := by decide

end MatthewsonKlechaBridge
