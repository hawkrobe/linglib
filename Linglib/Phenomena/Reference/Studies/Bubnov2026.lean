import Linglib.Theories.Semantics.Quantification.DependenceLogic
import Linglib.Theories.Semantics.Quantification.DeganoAloni2025
import Linglib.Theories.Morphology.Nanosyntax.Core
import Linglib.Phenomena.Reference.Studies.Dekier2021
import Linglib.Fragments.Slavic.Russian.Indefinites
import Linglib.Fragments.English.Indefinites
import Linglib.Fragments.German.Indefinites
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.Latin.Indefinites
import Linglib.Fragments.Yakut.Indefinites
import Linglib.Fragments.Kannada.Indefinites

/-!
# Bubnov (2026): Not all coexpressions are syncretisms
@cite{bubnov-2026}

Limiting Nanosyntax. *Glossa* 11(1), 1–15.

Argues against the universal applicability of nanosyntactic feature
decomposition to coexpression phenomena, using indefinite pronouns as a
test case. Key claims:

1. @cite{dekier-2021}'s nanosyntactic analysis of indefinites (a containment
   hierarchy F₁ ⊂ F₂ ⊂ F₃) fails empirically: no morphological containment
   is attested in indefinite paradigms.

2. The semantic account of @cite{degano-aloni-2025}, based on **variation**
   and **constancy** from team semantics (@cite{hodges-1997},
   @cite{vaananen-2007}), provides a better typology: 7 indefinite types
   from Boolean combinations of `var(y,x)` and `dep(y,x)`.

3. The semantic account correctly predicts:
   - Which indefinite type is unattested (type vi: SK+NS)
   - Bidirectional diachronic change, unlike nanosyntax which predicts
     only unidirectional change
   - The relative frequency of indefinite types (conjunctive requirements
     = rarer)

4. The broader implication: some coexpression patterns arise from
   **semantic underspecification** at LF, not structural containment at PF.

## Connection to linglib

- `DependenceLogic`: `variation` and `constancy` predicates formalize D&A's
  `var(y,x)` and `dep(y,x)`. `type_vi_contradictory` derives the gap.
- `Nanosyntax.Core`: `spellout` and `abaViolation` demonstrate the negative
  result — nanosyntax predicts containment that indefinites lack.
- `Typology.Indefinite`: `IndefiniteEntry` (consensus function-coverage
  + morphological-basis data) and `classifyTriple` for syncretism patterns.
- `Theories.Semantics.Quantification.DeganoAloni2025`: `DAType` and
  `surfaceDAType` / `consistentWith` projections from entries to D&A types.
- `Fragments.{Russian,English,German,Latin,Yakut,Kannada}.Indefinites`:
  per-language indefinite paradigms witnessing the typology.
- `Fragments.German.ModalIndefinites`: bridge connecting D&A's typology to
  Alonso-Ovalle & Royer's modal-indefinite typology for *irgend-*.
-/

set_option autoImplicit false

namespace Bubnov2026

open Semantics.Quantification.DependenceLogic
open Semantics.Quantification.DeganoAloni2025
open Morphology.Nanosyntax
open Dekier2021
open Typology.Indefinite
open Fragments.Slavic.Russian.Indefinites
open Fragments.English.Indefinites
open Fragments.German.Indefinites
open Fragments.German.ModalIndefinites
open Fragments.Latin.Indefinites
open Fragments.Yakut.Indefinites
open Fragments.Kannada.Indefinites

/-- Substring check on `List Char`. Kernel-reducible (no `String.splitOn`). -/
private def listContainsSub : List Char → List Char → Bool
  | _,                  []          => true
  | [],                 _ :: _      => false
  | cs@(_ :: rest),     needle      => needle.isPrefixOf cs || listContainsSub rest needle

/-- Conservative substring proxy for morphological containment. If two forms
    don't share substrings, they certainly don't share morphemes — sufficient
    for @cite{bubnov-2026}'s negative result. Operates on `String.toList` so
    kernel `decide` can reduce it. -/
private def morphContains (s sub : String) : Bool :=
  listContainsSub s.toList sub.toList

-- ============================================================================
-- §1. Morphological containment: present in case, absent in indefinites
-- ============================================================================

/-- @cite{bubnov-2026}'s key objection: nanosyntax predicts the ABC pattern
    should show morphological containment. This is NEVER attested for
    indefinites. The Russian forms are surface-level prefixed/suffixed to
    interrogative bases (`kto-nibud'`, `kto-to`, `koe-kto`); the indefinite
    morphemes themselves (`-nibud'`, `-to`, `koe-`) share no material. -/
theorem russian_no_containment :
    morphContains "-to" "-nibud'" = false ∧
    morphContains "koe-" "-to" = false ∧
    morphContains "koe-" "-nibud'" = false := by decide

/-- In case morphology, containment IS attested. In indefinites, NOT.
    This asymmetry supports @cite{bubnov-2026}'s claim that nanosyntax
    is the right tool for case but not for indefinites. -/
theorem case_has_containment_indefinites_dont :
    (.nom : Core.Case) ≤ .acc ∧
    (.acc : Core.Case) ≤ .gen ∧
    morphContains "-to" "-nibud'" = false ∧
    morphContains "koe-" "-to" = false :=
  ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- §2. Type (vi) is contradictory — derived from team semantics
-- ============================================================================

/-- Type (vi) (SK+NS) is predicted unattested because its semantic
    requirements are contradictory. `dep(∅,x)` requires x constant across
    all assignments; `var(v,x)` requires x to vary among v-agreeing
    assignments. By `variation_monotone`, this lifts to `var(∅,x)`,
    contradicting `dep(∅,x)` via `constancy_excludes_variation`. -/
theorem type_vi_contradictory
    {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v null x : V)
    (h_null_trivial : ∀ (a₁ a₂ : V → E), a₁ null = a₂ null)
    (h_dep : constancy t null x = true)
    (h_var : variation t v x = true) : False :=
  constancy_excludes_variation t null x h_dep
    (variation_monotone t v null x h_var
      (fun a₁ a₂ _ => h_null_trivial a₁ a₂))

/-- Profile-level verification: type (vi)'s D&A profile is the
    non-contiguous `{SK, NS}` — the contradiction surfaces structurally
    as a non-Haspelmath-adjacent function set. -/
theorem type_vi_profile :
    DAType.skPlusNS.profile =
      ({.specificKnown, .irrealis} : Finset _) := rfl

-- ============================================================================
-- §3. D&A profiles — verified at the substrate
-- ============================================================================

/-- Type (i) unmarked: no restriction → all three SK/SU/NS functions. -/
theorem unmarked_profile :
    DAType.unmarked.profile =
      ({.specificKnown, .specificUnknown, .irrealis} : Finset _) := rfl

/-- Type (iii) non-specific: `var(v,x)` → only NS. -/
theorem nonSpecific_profile :
    DAType.nonSpecific.profile = ({.irrealis} : Finset _) := rfl

/-- Type (iv) epistemic: `var(∅,x)` → SU + NS. -/
theorem epistemic_profile :
    DAType.epistemic.profile =
      ({.specificUnknown, .irrealis} : Finset _) := rfl

/-- Type (v) specific known: `dep(∅,x)` → only SK. -/
theorem specificKnown_profile :
    DAType.specificKnown.profile = ({.specificKnown} : Finset _) := rfl

/-- Type (vii) specific unknown: `dep(v,x) ∧ var(∅,x)` → only SU.
    Rare conjunctive type; Kannada *yāru-oo* is canonical. -/
theorem specificUnknown_profile :
    DAType.specificUnknown.profile = ({.specificUnknown} : Finset _) := rfl

-- ============================================================================
-- §4. Diachronic predictions — semantic weakening
-- ============================================================================

/-- Weakening from non-specific (iii) to epistemic (iv): dropping the
    within-world parameter makes variation global. The epistemic profile
    properly contains the non-specific profile, so the form gains SU
    while keeping NS. -/
theorem ns_weakens_to_epistemic :
    DAType.nonSpecific.profile ⊆ DAType.epistemic.profile ∧
    .specificUnknown ∈ DAType.epistemic.profile ∧
    .specificUnknown ∉ DAType.nonSpecific.profile := by decide

/-- Weakening from epistemic (iv) to unmarked (i): dropping the variation
    restriction. Unmarked profile properly contains epistemic. -/
theorem epistemic_weakens_to_unmarked :
    DAType.epistemic.profile ⊆ DAType.unmarked.profile ∧
    .specificKnown ∈ DAType.unmarked.profile ∧
    .specificKnown ∉ DAType.epistemic.profile := by decide

/-- Weakening from specific known (v) to specific (ii): broadening from
    cross-world constancy to within-world constancy. Specific profile
    properly contains specific-known. -/
theorem sk_weakens_to_specific :
    DAType.specificKnown.profile ⊆ DAType.specific.profile ∧
    .specificUnknown ∈ DAType.specific.profile ∧
    .specificUnknown ∉ DAType.specificKnown.profile := by decide

/-- The fundamental monotonicity underlying diachronic weakening:
    variation w.r.t. a finer parameter (within-world v) implies variation
    w.r.t. a coarser parameter (across-worlds ∅). This is
    `variation_monotone` from team semantics. -/
theorem diachronic_weakening_grounded
    {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v null x : V)
    (hvar : variation t v x = true)
    (h_null_trivial : ∀ (a₁ a₂ : V → E), a₁ null = a₂ null) :
    variation t null x = true :=
  variation_monotone t v null x hvar
    (fun a₁ a₂ _ => h_null_trivial a₁ a₂)

-- ============================================================================
-- §5. Nanosyntax diachronic predictions
-- ============================================================================

/-- Nanosyntax + Dekier: losing entry A (rank 0, NS-only) makes entry B
    (rank 1, SU) cover NS too via Superset Principle.
    Predicts SU → epistemic (AB → BB), but NOT NS → epistemic. -/
def dekierInitial : List LexEntry :=
  [⟨0, "A"⟩, ⟨1, "B"⟩]

def dekierAfterLoss : List LexEntry :=
  [⟨1, "B"⟩]

theorem dekier_initial_ab :
    spellout dekierInitial nsRank = some "A" ∧
    spellout dekierInitial suRank = some "B" := by decide

theorem dekier_after_loss_bb :
    spellout dekierAfterLoss nsRank = some "B" ∧
    spellout dekierAfterLoss suRank = some "B" := by decide

-- ============================================================================
-- §6. Bridge to Fragment data
-- ============================================================================

/-- *kto-nibud'* surface-classifies as type iii non-specific (actual = profile). -/
theorem nibud_matches_nonSpecific :
    nibudEntry.surfaceDAType = some .nonSpecific := by decide

/-- *kto-to* is classified as epistemic (`var(∅,x)`) per @cite{bubnov-2026} §7,
    BUT its actual distribution (SU only) is narrower than the epistemic
    profile (SU + NS) because *-nibud'* (type iii) blocks it for NS.

    Surface classifier returns type vii (specificUnknown) — the type whose
    profile exactly matches `{SU}`. Bubnov's manual type-iv classification
    is the `consistentWith` claim: actual ⊊ profile. The two layers
    are simultaneously asserted here. -/
theorem to_is_epistemic_with_competition :
    toEntry.surfaceDAType = some .specificUnknown ∧
    toEntry.consistentWith .epistemic = true ∧
    toEntry.functions ≠ DAType.epistemic.profile := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact absurd h (by decide)

/-- *koe-kto* surface-classifies as type v specific-known. -/
theorem koe_matches_specificKnown :
    koeEntry.surfaceDAType = some .specificKnown := by decide

/-- Latin *aliquis* surface-classifies as type iv epistemic. Unlike Russian
    *-to*, no competition: *quidam* only covers SK, so *aliquis* fills both
    SU + NS unblocked, matching the epistemic profile exactly. -/
theorem ali_matches_epistemic :
    aliEntry.surfaceDAType = some .epistemic := by decide

/-- Yakut *kim ere* surface-classifies as type ii specific (SK + SU). -/
theorem ere_matches_specific :
    ereEntry.surfaceDAType = some .specific := by decide

/-- Kannada *yāru-oo* is the canonical type vii specific unknown:
    `dep(v,x) ∧ var(∅,x)`, profile {SU}. -/
theorem oo_matches_specificUnknown :
    ooEntry.surfaceDAType = some .specificUnknown := by decide

/-- English *some-* surface-classifies as type i unmarked (all 3 functions). -/
theorem some_matches_unmarked :
    someEntry.surfaceDAType = some .unmarked := by decide

/-- Yakut *kim eme* surface-classifies as type iii non-specific. -/
theorem eme_matches_nonSpecific :
    emeEntry.surfaceDAType = some .nonSpecific := by decide

/-- Latin *quidam* surface-classifies as type v specific-known. -/
theorem dam_matches_specificKnown :
    damEntry.surfaceDAType = some .specificKnown := by decide

/-- Kannada *yāru-aadaruu* surface-classifies as type iii non-specific. -/
theorem aadaruu_matches_nonSpecific :
    aadaruuEntry.surfaceDAType = some .nonSpecific := by decide

-- ============================================================================
-- §7. Bridge to German modal indefinites
-- ============================================================================

/-- German *irgend-* is classified as type iv epistemic in D&A's typology
    AND as not-at-issue epistemic in Alonso-Ovalle & Royer's modal-indefinite
    typology. Compatible perspectives: the modal analysis describes WHAT
    *irgend-* does (domain widening); the team-semantic analysis describes
    its DISTRIBUTIONAL restriction (varying across epistemic alternatives).

    @cite{bubnov-2026} §6: German *irgend-* instantiates the diachronic
    path (iii) → (iv) (@cite{aloni-port-2015}). -/
theorem irgend_compatible_classifications :
    irgendEntry.surfaceDAType = some DAType.epistemic ∧
    irgendeinEntry.status = .notAtIssue ∧
    irgendeinEntry.hasFlavor Core.Modality.ModalFlavor.epistemic := by
  exact ⟨by decide, rfl, by decide⟩

-- ============================================================================
-- §8. The broader claim: coexpression ≠ syncretism
-- ============================================================================

-- @cite{bubnov-2026}'s central theoretical claim: not all coexpression
-- patterns arise from hierarchical feature containment (nanosyntactic
-- syncretism). Some arise from semantic underspecification.
--
-- Evidence: the indefinite domain shows coexpression (same form for
-- multiple functions) without containment (no morphological nesting).
-- The semantic account (Degano & Aloni) predicts the attested patterns
-- without requiring any syntactic hierarchy among indefinite features.
--
-- Formalized here: the Russian ABC pattern is consistent with the
-- nanosyntax spellout algorithm BUT the absence of morphological
-- containment is unexpected if the hierarchy is real. The D&A profiles
-- correctly predict the typology, and `type_vi_contradictory` derives
-- the gap from the fundamental incompatibility of constancy and variation.

end Bubnov2026
