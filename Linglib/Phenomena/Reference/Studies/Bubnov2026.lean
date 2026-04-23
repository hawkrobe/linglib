import Linglib.Theories.Semantics.Quantification.DependenceLogic
import Linglib.Theories.Morphology.Nanosyntax.Core
import Linglib.Phenomena.Reference.Studies.Dekier2021
import Linglib.Fragments.Russian.Indefinites
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

This paper argues against the universal applicability of nanosyntactic
feature decomposition to coexpression phenomena, using indefinite
pronouns as a test case. The key claims:

1. @cite{dekier-2021}'s nanosyntactic analysis of indefinites (a
   containment hierarchy F₁ ⊂ F₂ ⊂ F₃) fails empirically: no
   morphological containment is attested in indefinite paradigms.

2. The semantic account of @cite{degano-aloni-2025}, based on
   **variation** and **constancy** from team semantics
   (@cite{hodges-1997}, @cite{vaananen-2007}), provides a better
   typology: 7 indefinite types derived from Boolean combinations
   of `var` and `dep` predicates.

3. The semantic account correctly predicts:
   - Which indefinite type is unattested (type vi: SK+NS)
   - Bidirectional diachronic change (semantic weakening in both
     directions), unlike nanosyntax which predicts only
     unidirectional change
   - The relative frequency of indefinite types (conjunctive
     requirements = rarer)

4. The broader implication: some coexpression patterns arise from
   **semantic underspecification** at LF, not from structural
   containment at PF.

## Connection to linglib

This study connects six modules:

- `DependenceLogic`: `variation` and `constancy` predicates formalize
  Degano & Aloni's `var(y,x)` and `dep(y,x)`.
  `type_vi_contradictory` derives the gap from these predicates.
- `Nanosyntax.Core`: `spellout` and `abaViolation` demonstrate the
  negative result — nanosyntax predicts containment patterns that
  indefinites lack
- `Features.IndefiniteType`: `IndefiniteSpecType` with derived semantic
  profiles (`profileSK/SU/NS`) and `classifyTriple` for computing
  syncretism patterns from forms
- `Fragments.{Russian,English,German,Latin,Yakut,Kannada}.Indefinites`:
  per-language indefinite entries witnessing the typology
- `Fragments.German.ModalIndefinites`: bridge connecting the Degano
  & Aloni typology to the Alonso-Ovalle & Royer modal indefinite
  classification for *irgend-*
-/

set_option autoImplicit false

namespace Bubnov2026

open Semantics.Quantification.DependenceLogic
open Morphology.Nanosyntax
open Dekier2021
open Features.IndefiniteType
open Fragments.Russian.Indefinites
open Fragments.English.Indefinites
open Fragments.German.Indefinites
open Fragments.German.ModalIndefinites
open Fragments.Latin.Indefinites
open Fragments.Yakut.Indefinites
open Fragments.Kannada.Indefinites

/-- String substring test, used as a CONSERVATIVE proxy for morphological
    containment. If two forms don't even share substrings, they certainly
    don't share morphemes. This is sufficient for @cite{bubnov-2026}'s
    negative result: Russian indefinite forms share no morphological material.

    For the full Haspelmath implicational map with adjacency structure and
    contiguity checking, see `Phenomena.Polarity.Typology.IndefiniteFunction`. -/
private def morphContains (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- ============================================================================
-- §1. Morphological Containment: Present in Case, Absent in Indefinites
-- ============================================================================

/-! The nanosyntactic hierarchy, ranks, lexicons, and syncretism
    pattern theorems are defined in `Dekier2021.lean` and imported here.
    Bubnov's critique takes Dekier's analysis as given and argues that
    it fails on morphological containment and diachronic change. -/

/-- @cite{bubnov-2026}'s key objection: nanosyntax predicts the ABC
    pattern should show morphological containment. This is NEVER
    attested for indefinites. -/
theorem russian_no_containment :
    morphContains "-to" "-nibud'" = false ∧
    morphContains "koe-" "-to" = false ∧
    morphContains "koe-" "-nibud'" = false := by native_decide

/-- In case morphology, containment IS attested. In indefinites, it
    is NOT. This asymmetry supports @cite{bubnov-2026}'s claim that
    nanosyntax is the right tool for case but not for indefinites. -/
theorem case_has_containment_indefinites_dont :
    (.nom : Core.Case) ≤ .acc ∧
    (.acc : Core.Case) ≤ .gen ∧
    morphContains "-to" "-nibud'" = false ∧
    morphContains "koe-" "-to" = false :=
  ⟨by decide, by decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §2. Type (vi) is Contradictory — Derived from Team Semantics
-- ============================================================================

-- Type (vi) requires dep(∅,x) (constancy across all worlds) AND
-- var(v,x) (variation within some world). This is unsatisfiable:
--
-- 1. var(v,x) holds → by `variation_monotone`, var(∅,x) holds
--    (since ∅ is trivially agreed on, v determines ∅)
-- 2. dep(∅,x) = constancy(t, ∅, x)
-- 3. var(∅,x) = variation(t, ∅, x)
-- 4. By `constancy_excludes_variation`: contradiction.

/-- Type (vi) (SK+NS) is predicted unattested because its semantic
    requirements are contradictory. dep(∅,x) requires x to be constant
    across all assignments (since all assignments trivially agree on
    ∅). var(v,x) requires x to vary among some v-agreeing assignments.
    By `variation_monotone`, this lifts to var(∅,x), contradicting
    dep(∅,x) via `constancy_excludes_variation`.

    This theorem connects the profile-level prediction (type vi has no
    examples) to the deeper team-semantic infrastructure. -/
theorem type_vi_contradictory
    {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v null x : V)
    (h_null_trivial : ∀ (a₁ a₂ : V → E), a₁ null = a₂ null)
    (h_dep : constancy t null x = true)
    (h_var : variation t v x = true) : False :=
  constancy_excludes_variation t null x h_dep
    (variation_monotone t v null x h_var
      (fun a₁ a₂ _ => h_null_trivial a₁ a₂))

/-- Profile-level verification: type (vi) skips SU. -/
theorem type_vi_profile :
    IndefiniteSpecType.profileSK .skPlusNS = true ∧
    IndefiniteSpecType.profileSU .skPlusNS = false ∧
    IndefiniteSpecType.profileNS .skPlusNS = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §3. Semantic Profiles — Derived from IndefiniteSpecType
-- ============================================================================

/-- Type (i) unmarked: no restriction → all three functions available. -/
theorem unmarked_profile :
    IndefiniteSpecType.profileSK .unmarked = true ∧
    IndefiniteSpecType.profileSU .unmarked = true ∧
    IndefiniteSpecType.profileNS .unmarked = true := ⟨rfl, rfl, rfl⟩

/-- Type (iii) non-specific: var(v,x) → only NS available. -/
theorem nonSpecific_profile :
    IndefiniteSpecType.profileSK .nonSpecific = false ∧
    IndefiniteSpecType.profileSU .nonSpecific = false ∧
    IndefiniteSpecType.profileNS .nonSpecific = true := ⟨rfl, rfl, rfl⟩

/-- Type (iv) epistemic: var(∅,x) → SU and NS available, not SK. -/
theorem epistemic_profile :
    IndefiniteSpecType.profileSK .epistemic = false ∧
    IndefiniteSpecType.profileSU .epistemic = true ∧
    IndefiniteSpecType.profileNS .epistemic = true := ⟨rfl, rfl, rfl⟩

/-- Type (v) specific known: dep(∅,x) → only SK available. -/
theorem specificKnown_profile :
    IndefiniteSpecType.profileSK .specificKnown = true ∧
    IndefiniteSpecType.profileSU .specificKnown = false ∧
    IndefiniteSpecType.profileNS .specificKnown = false := ⟨rfl, rfl, rfl⟩

/-- Type (vii) specific unknown: dep(v,x) ∧ var(∅,x) → only SU.
    Rare: conjunctive requirement. Kannada *-oo* is canonical. -/
theorem specificUnknown_profile :
    IndefiniteSpecType.profileSK .specificUnknown = false ∧
    IndefiniteSpecType.profileSU .specificUnknown = true ∧
    IndefiniteSpecType.profileNS .specificUnknown = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §4. Diachronic Predictions — Semantic Weakening
-- ============================================================================

-- Semantic weakening: dropping a restriction makes an indefinite usable
-- in MORE contexts. The semantic account predicts diachronic change
-- follows weakening paths (@cite{bubnov-2026} §6).
--
-- Path 1 (extension from NS to the left, Figure 3):
--   var(v,x) → var(∅,x) → no restriction
--   (iii) non-specific → (iv) epistemic → (i) unmarked
--   Attested: German *irgend-* (@cite{aloni-port-2015}),
--             French *quelque*
--
-- Path 2 (constancy weakening):
--   dep(∅,x) → dep(v,x) → no restriction
--   (v) specific known → (ii) specific → (i) unmarked
--
-- Path 3 (extension from SU to the right, Figure 2):
--   dep(v,x) ∧ var(∅,x) → var(∅,x)
--   (vii) specific unknown → (iv) epistemic
--   Attested: Lithuanian *kaž-*, Albanian *di-*

/-- Weakening from non-specific (iii) to epistemic (iv): dropping the
    within-world parameter makes variation global. Gains SU context. -/
theorem ns_weakens_to_epistemic :
    IndefiniteSpecType.profileNS .nonSpecific = true ∧
    IndefiniteSpecType.profileNS .epistemic = true ∧
    IndefiniteSpecType.profileSU .epistemic = true ∧
    IndefiniteSpecType.profileSU .nonSpecific = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Weakening from epistemic (iv) to unmarked (i): dropping the
    variation restriction entirely. Gains SK context. -/
theorem epistemic_weakens_to_unmarked :
    IndefiniteSpecType.profileSU .epistemic = true ∧
    IndefiniteSpecType.profileNS .epistemic = true ∧
    IndefiniteSpecType.profileSK .unmarked = true ∧
    IndefiniteSpecType.profileSK .epistemic = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Weakening from specific known (v) to specific (ii): broadening
    from cross-world constancy to within-world constancy. Gains SU. -/
theorem sk_weakens_to_specific :
    IndefiniteSpecType.profileSK .specificKnown = true ∧
    IndefiniteSpecType.profileSK .specific = true ∧
    IndefiniteSpecType.profileSU .specific = true ∧
    IndefiniteSpecType.profileSU .specificKnown = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The fundamental monotonicity underlying diachronic weakening:
    variation with respect to a finer parameter (within-world v) implies
    variation with respect to a coarser parameter (across-worlds ∅).
    This is `variation_monotone` from `TeamSemantics`. -/
theorem diachronic_weakening_grounded
    {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v null x : V)
    (hvar : variation t v x = true)
    (h_null_trivial : ∀ (a₁ a₂ : V → E), a₁ null = a₂ null) :
    variation t null x = true :=
  variation_monotone t v null x hvar
    (fun a₁ a₂ _ => h_null_trivial a₁ a₂)

-- ============================================================================
-- §5. Nanosyntax Diachronic Predictions
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
    spellout dekierInitial suRank = some "B" := by native_decide

theorem dekier_after_loss_bb :
    spellout dekierAfterLoss nsRank = some "B" ∧
    spellout dekierAfterLoss suRank = some "B" := by native_decide

-- ============================================================================
-- §6. Bridge to Fragment Data
-- ============================================================================

/-- *-nibud'* distribution matches the non-specific semantic profile. -/
theorem nibud_matches_nonSpecific :
    nibud.specType = .nonSpecific ∧
    nibud.allowsSK = nibud.specType.profileSK ∧
    nibud.allowsSU = nibud.specType.profileSU ∧
    nibud.allowsNS = nibud.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- *-to* is typed as epistemic (var(∅,x)) per @cite{bubnov-2026} §7.
    Its actual distribution (SU only) is narrower than the epistemic
    profile (SU + NS) because *-nibud'* blocks it for NS. -/
theorem to_is_epistemic :
    to_.specType = .epistemic ∧
    to_.allowsSU = true ∧
    to_.allowsNS = false ∧
    to_.specType.profileNS = true := ⟨rfl, rfl, rfl, rfl⟩

/-- *koe-* distribution matches the specific-known semantic profile. -/
theorem koe_matches_specificKnown :
    koe.specType = .specificKnown ∧
    koe.allowsSK = koe.specType.profileSK ∧
    koe.allowsSU = koe.specType.profileSU ∧
    koe.allowsNS = koe.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Latin *ali-* distribution matches the epistemic semantic profile.
    Unlike Russian *-to*, there is no competition: *-dam* only covers
    SK, so *ali-* fills both SU and NS unblocked. -/
theorem ali_matches_epistemic :
    ali.specType = .epistemic ∧
    ali.allowsSK = ali.specType.profileSK ∧
    ali.allowsSU = ali.specType.profileSU ∧
    ali.allowsNS = ali.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Yakut *-ere* distribution matches the specific profile. -/
theorem ere_matches_specific :
    ere.specType = .specific ∧
    ere.allowsSK = ere.specType.profileSK ∧
    ere.allowsSU = ere.specType.profileSU ∧
    ere.allowsNS = ere.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Kannada *-oo* is the canonical type (vii) specific unknown:
    dep(v,x) ∧ var(∅,x). Rare conjunctive type. -/
theorem oo_matches_specificUnknown :
    oo.specType = .specificUnknown ∧
    oo.allowsSK = oo.specType.profileSK ∧
    oo.allowsSU = oo.specType.profileSU ∧
    oo.allowsNS = oo.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- English *some-* distribution matches the unmarked profile (type i). -/
theorem some_matches_unmarked :
    some_.specType = .unmarked ∧
    some_.allowsSK = some_.specType.profileSK ∧
    some_.allowsSU = some_.specType.profileSU ∧
    some_.allowsNS = some_.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Yakut *-eme* distribution matches the non-specific profile (type iii). -/
theorem eme_matches_nonSpecific :
    eme.specType = .nonSpecific ∧
    eme.allowsSK = eme.specType.profileSK ∧
    eme.allowsSU = eme.specType.profileSU ∧
    eme.allowsNS = eme.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Latin *-dam* distribution matches the specific-known profile (type v). -/
theorem dam_matches_specificKnown :
    dam.specType = .specificKnown ∧
    dam.allowsSK = dam.specType.profileSK ∧
    dam.allowsSU = dam.specType.profileSU ∧
    dam.allowsNS = dam.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

/-- Kannada *-aadaruu* distribution matches the non-specific profile. -/
theorem aadaruu_matches_nonSpecific :
    aadaruu.specType = .nonSpecific ∧
    aadaruu.allowsSK = aadaruu.specType.profileSK ∧
    aadaruu.allowsSU = aadaruu.specType.profileSU ∧
    aadaruu.allowsNS = aadaruu.specType.profileNS := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §7. Bridge to German Modal Indefinites
-- ============================================================================

/-- German *irgend-* is classified as type (iv) epistemic in the Degano
    & Aloni typology, and as not-at-issue epistemic in the Alonso-Ovalle
    & Royer modal indefinite typology. These are compatible perspectives:
    the modal analysis describes WHAT *irgend-* does (domain widening);
    the team-semantic analysis describes its DISTRIBUTIONAL restriction
    (varying across epistemic alternatives).

    @cite{bubnov-2026} §6: German *irgend-* instantiates the diachronic
    path (iii) non-specific → (iv) epistemic (@cite{aloni-port-2015}). -/
theorem irgend_compatible_classifications :
    irgend.specType = .epistemic ∧
    irgendeinEntry.status = .notAtIssue ∧
    irgendeinEntry.hasEpistemic := by
  exact ⟨rfl, rfl, by decide⟩

-- ============================================================================
-- §8. The Broader Claim: Coexpression ≠ Syncretism
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
-- containment is unexpected if the hierarchy is real. The semantic
-- profiles computed from `IndefiniteSpecType` correctly predict the
-- typology, and `type_vi_contradictory` derives the gap from the
-- fundamental incompatibility of constancy and variation.

end Bubnov2026
