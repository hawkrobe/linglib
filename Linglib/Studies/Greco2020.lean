import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Semantics.Negation.Expletive
import Linglib.Semantics.Negation.CzechNegation
import Linglib.Semantics.Negation.Defs
import Linglib.Semantics.Polarity.Item
import Mathlib.Data.Fintype.Basic

/-!
# Phase-Based Analysis of Surprise Negation
[greco-2020] [chomsky-2001]

Greco, M. (2020). On the syntax of surprise negation sentences: A case
study on expletive negation. *NLLT* 38(3), 775–825.

## Overview

Surprise negation (Sneg) arises when a negative morpheme merges in the
CP layer rather than in the standard TP-internal NegP position. Greco's
analysis rests on four factors:

1. A negative morpheme α exists in the language
2. α is a **syntactic head** (X°), not a phrase (XP)
3. α merges in the **CP phase** after vP-phase exhaustion (Transfer)
4. TP is **focused** (moves to Spec-FocP)

The head requirement (2) explains why Italian (*non*, X°) has Sneg but
Spanish (*no*, XP) does not: only heads can merge directly into the
functional spine without projecting their own phrase. The phase-based
account (3) explains why Sneg negation is non-truth-conditional: by the
time the neg head merges, the vP complement has been transferred to LF,
so the negation cannot scope into the propositional content.

## Two structural primitives

All Sneg predictions derive from exactly two structural consequences of
the representation [CP ... [X° non] ... [FocP [TP ...] Foc° ...]]:

- **vP transferred**: neg merged in CP → PIC → no scope into vP
  (blocks: NPIs, N-words, NEG-raising, DE inferences, Aux-to-Comp;
   licenses: PPIs)
- **FocP occupied**: TP fills [Spec, FocP] → unique FocP exhausted
  (blocks: other foci, Wh-elements, entity-question answers;
   forces: root-only, preverbal-subject topicalization;
   licenses: EE)

## Connections

- `Semantics.Negation` — framework-agnostic EN types (ENType, ENStrength, PolarityLicensing)
- `Minimalist.NegScope` — merge position, scope, classification chain (defined below)
- `ENEnvironment` (below) — the eleven Italian EN environments of Tables 1–2
- `SnegAttestation` (below) — per-language head status, Greco's own classification
- `Minimalist.fValue` / `isCPArea` — f-value classification
- `Italian.Negation.enTriggerNegators` — the consensus EN trigger inventory
  ([jin-koenig-2021]); Greco's construction-level classification is finer-grained

## Neg-Merge-Position Apparatus (relocated from `Minimalism/NegScope.lean`)

The `NegMergePosition` type and its bridges to `ENType`, `ENStrength`,
and `PolarityLicensing` are paper-specific to [greco-2020] (with
[rett-2026]'s high/low EN distinction and [stankova-2025]'s
Czech three-way coarsening). Not consumed elsewhere in the library, so
they live here under `namespace Minimalist.NegScope` for symmetry with
other Minimalist apparatus and to support qualified lookup if a future
paper picks them up.
-/

namespace Minimalist.NegScope

open Minimalist (Cat fValue isCPArea)
open Semantics.Negation (ENType ENStrength PolarityLicensing PolarityClass weakENProfile strongENProfile)

/-! ### Neg merge position -/

/-- Where a negation head is merged in the extended projection.

    Standard NegP is in the inflectional domain (F2, between v and C).
    In expletive negation, negation may merge in the CP layer (F3+),
    above the inflectional domain. The merge position determines scope,
    truth-conditionality, and polarity licensing.

    Compare `Semantics.Negation.CzechNegation.NegPosition`
    which classifies three LF positions (inner/medial/outer) for
    Czech negation. This type is coarser: TP subsumes both inner
    and medial positions. -/
inductive NegMergePosition where
  | tp   -- Inflectional domain (F0–F2): standard NegP
  | cp   -- Left periphery (F3+): CP-area negation
  deriving DecidableEq, Repr

/-- Whether a Neg head at this position can scope into the vP domain.

    Under PIC: vP complement is transferred when the CP-phase head is
    merged. TP-area Neg (F2) is merged before the phase head, so vP is
    still accessible. CP-area Neg is merged during/after the CP-phase,
    when vP complement has been transferred. -/
def NegMergePosition.scopesIntoVP : NegMergePosition → Bool
  | .tp => true    -- Merged before CP-phase head, vP still accessible
  | .cp => false   -- Merged with/after CP-phase head, vP transferred

-- ── NegMergePosition: Equiv, Fintype, LinearOrder ──

/-- NegMergePosition ≃ Bool: tp ↦ false, cp ↦ true.
    Aligned with the LinearOrder (tp < cp) and the ENType/ENStrength
    equivalences (low/weak ↦ false, high/strong ↦ true). -/
def NegMergePosition.equivBool : NegMergePosition ≃ Bool where
  toFun | .tp => false | .cp => true
  invFun | false => .tp | true => .cp
  left_inv p := by cases p <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype NegMergePosition := Fintype.ofEquiv _ NegMergePosition.equivBool.symm

/-- Numeric embedding: tp ↦ 0, cp ↦ 1 (by f-value position). -/
def NegMergePosition.toNat : NegMergePosition → Nat
  | .tp => 0 | .cp => 1

instance : LinearOrder NegMergePosition :=
  LinearOrder.lift' NegMergePosition.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [NegMergePosition.toNat])

/-! ### Bridge: merge position → EN type -/

/-- CP-area negation is non-truth-conditional (high EN).
    TP-area negation is truth-conditional (low EN). -/
def NegMergePosition.toENType : NegMergePosition → ENType
  | .tp => .low   -- Can scope → truth-conditional
  | .cp => .high  -- Cannot scope → non-truth-conditional

/-! ### Bridge: merge position → EN strength + polarity -/

/-- Merge position determines EN strength. -/
def NegMergePosition.toENStrength : NegMergePosition → ENStrength
  | .tp => .weak
  | .cp => .strong

/-- Merge position determines polarity licensing profile.

    CP-area negation cannot create a downward-entailing context in vP
    (the vP phase complement has been transferred), so it cannot license
    any polarity-sensitive elements. TP-area negation retains scope into
    vP, preserving some licensing ability (weak NPIs, N-words).

    This is [greco-2020]'s core theoretical claim: the weak/strong
    EN distinction reduces to where negation merges relative to the
    vP-phase boundary. -/
def NegMergePosition.polarityProfile : NegMergePosition → PolarityLicensing
  | .tp => weakENProfile
  | .cp => strongENProfile

-- ── Equiv chain: NegMergePosition ≃ ENType ≃ ENStrength ≃ Bool ──

/-- NegMergePosition ≃ ENType: tp ↦ low, cp ↦ high. -/
def NegMergePosition.equivENType : NegMergePosition ≃ ENType where
  toFun := NegMergePosition.toENType
  invFun | .low => .tp | .high => .cp
  left_inv p := by cases p <;> rfl
  right_inv t := by cases t <;> rfl

/-- NegMergePosition ≃ ENStrength: tp ↦ weak, cp ↦ strong. -/
def NegMergePosition.equivENStrength : NegMergePosition ≃ ENStrength where
  toFun := NegMergePosition.toENStrength
  invFun | .weak => .tp | .strong => .cp
  left_inv p := by cases p <;> rfl
  right_inv s := by cases s <;> rfl

/-- The Equiv chain factors through Bool:
    `toENType p = equivBool.symm (scopesIntoVP p)` pointwise. -/
theorem equiv_factors_entype (p : NegMergePosition) :
    NegMergePosition.equivENType p =
    ENType.equivBool.invFun (NegMergePosition.equivBool p) := by
  cases p <;> rfl

/-- The Equiv chain factors through Bool:
    `equivENStrength = equivBool ∘ ENStrength.equivBool⁻¹` pointwise. -/
theorem equiv_factors_enstrength (p : NegMergePosition) :
    NegMergePosition.equivENStrength p =
    ENStrength.equivBool.invFun (NegMergePosition.equivBool p) := by
  cases p <;> rfl

-- ── Bridge to Defs.lean semantic chain ──

open Semantics.Negation (scopeToENType scopeToLicensing enTypeToLicensing)

/-- Merge position's `scopesIntoVP` determines EN type via the
    semantic chain from `Defs.lean`. -/
theorem merge_position_semantic_bridge (pos : NegMergePosition) :
    scopeToENType pos.scopesIntoVP = pos.toENType := by
  cases pos <;> rfl

/-- Merge position determines licensing via the full semantic chain:
    merge → scopesIntoVP → scopeToENType → enTypeToLicensing. -/
theorem merge_position_licensing (pos : NegMergePosition) :
    scopeToLicensing pos.scopesIntoVP = pos.polarityProfile := by
  cases pos <;> rfl

/-! ### All classifications are in bijection

`NegMergePosition`, `ENType`, `ENStrength`, and `Bool` (via `scopesIntoVP`)
are all two-element types. The bridge functions between them are bijections.
Rather than proving each pairwise, we state a single theorem: all four
two-valued properties agree on which merge position they classify as
"active" (scope-bearing, low, weak, NPI-licensing). -/

/-- The classification chain: all four two-valued properties of
    `NegMergePosition` are in bijection. Scope access, EN type,
    EN strength, and weak-NPI licensing all partition merge positions
    the same way.

    This means any result proved about one classification
    automatically constrains the others. -/
theorem classifications_agree (pos : NegMergePosition) :
    (pos.scopesIntoVP = true) = (pos.toENType == .low) ∧
    (pos.toENType == .low) = (pos.toENStrength == .weak) ∧
    (pos.toENStrength == .weak) = (pos.polarityProfile.licenses .weakNPI) := by
  cases pos <;> exact ⟨rfl, rfl, rfl⟩

/-- Scope determines EN type (Iff form). -/
theorem scope_determines_entype (pos : NegMergePosition) :
    (pos.scopesIntoVP = true) ↔ (pos.toENType = .low) := by
  cases pos <;> simp [NegMergePosition.scopesIntoVP, NegMergePosition.toENType]

/-- High EN is strong EN. -/
theorem high_en_is_strong (pos : NegMergePosition)
    (h : pos.toENType = .high) :
    pos.toENStrength = .strong := by
  cases pos <;> simp_all [NegMergePosition.toENType, NegMergePosition.toENStrength]

/-! ### Grounding scope in the extended projection

The TP/CP distinction in `NegMergePosition` is not stipulated — it
corresponds to position in the extended projection relative to the
CP boundary (F3 = Fin). This section connects `scopesIntoVP` to
`isCPArea` and `fValue`, showing that scope accessibility follows
from f-value ordering under PIC. -/

/-- Scope into vP = NOT in CP area (for the canonical heads).

    Standard NegP (F2) is below the CP boundary → scope into vP.
    FocP (F4) is above the CP boundary → no scope into vP.
    This grounds the two-way scope distinction in the extended
    projection's f-value monotonicity. -/
theorem scope_iff_not_cp_area :
    NegMergePosition.tp.scopesIntoVP = !isCPArea .Neg ∧
    NegMergePosition.cp.scopesIntoVP = !isCPArea .Foc := by decide

/-- Standard NegP (F2) is in the inflectional domain, not the CP area. -/
theorem neg_in_tp : isCPArea .Neg = false := by decide

/-- Foc (F4) is in the CP area. -/
theorem foc_in_cp : isCPArea .Foc = true := by decide

/-- Fin (F3) is the CP boundary (inclusive — lowest CP head). -/
theorem fin_is_cp_boundary : isCPArea .Fin = true := by decide

/-- The f-value boundary: CP area is strictly above standard NegP. -/
theorem cp_area_above_neg : fValue .Fin > fValue .Neg := by decide

/-! ### Coarsening Czech three-way negation
[stankova-2025]

Czech polar questions distinguish three LF positions for negation:
inner (TP), medial (ModP), and outer (PolP). The EN-relevant
`NegMergePosition` is coarser: inner and medial are both in the
inflectional domain (tp), while outer is in the CP area (cp).

This coercion shows that the two-way EN distinction is a proper
abstraction over the three-way Czech distinction — any result
proved for `NegMergePosition` applies to Czech negation positions
via this mapping. -/

open Semantics.Negation.CzechNegation (NegPosition)

/-- Map Czech three-way negation positions to the coarser two-way
    EN merge position.

    - **Inner** (TP, propositional ¬p): inflectional domain → tp
    - **Medial** (ModP, scopes over □_ev): still inflectional → tp
    - **Outer** (PolP, FALSUM): CP area → cp -/
def NegPosition.toNegMergePosition : NegPosition → NegMergePosition
  | .inner  => .tp
  | .medial => .tp
  | .outer  => .cp

/-- Inner/medial map to tp, outer maps to cp. -/
theorem inner_is_tp : NegPosition.toNegMergePosition .inner = .tp := rfl
theorem medial_is_tp : NegPosition.toNegMergePosition .medial = .tp := rfl
theorem outer_is_cp : NegPosition.toNegMergePosition .outer = .cp := rfl

/-- The Czech NCI licensing diagnostic aligns with vP scope:
    inner licenses NCIs (scopes into vP), outer does not (no vP scope). -/
theorem nci_licensing_matches_scope :
    Semantics.Negation.CzechNegation.licenses .inner .nciLicensed =
    (NegPosition.toNegMergePosition .inner).scopesIntoVP ∧
    Semantics.Negation.CzechNegation.licenses .outer .nciLicensed =
    (NegPosition.toNegMergePosition .outer).scopesIntoVP := ⟨rfl, rfl⟩

/-- The Czech three-way → two-way coarsening preserves scope ordering:
    inner ≤ medial ≤ outer maps to tp ≤ tp ≤ cp (monotone). -/
theorem toNegMergePosition_monotone :
    Monotone NegPosition.toNegMergePosition := by
  intro a b hab
  -- Both ≤ relations reduce to toNat comparisons via LinearOrder.lift'
  change NegMergePosition.toNat _ ≤ NegMergePosition.toNat _
  change NegPosition.toNat a ≤ NegPosition.toNat b at hab
  cases a <;> cases b <;>
    simp only [NegPosition.toNegMergePosition, NegMergePosition.toNat,
               NegPosition.toNat] at * <;> omega

end Minimalist.NegScope

namespace Greco2020

open Minimalist (Cat fValue isCPArea)
open Minimalist.NegScope (NegMergePosition)
open Semantics.Negation (ENStrength PolarityLicensing PolarityClass weakENProfile strongENProfile)

/-! ### Tables 1–2: the eleven Italian EN environments

[greco-2020] Table 1 (p. 779) classifies ten Italian EN clause types by
four polarity diagnostics (weak NPIs, strong NPIs, not-also conjunctions,
N-words); Table 2 (p. 818) adds Snegs as the eleventh row. The rows are
uniform within each strength class: weak environments license weak NPIs
and N-words only, strong environments license nothing. The weak/strong
taxonomy itself predates the paper (it is credited there to the author's
earlier work); Table 2's contribution is placing Snegs in the strong class. -/

/-- The eleven Italian EN construction types of [greco-2020] Tables 1–2. -/
inductive ENEnvironment where
  | untilClauses
  | whoKnowsClauses
  | unlessClauses
  | indirectInterrogatives
  | comparativeClauses
  | negativeExclamatives
  | rhetoricalQuestions
  | notThatClauses
  | ratherThanClauses
  | beforeClauses
  | snegs
  deriving DecidableEq, Repr

/-- Tables 1–2 classification: the empirical weak/strong assignment. -/
def ENEnvironment.strength : ENEnvironment → ENStrength
  | .untilClauses           => .weak
  | .whoKnowsClauses        => .weak
  | .unlessClauses          => .weak
  | .indirectInterrogatives => .weak
  | .comparativeClauses     => .weak
  | .negativeExclamatives   => .strong
  | .rhetoricalQuestions    => .strong
  | .notThatClauses         => .strong
  | .ratherThanClauses      => .strong
  | .beforeClauses          => .strong
  | .snegs                  => .strong

/-- Each environment's polarity fingerprint, via its strength class
    (Table 1's rows are uniform within each class). -/
def ENEnvironment.licensing (e : ENEnvironment) : PolarityLicensing :=
  e.strength.profile

/-- The table agrees with the merge-position theory: each environment's
    licensing is exactly what `polarityProfile` predicts for the merge
    position corresponding to its strength. -/
theorem licensing_matches_merge_theory (e : ENEnvironment) :
    (NegMergePosition.equivENStrength.symm e.strength).polarityProfile
      = e.licensing := by
  cases e <;> rfl

/-! ### Greco's four factors for surprise negation -/

/-- [greco-2020]: four necessary conditions for surprise negation.
    (i) a negative morpheme α, (ii) α is a syntactic head (X°),
    (iii) α merges in the CP-phase after vP-phase exhaustion,
    (iv) TP is focused (moves to Spec-FocP). -/
structure SnegConditions where
  hasNegMorpheme : Bool
  negIsHead : Bool
  mergePosition : NegMergePosition
  tpIsFocused : Bool
  deriving DecidableEq, Repr

/-- A set of conditions yields surprise negation iff all four
    are satisfied. -/
def SnegConditions.yieldsSnegs (c : SnegConditions) : Bool :=
  c.hasNegMorpheme && c.negIsHead &&
  c.mergePosition == .cp && c.tpIsFocused

/-- Italian satisfies all four Sneg conditions. -/
def italianSnegConditions : SnegConditions :=
  { hasNegMorpheme := true
  , negIsHead := true      -- non is X° (clitic)
  , mergePosition := .cp
  , tpIsFocused := true }

theorem italian_yields_snegs :
    italianSnegConditions.yieldsSnegs = true := by decide

/-- Spanish fails condition (ii): *no* is XP, not X°. -/
def spanishSnegConditions : SnegConditions :=
  { hasNegMorpheme := true
  , negIsHead := false     -- no is XP (can be focused/coordinated)
  , mergePosition := .cp
  , tpIsFocused := true }

theorem spanish_no_snegs :
    spanishSnegConditions.yieldsSnegs = false := by decide

/-! ### Cross-linguistic predictions -/

/-- Sneg attestation datum: [greco-2020]'s head-status classification of a
    language's negative marker, paired with whether surprise negation is
    attested. -/
structure SnegAttestation where
  language : String
  attested : Bool
  negIsHead : Bool
  deriving DecidableEq, Repr

/-- Italian *non* is X° (clitic); Snegs attested. -/
def italianSnegs : SnegAttestation :=
  { language := "Italian", attested := true, negIsHead := true }

/-- Spanish *no* is XP (can be focused and coordinated); no Snegs. -/
def spanishSnegs : SnegAttestation :=
  { language := "Spanish", attested := false, negIsHead := false }

/-- Brazilian Portuguese *não* is X°; Snegs attested. -/
def brazilianPortugueseSnegs : SnegAttestation :=
  { language := "Brazilian Portuguese", attested := true
  , negIsHead := true }

def allSnegAttestations : List SnegAttestation :=
  [italianSnegs, spanishSnegs, brazilianPortugueseSnegs]

/-- Greco's prediction: Snegs are attested only when the negative marker is
    a head. (Head status is necessary, not sufficient — French *ne* is X°
    yet lacks Snegs because factor (iii) fails; see `frenchSnegConditions`.) -/
theorem sneg_requires_head :
    allSnegAttestations.all (λ s => !s.attested || s.negIsHead) = true := by decide

/-! ### Phase theory connection -/

/-- NegP and T share the same f-value (both F2, inflectional domain). -/
theorem neg_t_same_fvalue : fValue .Neg = fValue .T := by decide

/-! ### Derived predictions from [CP ... [X° non] ... [FocP [TP ...] Foc° ...]]

[greco-2020] §4.2 derives 11 properties from a single structural
representation. Every prediction reduces to one of two structural
primitives:

- `vpTransferred`: neg merged in CP → vP complement transferred by PIC
- `focPOccupied`: TP fills [Spec, FocP] → FocP projection exhausted

These are the only two structural consequences. Each of Greco's
predictions is a one-line derivation from one primitive. -/

/-- The structural representation of a Sneg ([greco-2020] (59)/(106)):
    the negative head merges in the CP layer, and TP occupies [Spec, FocP]. -/
structure SnegRepresentation where
  /-- The negative head merges in the CP area (F3+). -/
  negPos : NegMergePosition
  negInCP : negPos = .cp
  /-- TP moves to [Spec, FocP]: the whole predicate is focused. -/
  tpFocused : Bool
  tpFocused_eq : tpFocused = true

/-- **Primitive A**: vP complement has been transferred by PIC.
    Neg merged in CP → past the phase boundary → vP shipped to LF.
    This blocks all propositional-scope interactions. -/
def SnegRepresentation.vpTransferred (s : SnegRepresentation) : Bool :=
  !s.negPos.scopesIntoVP

/-- **Primitive B**: FocP projection is occupied by TP.
    The unique Italian FocP ([rizzi-1997]) is exhausted, blocking
    any other element that targets [Spec, FocP]. -/
def SnegRepresentation.focPOccupied (s : SnegRepresentation) : Bool :=
  s.tpFocused

-- Master lemmas: both primitives are true for every Sneg

theorem vp_transferred (s : SnegRepresentation) : s.vpTransferred = true := by
  simp [SnegRepresentation.vpTransferred, s.negInCP, NegMergePosition.scopesIntoVP]

theorem focp_occupied (s : SnegRepresentation) : s.focPOccupied = true := by
  simp [SnegRepresentation.focPOccupied, s.tpFocused_eq]

/-! ### Category A: consequences of vP transfer -/

/-! Predictions that follow from the vP complement being transferred.
    In each case, the blocked operation requires negation to scope into
    the propositional content — impossible when vP is gone. -/

/-- **Prediction 6** ([greco-2020] §4.2.3): No NEG-raising.
    NEG-raising requires neg in TP scope domain. -/
def SnegRepresentation.allowsNegRaising (s : SnegRepresentation) : Bool :=
  !s.vpTransferred

/-- **Prediction 8** ([greco-2020] §4.2.5, (64)): No Aux-to-Comp.
    Aux-to-Comp requires neg to originate in TP. -/
def SnegRepresentation.allowsAuxToComp (s : SnegRepresentation) : Bool :=
  !s.vpTransferred

/-- **§2.3 (25)**: Sneg negation is not downward entailing.
    DE requires neg to scope over the predicate. -/
def SnegRepresentation.isDownwardEntailing (s : SnegRepresentation) : Bool :=
  !s.vpTransferred

theorem snegs_block_neg_raising (s : SnegRepresentation) :
    s.allowsNegRaising = false := by
  simp [SnegRepresentation.allowsNegRaising, vp_transferred s]

theorem snegs_block_aux_to_comp (s : SnegRepresentation) :
    s.allowsAuxToComp = false := by
  simp [SnegRepresentation.allowsAuxToComp, vp_transferred s]

theorem sneg_not_downward_entailing (s : SnegRepresentation) :
    s.isDownwardEntailing = false := by
  simp [SnegRepresentation.isDownwardEntailing, vp_transferred s]

/-! ### Category B: consequences of FocP occupancy -/

/-! Predictions that follow from TP filling [Spec, FocP].
    In each case, the blocked operation requires access to FocP,
    which is already occupied. -/

/-- **Prediction 2** ([greco-2020] §4.2.4): Snegs reject foci.
    FocP is already occupied by TP. -/
def SnegRepresentation.allowsFocus (s : SnegRepresentation) : Bool :=
  !s.focPOccupied

/-- **Prediction 3** ([greco-2020] §4.2.4): Snegs reject Wh.
    Wh-phrases target [Spec, FocP], same as TP. -/
def SnegRepresentation.allowsWh (s : SnegRepresentation) : Bool :=
  !s.focPOccupied

/-- **Prediction 1** ([greco-2020] §4.2.5): Snegs are root-only.
    Subordinate clauses block whole-TP focalization. -/
def SnegRepresentation.requiresRoot (s : SnegRepresentation) : Bool :=
  s.focPOccupied

/-- **Prediction 7** ([greco-2020] §4.2.7): Snegs license EE.
    EE is parasitic on an active FocP ([poletto-2005]). -/
def SnegRepresentation.licensesEE (s : SnegRepresentation) : Bool :=
  s.focPOccupied

/-- Topics are freely allowed — TopP is recursive and independent
    of FocP. This is NOT derived from either primitive. -/
def SnegRepresentation.allowsTopics (_s : SnegRepresentation) : Bool :=
  true

theorem snegs_reject_focus (s : SnegRepresentation) :
    s.allowsFocus = false := by
  simp [SnegRepresentation.allowsFocus, focp_occupied s]

theorem snegs_reject_wh (s : SnegRepresentation) :
    s.allowsWh = false := by
  simp [SnegRepresentation.allowsWh, focp_occupied s]

theorem snegs_require_root (s : SnegRepresentation) :
    s.requiresRoot = true := by
  simp [SnegRepresentation.requiresRoot, focp_occupied s]

theorem snegs_license_ee (s : SnegRepresentation) :
    s.licensesEE = true := by
  simp [SnegRepresentation.licensesEE, focp_occupied s]

theorem snegs_allow_topics (s : SnegRepresentation) :
    s.allowsTopics = true := rfl

/-! ### Parameterized predictions (FocP-derived) -/

/-- **Prediction 4** ([greco-2020] §4.2.4, (26)–(27)): Snegs answer
    propositional questions but NOT entity questions.

    TP-focalization means the WHOLE predicate is new-information focus.
    Propositional questions ask about the entire proposition — compatible.
    Entity questions require sub-TP focus — incompatible. -/
inductive QuestionType where
  | propositional   -- "Cos'è successo?" (What happened?)
  | entity          -- "Chi è sceso dal treno?" (Who got off the train?)
  deriving DecidableEq, Repr

def SnegRepresentation.answersQuestion (s : SnegRepresentation) :
    QuestionType → Bool
  | .propositional => s.focPOccupied
  | .entity        => !s.focPOccupied

theorem snegs_answer_propositional (s : SnegRepresentation) :
    s.answersQuestion .propositional = true := by
  simp [SnegRepresentation.answersQuestion, focp_occupied s]

theorem snegs_reject_entity (s : SnegRepresentation) :
    s.answersQuestion .entity = false := by
  simp [SnegRepresentation.answersQuestion, focp_occupied s]

/-- **Prediction 5** ([greco-2020] §4.2.6): Preverbal subjects
    are topicalized. FocP full → subject forced to TopP. -/
inductive SubjectPosition where
  | preverbal   -- [Spec, TopP]: topicalized
  | postverbal  -- Inside TP (in [Spec, FocP]): part of focus
  deriving DecidableEq, Repr

def SnegRepresentation.subjectIsTopicalized (s : SnegRepresentation) :
    SubjectPosition → Bool
  | .preverbal  => s.focPOccupied
  | .postverbal => false

theorem preverbal_subject_topicalized (s : SnegRepresentation) :
    s.subjectIsTopicalized .preverbal = true := by
  simp [SnegRepresentation.subjectIsTopicalized, focp_occupied s]

/-! ### PPI licensing ([greco-2020] §2.3 (24), [giannakidou-2011])

Snegs CAN host PPIs like *già* ("already"), despite containing a
negative marker. Since vP has been transferred, the PPI inside vP
is outside negation's scope — it has already "escaped" by PIC. -/

/-- PPIs survive because vP has been transferred. -/
theorem ppi_survives_in_sneg (s : SnegRepresentation) :
    s.vpTransferred = true := vp_transferred s

/-! ### Ethical Dative interaction ([greco-2020] §2.2 (13))

When Ethical Dative (*mi*/*ti*) co-occurs with *non*, only the Sneg
reading is available — standard negation is ruled out. ED is
associated with the CP layer (discourse-level emotional participation),
which is exactly where Sneg *non* merges. -/

/-- ED disambiguates: presence of ED forces the Sneg reading. -/
structure EDDisambiguation where
  hasEthicalDative : Bool
  negInterpretation : NegMergePosition
  ed_forces_sneg : hasEthicalDative = true → negInterpretation = .cp

def snegWithED : EDDisambiguation :=
  { hasEthicalDative := true
  , negInterpretation := .cp
  , ed_forces_sneg := λ _ => rfl }

/-! ### Parametric variation ([greco-2020] §4.2.9)

Snegs require the conspiracy of four factors. Blocking any one prevents
Snegs. French *ne* is X° (head) but merges in TP, not CP — factor
(iii) fails. -/

/-- French: *ne* is X° (head), but Snegs are not attested.
    [greco-2020] §4.2.9: *ne* merges in TP area (standard NegP),
    not externally merged in CP, so factor (iii) fails. -/
def frenchSnegConditions : SnegConditions :=
  { hasNegMorpheme := true
  , negIsHead := true
  , mergePosition := .tp
  , tpIsFocused := false }

theorem french_no_snegs :
    frenchSnegConditions.yieldsSnegs = false := by decide

/-! ### Differentiation from NRQs and ENEs ([greco-2020] §3)

All three belong to strong EN but differ on four diagnostics:

| Property             | Sneg | NRQ  | ENE  |
|----------------------|------|------|------|
| Wh-elements          | ✗    | ✓    | ✓    |
| Answerhood           | ✓    | ✗    | ✗    |
| Embeddable (factive) | ✗    | —    | ✓    |
| *dopo tutto*         | ✗    | ✓    | —    |
-/

inductive StrongENType where
  | sneg | nrq | ene
  deriving DecidableEq, Repr

-- ── StrongENType: Fintype ──

/-- StrongENType ≃ Fin 3. -/
def StrongENType.equivFin : StrongENType ≃ Fin 3 where
  toFun | .sneg => 0 | .nrq => 1 | .ene => 2
  invFun | ⟨0, _⟩ => .sneg | ⟨1, _⟩ => .nrq | ⟨2, _⟩ => .ene
         | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv t := by cases t <;> rfl
  right_inv i := by
    match i with
    | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    | ⟨n + 3, h⟩ => exact absurd h (by omega)

instance : Fintype StrongENType := Fintype.ofEquiv _ StrongENType.equivFin.symm

def StrongENType.allowsWh : StrongENType → Bool
  | .sneg => false
  | .nrq  => true
  | .ene  => true

def StrongENType.isAnswer : StrongENType → Bool
  | .sneg => true
  | .nrq  => false
  | .ene  => false

def StrongENType.embeddableUnderFactive : StrongENType → Bool
  | .sneg => false
  | .nrq  => false
  | .ene  => true

def StrongENType.enStrength : StrongENType → ENStrength
  | .sneg => .strong
  | .nrq  => .strong
  | .ene  => .strong

theorem all_strong_en (t : StrongENType) :
    t.enStrength = .strong := by cases t <;> rfl

/-- Snegs are the only strong EN type that can serve as answers. -/
theorem sneg_unique_answerhood :
    [StrongENType.sneg, .nrq, .ene].filter StrongENType.isAnswer
    = [.sneg] := rfl

/-- Snegs are the only strong EN type that rejects Wh-elements. -/
theorem sneg_unique_wh_rejection :
    [StrongENType.sneg, .nrq, .ene].filter (fun t => !t.allowsWh)
    = [.sneg] := rfl

/-- The three-column diagnostic table (Wh, answerhood, embeddability)
    uniquely identifies each StrongENType — formalizing [greco-2020]
    Table 3's claim that sneg, NRQ, and ENE are empirically distinct. -/
theorem strongEN_fingerprint_injective :
    Function.Injective (fun t : StrongENType =>
      (t.allowsWh, t.isAnswer, t.embeddableUnderFactive)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [StrongENType.allowsWh,
    StrongENType.isAnswer, StrongENType.embeddableUnderFactive]

end Greco2020
