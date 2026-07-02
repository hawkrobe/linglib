/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Tone.Grammatical
import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Core.Computability.TierProjection

/-!
# Rolle 2018 — Grammatical tone: CoP-scope and Matrix-Basemap Correspondence

[rolle-2018]'s thesis frames dominant vs. non-dominant grammatical tone (GT)
via three problems: the **origin** (where does the grammatical tune come from?),
the **erasure** (why do the target's underlying tones go unrealized?), and the
**scope** (what determines the domain of the GT operation?). This file
formalises Rolle's two central mechanisms; the origin problem is solved by the
floating-tone representation (the tune is part of the trigger's UR, in
`Tone/Grammatical.lean`).

* **CoP-scope** (Ch 6) — the *scope* problem. Structural positions in a
  cophonological domain are ordered Spec > Head > Complement, and at spell-out
  syntactic structure is mapped to a morpho-phonological tree via **hierarchy
  exchange**. The dominant-GT asymmetry (triggers are dependents, targets are
  heads) is *derived* from this ordering rather than stipulated.
* **Matrix-Basemap Correspondence (MxBM-C)** (Ch 5) — the *erasure* problem.
  Dominant GT is faithfulness to a *basemap* output (a "deficient projection"
  of the input with all valued tones stripped), extending Output-Output
  Correspondence ([benua-1997]) to the tonal tier.

## Main definitions

### CoP-scope
* `CoPPosition`, `CoPPosition.rank`, `scopesOver`, `CoPPosition.isDependent`
* `CoPNode`, `hierarchyExchange`
* `dominant_gt_asymmetry_from_scope` — derives the asymmetry from scope

### Matrix-Basemap Correspondence
* `deficientProjection`, `basemapOutput`, `tonalTier`
* `basemapViolations` — IDENT-OO ([mccarthy-prince-1995]) on the tonal tier,
  derived from `Corr.identViol`
* `mkBasemapConstraint`, `tonalOverwrite_basemap_faithful`

## References

* [rolle-2018]
* [benua-1997], [mccarthy-prince-1995] — Output-Output Correspondence
* [goldsmith-1976]
-/

namespace Rolle2018

open Tone
open OptimalityTheory.Correspondence (Corr)
open Constraints OptimalityTheory

/-! ## CoP-scope: cophonological domain scope hierarchy -/

/-! ### CoP-scope positions -/

/-- Structural positions within a cophonological domain (CoP), ordered
    by scope. The ordering Spec > Head > Complement determines which
    VI's cophonology takes precedence within the domain.

    [rolle-2018] Ch 6 §6.2: each VI has cophonology-scope over
    all inwardly located morphemes, and cophonologies apply cyclically
    up the tree, producing layered grammatical tone effects. -/
inductive CoPPosition where
  /-- Specifier: outermost scope. Dependents (modifiers, possessors)
      typically occupy this position. -/
  | spec
  /-- Head: middle scope. Lexical heads (roots, stems) occupy this
      position. -/
  | head
  /-- Complement: innermost scope. Complements and some affixes
      occupy this position. -/
  | complement
  deriving DecidableEq, Repr

/-! ### Scope ordering -/

/-- Numeric rank for scope ordering: higher rank = wider scope.
    Spec (2) > Head (1) > Complement (0). -/
def CoPPosition.rank : CoPPosition → Nat
  | .spec       => 2
  | .head       => 1
  | .complement => 0

/-- Does position `a` scope over position `b`? -/
def scopesOver (a b : CoPPosition) : Bool := a.rank > b.rank

/-- Specifiers scope over heads. -/
theorem spec_scopes_over_head : scopesOver .spec .head = true := rfl

/-- Heads scope over complements. -/
theorem head_scopes_over_complement : scopesOver .head .complement = true := rfl

/-- Specifiers scope over complements (transitivity). -/
theorem spec_scopes_over_complement : scopesOver .spec .complement = true := rfl

/-- No position scopes over itself. -/
theorem no_self_scope (p : CoPPosition) : scopesOver p p = false := by
  cases p <;> rfl

/-- Heads do not scope over specifiers (asymmetry). -/
theorem head_not_over_spec : scopesOver .head .spec = false := rfl

/-- Complements do not scope over heads (asymmetry). -/
theorem complement_not_over_head : scopesOver .complement .head = false := rfl

/-! ### Dependency status (derived from position) -/

/-- Whether a position is a dependent position. Derived from the CoP
    structure: specifiers and complements are dependents; heads are not.

    This is not an independent stipulation — it follows from the
    structural definition of the CoP, where the head is the structural
    center and specifiers/complements are its dependents. -/
def CoPPosition.isDependent : CoPPosition → Bool
  | .spec       => true
  | .head       => false
  | .complement => true

/-- Specifiers are dependents. -/
theorem spec_is_dependent : CoPPosition.isDependent .spec = true := rfl

/-- Heads are not dependents. -/
theorem head_is_not_dependent : CoPPosition.isDependent .head = false := rfl

/-- Complements are dependents. -/
theorem complement_is_dependent : CoPPosition.isDependent .complement = true := rfl

/-! ### CoP node — morpho-phonological tree node -/

/-- A node in a morpho-phonological tree within a cophonological domain.
    Each node represents a morpheme at a structural position, with an
    optional grammatical tone specification.

    Dependency status is **derived from position** via
    `CoPPosition.isDependent`, not independently stipulated. After
    hierarchy exchange ([rolle-2018] Ch 4), syntactic structure
    maps to a CoP tree where scope ordering determines evaluation order:
    outer-scoping VIs' cophonologies apply after (and thus override)
    inner-scoping ones. -/
structure CoPNode where
  /-- Structural position within the CoP. -/
  position : CoPPosition
  /-- Optional GT specification. `none` if this morpheme has no
      grammatical tone. -/
  gtSpec : Option GTSpec := none
  deriving Repr

/-- Derived dependency status: a node is a dependent iff its position
    is Spec or Complement. -/
def CoPNode.isDependent (n : CoPNode) : Bool := n.position.isDependent

/-! ### Hierarchy exchange -/

/-- **Hierarchy exchange**: map a set of morphemes (from syntactic
    structure) to a cophonological evaluation order. The result is
    sorted by scope rank (highest first), so outer-scoping cophonologies
    are evaluated last — their effects take precedence.

    [rolle-2018] Ch 4: hierarchy exchange preserves the inside-out
    derivational history of the syntactic module by referencing
    asymmetrical c-command, mediated through the CoP-scope ordering. -/
def hierarchyExchange (nodes : List CoPNode) : List CoPNode :=
  nodes.mergeSort (λ a b => a.position.rank ≥ b.position.rank)

/-- Hierarchy exchange preserves the node set (it only reorders). -/
theorem hierarchyExchange_perm (nodes : List CoPNode) :
    (hierarchyExchange nodes).length = nodes.length := by
  simp [hierarchyExchange, List.length_mergeSort]

/-! ### Deriving the dominant GT asymmetry -/

/-- **The key lemma**: if a position scopes over Head, it must be Spec.

    Complement has lower rank than Head, so it cannot scope over Head.
    Head cannot scope over itself. Only Spec (rank 2 > 1) qualifies.

    This is the structural backbone of the dominant GT asymmetry:
    if dominant GT requires scoping over the head, and only Spec
    scopes over Head, then dominant triggers must be at Spec. -/
theorem scopes_over_head_implies_spec (p : CoPPosition)
    (h : scopesOver p .head = true) : p = .spec := by
  cases p with
  | spec => rfl
  | head => exact absurd h (by decide)
  | complement => exact absurd h (by decide)

/-- A position that scopes over Head is a dependent position.

    Follows from `scopes_over_head_implies_spec` (it must be Spec)
    and `spec_is_dependent` (Spec is a dependent). -/
theorem scopes_over_head_is_dependent (p : CoPPosition)
    (h : scopesOver p .head = true) : p.isDependent = true := by
  have := scopes_over_head_implies_spec p h
  subst this; rfl

/-- **The dominant GT asymmetry derived from CoP-scope.**

    Hypotheses:
    1. The target is at Head position (it's the lexical head)
    2. The trigger scopes over the target (required for dominance)

    From these two facts alone, the CoP-scope hierarchy determines:
    - The trigger is at Spec (only Spec scopes over Head)
    - Spec is a dependent position
    - Head is not a dependent position

    Therefore `DominantGTAsymmetry.holds` is satisfied: the trigger
    is a dependent and the target is a head. The Bool values are
    **computed from positions**, not independently stipulated.

    Non-trivial prediction: complements are dependents but cannot be
    dominant triggers, because Complement does not scope over Head. -/
theorem dominant_gt_asymmetry_from_scope (triggerPos targetPos : CoPPosition)
    (hTarget : targetPos = .head)
    (hScope : scopesOver triggerPos targetPos = true) :
    DominantGTAsymmetry.holds
      ⟨triggerPos.isDependent, !targetPos.isDependent⟩ = true := by
  subst hTarget
  have := scopes_over_head_implies_spec triggerPos hScope
  subst this; rfl

/-- Complements cannot be dominant triggers despite being dependents:
    Complement does not scope over Head. This is a non-trivial prediction
    of the CoP-scope account — the asymmetry is not simply "dependents
    dominate heads" but specifically "dependents that scope over heads
    dominate heads." -/
theorem complement_cannot_dominate_head :
    scopesOver .complement .head = false := rfl

/-- Heads cannot impose dominant GT on specifiers (outward dominance). -/
theorem head_cannot_dominate_spec :
    scopesOver .head .spec = false := rfl

/-! ## Matrix-Basemap Correspondence (MxBM-C)

A **basemap** is an abstract I/O mapping derived from a "deficient projection"
of the input: all valued (lexical) tones on the target are stripped, leaving
only floating (grammatical) tones. **Dominant GT** = faithfulness to the
basemap output; since the basemap has no valued tones to preserve, the matrix
output is forced to match the grammatical tune, so the target's underlying
tones go unrealized.
-/

open Tone (TRN)

/-! ### Basemap — deficient projection -/

/-- Strip all tones from a host word, replacing them with a default tone.
    The **deficient projection** of [rolle-2018] Ch 5: the input with
    all valued (lexical) tones removed, leaving only the segmental skeleton
    ready to receive floating (grammatical) tones.

    The `defaultTone` is the tone assigned to "unvalued" TBUs —
    language-specific (often L in African tone languages). -/
def deficientProjection {S : Type} (host : List (TBU S)) (defaultTone : TRN) :
    List (TBU S) :=
  host.map fun tbu => { tbu with tone := defaultTone }

/-- Deficient projection produces uniform tone: every TBU gets the
    default tone. -/
theorem deficientProjection_uniform {S : Type}
    (host : List (TBU S)) (defaultTone : TRN) :
    (deficientProjection host defaultTone).map TBU.tone =
    host.map fun _ => defaultTone := by
  simp only [deficientProjection, List.map_map]; congr 1

/-! ### Basemap output -/

/-- Compute the basemap output: apply the grammatical tune to the
    deficient projection. This represents what the output would look
    like if the target had no underlying tones — only the floating
    tones from the trigger determine the surface pattern.

    For replacive-dominant GT with a whole-word melody, the basemap
    output has the grammatical tune on every TBU. -/
def basemapOutput {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (spec : Spec) (defaultTone : TRN) : List (TBU S) :=
  tonalOverwrite (deficientProjection host defaultTone) spec

/-! ### Tonal tier extraction -/

/-- Extract the tonal tier from a list of TBUs.

    Grounded in the `Tier` abstraction
    (`TierProjection.apply (TierProjection.total TBU.tone)`): an erasing string
    homomorphism `(TBU S)* → TRN*` in the Kleisli category of `Option`.
    The tonal tier is the `total` (no-erasure) case [goldsmith-1976]. -/
def tonalTier {S : Type} (tbus : List (TBU S)) : List TRN :=
  TierProjection.apply (TierProjection.total TBU.tone) tbus

/-- The tonal tier reduces to `List.map TBU.tone` (the historical
    formulation), via `TierProjection.total`'s length-preservation property. -/
@[simp] theorem tonalTier_eq_map {S : Type} (tbus : List (TBU S)) :
    tonalTier tbus = tbus.map TBU.tone :=
  TierProjection.apply_total _ _

/-! ### Matrix-Basemap Correspondence — derived from `Corr` -/

/-- Matrix-Basemap Correspondence violation count: Hamming distance between
    the matrix tonal tier and the basemap tonal tier.

    **Derived from `Corr.identViol`** on the `(false, true)` edge of the
    binary parallel-pair correspondence between the two tiers. This
    structurally identifies MxBM-C as IDENT-OO of [mccarthy-prince-1995]
    / [benua-1997] specialized to the tonal tier — no separate Hamming
    implementation, no bridge theorem required.

    On unequal-length tiers, the underlying `Corr.parallel` truncates to the
    shorter prefix (matching `List.zip` semantics). -/
def basemapViolations (tier₁ tier₂ : List TRN) : Nat :=
  (Corr.parallel tier₁ tier₂).identViol .lhs .rhs

/-- Self-comparison has zero basemap violations: a tonal tier is
    perfectly faithful to itself. Derived from `Corr.identity_ident_zero`. -/
theorem basemapViolations_self_eq_zero (t : List TRN) :
    basemapViolations t t = 0 :=
  Corr.identity_ident_zero t

/-- Zero basemap violations with equal-length tiers implies the tiers are
    identical. The equal-length hypothesis is necessary because the
    underlying `Corr.parallel` truncates to `min`. -/
theorem basemapViolations_eq_zero_imp
    (t₁ t₂ : List TRN) (hLen : t₁.length = t₂.length)
    (hZero : basemapViolations t₁ t₂ = 0) : t₁ = t₂ := by
  unfold basemapViolations Corr.identViol at hZero
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
  apply List.ext_getElem hLen
  intro n hn₁ hn₂
  have hmem : ((⟨n, hn₁⟩ : Fin t₁.length), (⟨n, hn₂⟩ : Fin t₂.length)) ∈
      (Corr.parallel t₁ t₂).edge .lhs .rhs := by
    rw [Corr.parallel_edge_lhs_rhs]
    exact (Corr.mem_diagDiag _ _).mpr rfl
  have hne := hZero hmem
  simp only [Corr.parallel_form_lhs, Corr.parallel_form_rhs, not_not] at hne
  simpa using hne

/-! ### Constraint bridge -/

/-- Wrap `basemapViolations` as a `Constraint` for use in OT
    tableaux and cophonological evaluation.

    Given a fixed basemap output (the tonal tier of the basemap-faithful
    form), this constraint evaluates each candidate by comparing its
    tonal tier against the basemap. In [rolle-2018]'s analysis,
    dominant triggers promote this constraint above default markedness
    in their cophonology's subranking.

    `extractTier` converts a candidate to its tonal tier for comparison.
    This allows the constraint to work with any candidate type, not
    just raw `List TRN`. -/
def mkBasemapConstraint {C : Type}
    (basemapTier : List TRN)
    (extractTier : C → List TRN) : Constraint C :=
  fun c => basemapViolations (extractTier c) basemapTier

/-! ### Dominance as basemap faithfulness -/

/-- Helper: whole-word `tonalOverwrite` reduces to `List.map`. -/
private theorem tonalOverwrite_whole_eq_map {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : TRN) :
    tonalOverwrite host ⟨"", [t], .whole⟩ =
    host.map fun tbu => { tbu with tone := t } := rfl

/-- The central theorem of MxBM-C: for replacive-dominant GT with a
    whole-word single-tone melody, the matrix output's tonal tier
    equals the basemap output's tonal tier.

    This captures [rolle-2018]'s key insight: dominant GT is not
    a special deletion rule or markedness constraint, but faithfulness
    to an abstract basemap. The target's underlying tones go unrealized
    because the output must match what would happen if those tones
    were never there. -/
theorem tonalOverwrite_basemap_faithful {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : TRN) (defaultTone : TRN) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (tonalOverwrite host spec) =
    tonalTier (basemapOutput host spec defaultTone) := by
  simp only [tonalTier_eq_map, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  congr 1

/-- The basemap output's tonal tier is independent of the host's
    underlying tones: for whole-word replacement, two hosts with
    different lexical tones but identical segmental content produce
    the same basemap tonal tier.

    The formal content of "transparadigmatic uniformity"
    ([rolle-2018] Ch 5): the basemap abstracts away from the
    paradigmatic tonal variation of the target. -/
theorem basemapOutput_tone_independent_whole {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host₁ host₂ : List (TBU S)) (t defaultTone : TRN)
    (hLen : host₁.length = host₂.length) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (basemapOutput host₁ spec defaultTone) =
    tonalTier (basemapOutput host₂ spec defaultTone) := by
  simp only [tonalTier_eq_map, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  have mapConst : ∀ xs : List (TBU S),
      List.map (TBU.tone ∘ (fun tbu : TBU S => { tbu with tone := t }) ∘
        fun tbu : TBU S => { tbu with tone := defaultTone }) xs =
      List.replicate xs.length t := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ _ ih =>
      simp only [List.map_cons, Function.comp_def, List.length_cons,
                 List.replicate_succ]
      exact congrArg _ ih
  rw [mapConst, mapConst, hLen]

end Rolle2018
