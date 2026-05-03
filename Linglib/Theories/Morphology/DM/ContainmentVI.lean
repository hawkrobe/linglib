import Linglib.Core.Morphology.Containment
import Linglib.Core.Morphology.DegreeContainment
import Linglib.Core.Morphology.DomainLocality
import Mathlib.Order.WithBot
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Basic

/-!
# DM Vocabulary Insertion under Containment Locality
@cite{bobaljik-2012} @cite{bobaljik-2000} @cite{halle-marantz-1993}
@cite{smith-moskal-xu-kang-bobaljik-2019}

The DM-flavored derivation of the *ABA generalization for inflectional
morphology under root-out Vocabulary Insertion (@cite{bobaljik-2000}):
root VI rules can only be conditioned on features inside their local
domain, which means the same VI rule set competes at multiple cells of
a containment hierarchy and the Elsewhere mechanism picks identical
winners — giving plateau behavior, hence *ABA exclusion.

This file is the DM-side derivation of substrate facts in
`Core/Morphology/Containment.lean` and `Core/Morphology/DegreeContainment.lean`.
The Nanosyntax-side derivation (Superset Principle on phrasal
spellout) would live in `Theories/Morphology/Nanosyntax/`.

## File layout — two layers

**PART I** (n-parametric, §§1–6): the general containment-VI
machinery, parameterized by hierarchy depth `n`. The headline lemma is
`applicableRules_sublist_of_le` — under root-out locality, the set of
applicable rules is monotone in position. From monotonicity + a
**locality cap** `M` (no rule has `contextLevel > M`), the function
`viWinner` is constant on positions `p ≥ M` (the plateau theorem
`viWinningContextLevel_const_above_cap`). Specialized to `n = 3, M = 1`
this is the comparative-superlative result `vi_cmpr_eq_sprl`.

**PART II** (degree specialization, §§7–9, sub-namespace `Degree`):
the n=3 degree case derived from PART I via subtype refinement.
`Degree.LocalVIRule := { r : ContainmentVIRule 3 // r.contextLevel ≤ cmprLevel }`
bundles the locality cap into the rule type (mathlib `OrderHom` idiom).
`Degree.vi_cmpr_eq_sprl` is a one-line corollary of PART I's
`viExponent_const_above_cap`. Consumers (`Bobaljik2012`,
`SmithMoskalEtAl2019`) keep their `DegreePattern`-typed signatures
unchanged — `Degree.viPattern` still returns `DegreePattern`.

## The deep mathematical content

The headline lemma `applicableRules_sublist_of_le` is structural and
pre-morphological: as a position climbs from POS to SPRL (degree),
ABS to OBL (case), or SG to DL (number), strictly more rules become
applicable — those whose conditioning context is contained in the
current position. The remaining lemmas in PART I are pure plumbing on
this monotone structure:

- `applicableRules_eq_squeeze`: when the applicable sets at two
  endpoints `p ≤ r` agree, every position `q` squeezed between them
  has the same applicable set. Structural analog of
  `Monotone.eq_of_le_of_le`.
- `viWinner_eq_of_applicableRules_eq`: when applicable sets agree, the
  Elsewhere mechanism picks the same winner.
- `applicableRules_eq_above_cap`: under the cap, all positions ≥ M
  share the same applicable set.
- `viWinningContextLevel_const_above_cap`: combine to get plateau.

For the bridge to `Morphology.Containment.ViolatesABA`, see
PART II's `vi_cmpr_eq_sprl` (n=3 case directly) or apply
`viExponent_const_above_cap` at adjacent positions in the n>3 case.

## Future work

The `Theories/Morphology/Nanosyntax/` parallel — phrasal spellout +
Superset Principle deriving the same *ABA exclusion — is a separate
file the substrate anticipates but does not yet exist.
-/

namespace Theories.Morphology.DM.ContainmentVI

variable {n : Nat}

-- ============================================================================
-- PART I — N-PARAMETRIC CONTAINMENT VI
-- ============================================================================

-- ============================================================================
-- § 1: Containment VI Rule
-- ============================================================================

/-- A Vocabulary Insertion rule for an `n`-position containment hierarchy.

    - `exponent` is the phonological form inserted at the terminal.
    - `contextLevel` is the deepest position whose features the rule's
      context refers to. Under root-out insertion (@cite{bobaljik-2000}),
      the rule applies at any position `p` such that `contextLevel ≤ p`
      (positions strictly contain the contextLevel cell's features).
    - `specificity` is the Elsewhere ranking (higher = more specific).
      When two rules both apply, the higher-specificity one wins.

    The locality cap from @cite{bobaljik-2012} is *not* baked into the
    structure; it is a separate hypothesis on rule lists in §6. -/
structure ContainmentVIRule (n : Nat) where
  /-- Phonological exponent inserted at the terminal. -/
  exponent : Nat
  /-- Deepest position whose features condition this rule. -/
  contextLevel : Fin n
  /-- Specificity for Elsewhere ordering. -/
  specificity : Nat
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Applicability
-- ============================================================================

/-- A rule applies at position `p` iff its `contextLevel` is `≤ p`
    (root-out: outer positions can be conditioned on inner features). -/
def ContainmentVIRule.AppliesAt (r : ContainmentVIRule n) (p : Fin n) : Prop :=
  r.contextLevel ≤ p

instance (r : ContainmentVIRule n) (p : Fin n) : Decidable (r.AppliesAt p) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Applicability is monotone in position: if a rule applies at `p`
    and `p ≤ q`, it applies at `q`. -/
theorem ContainmentVIRule.AppliesAt.mono {r : ContainmentVIRule n}
    {p q : Fin n} (h : p ≤ q) : r.AppliesAt p → r.AppliesAt q :=
  fun hp => le_trans hp h

/-- The list of rules applicable at position `p`, preserving the order
    of the input list (so Elsewhere ties break by source order). -/
def applicableRules (rules : List (ContainmentVIRule n)) (p : Fin n) :
    List (ContainmentVIRule n) :=
  rules.filter (fun r => decide (r.AppliesAt p))

@[simp] theorem mem_applicableRules
    {rules : List (ContainmentVIRule n)} {p : Fin n}
    {r : ContainmentVIRule n} :
    r ∈ applicableRules rules p ↔ r ∈ rules ∧ r.AppliesAt p := by
  unfold applicableRules
  rw [List.mem_filter, decide_eq_true_iff]

-- ============================================================================
-- § 3: Headline — monotonicity of `applicableRules`
-- ============================================================================

/-- **Headline structural lemma**. As the position climbs the
    containment hierarchy, the set of applicable rules grows
    monotonically. This is the deep mathematical content from which
    *ABA exclusion follows in two further short steps (`§4`, `§6`).

    Stated as `List.Sublist`: every rule applicable at the lower
    position is applicable at the higher position, in the same order. -/
theorem applicableRules_sublist_of_le
    (rules : List (ContainmentVIRule n)) {p q : Fin n} (h : p ≤ q) :
    (applicableRules rules p).Sublist (applicableRules rules q) := by
  unfold applicableRules
  apply List.monotone_filter_right
  intro r hr
  simp only [decide_eq_true_iff] at hr ⊢
  exact hr.mono h

/-- The rule-set form (Set inclusion). The Set-level statement is the
    canonical mathlib idiom for `Monotone` of a function into a powerset
    lattice; the `List.Sublist` form above is the constructive analog
    that respects Elsewhere's source-order tie-breaking. -/
theorem applicableRules_subset_of_le
    (rules : List (ContainmentVIRule n)) {p q : Fin n} (h : p ≤ q) :
    {r | r ∈ applicableRules rules p} ⊆ {r | r ∈ applicableRules rules q} := by
  intro r hr
  simp only [Set.mem_setOf_eq, mem_applicableRules] at hr ⊢
  exact ⟨hr.1, hr.2.mono h⟩

-- ============================================================================
-- § 4: Squeeze — monotone applicableRules + endpoint equality → middle equality
-- ============================================================================

/-- **Squeeze lemma**. When `applicableRules` at two endpoints `p ≤ r`
    agree, every position `q` between them has the same applicable set.

    Pure-list reasoning: under monotonicity (§3), the middle filter is
    sandwiched between the equal endpoint filters, forcing equality.
    This is the structural analog of `Monotone.eq_of_le_of_le`. -/
theorem applicableRules_eq_squeeze
    (rules : List (ContainmentVIRule n)) {p q r : Fin n}
    (h_pq : p ≤ q) (h_qr : q ≤ r)
    (h_pr : applicableRules rules p = applicableRules rules r) :
    applicableRules rules q = applicableRules rules p := by
  unfold applicableRules at *
  symm
  apply List.filter_congr
  intro x hx
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  refine ⟨fun hp => hp.mono h_pq, fun hq => ?_⟩
  have happl_r : x.AppliesAt r := hq.mono h_qr
  have hmem_r : x ∈ rules.filter (fun y => decide (y.AppliesAt r)) := by
    rw [List.mem_filter]
    exact ⟨hx, decide_eq_true happl_r⟩
  rw [← h_pr, List.mem_filter, decide_eq_true_iff] at hmem_r
  exact hmem_r.2

-- ============================================================================
-- § 5: VI Winner — determined by applicableRules
-- ============================================================================

/-- The winning rule at position `p`: highest-specificity applicable
    rule. `mergeSort` is stable, so ties break by input-list order
    (the standard interpretation of Elsewhere when specificities tie). -/
def viWinner (rules : List (ContainmentVIRule n)) (p : Fin n) :
    Option (ContainmentVIRule n) :=
  let applicable := applicableRules rules p
  let sorted := applicable.mergeSort (fun a b => a.specificity ≥ b.specificity)
  sorted.head?

/-- The contextLevel of the winning rule at position `p`, as
    `WithBot (Fin n)` (returns `⊥` if no rule applies). -/
def viWinningContextLevel (rules : List (ContainmentVIRule n)) (p : Fin n) :
    WithBot (Fin n) :=
  match viWinner rules p with
  | some r => (r.contextLevel : WithBot (Fin n))
  | none => ⊥

/-- The exponent of the winning rule at position `p`, falling back to
    `defaultForm` if no rule applies. -/
def viExponent (rules : List (ContainmentVIRule n)) (defaultForm : Nat)
    (p : Fin n) : Nat :=
  match viWinner rules p with
  | some r => r.exponent
  | none => defaultForm

/-- The realized cell pattern: list of exponents at each of the `n`
    positions, in containment order. -/
def viCellPattern (rules : List (ContainmentVIRule n)) (defaultForm : Nat) : List Nat :=
  (List.finRange n).map (viExponent rules defaultForm)

/-- **Bridge lemma**. The `viWinner` function depends only on
    `applicableRules`: when applicable sets agree, the same Elsewhere
    competition picks the same winner. -/
theorem viWinner_eq_of_applicableRules_eq
    {rules : List (ContainmentVIRule n)} {p q : Fin n}
    (h : applicableRules rules p = applicableRules rules q) :
    viWinner rules p = viWinner rules q := by
  unfold viWinner
  rw [h]

/-- Corollary: when applicable sets agree, exponent agrees. -/
theorem viExponent_eq_of_applicableRules_eq
    {rules : List (ContainmentVIRule n)} {defaultForm : Nat} {p q : Fin n}
    (h : applicableRules rules p = applicableRules rules q) :
    viExponent rules defaultForm p = viExponent rules defaultForm q := by
  unfold viExponent
  rw [viWinner_eq_of_applicableRules_eq h]

-- ============================================================================
-- § 6: Locality Cap → Plateau → *ABA Exclusion
-- ============================================================================

/-- A rule list is **capped at level `M`** when no rule has contextLevel
    strictly above `M`. This is @cite{bobaljik-2012}'s containment
    locality: root VI rules can be conditioned only on the immediately
    containing functional head, not on more distant ones. -/
def CappedAt (rules : List (ContainmentVIRule n)) (M : Fin n) : Prop :=
  ∀ r ∈ rules, r.contextLevel ≤ M

/-- Under the cap, applicable sets at positions `p, q ≥ M` agree.
    Both filters select the same set: every rule in the list (since
    every rule has contextLevel ≤ M ≤ p, q). -/
theorem applicableRules_eq_above_cap
    {rules : List (ContainmentVIRule n)} {M : Fin n}
    (hCap : CappedAt rules M) {p q : Fin n}
    (hp : M ≤ p) (hq : M ≤ q) :
    applicableRules rules p = applicableRules rules q := by
  unfold applicableRules
  apply List.filter_congr
  intro x hx
  have hx_le : x.contextLevel ≤ M := hCap x hx
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  exact ⟨fun _ => le_trans hx_le hq, fun _ => le_trans hx_le hp⟩

/-- **Plateau theorem**. Under the cap, `viExponent` is constant on
    positions `p, q ≥ M`. Specializing to `n = 3, M = 1` recovers
    `Degree.vi_cmpr_eq_sprl` (PART II). -/
theorem viExponent_const_above_cap
    {rules : List (ContainmentVIRule n)} {M : Fin n}
    (hCap : CappedAt rules M) (defaultForm : Nat) {p q : Fin n}
    (hp : M ≤ p) (hq : M ≤ q) :
    viExponent rules defaultForm p = viExponent rules defaultForm q :=
  viExponent_eq_of_applicableRules_eq (applicableRules_eq_above_cap hCap hp hq)

/-- **Headline corollary** (n-position generalization of
    `Degree.vi_cmpr_eq_sprl`). Under the cap at `M`,
    `viWinningContextLevel` is constant on positions `p ≥ M`. -/
theorem viWinningContextLevel_const_above_cap
    {rules : List (ContainmentVIRule n)} {M : Fin n}
    (hCap : CappedAt rules M) {p q : Fin n}
    (hp : M ≤ p) (hq : M ≤ q) :
    viWinningContextLevel rules p = viWinningContextLevel rules q := by
  unfold viWinningContextLevel
  rw [viWinner_eq_of_applicableRules_eq (applicableRules_eq_above_cap hCap hp hq)]

-- ============================================================================
-- PART II — DEGREE (n=3) SPECIALIZATION
-- ============================================================================

namespace Degree

open Core.Morphology.DegreeContainment

-- ============================================================================
-- § 7: LocalVIRule (subtype of `ContainmentVIRule 3`)
-- ============================================================================

/-- The locality cap for degree morphology: CMPR is the deepest
    position whose features a root VI rule can be conditioned on. -/
def cmprLevel : Fin 3 := ⟨1, by decide⟩

/-- A locality-constrained VI rule for root morphemes in degree
    contexts (@cite{bobaljik-2012}, @cite{bobaljik-2000}).

    Subtype of `ContainmentVIRule 3` with the locality cap `≤ cmprLevel`
    bundled in via subtype refinement. This is the mathlib `OrderHom`
    idiom (bundle the constraint with the carrier) applied to a
    morphological rule with a structural locality property.

    Root-out insertion (@cite{bobaljik-2000}) means root VI rules can
    only be conditioned on features in the root's local domain — the
    CMPR head that immediately contains the root. The SPRL head is
    outside CMPR and invisible to root VI; this is the cap. -/
abbrev LocalVIRule : Type := { r : ContainmentVIRule 3 // r.contextLevel ≤ cmprLevel }

/-- Project a list of `LocalVIRule` to the underlying
    `ContainmentVIRule 3` list. -/
private def liftRules (rules : List LocalVIRule) : List (ContainmentVIRule 3) :=
  rules.map (·.val)

/-- A lifted rule list automatically satisfies the cap — every member
    inherits the subtype constraint. -/
private theorem liftRules_capped (rules : List LocalVIRule) :
    CappedAt (liftRules rules) cmprLevel := by
  intro r hr
  obtain ⟨r', _, heq⟩ := List.mem_map.mp hr
  exact heq ▸ r'.property

-- ============================================================================
-- § 8: VI Competition + Core Theorems (derived from PART I)
-- ============================================================================

/-- The degree pattern generated by VI competition. Built directly from
    PART I's `viExponent`, applied at each grade's position via
    `DegreeGrade.toFin` (defined in `Core/Morphology/DegreeContainment.lean`). -/
def viPattern (rules : List LocalVIRule) (defaultForm : Nat) : DegreePattern :=
  ⟨viExponent (liftRules rules) defaultForm DegreeGrade.pos.toFin,
   viExponent (liftRules rules) defaultForm DegreeGrade.cmpr.toFin,
   viExponent (liftRules rules) defaultForm DegreeGrade.sprl.toFin⟩

/-- **Core result**: under degree locality, VI selects the same root
    form at CMPR and SPRL. Direct corollary of PART I's plateau theorem
    `viExponent_const_above_cap` at the cap `cmprLevel`, instantiated
    at positions 1 (CMPR) and 2 (SPRL).

    Formal content of @cite{bobaljik-2012}'s containment argument:
    root suppletion at SPRL ↔ root suppletion at CMPR. -/
theorem vi_cmpr_eq_sprl (rules : List LocalVIRule) (defaultForm : Nat) :
    (viPattern rules defaultForm).cmpr = (viPattern rules defaultForm).sprl :=
  viExponent_const_above_cap (liftRules_capped rules) defaultForm
    (le_refl cmprLevel) (by decide)

/-- **CSG Part I from VI**: root suppletive at CMPR ⇒ root suppletive at SPRL. -/
theorem csg_part1_vi (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).CmprSuppletive) :
    (viPattern rules defaultForm).SprlSuppletive := by
  unfold DegreePattern.CmprSuppletive DegreePattern.SprlSuppletive at *
  rwa [← vi_cmpr_eq_sprl]

/-- **CSG Part II from VI**: root suppletive at SPRL ⇒ root suppletive at CMPR. -/
theorem csg_part2_vi (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).SprlSuppletive) :
    (viPattern rules defaultForm).CmprSuppletive := by
  unfold DegreePattern.CmprSuppletive DegreePattern.SprlSuppletive at *
  rwa [vi_cmpr_eq_sprl]

/-- VI-generated root suppletion patterns are AAA or ABB only. *ABA is
    excluded by contiguity; *AAB and ABC (for root suppletion) are
    excluded by VI locality (CMPR cell = SPRL cell). -/
theorem vi_pattern_abb_or_aaa (rules : List LocalVIRule) (defaultForm : Nat) :
    (viPattern rules defaultForm).cmpr = (viPattern rules defaultForm).sprl :=
  vi_cmpr_eq_sprl rules defaultForm

-- ============================================================================
-- § 9: Domain-Aware Framing
-- ============================================================================

/-! `vi_cmpr_eq_sprl` is implicitly an "all-positions-same-domain"
theorem: under @cite{bobaljik-2012}'s strong-locality assumption
(now expressed as the subtype refinement `LocalVIRule := { r // r.contextLevel ≤ cmprLevel }`),
positions 1 (CMPR) and 2 (SPRL) are forced to share a winning rule
because no rule sees beyond CMPR. This is a degenerate case of
@cite{moskal-2015a-dissertation}'s domain-based locality where the
trivial partition (every position in one domain) makes the
domain-aware constraint vacuous and the structural-locality
constraint the only operative one.

The corollary below makes the domain-aware framing parametric: future
consumers (e.g., `Phenomena/Allomorphy/Studies/SmithMoskalEtAl2019`
§4 wiring case + number partitions) can thread a `DomainPartition`
explicitly. The `SameDomain π 1 2` hypothesis is unused in the proof
because the original theorem holds unconditionally — the parametric
form is a future-proofing shim, not a structural strengthening.

A real domain-relativized variant (where the cap is replaced by a
partition-aware bound, and the theorem becomes "under domain locality,
CMPR = SPRL only when in same domain") requires the cap-refinement to
itself be partition-aware. Deferred until a consumer requires it. -/

open Morphology.DomainLocality

/-- Domain-aware framing of `vi_cmpr_eq_sprl`: under any partition
    where positions 1 and 2 are in the same domain, VI selects the
    same root form at CMPR and SPRL. The proof discharges the
    `SameDomain` hypothesis as unused — the structural-locality
    refinement on `LocalVIRule` already forces the equality
    unconditionally. -/
theorem vi_cmpr_eq_sprl_under_domain
    {Tag : Type*} [DecidableEq Tag] (π : DomainPartition Tag)
    (rules : List LocalVIRule) (defaultForm : Nat)
    (_h : SameDomain π 1 2) :
    (viPattern rules defaultForm).cmpr = (viPattern rules defaultForm).sprl :=
  vi_cmpr_eq_sprl rules defaultForm

/-- Trivial-partition recovery: under `DomainPartition.trivial`, the
    `SameDomain` hypothesis is `rfl`, so `vi_cmpr_eq_sprl_under_domain`
    reduces to the original `vi_cmpr_eq_sprl`. -/
theorem vi_cmpr_eq_sprl_trivial (rules : List LocalVIRule) (defaultForm : Nat) :
    (viPattern rules defaultForm).cmpr = (viPattern rules defaultForm).sprl :=
  vi_cmpr_eq_sprl_under_domain DomainPartition.trivial rules defaultForm rfl

end Degree

end Theories.Morphology.DM.ContainmentVI
