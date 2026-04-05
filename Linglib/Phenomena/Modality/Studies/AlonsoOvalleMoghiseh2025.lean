import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Fragments.Farsi.Determiners

/-!
# Alonso-Ovalle & Moghiseh 2025: Existential Free Choice Items
@cite{alonso-ovalle-moghiseh-2025}

Existential free choice items: The case of Farsi *yek-i* DPs.
*Semantics & Pragmatics* 18, Article 4.

## Core Contribution

Farsi *yek-i* DPs instantiate a new EFCI profile: they pattern with
other EFCIs in DE and modal contexts (plain existential in DE, strengthened
under modals), but in root contexts they are grammatical, have no modal
component, and convey uniqueness. The paper argues this profile derives
from **split exhaustification**: scalar and domain alternatives are
exhaustified by independent operators, with scalar exhaustification
clause-bounded below the modal.

## Key Theoretical Results Formalized Here

1. **Root + full exhaustification = ⊥** (motivates rescue mechanisms)
2. **Root + scalar-only = uniqueness** (yek-i's partial exhaustification)
3. **Root + domain-only = conjunction** (blocked by Economy Principle)
4. **◇ + split exh = FC + embedded uniqueness** (yek-i under deontic ◇)
5. **DE + scalar exh weakens** (Maximize Strength blocks it)
6. **EFCI typology** (Table 2: modal insertion × partial exh)
7. **Split necessity** (eqs. 143-146: single/two-operator alternatives fail)

## Relationship to `SplitExhaustification.lean`

This file verifies each result computationally via `native_decide` on
small finite world types (PQWorld, PermW, CondW). The companion module
`Exhaustification.SplitExhaustification` proves the same results
structurally at the Prop level for arbitrary domains, without
`native_decide`. The two are complementary: the general module proves
WHY the results hold; this file verifies the algorithm (`exhB`)
computes the right answers.
-/

namespace Phenomena.Modality.Studies.AlonsoOvalleMoghiseh2025

open Exhaustification.InnocentExclusion


-- ============================================================
-- § 1. Root Context: Two-Book Domain
-- ============================================================

/-!
## Root Contexts (§4)

With a domain D = {b₁, b₂}, the assertion of unembedded *yek-i* is
b₁ ∨ b₂ ("Forood bought a book"). We reuse `PQWorld` from
`InnocentExclusion` (renaming p → b₁, q → b₂).

The three alternative classes:
- **Scalar**: {b₁ ∧ b₂} (bought ≥ 2, from replacing numeral *yek*)
- **Domain**: {b₁, b₂} (restricting quantification to subdomains)
- **Pre-exhaustified domain**: {b₁ ∧ ¬b₂, b₂ ∧ ¬b₁}
-/

section RootContext

-- Reuse PQWorld infrastructure (p = b₁, q = b₂)

/-- Assertion: ∃x ∈ {b₁,b₂}. bought(x) = b₁ ∨ b₂ -/
private abbrev assertion := pOrQ

/-- Scalar alternative: bought ≥ 2 = b₁ ∧ b₂ -/
private abbrev scalarAlt := pAndQ

/-- Pre-exhaustified domain alternatives: {b₁ ∧ ¬b₂, b₂ ∧ ¬b₁}

    Each domain alternative exhaustified w.r.t. the other domain alts.
    exh({b₁,b₂})(b₁) = b₁ ∧ ¬b₂; exh({b₁,b₂})(b₂) = b₂ ∧ ¬b₁. -/
private def preExhDomAlts : List (PQWorld → Bool) :=
  [ fun w => pProp w && !qProp w    -- b₁ ∧ ¬b₂
  , fun w => qProp w && !pProp w ]  -- b₂ ∧ ¬b₁

/-- Pre-exhaustified domain alternatives are derived from IE, not stipulated.
    exhB({b₁,b₂})(b₁) = b₁ ∧ ¬b₂ and exhB({b₁,b₂})(b₂) = b₂ ∧ ¬b₁. -/
theorem preExhDom_from_exhB_root :
    (∀ w, exhB pqDomain [pProp, qProp] pProp w = (pProp w && !qProp w)) ∧
    (∀ w, exhB pqDomain [pProp, qProp] qProp w = (qProp w && !pProp w)) := by
  constructor <;> intro w <;> cases w <;> native_decide

/-- All alternatives (scalar + pre-exhaustified domain). -/
private def allAlts : List (PQWorld → Bool) :=
  [scalarAlt] ++ preExhDomAlts


-- ── Result 1: Full exhaustification yields contradiction ─────

/-- **Theorem (eq. 92)**: Chierchia's O_ALT applied to all alternatives
    yields ⊥ — the assertion conjoined with negation of all non-entailed
    alternatives is unsatisfiable.

    (b₁∨b₂) ∧ ¬(b₁∧b₂) ∧ ¬(b₁∧¬b₂) ∧ ¬(b₂∧¬b₁) ⟺ ⊥ -/
theorem root_full_exhAll_contradiction :
    ∀ w : PQWorld, exhAll pqDomain allAlts assertion w = false := by
  intro w; cases w <;> native_decide

/-- With Fox's IE, full exhaustification is vacuous (IE = ∅, no
    alternative is in every MCE).

    **Note on MCE count**: The paper's (101) lists 2 MCEs for this
    alternative set, but there are actually 3 — {b₁∧b₂, b₁∧¬b₂},
    {b₁∧b₂, b₂∧¬b₁}, and {b₁∧¬b₂, b₂∧¬b₁}. Since no alternative
    appears in all 3, IE = ∅ and Fox's operator is vacuous. The paper's
    result (103) = uniqueness requires IE = {b₁∧b₂}, which holds when
    the operators are applied separately (scalar-only IE correctly
    excludes b₁∧b₂ — see `root_scalar_only_uniqueness`).

    **exhB vs exhAll**: For this specific alternative set, `exhAll`
    yields ⊥ while `exhB` is vacuous — they differ maximally. The split
    exhaustification architecture (O_σ and O_EXH-D as independent
    operators) means the paper's predictions go through `exhB` on each
    operator separately, not `exhAll` on the combined set. -/
theorem root_full_exhB_vacuous :
    ∀ w : PQWorld, exhB pqDomain allAlts assertion w = assertion w := by
  intro w; cases w <;> native_decide


-- ── Result 2: Scalar-only exhaustification yields uniqueness ─

/-- **Theorem (eq. 93a)**: O_σ (scalar-only exhaustification) yields
    uniqueness: (b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂) = "exactly one book."

    This is yek-i's reading in root contexts via partial exhaustification. -/
theorem root_scalar_only_uniqueness :
    ∀ w : PQWorld, exhB pqDomain [scalarAlt] assertion w =
      (assertion w && !scalarAlt w) := by
  intro w; cases w <;> native_decide

/-- Uniqueness is contingent (not contradictory). -/
theorem root_scalar_only_contingent :
    (∃ w, exhB pqDomain [scalarAlt] assertion w = true) ∧
    (∃ w, exhB pqDomain [scalarAlt] assertion w = false) :=
  ⟨⟨.pOnly, by native_decide⟩, ⟨.both, by native_decide⟩⟩


-- ── Result 3: Domain-only exhaustification yields conjunction ─

/-- **Theorem (eq. 93b)**: O_EXH-D (domain-only exhaustification) yields
    conjunction: (b₁ ∨ b₂) ∧ (b₁ ↔ b₂) ⟺ b₁ ∧ b₂.

    This is blocked by Chierchia's Economy Principle (the result is
    equivalent to the scalar alternative). -/
theorem root_domain_only_conjunction :
    ∀ w : PQWorld, exhB pqDomain preExhDomAlts assertion w = pAndQ w := by
  intro w; cases w <;> native_decide

/-- Domain-only result is equivalent to the scalar alternative → blocked
    by the Exhaustification Economy Principle. -/
theorem domain_exh_equiv_scalar_alt :
    ∀ w : PQWorld, exhB pqDomain preExhDomAlts assertion w = scalarAlt w := by
  intro w; cases w <;> native_decide

end RootContext


-- ============================================================
-- § 2. Deontic Possibility: Split Exhaustification
-- ============================================================

/-!
## Deontic Possibility (§5, eq. 114–119)

LF: O_EXH-D ◇ O_σ [IP ye book-i ... Forood buy t₁]

**Step 1**: O_σ on IP → (b₁∨b₂) ∧ ¬(b₁∧b₂) = "exactly one book"
**Step 2**: ◇ applied → ◇(b₁⊻b₂) = "permitted to buy exactly one"
**Step 3**: O_EXH-D negates pre-exhaustified domain alternatives

The result is FC + embedded uniqueness: ◇b₁ ∧ ◇b₂ ∧ ◇(b₁⊻b₂),
meaning each book is a permitted option and in each permitted world
exactly one book is bought.

### World Type

Worlds are parameterized by which atomic modal propositions hold:
◇(b₁∧¬b₂), ◇(b₂∧¬b₁), ◇(b₁∧b₂). This gives 8 possible states.
-/

section DeonticPossibility

/-- Modal worlds for the EFCI analysis. Each world represents a
    permission state parameterized by three atomic modal propositions:
    ◇(b₁∧¬b₂), ◇(b₂∧¬b₁), ◇(b₁∧b₂). Named by which are true (1) or
    false (0) in order. -/
inductive PermW where
  | w000  -- nothing permitted
  | w100  -- only b₁-exclusive worlds accessible
  | w010  -- only b₂-exclusive worlds accessible
  | w110  -- both exclusive worlds accessible (no joint)
  | w001  -- only joint-purchase world accessible
  | w101  -- b₁-exclusive and joint accessible
  | w011  -- b₂-exclusive and joint accessible
  | w111  -- all three types accessible
  deriving Repr, DecidableEq, BEq

private def permDomain : List PermW :=
  [.w000, .w100, .w010, .w110, .w001, .w101, .w011, .w111]

-- Atomic modal propositions
private def canExB1 : PermW → Bool  -- ◇(b₁ ∧ ¬b₂)
  | .w100 | .w110 | .w101 | .w111 => true | _ => false
private def canExB2 : PermW → Bool  -- ◇(b₂ ∧ ¬b₁)
  | .w010 | .w110 | .w011 | .w111 => true | _ => false
private def canJoint : PermW → Bool  -- ◇(b₁ ∧ b₂)
  | .w001 | .w101 | .w011 | .w111 => true | _ => false

-- Derived modal propositions
private def canB1 (w : PermW) : Bool := canExB1 w || canJoint w  -- ◇b₁
private def canB2 (w : PermW) : Bool := canExB2 w || canJoint w  -- ◇b₂
private def canExOr (w : PermW) : Bool := canExB1 w || canExB2 w  -- ◇(b₁⊻b₂)


-- ── Step 1: O_σ on IP (already proved in RootContext) ────────
-- Result: b₁ ⊻ b₂ = "exactly one book"

-- ── Step 2: ◇ applied ───────────────────────────────────────
-- Assertion at modal level: ◇(b₁⊻b₂) = canExOr

-- ── Step 3: O_EXH-D ─────────────────────────────────────────

/-- Pre-exhaustified domain alternatives under ◇: {◇b₁ ∧ ¬◇b₂, ◇b₂ ∧ ¬◇b₁}

    Computed by exhaustifying each domain alt {◇b₁, ◇b₂} w.r.t. the
    other domain alts, following @cite{chierchia-2013}'s pre-exhaustification
    of subdomain alternatives. -/
private def modalPreExhDomAlts : List (PermW → Bool) :=
  [ fun w => canB1 w && !canB2 w    -- ◇b₁ ∧ ¬◇b₂
  , fun w => canB2 w && !canB1 w ]  -- ◇b₂ ∧ ¬◇b₁

/-- Pre-exhaustified domain alts are correctly computed by applying `exhB`
    to each domain alternative w.r.t. the domain alternative set. -/
theorem preExhDom_from_exhB :
    (∀ w, exhB permDomain [canB1, canB2] canB1 w = (canB1 w && !canB2 w)) ∧
    (∀ w, exhB permDomain [canB1, canB2] canB2 w = (canB2 w && !canB1 w)) := by
  constructor <;> intro w <;> cases w <;> native_decide

/-- **Theorem (eq. 119)**: Split exhaustification under ◇ derives
    FC + embedded uniqueness:
    ◇(b₁⊻b₂) ∧ (◇b₁ ↔ ◇b₂)

    Equivalently: ◇(b₁⊻b₂) ∧ ◇b₁ ∧ ◇b₂ — each book is a permitted
    option, and in each permitted world exactly one book is bought. -/
theorem deontic_poss_split_exh :
    ∀ w : PermW, exhB permDomain modalPreExhDomAlts canExOr w =
      (canExOr w && (canB1 w == canB2 w)) := by
  intro w; cases w <;> native_decide

/-- FC component: the result entails ◇b₁ ∧ ◇b₂ whenever true. -/
theorem deontic_poss_fc (w : PermW)
    (h : exhB permDomain modalPreExhDomAlts canExOr w = true) :
    canB1 w = true ∧ canB2 w = true := by
  cases w <;> revert h <;> native_decide

/-- Embedded uniqueness: the assertion ◇(b₁⊻b₂) means in every
    permitted world exactly one book is bought (the ⊻ is under ◇). -/
theorem deontic_poss_embedded_uniqueness (w : PermW)
    (h : exhB permDomain modalPreExhDomAlts canExOr w = true) :
    canExOr w = true := by
  cases w <;> revert h <;> native_decide

/-- The result is compatible with ◇(b₁∧b₂) being true (fn. 14):
    Forood may be permitted to buy more than one book. -/
theorem deontic_poss_compatible_with_joint :
    exhB permDomain modalPreExhDomAlts canExOr .w111 = true := by
  native_decide


-- ── Single IE without split: no FC ─────────────────────────

/-- ◇(b₁ ∨ b₂): at least one book is permitted. -/
private def canBuyAny (w : PermW) : Bool := canB1 w || canB2 w

/-- Standard Sauerland-style alternatives at the modal level
    (without scalar exhaustification below the modal):
    {◇b₁, ◇b₂, ◇(b₁∧b₂)}. Note ◇(b₁∧b₂) = `canJoint`, NOT
    ◇b₁ ∧ ◇b₂ = `canB1 && canB2` — these are distinct propositions. -/
private def unsplitModalAlts : List (PermW → Bool) :=
  [canB1, canB2, canJoint]

/-- **Theorem**: Single IE on ◇(b₁∨b₂) without split gives
    ◇(b₁∨b₂) ∧ ¬◇(b₁∧b₂) — anti-conjunction at the modal level
    (only ◇(b₁∧b₂) is innocently excludable), but NOT free choice.

    This shows split exhaustification is necessary for yek-i's
    distinctive FC + embedded uniqueness profile. -/
theorem single_exh_no_fc :
    ∀ w : PermW, exhB permDomain unsplitModalAlts canBuyAny w =
      (canBuyAny w && !canJoint w) := by
  intro w; cases w <;> native_decide

/-- The single-exh result is NOT free choice: there exists a world
    satisfying the exhaustified assertion where ◇b₁ but ¬◇b₂. -/
theorem single_exh_not_fc_witness :
    ∃ w : PermW, exhB permDomain unsplitModalAlts canBuyAny w = true ∧
      canB1 w = true ∧ canB2 w = false :=
  ⟨.w100, by native_decide, rfl, rfl⟩


-- ── Why split is necessary (§5, eqs. 143-146) ────────────────

/-!
### Why Split Exhaustification Is Necessary

The paper argues that only split exhaustification — two independent
operators targeting different alternative classes — derives the correct
result. Three alternative architectures all fail:

1. **Single operator below ◇** (eq. 143): gives ◇(uniqueness), too weak
2. **Single operator above ◇** (eq. 146): gives FC + unwanted ¬◇(b₁∧b₂)
3. **Two operators above+below** (eq. 144): same as (2) — too strong

Only split exh (O_EXH-D above ◇, O_σ below ◇) avoids negating the modal
scalar alternative, producing FC + uniqueness without ¬◇(b₁∧b₂).
-/

/-- All alternatives at the modal level: scalar ◇(b₁∧b₂) plus
    pre-exhaustified domain alternatives {◇b₁∧¬◇b₂, ◇b₂∧¬◇b₁}.
    Used by single-operator-above and two-operator architectures. -/
private def allModalAlts : List (PermW → Bool) :=
  [canJoint] ++ modalPreExhDomAlts

/-- **Single operator below ◇ too weak (eq. 143)**: after scalar
    exhaustification below the modal gives ◇(b₁⊻b₂), the result is
    compatible with only one book being permitted — no FC emerges
    without domain exhaustification above the modal. -/
theorem below_modal_only_no_fc :
    ∃ w : PermW, canExOr w = true ∧ canB1 w = true ∧ canB2 w = false :=
  ⟨.w100, rfl, rfl, rfl⟩

/-- **Single operator above ◇ too strong (eq. 146)**: a single IE
    operator above ◇ with all alternatives on the unexhaustified assertion
    ◇(b₁∨b₂) gives FC (from domain alts) BUT ALSO ¬◇(b₁∧b₂) (from
    scalar alt).

    Compare with split exh (`deontic_poss_split_exh`): the only
    difference is `&& !canJoint w`. Split exh allows ◇(b₁∧b₂),
    this forbids it. -/
theorem above_only_all_alts_too_strong :
    ∀ w : PermW, exhB permDomain allModalAlts canBuyAny w =
      (canBuyAny w && (canB1 w == canB2 w) && !canJoint w) := by
  intro w; cases w <;> native_decide

/-- **Two operators above+below ◇ too strong (eq. 144-145)**: two IE
    operators (O_σ below gives ◇(b₁⊻b₂), then full IE above) produces
    FC + embedded uniqueness BUT ALSO ¬◇(b₁∧b₂).

    Compare with split exh: identical result except for `&& !canJoint w`.
    The scalar alternative ◇(b₁∧b₂) is innocently excludable because it
    is non-entailed and consistently negatable alongside domain-alt
    negations. -/
theorem two_ie_above_below_too_strong :
    ∀ w : PermW, exhB permDomain allModalAlts canExOr w =
      (canExOr w && (canB1 w == canB2 w) && !canJoint w) := by
  intro w; cases w <;> native_decide

/-- Two-IE exhaustification is strictly stronger than split: it entails
    the split result but not vice versa. The difference is exactly
    ¬◇(b₁∧b₂) — split exh never negates the modal scalar alternative. -/
theorem two_ie_strictly_stronger :
    (∀ w, exhB permDomain allModalAlts canExOr w = true →
          exhB permDomain modalPreExhDomAlts canExOr w = true) ∧
    (∃ w, exhB permDomain modalPreExhDomAlts canExOr w = true ∧
          exhB permDomain allModalAlts canExOr w = false) := by
  constructor
  · intro w h; cases w <;> revert h <;> native_decide
  · exact ⟨.w111, by native_decide, by native_decide⟩

/-- The distinguishing case: split exh allows ◇(b₁∧b₂) (compatible with
    Forood buying both), while any architecture targeting the scalar
    alternative at the modal level forbids it. -/
theorem split_allows_joint_two_ie_forbids :
    (∃ w, exhB permDomain modalPreExhDomAlts canExOr w = true ∧
          canJoint w = true) ∧
    (∀ w, exhB permDomain allModalAlts canExOr w = true →
          canJoint w = false) := by
  constructor
  · exact ⟨.w111, by native_decide, rfl⟩
  · intro w h; cases w <;> revert h <;> native_decide

end DeonticPossibility


-- ============================================================
-- § 2b. Deontic Necessity: Split Exhaustification under □
-- ============================================================

/-!
## Deontic Necessity (§5, eq. 120)

LF: O_EXH-D □ O_σ [IP ye book-i ... Forood buy t₁]

The same split exhaustification structure under □ instead of ◇.

**Step 1**: O_σ on IP → b₁⊻b₂ (as before)
**Step 2**: □ applied → □(b₁⊻b₂) = "must buy exactly one"
**Step 3**: O_EXH-D negates pre-exhaustified domain alternatives under □

### Box Operators (reusing PermW)

□b₁ = ¬◇(b₂∧¬b₁) = ¬canExB2: every accessible world has b₁.
□b₂ = ¬◇(b₁∧¬b₂) = ¬canExB1: every accessible world has b₂.
□(b₁⊻b₂) = ¬◇(b₁∧b₂) = ¬canJoint: no joint-purchase world accessible.
-/

section DeonticNecessity

-- Box operators derived from PermW's possibility atoms
private def boxB1 (w : PermW) : Bool := !canExB2 w  -- □b₁ = ¬◇(b₂∧¬b₁)
private def boxB2 (w : PermW) : Bool := !canExB1 w  -- □b₂ = ¬◇(b₁∧¬b₂)
private def boxExOr (w : PermW) : Bool := !canJoint w  -- □(b₁⊻b₂) = ¬◇(b₁∧b₂)

/-- Pre-exhaustified domain alternatives under □: {□b₁ ∧ ¬□b₂, □b₂ ∧ ¬□b₁} -/
private def necPreExhDomAlts : List (PermW → Bool) :=
  [ fun w => boxB1 w && !boxB2 w    -- □b₁ ∧ ¬□b₂
  , fun w => boxB2 w && !boxB1 w ]  -- □b₂ ∧ ¬□b₁

/-- Pre-exhaustified domain alts under □ are derived from IE. -/
theorem preExhDom_from_exhB_nec :
    (∀ w, exhB permDomain [boxB1, boxB2] boxB1 w = (boxB1 w && !boxB2 w)) ∧
    (∀ w, exhB permDomain [boxB1, boxB2] boxB2 w = (boxB2 w && !boxB1 w)) := by
  constructor <;> intro w <;> cases w <;> native_decide

/-- **Theorem (eq. 120)**: Split exhaustification under □ derives
    FC + embedded uniqueness: □(b₁⊻b₂) ∧ (□b₁ ↔ □b₂).

    "Must buy exactly one book, and neither book is predetermined" —
    each book remains a possible choice within the obligation. -/
theorem deontic_nec_split_exh :
    ∀ w : PermW, exhB permDomain necPreExhDomAlts boxExOr w =
      (boxExOr w && (boxB1 w == boxB2 w)) := by
  intro w; cases w <;> native_decide

/-- FC component under □: ¬□b₁ ∧ ¬□b₂ (neither book is obligatory)
    whenever the exhaustified assertion holds non-vacuously. -/
theorem deontic_nec_fc (w : PermW)
    (h : exhB permDomain necPreExhDomAlts boxExOr w = true)
    (hne : canExB1 w = true ∨ canExB2 w = true) :
    boxB1 w = false ∧ boxB2 w = false := by
  cases w <;> revert hne <;> revert h <;> native_decide

/-- Embedded uniqueness under □: no joint-purchase world is accessible. -/
theorem deontic_nec_embedded_uniqueness (w : PermW)
    (h : exhB permDomain necPreExhDomAlts boxExOr w = true) :
    canJoint w = false := by
  cases w <;> revert h <;> native_decide

end DeonticNecessity


-- ============================================================
-- § 3. Downward-Entailing Contexts: Maximize Strength
-- ============================================================

/-!
## DE Contexts (§5, eq. 129–135)

In DE contexts (e.g., conditional antecedents), scalar exhaustification
below the operator is blocked by Maximize Strength: it globally weakens
the matrix sentence.

"If Forood reads ye book-i, he gets a gift"
- Without O_σ: (b₁ ∨ b₂) → g
- With O_σ:    ((b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂)) → g  ← strictly weaker!

Since weakening is detected, O_σ is blocked, and the EFCI contributes
plain existential force.
-/

section DEContext

/-- Worlds for the conditional: b₁, b₂, g (gift). -/
inductive CondW where
  | b1g | b2g | bg | b1 | b2 | b | g | none
  deriving Repr, DecidableEq

private def condDomain : List CondW :=
  [.b1g, .b2g, .bg, .b1, .b2, .b, .g, .none]

private def cb1 : CondW → Bool
  | .b1g | .bg | .b1 | .b => true | _ => false
private def cb2 : CondW → Bool
  | .b2g | .bg | .b2 | .b => true | _ => false
private def cg : CondW → Bool
  | .b1g | .b2g | .bg | .g => true | _ => false

/-- Without exhaustification: (b₁ ∨ b₂) → g -/
private def condNoExh (w : CondW) : Bool :=
  !(cb1 w || cb2 w) || cg w

/-- With scalar exhaustification: ((b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂)) → g -/
private def condWithExh (w : CondW) : Bool :=
  !((cb1 w || cb2 w) && !(cb1 w && cb2 w)) || cg w

/-- **Theorem (eq. 131–134)**: Scalar exhaustification inside a
    conditional antecedent strictly weakens the matrix.

    condWithExh ⊂ condNoExh: every world making condWithExh true also
    makes condNoExh true, but w = .b (b₁∧b₂ without gift) makes
    condNoExh false but condWithExh true. -/
theorem de_scalar_exh_weakens :
    maximizeStrength condDomain condWithExh condNoExh = false := by
  native_decide

/-- Without exhaustification, the conditional is stronger. -/
theorem de_no_exh_stronger :
    condDomain.any (fun w => condNoExh w && !condWithExh w) = false := by
  native_decide

/-- With exhaustification, there's a world satisfying condWithExh
    but not condNoExh. -/
theorem de_exh_weaker_witness :
    condDomain.any (fun w => !condNoExh w && condWithExh w) = true := by
  native_decide

/-- Domain alternatives in the conditional: subdomain conditionals
    b₁→g and b₂→g. -/
private def condDomAlts : List (CondW → Bool) :=
  [ fun w => !cb1 w || cg w     -- b₁ → g
  , fun w => !cb2 w || cg w ]   -- b₂ → g

/-- Pre-exhaustified domain alternatives in the conditional:
    {(b₁→g) ∧ ¬(b₂→g), (b₂→g) ∧ ¬(b₁→g)} -/
private def condPreExhDomAlts : List (CondW → Bool) :=
  [ fun w => (!cb1 w || cg w) && !(!cb2 w || cg w)  -- (b₁→g) ∧ ¬(b₂→g)
  , fun w => (!cb2 w || cg w) && !(!cb1 w || cg w)] -- (b₂→g) ∧ ¬(b₁→g)

/-- **Theorem**: In DE contexts, domain exhaustification on the
    conditional is vacuous. The assertion (b₁∨b₂)→g already entails
    both b₁→g and b₂→g, so the pre-exhaustified domain alternatives
    (b₁→g ∧ ¬(b₂→g)) and (b₂→g ∧ ¬(b₁→g)) are both inconsistent
    with the assertion. IE correctly returns ∅, and exhB is the identity.

    This means even without Maximize Strength blocking O_σ, O_EXH-D
    alone contributes nothing in DE contexts — the plain existential
    reading emerges regardless. -/
theorem de_domain_exh_vacuous :
    ∀ w : CondW, exhB condDomain condPreExhDomAlts condNoExh w = condNoExh w := by
  intro w; cases w <;> native_decide

end DEContext


-- ============================================================
-- § 4. EFCI Typology (Table 2)
-- ============================================================

/-!
## EFCI Typology

@cite{alonso-ovalle-moghiseh-2025} Table 2: EFCIs vary along two
parameters — modal insertion and partial exhaustification.

| Type           | Modal insertion | Partial exh |
|----------------|:-:|:-:|
| *vreun*        | − | − |
| *irgendein*    | + | − |
| *yek-i*        | − | + |

- *vreun*: neither mechanism → contradiction in root → ungrammatical
- *irgendein*: modal insertion → covert □ rescues → epistemic ignorance
- *yek-i*: partial exh (scalar only) → uniqueness in root
-/

section Typology

/-- A rescue parameter bundle for an EFCI. -/
structure EFCIParams where
  modalInsertion : Bool
  partialExh : Bool
  deriving DecidableEq, Repr, BEq

def vreunParams : EFCIParams := ⟨false, false⟩
def irgendeinParams : EFCIParams := ⟨true, false⟩
def yekiParams : EFCIParams := ⟨false, true⟩

/-- Grammaticality in root: an EFCI is grammatical iff at least one
    rescue mechanism is available. -/
def grammaticalInRoot (p : EFCIParams) : Bool :=
  p.modalInsertion || p.partialExh

theorem vreun_ungrammatical : grammaticalInRoot vreunParams = false := rfl
theorem irgendein_grammatical : grammaticalInRoot irgendeinParams = true := rfl
theorem yeki_grammatical : grammaticalInRoot yekiParams = true := rfl

/-- Root reading when grammatical. -/
inductive RootReading where
  | uniqueness          -- partial exh (scalar only)
  | epistemicIgnorance  -- modal insertion (covert □)
  | ungrammatical       -- no rescue
  deriving DecidableEq, Repr

/-- Derive root reading from rescue parameters.
    Modal insertion takes priority when both are available. -/
def rootReading (p : EFCIParams) : RootReading :=
  if p.modalInsertion then .epistemicIgnorance
  else if p.partialExh then .uniqueness
  else .ungrammatical

theorem vreun_root : rootReading vreunParams = .ungrammatical := rfl
theorem irgendein_root_reading : rootReading irgendeinParams = .epistemicIgnorance := rfl
theorem yeki_root_reading : rootReading yekiParams = .uniqueness := rfl

end Typology


-- ============================================================
-- § 5. Bridge: Study Typology ↔ Lexicon
-- ============================================================

/-!
## Bridge to Determiners Lexicon

The study's `EFCIParams`/`rootReading` and the Fragment lexicon's
`IndefiniteEntry`/`getReading` are two views of the same typology.
These bridge theorems prove they agree for all three EFCI types.
-/

section Bridge

open Fragments.Farsi.Determiners

/-- Convert study-level RootReading to Determiners EFCIReading option. -/
def RootReading.toDetReading : RootReading → Option EFCIReading
  | .uniqueness => some .uniqueness
  | .epistemicIgnorance => some .epistemicIgnorance
  | .ungrammatical => none

/-- yek-i: study predicts uniqueness, lexicon agrees. -/
theorem yeki_reading_agrees :
    getReading yeki rootContext = (rootReading yekiParams).toDetReading := rfl

/-- irgendein: study predicts epistemic ignorance, lexicon agrees. -/
theorem irgendein_reading_agrees :
    getReading irgendein_de rootContext = (rootReading irgendeinParams).toDetReading := rfl

/-- vreun: study predicts ungrammatical (none), lexicon agrees. -/
theorem vreun_reading_agrees :
    getReading vreun_ro rootContext = (rootReading vreunParams).toDetReading := rfl

/-- The study's grammaticality prediction matches the lexicon:
    getReading returns `some _` iff `grammaticalInRoot` is true. -/
theorem yeki_grammaticality_agrees :
    (getReading yeki rootContext).isSome = grammaticalInRoot yekiParams := rfl

theorem irgendein_grammaticality_agrees :
    (getReading irgendein_de rootContext).isSome = grammaticalInRoot irgendeinParams := rfl

theorem vreun_grammaticality_agrees :
    (getReading vreun_ro rootContext).isSome = grammaticalInRoot vreunParams := rfl

end Bridge


end Phenomena.Modality.Studies.AlonsoOvalleMoghiseh2025
