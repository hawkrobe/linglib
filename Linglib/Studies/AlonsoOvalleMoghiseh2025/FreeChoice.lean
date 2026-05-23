import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Exhaustification.Tolerant
import Linglib.Fragments.Farsi.Determiners
import Mathlib.Tactic.DeriveFintype

/-!
# Alonso-Ovalle & Moghiseh 2025: Existential Free Choice Items
@cite{alonso-ovalle-moghiseh-2025}

Existential free choice items: The case of Farsi *yek-i* DPs.
*Semantics & Pragmatics* 18, Article 4.

Farsi *yek-i* DPs pattern with other EFCIs in DE and modal contexts
but are grammatical, modality-free, and uniqueness-conveying in root
contexts. The paper derives this profile from **split exhaustification**:
scalar and domain alternatives are targeted by independent operators,
with scalar exhaustification clause-bounded below the modal.

## Main declarations

* `root_full_innocent_vacuous` — full IE on the 2-book root alternative
  set is vacuous (3 MCEs, no shared alt; IE = ∅).
* `root_full_tolerant_contradiction` — Chierchia's tolerant operator
  yields ⊥ on the same set (paper eq. 92).
* `root_scalar_only_uniqueness` — yek-i's partial scalar exhaustification
  gives uniqueness (eq. 93a).
* `root_domain_only_conjunction` — partial domain exhaustification gives
  conjunction (eq. 93b), blocked by Chierchia's Economy Principle.
* `deontic_poss_split_exh` — split exh under ◇ derives FC + embedded
  uniqueness (eq. 119).
* `deontic_nec_split_exh` — split exh under □ (eq. 120).
* `de_scalar_exh_weakens` — scalar exh inside a DE conditional
  strictly weakens the matrix (cf. eq. 129–135).
* `single_exh_no_fc`, `above_only_all_alts_too_strong`,
  `two_ie_above_below_too_strong` — three non-split architectures fail.
* `rootReading` and `*_reading_agrees` — Table 2 typology and its
  bridge to the `Fragments.Farsi.Determiners` lexicon.

## Implementation notes

Three finite world types: `PQWorld` (4 worlds), `PermW` (8 worlds),
`CondW` (8 worlds). Theorems close by `decide` over `Finset` substrate;
`abbrev` aliases on the alternative-set Finsets drive reduction.

The sibling module `Studies.AlonsoOvalleMoghiseh2025.Generic` proves
the same results structurally at the `Prop` level for arbitrary domains
and lifts them to arbitrary Kripke frames. The two are complementary:
`Generic` proves *why* the results hold; this file checks that the
algorithm computes the right answers.

The 2-book root case exposes a counting subtlety: the paper's (101)
lists 2 MCEs for the full alternative set, but there are actually 3
(`{b₁∧b₂, b₁∧¬b₂}`, `{b₁∧b₂, b₂∧¬b₁}`, `{b₁∧¬b₂, b₂∧¬b₁}`), so IE = ∅
and `innocent.exh` is vacuous (see `root_full_innocent_vacuous`). The
paper's result (103) requires applying operators separately — exactly
the split-exhaustification architecture.

## Todo

* The bridge theorems use a local `RootReading` enum mapped to
  `Fragments.Farsi.Determiners.EFCIReading` via `RootReading.toDetReading`.
  Using `EFCIReading` directly would eliminate the conversion.
-/

namespace AlonsoOvalleMoghiseh2025

open Exhaustification (innocent tolerant predToFinset altsFromPreds)


/-!
### Root Contexts (§4)

With a domain D = {b₁, b₂}, the assertion of unembedded *yek-i* is
b₁ ∨ b₂ ("Forood bought a book"). `PQWorld` enumerates the four
possible book-buying configurations.

The three alternative classes:
- **Scalar**: {b₁ ∧ b₂} (bought ≥ 2, from replacing numeral *yek*)
- **Domain**: {b₁, b₂} (restricting quantification to subdomains)
- **Pre-exhaustified domain**: {b₁ ∧ ¬b₂, b₂ ∧ ¬b₁}
-/

section RootContext

/-- Four book-buying configurations: each book independently bought or not. -/
inductive PQWorld where
  | pOnly | qOnly | both | neither
  deriving Repr, DecidableEq, Fintype

def pProp : PQWorld → Bool | .pOnly | .both => true | _ => false
def qProp : PQWorld → Bool | .qOnly | .both => true | _ => false
def pOrQ  : PQWorld → Bool | .neither => false | _ => true
def pAndQ : PQWorld → Bool | .both => true | _ => false

/-- Assertion: ∃x ∈ {b₁,b₂}. bought(x) = b₁ ∨ b₂ -/
private def assertion : PQWorld → Bool := pOrQ

/-- Scalar alternative: bought ≥ 2 = b₁ ∧ b₂ -/
private def scalarAlt : PQWorld → Bool := pAndQ

/-- Pre-exhaustified domain alternatives: {b₁ ∧ ¬b₂, b₂ ∧ ¬b₁}.

    Each domain alternative exhaustified w.r.t. the other. -/
private def preExhDomAlt1 : PQWorld → Bool := fun w => pProp w && !qProp w
private def preExhDomAlt2 : PQWorld → Bool := fun w => qProp w && !pProp w

private def preExhDomAlts : List (PQWorld → Bool) := [preExhDomAlt1, preExhDomAlt2]

private abbrev domAlts : Finset (Finset PQWorld) := altsFromPreds [pProp, qProp]
private abbrev assertionF : Finset PQWorld := predToFinset assertion
private abbrev scalarAltF : Finset PQWorld := predToFinset scalarAlt
private abbrev preExhDomAltsF : Finset (Finset PQWorld) := altsFromPreds preExhDomAlts
private abbrev allAltsF : Finset (Finset PQWorld) :=
  altsFromPreds ([scalarAlt] ++ preExhDomAlts)

/-- Pre-exhaustified domain alternatives are derived from IE, not stipulated.
    `innocent.exh({b₁,b₂})(b₁) = b₁ ∧ ¬b₂` and dually for b₂. -/
theorem preExhDom_from_innocent_root :
    innocent.exh domAlts (predToFinset pProp) = predToFinset preExhDomAlt1 ∧
    innocent.exh domAlts (predToFinset qProp) = predToFinset preExhDomAlt2 := by
  refine ⟨?_, ?_⟩ <;> decide


/-! #### Result 1: Full exhaustification yields contradiction -/

/-- **Theorem (eq. 92)**: Chierchia's contradiction-tolerating operator
    applied to all alternatives yields ⊥ — the assertion conjoined with
    negation of all non-entailed alternatives is unsatisfiable.

    (b₁∨b₂) ∧ ¬(b₁∧b₂) ∧ ¬(b₁∧¬b₂) ∧ ¬(b₂∧¬b₁) ⟺ ⊥ -/
theorem root_full_tolerant_contradiction :
    tolerant.exh allAltsF assertionF = ∅ := by decide

/-- With Fox's IE, full exhaustification is vacuous (IE = ∅, no
    alternative is in every MCE).

    **Note on MCE count**: The paper's (101) lists 2 MCEs for this
    alternative set, but there are actually 3 — {b₁∧b₂, b₁∧¬b₂},
    {b₁∧b₂, b₂∧¬b₁}, and {b₁∧¬b₂, b₂∧¬b₁}. Since no alternative
    appears in all 3, IE = ∅ and Fox's operator is vacuous. The paper's
    result (103) = uniqueness requires IE = {b₁∧b₂}, which holds when
    the operators are applied separately (scalar-only IE correctly
    excludes b₁∧b₂ — see `root_scalar_only_uniqueness`).

    **Innocent vs tolerant**: For this specific alternative set, `tolerant`
    yields ⊥ while `innocent` is vacuous — they differ maximally. The
    split exhaustification architecture (O_σ and O_EXH-D as independent
    operators) means the paper's predictions go through `innocent` on
    each operator separately, not `tolerant` on the combined set. -/
theorem root_full_innocent_vacuous :
    innocent.exh allAltsF assertionF = assertionF := by decide


/-! #### Result 2: Scalar-only exhaustification yields uniqueness -/

/-- **Theorem (eq. 93a)**: O_σ (scalar-only exhaustification) yields
    uniqueness: (b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂) = "exactly one book."

    This is yek-i's reading in root contexts via partial exhaustification. -/
theorem root_scalar_only_uniqueness :
    innocent.exh (altsFromPreds [scalarAlt]) assertionF
      = assertionF \ scalarAltF := by decide

/-- Uniqueness is contingent (not contradictory). -/
theorem root_scalar_only_contingent :
    PQWorld.pOnly ∈ innocent.exh (altsFromPreds [scalarAlt]) assertionF ∧
    PQWorld.both ∉ innocent.exh (altsFromPreds [scalarAlt]) assertionF := by decide


/-! #### Result 3: Domain-only exhaustification yields conjunction -/

/-- **Theorem (eq. 93b)**: O_EXH-D (domain-only exhaustification) yields
    conjunction: (b₁ ∨ b₂) ∧ (b₁ ↔ b₂) ⟺ b₁ ∧ b₂.

    This is blocked by Chierchia's Economy Principle (the result is
    equivalent to the scalar alternative). -/
theorem root_domain_only_conjunction :
    innocent.exh preExhDomAltsF assertionF = predToFinset pAndQ := by decide

/-- Domain-only result is equivalent to the scalar alternative → blocked
    by the Exhaustification Economy Principle. -/
theorem domain_exh_equiv_scalar_alt :
    innocent.exh preExhDomAltsF assertionF = scalarAltF := by decide

end RootContext


/-!
### Deontic Possibility (§5, eq. 114–119)

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
  deriving Repr, DecidableEq, Fintype

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


/-- Pre-exhaustified domain alternatives under ◇: {◇b₁ ∧ ¬◇b₂, ◇b₂ ∧ ¬◇b₁}.

    Computed by exhaustifying each domain alt {◇b₁, ◇b₂} w.r.t. the
    other domain alts, following @cite{chierchia-2013}'s
    pre-exhaustification of subdomain alternatives. -/
private def modalPreExhDomAlt1 : PermW → Bool := fun w => canB1 w && !canB2 w
private def modalPreExhDomAlt2 : PermW → Bool := fun w => canB2 w && !canB1 w

private def modalPreExhDomAlts : List (PermW → Bool) :=
  [modalPreExhDomAlt1, modalPreExhDomAlt2]

private abbrev modalPreExhDomAltsF : Finset (Finset PermW) :=
  altsFromPreds modalPreExhDomAlts

private abbrev modalDomAltsF : Finset (Finset PermW) := altsFromPreds [canB1, canB2]
private abbrev canExOrF : Finset PermW := predToFinset canExOr

/-- Pre-exhaustified domain alts are correctly computed by applying `innocent.exh`
    to each domain alternative w.r.t. the domain alternative set. -/
theorem preExhDom_from_innocent :
    innocent.exh modalDomAltsF (predToFinset canB1) = predToFinset modalPreExhDomAlt1 ∧
    innocent.exh modalDomAltsF (predToFinset canB2) = predToFinset modalPreExhDomAlt2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Theorem (eq. 119)**: Split exhaustification under ◇ derives
    FC + embedded uniqueness:
    ◇(b₁⊻b₂) ∧ (◇b₁ ↔ ◇b₂)

    Equivalently: ◇(b₁⊻b₂) ∧ ◇b₁ ∧ ◇b₂ — each book is a permitted
    option, and in each permitted world exactly one book is bought. -/
theorem deontic_poss_split_exh :
    innocent.exh modalPreExhDomAltsF canExOrF
      = canExOrF.filter (fun w => canB1 w == canB2 w) := by decide

/-- FC component: the result entails ◇b₁ ∧ ◇b₂ whenever true. -/
theorem deontic_poss_fc (w : PermW)
    (h : w ∈ innocent.exh modalPreExhDomAltsF canExOrF) :
    canB1 w = true ∧ canB2 w = true := by
  revert h; cases w <;> decide

/-- Embedded uniqueness: the assertion ◇(b₁⊻b₂) means in every
    permitted world exactly one book is bought (the ⊻ is under ◇). -/
theorem deontic_poss_embedded_uniqueness (w : PermW)
    (h : w ∈ innocent.exh modalPreExhDomAltsF canExOrF) :
    canExOr w = true := by
  revert h; cases w <;> decide

/-- The result is compatible with ◇(b₁∧b₂) being true: Forood may be
    permitted to buy more than one book (paper main text near eq. 60,
    p. 21: "compatible with a scenario where he is allowed to buy one
    book and he is allowed to buy more than one book"). -/
theorem deontic_poss_compatible_with_joint :
    PermW.w111 ∈ innocent.exh modalPreExhDomAltsF canExOrF := by decide


/-! #### Without split: no FC -/

/-- ◇(b₁ ∨ b₂): at least one book is permitted. -/
private def canBuyAny (w : PermW) : Bool := canB1 w || canB2 w

private abbrev canBuyAnyF : Finset PermW := predToFinset canBuyAny

/-- Standard Sauerland-style alternatives at the modal level
    (without scalar exhaustification below the modal):
    {◇b₁, ◇b₂, ◇(b₁∧b₂)}. Note ◇(b₁∧b₂) = `canJoint`, NOT
    ◇b₁ ∧ ◇b₂ = `canB1 && canB2` — these are distinct propositions. -/
private def unsplitModalAlts : List (PermW → Bool) := [canB1, canB2, canJoint]
private abbrev unsplitModalAltsF : Finset (Finset PermW) :=
  altsFromPreds unsplitModalAlts

/-- **Theorem**: Single IE on ◇(b₁∨b₂) without split gives
    ◇(b₁∨b₂) ∧ ¬◇(b₁∧b₂) — anti-conjunction at the modal level
    (only ◇(b₁∧b₂) is innocently excludable), but NOT free choice.

    This shows split exhaustification is necessary for yek-i's
    distinctive FC + embedded uniqueness profile. -/
theorem single_exh_no_fc :
    innocent.exh unsplitModalAltsF canBuyAnyF
      = canBuyAnyF.filter (fun w => !canJoint w) := by decide

/-- The single-exh result is NOT free choice: there exists a world
    satisfying the exhaustified assertion where ◇b₁ but ¬◇b₂. -/
theorem single_exh_not_fc_witness :
    PermW.w100 ∈ innocent.exh unsplitModalAltsF canBuyAnyF ∧
    canB1 PermW.w100 = true ∧ canB2 PermW.w100 = false := by decide


/-!
#### Why Split Exhaustification Is Necessary

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
private def allModalAlts : List (PermW → Bool) := [canJoint] ++ modalPreExhDomAlts
private abbrev allModalAltsF : Finset (Finset PermW) := altsFromPreds allModalAlts

/-- **Single operator below ◇ too weak (eq. 143)**: after scalar
    exhaustification below the modal gives ◇(b₁⊻b₂), the result is
    compatible with only one book being permitted — no FC emerges
    without domain exhaustification above the modal. -/
theorem below_modal_only_no_fc :
    canExOr PermW.w100 = true ∧ canB1 PermW.w100 = true ∧ canB2 PermW.w100 = false := by
  decide

/-- **Single operator above ◇ too strong (eq. 146)**: a single IE
    operator above ◇ with all alternatives on the unexhaustified assertion
    ◇(b₁∨b₂) gives FC (from domain alts) BUT ALSO ¬◇(b₁∧b₂) (from
    scalar alt).

    Compare with split exh (`deontic_poss_split_exh`): the only
    difference is `&& !canJoint w`. Split exh allows ◇(b₁∧b₂),
    this forbids it. -/
theorem above_only_all_alts_too_strong :
    innocent.exh allModalAltsF canBuyAnyF
      = canBuyAnyF.filter (fun w => (canB1 w == canB2 w) && !canJoint w) := by decide

/-- **Two operators above+below ◇ too strong (eq. 144-145)**: two IE
    operators (O_σ below gives ◇(b₁⊻b₂), then full IE above) produces
    FC + embedded uniqueness BUT ALSO ¬◇(b₁∧b₂).

    Compare with split exh: identical result except for `&& !canJoint w`.
    The scalar alternative ◇(b₁∧b₂) is innocently excludable because it
    is non-entailed and consistently negatable alongside domain-alt
    negations. -/
theorem two_ie_above_below_too_strong :
    innocent.exh allModalAltsF canExOrF
      = canExOrF.filter (fun w => (canB1 w == canB2 w) && !canJoint w) := by decide

/-- Two-IE exhaustification is strictly stronger than split: it entails
    the split result but not vice versa. The difference is exactly
    ¬◇(b₁∧b₂) — split exh never negates the modal scalar alternative. -/
theorem two_ie_strictly_stronger :
    innocent.exh allModalAltsF canExOrF ⊆ innocent.exh modalPreExhDomAltsF canExOrF ∧
    PermW.w111 ∈ innocent.exh modalPreExhDomAltsF canExOrF ∧
    PermW.w111 ∉ innocent.exh allModalAltsF canExOrF := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The distinguishing case: split exh allows ◇(b₁∧b₂) (compatible with
    Forood buying both), while any architecture targeting the scalar
    alternative at the modal level forbids it. -/
theorem split_allows_joint_two_ie_forbids :
    (PermW.w111 ∈ innocent.exh modalPreExhDomAltsF canExOrF ∧ canJoint PermW.w111 = true) ∧
    (∀ w, w ∈ innocent.exh allModalAltsF canExOrF → canJoint w = false) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · decide
  · decide
  · intro w h; revert h; cases w <;> decide

end DeonticPossibility


/-!
### Deontic Necessity (§5, eq. 120)

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

/-! Box operators derived from `PermW`'s possibility atoms. The
encodings rely on the implicit constraint `□(b₁∨b₂)` — every accessible
world has at least one book bought — which holds by construction of
`PermW` since worlds with neither book are not in the state space. Under
that constraint:
- `□b₁` = ¬◇(b₂ ∧ ¬b₁), and
- `□(b₁⊻b₂)` collapses to ¬◇(b₁∧b₂), since the only way to violate
  exactly-one-per-world is via a joint-purchase world. -/
private def boxB1 (w : PermW) : Bool := !canExB2 w  -- □b₁
private def boxB2 (w : PermW) : Bool := !canExB1 w  -- □b₂
private def boxExOr (w : PermW) : Bool := !canJoint w  -- □(b₁⊻b₂), given □(b₁∨b₂)

/-- Pre-exhaustified domain alternatives under □: {□b₁ ∧ ¬□b₂, □b₂ ∧ ¬□b₁} -/
private def necPreExhDomAlt1 : PermW → Bool := fun w => boxB1 w && !boxB2 w
private def necPreExhDomAlt2 : PermW → Bool := fun w => boxB2 w && !boxB1 w
private def necPreExhDomAlts : List (PermW → Bool) := [necPreExhDomAlt1, necPreExhDomAlt2]

private abbrev necPreExhDomAltsF : Finset (Finset PermW) := altsFromPreds necPreExhDomAlts
private abbrev boxExOrF : Finset PermW := predToFinset boxExOr
private abbrev boxDomAltsF : Finset (Finset PermW) := altsFromPreds [boxB1, boxB2]

/-- Pre-exhaustified domain alts under □ are derived from IE. -/
theorem preExhDom_from_innocent_nec :
    innocent.exh boxDomAltsF (predToFinset boxB1) = predToFinset necPreExhDomAlt1 ∧
    innocent.exh boxDomAltsF (predToFinset boxB2) = predToFinset necPreExhDomAlt2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Theorem (eq. 120)**: Split exhaustification under □ derives
    FC + embedded uniqueness: □(b₁⊻b₂) ∧ (□b₁ ↔ □b₂).

    "Must buy exactly one book, and neither book is predetermined" —
    each book remains a possible choice within the obligation. -/
theorem deontic_nec_split_exh :
    innocent.exh necPreExhDomAltsF boxExOrF
      = boxExOrF.filter (fun w => boxB1 w == boxB2 w) := by decide

/-- FC component under □: ¬□b₁ ∧ ¬□b₂ (neither book is obligatory)
    whenever the exhaustified assertion holds non-vacuously. -/
theorem deontic_nec_fc (w : PermW)
    (h : w ∈ innocent.exh necPreExhDomAltsF boxExOrF)
    (hne : canExB1 w = true ∨ canExB2 w = true) :
    boxB1 w = false ∧ boxB2 w = false := by
  revert h hne; cases w <;> decide

/-- Embedded uniqueness under □: no joint-purchase world is accessible. -/
theorem deontic_nec_embedded_uniqueness (w : PermW)
    (h : w ∈ innocent.exh necPreExhDomAltsF boxExOrF) :
    canJoint w = false := by
  revert h; cases w <;> decide

end DeonticNecessity


/-!
### DE Contexts (§5, eq. 129–135)

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
  deriving Repr, DecidableEq, Fintype

private def condB1 : CondW → Bool
  | .b1g | .bg | .b1 | .b => true | _ => false
private def condB2 : CondW → Bool
  | .b2g | .bg | .b2 | .b => true | _ => false
private def condG : CondW → Bool
  | .b1g | .b2g | .bg | .g => true | _ => false

/-- Without exhaustification: (b₁ ∨ b₂) → g -/
private def condNoExh (w : CondW) : Bool :=
  !(condB1 w || condB2 w) || condG w

/-- With scalar exhaustification: ((b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂)) → g -/
private def condWithExh (w : CondW) : Bool :=
  !((condB1 w || condB2 w) && !(condB1 w && condB2 w)) || condG w

private abbrev condNoExhF : Finset CondW := predToFinset condNoExh
private abbrev condWithExhF : Finset CondW := predToFinset condWithExh

/-- **Theorem (eq. 131–134)**: Scalar exhaustification inside a
    conditional antecedent strictly weakens the matrix.

    `condNoExhF ⊂ condWithExhF`: the exhaustified version is true in
    strictly more worlds, so it carries less information. -/
theorem de_scalar_exh_weakens : condNoExhF ⊂ condWithExhF := by decide

/-- Without exhaustification, the conditional is stronger: every
    `condNoExh`-world is a `condWithExh`-world. -/
theorem de_no_exh_stronger : condNoExhF ⊆ condWithExhF := by decide

/-- With exhaustification, there's a world satisfying `condWithExh`
    but not `condNoExh`. -/
theorem de_exh_weaker_witness : ∃ w, w ∈ condWithExhF ∧ w ∉ condNoExhF :=
  ⟨.b, by decide⟩

/-- Pre-exhaustified domain alternatives in the conditional:
    {(b₁→g) ∧ ¬(b₂→g), (b₂→g) ∧ ¬(b₁→g)} -/
private def condPreExhDomAlts : List (CondW → Bool) :=
  [ fun w => (!condB1 w || condG w) && !(!condB2 w || condG w)
  , fun w => (!condB2 w || condG w) && !(!condB1 w || condG w)]

private abbrev condPreExhDomAltsF : Finset (Finset CondW) :=
  altsFromPreds condPreExhDomAlts

/-- **Theorem**: In DE contexts, domain exhaustification on the
    conditional is vacuous. The assertion (b₁∨b₂)→g already entails
    both b₁→g and b₂→g, so the pre-exhaustified domain alternatives
    (b₁→g ∧ ¬(b₂→g)) and (b₂→g ∧ ¬(b₁→g)) are both inconsistent
    with the assertion. IE correctly returns ∅, and `innocent.exh`
    is the identity.

    This means even without Maximize Strength blocking O_σ, O_EXH-D
    alone contributes nothing in DE contexts — the plain existential
    reading emerges regardless. -/
theorem de_domain_exh_vacuous :
    innocent.exh condPreExhDomAltsF condNoExhF = condNoExhF := by decide

end DEContext


/-!
### EFCI Typology

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
  deriving DecidableEq, Repr

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


/-!
### Bridge to Determiners Lexicon

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


end AlonsoOvalleMoghiseh2025
