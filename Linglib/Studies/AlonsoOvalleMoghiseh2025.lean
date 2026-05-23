import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Exhaustification.Tolerant
import Linglib.Semantics.Exhaustification.Structural
import Linglib.Fragments.Farsi.Determiners
import Linglib.Data.Examples.Schema
import Linglib.Core.Logic.Quantification.Exclusive
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

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

### Computational verification (decide-checked on finite world types)

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

### Structural Prop-level proofs (`Generic` sub-namespace)

These lift the paper claims to arbitrary `D : Type*` with `P : D → Prop`,
plus arbitrary Kripke frames via `Acc : W → Prop` + `Q : D → W → Prop`.

* `Generic.scalar_exh_uniqueness` — "at least one and not at least two" ↔ "exactly one"
* `Generic.fc_two_element` — for |D|=2, ∃≥2 = ∀d
* `Generic.root_full_exh_contradiction` — full exh on |D|=2 → ⊥
* `Generic.exclusive_pairwise_inconsistent` — Spector closure observation
* `Generic.full_exh_consistent_three` — root contradiction is |D|=2-specific
* `Generic.modal_split_exh_fc`, `Generic.modal_split_exh_full` —
  Kripke-frame lift of the deontic-possibility split-exh result

Table 2 typology is canonicalized in `Fragments.Farsi.Determiners`
(`EFCIRescue` enum, per-item `yeki`/`irgendein_de`/`vreun_ro` entries,
per-item root-reading theorems). See the EFCI Typology section below.

## Implementation notes

Two complementary layers:

1. **Computational** (top-level): three finite world types (`PQWorld`
   4 worlds, `PermW` 8 worlds, `CondW` 8 worlds) with theorems closed by
   `decide` over `Finset` substrate from `Linglib.Semantics.Exhaustification`.
2. **Structural** (`Generic` sub-namespace): Prop-level proofs over
   arbitrary `D : Type*` and Kripke frames. The structural layer proves
   *why* the results hold; the computational layer verifies the algorithm
   computes the right answers on the paper's worked 2-book domain.

The 2-book root case exposes a counting subtlety: the paper's (101)
lists 2 MCEs for the full alternative set, but there are actually 3
(`{b₁∧b₂, b₁∧¬b₂}`, `{b₁∧b₂, b₂∧¬b₁}`, `{b₁∧¬b₂, b₂∧¬b₁}`), so IE = ∅
and `innocent.exh` is vacuous (see `root_full_innocent_vacuous`). The
paper's result (103) requires applying operators separately — exactly
the split-exhaustification architecture.

-/

namespace AlonsoOvalleMoghiseh2025

open Exhaustification (innocent tolerant predToFinset altsFromPreds
  altsFromPreds_singleton tolerant_exh_eq_empty_of_covered
  innocent_exh_eq_phi_of_innocentlyExcludable_empty
  innocent_exh_singleton_proper
  innocent_exh_pairwise_disjoint_partial)
open Data.Examples (LinguisticExample)
export Fragments.Farsi.Determiners (EFCIRescue EFCIReading ModalFlavor)


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

    `(b₁∨b₂) ∧ ¬(b₁∧b₂) ∧ ¬(b₁∧¬b₂) ∧ ¬(b₂∧¬b₁) ⟺ ⊥`.

    Derived from the structural substrate theorem
    `tolerant_exh_eq_empty_of_covered`: every `assertionF`-world (each of
    `pOnly`, `qOnly`, `both`) belongs to some non-entailed alternative
    (`preExhDomAlt1F`, `preExhDomAlt2F`, or `scalarAltF` respectively),
    so tolerant exhaustification has no surviving witness. -/
theorem root_full_tolerant_contradiction :
    tolerant.exh allAltsF assertionF = ∅ :=
  tolerant_exh_eq_empty_of_covered (by decide)

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
    each operator separately, not `tolerant` on the combined set.

    Derived from `innocent_exh_eq_phi_of_innocentlyExcludable_empty`
    (the substrate's IE-vacuity lemma): the IE algorithm returns the
    empty set on this 3-alt configuration, so exhaustification reduces
    to the identity. -/
theorem root_full_innocent_vacuous :
    innocent.exh allAltsF assertionF = assertionF :=
  innocent_exh_eq_phi_of_innocentlyExcludable_empty (by decide)


/-! #### Result 2: Scalar-only exhaustification yields uniqueness -/

/-- **Theorem (eq. 93a)**: O_σ (scalar-only exhaustification) yields
    uniqueness: (b₁ ∨ b₂) ∧ ¬(b₁ ∧ b₂) = "exactly one book."

    This is yek-i's reading in root contexts via partial exhaustification.

    Derived from `innocent_exh_singleton_proper`: when ALT is the
    singleton `{scalarAltF}` and `scalarAltF ⊊ assertionF` (i.e.,
    `{both} ⊊ {pOnly, qOnly, both}`), the substrate gives
    `innocent.exh = assertionF \ scalarAltF`. -/
theorem root_scalar_only_uniqueness :
    innocent.exh (altsFromPreds [scalarAlt]) assertionF
      = assertionF \ scalarAltF := by
  simp only [altsFromPreds_singleton]
  exact innocent_exh_singleton_proper (by decide)

/-- Uniqueness is contingent (not contradictory). -/
theorem root_scalar_only_contingent :
    PQWorld.pOnly ∈ innocent.exh (altsFromPreds [scalarAlt]) assertionF ∧
    PQWorld.both ∉ innocent.exh (altsFromPreds [scalarAlt]) assertionF := by decide


/-! #### Result 3: Domain-only exhaustification yields conjunction -/

/-- **Theorem (eq. 93b)**: O_EXH-D (domain-only exhaustification) yields
    conjunction: (b₁ ∨ b₂) ∧ (b₁ ↔ b₂) ⟺ b₁ ∧ b₂.

    This is blocked by Chierchia's Economy Principle (the result is
    equivalent to the scalar alternative).

    Derived from `innocent_exh_pairwise_disjoint_partial`: the two
    pre-exhaustified domain alternatives (`{pOnly}` and `{qOnly}`) are
    pairwise-disjoint singletons both ⊆ `assertionF`, with witness
    `both ∈ assertionF \ (alt₁ ∪ alt₂)`. The substrate returns
    `assertionF \ ({pOnly} ∪ {qOnly}) = {both} = predToFinset pAndQ`. -/
theorem root_domain_only_conjunction :
    innocent.exh preExhDomAltsF assertionF = predToFinset pAndQ := by
  have hcompat : (assertionF \ preExhDomAltsF.sup id).Nonempty := by decide
  rw [innocent_exh_pairwise_disjoint_partial hcompat]
  decide

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
    option, and in each permitted world exactly one book is bought.

    Derived from `innocent_exh_pairwise_disjoint_partial`: the two
    pre-exhaustified modal domain alternatives (`canB1 ∧ ¬canB2` and
    `canB2 ∧ ¬canB1`) are pairwise-disjoint subsets of `canExOrF`,
    with worlds satisfying both `canB1` and `canB2` (e.g. `w111`)
    surviving as the partial-cover witness. The set-difference RHS
    then equals the filter RHS by Finset extensionality. -/
theorem deontic_poss_split_exh :
    innocent.exh modalPreExhDomAltsF canExOrF
      = canExOrF.filter (fun w => canB1 w == canB2 w) := by
  have hcompat : (canExOrF \ modalPreExhDomAltsF.sup id).Nonempty := by decide
  rw [innocent_exh_pairwise_disjoint_partial hcompat]
  decide

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
    each book remains a possible choice within the obligation.

    Derived from `innocent_exh_pairwise_disjoint_partial`, analogous to
    `deontic_poss_split_exh` under □: with `boxExOrF \ ALT.sup id`
    non-empty (joint-allowing worlds outside both alts), every
    alternative is innocently excludable. Note the alts here are *not*
    subsets of `boxExOrF` — a world like `w101` (joint allowed,
    `boxB1 ∧ ¬boxB2` holds) lies in `necPreExhDomAlt1` but outside
    `boxExOrF`. The substrate's `φ \ ALT.sup id` formulation handles
    this by intersecting alts with `φ` automatically. -/
theorem deontic_nec_split_exh :
    innocent.exh necPreExhDomAltsF boxExOrF
      = boxExOrF.filter (fun w => boxB1 w == boxB2 w) := by
  have hcompat : (boxExOrF \ necPreExhDomAltsF.sup id).Nonempty := by decide
  rw [innocent_exh_pairwise_disjoint_partial hcompat]
  decide

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
### EFCI Typology (Table 2)

@cite{alonso-ovalle-moghiseh-2025} Table 2: EFCIs vary along two
parameters — modal insertion and partial exhaustification.

| Type        | Modal insertion | Partial exh | Lexicon entry |
|-------------|:-:|:-:|---|
| *vreun*     | − | − | `Fragments.Farsi.Determiners.vreun_ro` |
| *irgendein* | + | − | `Fragments.Farsi.Determiners.irgendein_de` |
| *yek-i*     | − | + | `Fragments.Farsi.Determiners.yeki` |

The typology is canonicalized in `Fragments.Farsi.Determiners.EFCIRescue`
(re-exported above), and the per-item root-reading predictions are
checked there:

- `Fragments.Farsi.Determiners.yeki_root : getReading yeki rootContext = some .uniqueness`
- `Fragments.Farsi.Determiners.irgendein_root : getReading irgendein_de rootContext = some .epistemicIgnorance`
- `Fragments.Farsi.Determiners.vreun_root_ungrammatical : getReading vreun_ro rootContext = none`
-/


/-! ### Structural Prop-level proofs (`Generic`)

These lift the paper claims to arbitrary `D : Type*` with `P : D → Prop`,
plus arbitrary Kripke frames via `Acc : W → Prop` + `Q : D → W → Prop`.
The computational sections above verify the algorithm computes the right
answers on the paper's worked 2-book domain; this section proves *why*
the results hold at full generality.
-/

namespace Generic

open Core.Quantification (exclusive_pairwise_inconsistent neg_all_exclusive_alts
  exclusive_false_of_universal uniqueness_precludes_universality)


/-! #### Scalar exhaustification → uniqueness -/

/-- **Scalar uniqueness**: "at least one and not at least two" is
equivalent to "exactly one."

This is the semantic content of O_σ: with a single scalar alternative
(the next numeral on the Horn scale), innocent exclusion trivially
returns that alternative (singleton MCE), and its negation gives
uniqueness. General over any domain D — no finiteness needed. -/
theorem scalar_exh_uniqueness {D : Type*} (P : D → Prop) :
    ((∃ d, P d) ∧ ¬∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂) ↔
    ∃ d, P d ∧ ∀ e, P e → e = d := by
  constructor
  · rintro ⟨⟨d, hd⟩, hNotTwo⟩
    exact ⟨d, hd, fun e he => by_contra fun hne =>
      hNotTwo ⟨e, d, hne, he, hd⟩⟩
  · rintro ⟨d, hd, huniq⟩
    exact ⟨⟨d, hd⟩, fun ⟨d₁, d₂, hne, h1, h2⟩ =>
      hne ((huniq d₁ h1).trans (huniq d₂ h2).symm)⟩


/-! #### Domain exhaustification → free choice -/

/-- **Two-element free choice**: for a two-element domain, existence plus
negation of all exclusive alternatives forces every element to satisfy P.

This completes the FC derivation for yek-i under deontic modals:
O_EXH-D negates the two exclusive modal alternatives, and since |D| = 2,
"at least 2 satisfy ◇P" becomes "both satisfy ◇P" — free choice. -/
theorem fc_two_element (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∀ d, P d := by
  obtain ⟨d₁, d₂, hne, h1, h2⟩ := neg_all_exclusive_alts P hExist hNegExcl
  intro d; fin_cases d <;> fin_cases d₁ <;> fin_cases d₂ <;> simp_all


/-! #### Root contradiction -/

/-- **Root contradiction**: asserting "at least one," negating "all"
(scalar), and negating both exclusive domain alternatives yields ⊥
for a two-element domain. -/
theorem root_full_exh_contradiction (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNotAll : ¬∀ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    False :=
  hNotAll (fc_two_element P hExist hNegExcl)

/-- Uniqueness (from scalar-only exhaustification) is satisfiable:
unlike full exhaustification, O_σ alone yields a consistent result.
This witnesses that partial exhaustification is a genuine rescue. -/
theorem uniqueness_satisfiable :
    ∃ P : Fin 2 → Prop, ∃ d, P d ∧ ∀ e, P e → e = d :=
  ⟨(· = 0), 0, rfl, fun _ h => h⟩


/-! #### DE contexts -/

/-- **Antecedent monotonicity**: strengthening a conditional's antecedent
weakens the conditional. -/
theorem antecedent_weakening {P Q R : Prop} (hQP : Q → P) :
    (P → R) → (Q → R) :=
  fun hPR hQ => hPR (hQP hQ)

/-- **Strict weakening witness**: when Q ⊂ P strictly, there is a world
where the weaker conditional P → R fails but the stronger conditional
Q → R holds. -/
theorem strict_antecedent_weakening {W : Type*} (P Q R : W → Prop)
    (hWitness : ∃ w, P w ∧ ¬Q w ∧ ¬R w) :
    ∃ w, ¬(P w → R w) ∧ (Q w → R w) := by
  obtain ⟨w, hPw, hNQw, hNRw⟩ := hWitness
  exact ⟨w, fun hPR => hNRw (hPR hPw), fun hQw => absurd hQw hNQw⟩

/-- **Domain alternatives entailed in DE**: the full-domain conditional
(∃x P(x)) → R entails each subdomain conditional P(d) → R. -/
theorem de_domain_alt_entailed {D : Type*} (P : D → Prop) (R : Prop) (d : D) :
    ((∃ x, P x) → R) → (P d → R) :=
  fun h hPd => h ⟨d, hPd⟩


/-! #### Why split exhaustification is necessary

@cite{alonso-ovalle-moghiseh-2025} argue (§5, eqs. 143–146) that only
split exhaustification derives the correct FC + embedded uniqueness for
EFCIs under modals. The structural core:

1. Domain-exh preserves scalar compatibility — when all elements satisfy
   P, every exclusive alternative is false (`exclusive_false_of_universal`,
   imported from `Core.Quantification`).
2. Full exh contradicts for |D|=2 (`root_full_exh_contradiction`).
3. Full exh is consistent for |D|≥3 (`full_exh_consistent_three`).
-/

/-- **Domain-exh result compatible with scalar**: there exists a model
satisfying all three conditions simultaneously — assertion (∃d P d),
domain-exh negations (∀d ¬exclusive(d)), AND scalar (∀d P d). -/
theorem domain_exh_result_compatible_with_scalar {D : Type*} {a b : D}
    (hab : a ≠ b) :
    ∃ P : D → Prop,
      (∃ d, P d) ∧
      (∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) ∧
      (∀ d, P d) := by
  refine ⟨fun _ => True, ⟨a, trivial⟩, ?_, fun _ => trivial⟩
  exact exclusive_false_of_universal hab _ (fun _ => trivial)

/-- **Full exh consistent for 3-element domain**: unlike the 2-element
case, for |D|=3 we can simultaneously have (∃d P d), ¬(∀d P d), and
(∀d ¬exclusive(d)). The root contradiction is |D|=2-specific. -/
theorem full_exh_consistent_three :
    ∃ P : Fin 3 → Prop,
      (∃ d, P d) ∧
      ¬(∀ d, P d) ∧
      (∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) := by
  refine ⟨(· ≠ (2 : Fin 3)), ⟨0, by decide⟩, fun h => h 2 rfl, ?_⟩
  intro d ⟨hPd, hexcl⟩
  fin_cases d
  · exact hexcl 1 (by decide) (by decide)
  · exact hexcl 0 (by decide) (by decide)
  · exact hPd rfl


/-! #### Modal split exhaustification (Kripke-frame lift)

All root-level results lift to arbitrary Kripke frames by instantiating
`P : D → Prop` with `fun d => ∃ w, Acc w ∧ Q d w` where `Acc : W → Prop`
is the accessibility predicate and `Q : D → W → Prop` is the base
property. Modal operators: ◇φ ≡ `∃ w, Acc w ∧ φ w`; □φ ≡ `∀ w, Acc w → φ w`.
-/

/-- **◇ preserves existential**: if some accessible world satisfies
∃x, Q x, then ∃d, ◇(Q d). -/
theorem diamond_preserves_exist {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (h : ∃ w, Acc w ∧ ∃ d, Q d w) :
    ∃ d, ∃ w, Acc w ∧ Q d w := by
  obtain ⟨w, hw, d, hd⟩ := h
  exact ⟨d, w, hw, hd⟩

/-- **◇ preserves existence from uniqueness**: ◇(∃!d, Q d) entails
∃d, ◇(Q d). -/
theorem diamond_uniqueness_implies_exist {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (h : ∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) :
    ∃ d, ∃ w, Acc w ∧ Q d w := by
  obtain ⟨w, hw, d, hd, _⟩ := h
  exact ⟨d, w, hw, hd⟩

/-- **Modal domain-exh gives plurality**: for any domain D, if
◇(∃x, Q x) and domain-exh negates all exclusive modal alternatives, then
at least two domain elements are possible. -/
theorem modal_domain_exh_plurality {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ (∃ w, Acc w ∧ Q d₁ w) ∧ (∃ w, Acc w ∧ Q d₂ w) :=
  neg_all_exclusive_alts (fun d => ∃ w, Acc w ∧ Q d w) hExist hNegExcl

/-- **Modal split exh gives FC (|D|=2)**: for a 2-element domain,
domain-exh above ◇ gives full free choice: every element is permitted. -/
theorem modal_split_exh_fc {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    ∀ d, ∃ w, Acc w ∧ Q d w :=
  fc_two_element (fun d => ∃ w, Acc w ∧ Q d w) hExist hNegExcl

/-- **Full split exh composition**: O_σ below ◇ gives uniqueness;
domain-exh above ◇ gives FC. Together: FC + embedded uniqueness. -/
theorem modal_split_exh_full {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hUniq : ∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    (∀ d, ∃ w, Acc w ∧ Q d w) ∧
    (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) :=
  ⟨modal_split_exh_fc Acc Q
    (diamond_uniqueness_implies_exist Acc Q hUniq) hNegExcl,
   hUniq⟩

/-- **◇(uniqueness) doesn't entail FC**: countermodel where only d=0
satisfies Q in the unique accessible world. -/
theorem modal_uniqueness_not_fc :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) ∧
      ¬(∀ d, ∃ w, Acc w ∧ Q d w) :=
  ⟨Unit, fun _ => True, fun d _ => d = 0,
   ⟨(), trivial, 0, rfl, fun _ h => h⟩,
   fun h => by obtain ⟨_, _, h1⟩ := h 1; exact absurd h1 (by decide)⟩

/-- **Full exh above ◇ contradicts FC (|D|=2)**: adding scalar
negation ¬(∀d, ◇(Q d)) to domain-exh yields ⊥. -/
theorem modal_full_exh_contradiction {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNotAll : ¬∀ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    False :=
  root_full_exh_contradiction (fun d => ∃ w, Acc w ∧ Q d w)
    hExist hNotAll hNegExcl

/-- **∀d ◇(Q d) negates all exclusives**: if every element is possible,
then no element is exclusively possible. -/
theorem modal_exclusive_false_of_universal {W D : Type*} {a b : D}
    (hab : a ≠ b) (Acc : W → Prop) (Q : D → W → Prop)
    (hAll : ∀ d, ∃ w, Acc w ∧ Q d w) :
    ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w) :=
  exclusive_false_of_universal hab _ hAll

/-- **Split exh compatible with ◇(∀d Q d)**: domain-exh premises, FC, and
the modal scalar ◇(∀d Q d) hold simultaneously. -/
theorem modal_split_compatible_with_joint :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ d, ∃ w, Acc w ∧ Q d w) ∧
      (∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) ∧
      (∀ d, ∃ w, Acc w ∧ Q d w) ∧
      (∃ w, Acc w ∧ ∀ d, Q d w) := by
  refine ⟨Unit, fun _ => True, fun _ _ => True,
    ⟨0, (), trivial, trivial⟩, ?_, fun _ => ⟨(), trivial, trivial⟩,
    ⟨(), trivial, fun _ => trivial⟩⟩
  intro d ⟨_, hall⟩
  obtain ⟨e, hne⟩ := exists_ne d
  exact hall e hne ⟨(), trivial, trivial⟩

/-- **Full split exh with joint compatibility**: FC + embedded uniqueness
+ ◇(∀d Q d) all hold simultaneously. -/
theorem modal_split_full_compatible_with_joint :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) ∧
      (∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) ∧
      (∀ d, ∃ w, Acc w ∧ Q d w) ∧
      (∃ w, Acc w ∧ ∀ d, Q d w) := by
  refine ⟨Fin 3, fun _ => True,
    fun d w => (d = 0 ∧ w ≠ 1) ∨ (d = 1 ∧ w ≠ 0),
    ?_, ?_, ?_, ?_⟩
  · exact ⟨0, trivial, 0, Or.inl ⟨rfl, by decide⟩,
      fun e he => by rcases he with ⟨rfl, _⟩ | ⟨rfl, h⟩ <;> [rfl; exact absurd rfl h]⟩
  · intro d ⟨_, hall⟩
    fin_cases d
    · exact hall 1 (by decide) ⟨1, trivial, Or.inr ⟨rfl, by decide⟩⟩
    · exact hall 0 (by decide) ⟨0, trivial, Or.inl ⟨rfl, by decide⟩⟩
  · intro d; fin_cases d
    · exact ⟨0, trivial, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨1, trivial, Or.inr ⟨rfl, by decide⟩⟩
  · refine ⟨2, trivial, fun d => ?_⟩
    fin_cases d
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨rfl, by decide⟩

end Generic


-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/AlonsoOvalleMoghiseh2025.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def aom2025_rootUniqueness : LinguisticExample :=
  { id := "aom2025_rootUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "root uniqueness, §2.4.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā umæd."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("umæd", "came")]
    translation := "One of the students came."
    context := "root context (no modal embedding)"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (exactly one student)", .acceptable)]
    paperFeatures := [("contextType", "root"), ("modalFlavor", ""), ("uniqueness", "true"), ("freeChoice", "false"), ("modalVariation", "false")]
    comment := "Supplementary illustration of yek-i's root uniqueness reading. Migrated from the legacy `FreeChoiceFarsi.lean` data file; the example is not a direct transcription from the paper but reflects the paper's central claim about yek-i in root contexts."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticFreeChoice : LinguisticExample :=
  { id := "aom2025_deonticFreeChoice"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, §2.3.1"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG")]
    translation := "You can pick one of these apples."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each apple is a permitted option)", .acceptable), ("embedded uniqueness (only one apple permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true"), ("modalVariation", "false")]
    comment := "Supplementary illustration. Migrated from `FreeChoiceFarsi.lean`. The paper's canonical deontic FC examples are (20a), (25), (26)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticBooks : LinguisticExample :=
  { id := "aom2025_deonticBooks"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, books variant"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in ketāb-hā-ro bekhuni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("ketāb-hā-ro", "book-PL-RA"), ("bekhuni", "read.2SG")]
    translation := "You can read one of these books."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each book is a permitted option)", .acceptable), ("embedded uniqueness (only one book permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Books variant of the deontic FC example. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicModalVariation : LinguisticExample :=
  { id := "aom2025_epistemicModalVariation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "epistemic modal variation, §2.3.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā ketāb-o dozid-e."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("ketāb-o", "book-RA"), ("dozid-e", "stole-3SG")]
    translation := "One of the students (might have) stolen the book."
    context := "epistemic possibility (covert or pragmatic) over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (at least two students are possible)", .acceptable), ("embedded uniqueness (exactly one stole it)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true"), ("freeChoice", "false")]
    comment := "Supplementary illustration of yek-i's modal variation reading under epistemic possibility. Migrated from `FreeChoiceFarsi.lean`. Paper's canonical epistemic example is (32)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicExplicit : LinguisticExample :=
  { id := "aom2025_epistemicExplicit"
    source := ⟨"alonso-ovalle-moghiseh-2025", "explicit epistemic modal"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "momken-e yek-i az dānešju-hā biyād."
    discourseSegments := []
    glossedTokens := [("momken-e", "possible-is"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG")]
    translation := "It's possible that one of the students will come."
    context := "explicit epistemic possibility modal over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (multiple students are possible)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true")]
    comment := "Supplementary example with overt epistemic possibility modal `momken`. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deNegation : LinguisticExample :=
  { id := "aom2025_deNegation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "negation context"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā-ro nadid-æm."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā-ro", "student-PL-RA"), ("nadid-æm", "NEG.see-1SG")]
    translation := "I didn't see any of the students."
    context := "downward-entailing: sentential negation, partitive structure"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (no student seen)", .acceptable)]
    paperFeatures := [("contextType", "DE (negation)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "yek-i in DE contexts contributes plain existential force. The paper (17) shows that bare yek-i cannot scope under sentential negation; this partitive variant (`yek-i az NP`) appears compatible with the polarity-item reading. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deConditional : LinguisticExample :=
  { id := "aom2025_deConditional"
    source := ⟨"alonso-ovalle-moghiseh-2025", "conditional antecedent"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "ægær yek-i az dānešju-hā biyād, xošhāl mišæm."
    discourseSegments := []
    glossedTokens := [("ægær", "if"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG"), ("xošhāl", "happy"), ("mišæm", "become.1SG")]
    translation := "If any of the students comes, I'll be happy."
    context := "downward-entailing: conditional antecedent"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (some student coming suffices)", .acceptable)]
    paperFeatures := [("contextType", "DE (conditional)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "Conditional antecedent is the canonical DE context where yek-i contributes plain existential force (paper §2.2; cf. eq. 16). Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_embeddedUniqueness : LinguisticExample :=
  { id := "aom2025_embeddedUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "embedded uniqueness contrast"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri, #væli do-tā nemituni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG"), ("væli", "but"), ("do-tā", "two-CL"), ("nemituni", "NEG.can.2SG")]
    translation := "You can pick one of these apples, #but not two."
    context := "deontic possibility, with continuation testing uniqueness"
    judgment := .marginal
    alternatives := [("mituni yek-i az in sib-ā-ro bardāri.", .acceptable)]
    readings := [("FC + embedded uniqueness (continuation redundant/contradictory)", .marginal)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Continuation `but not two` is infelicitous (marked `#`) because the embedded uniqueness component already entails that only one apple may be picked. Migrated from `FreeChoiceFarsi.lean` (the original recorded `do-tā væli næ` which appears garbled; corrected here to `do-tā nemituni` 'cannot two')."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_irgendein : LinguisticExample :=
  { id := "aom2025_contrast_irgendein"
    source := ⟨"kratzer-shimoyama-2002", "irgendein root"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(1), Table 1"⟩
    language := "stan1295"
    primaryText := "Irgendjemand hat angerufen."
    discourseSegments := []
    glossedTokens := [("Irgendjemand", "IRGEND.somebody"), ("hat", "AUX.3SG"), ("angerufen", "called.PTCP")]
    translation := "Somebody (the speaker doesn't know/care who) called."
    context := "root context (no modal); contrast with yek-i in (8)"
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic ignorance/indifference (modal insertion)", .acceptable)]
    paperFeatures := [("item", "irgendein"), ("language", "German"), ("rescueMechanism", "modalInsertion"), ("hasModalInRoot", "true"), ("efciType", "irgendein")]
    comment := "Cross-linguistic EFCI contrast: irgendein has a modal component in root contexts (covert epistemic insertion), unlike yek-i."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def aom2025_contrast_yeki : LinguisticExample :=
  { id := "aom2025_contrast_yeki"
    source := ⟨"alonso-ovalle-moghiseh-2025", "yek-i root contrast, §2.4"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Yek-i zæng zæd."
    discourseSegments := []
    glossedTokens := [("Yek-i", "one-INDF"), ("zæng", "ring"), ("zæd", "hit.3SG")]
    translation := "Exactly one person called."
    context := "root context (no modal); contrast with irgendein"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (no modal component)", .acceptable)]
    paperFeatures := [("item", "yek-i"), ("language", "Farsi"), ("rescueMechanism", "partialExhaustification"), ("hasModalInRoot", "false"), ("efciType", "yeki")]
    comment := "Cross-linguistic EFCI contrast row: yek-i in root yields uniqueness with no modal component, the paper's central novel claim."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_vreun : LinguisticExample :=
  { id := "aom2025_contrast_vreun"
    source := ⟨"falaus-2014", "p. 122 (cited at AOM 2025 ex. 4)"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(4), Table 1"⟩
    language := "roma1327"
    primaryText := "*Monica s-a întâlnit cu vreun prieten."
    discourseSegments := []
    glossedTokens := [("Monica", "Monica"), ("s-a", "REFL-have.3SG"), ("întâlnit", "met"), ("cu", "with"), ("vreun", "VREUN"), ("prieten", "friend.MASC")]
    translation := "(intended) Monica met a friend."
    context := "root context (no modal); contrast with irgendein and yek-i"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "vreun"), ("language", "Romanian"), ("rescueMechanism", "none"), ("hasModalInRoot", "false"), ("efciType", "vreun")]
    comment := "Cross-linguistic EFCI contrast: vreun has no rescue mechanism and is ungrammatical in unembedded contexts (Fălăuș 2014: 122, cited at AOM 2025 ex. 4 / Table 1)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [aom2025_rootUniqueness, aom2025_deonticFreeChoice, aom2025_deonticBooks, aom2025_epistemicModalVariation, aom2025_epistemicExplicit, aom2025_deNegation, aom2025_deConditional, aom2025_embeddedUniqueness, aom2025_contrast_irgendein, aom2025_contrast_yeki, aom2025_contrast_vreun]

end Examples
-- END GENERATED EXAMPLES


end AlonsoOvalleMoghiseh2025
