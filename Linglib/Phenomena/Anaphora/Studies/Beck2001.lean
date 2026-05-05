import Linglib.Theories.Semantics.Plurality.Cumulativity
import Linglib.Theories.Semantics.Plurality.Cover
import Linglib.Theories.Semantics.Reference.Reciprocals
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Cumulativity
import Linglib.Phenomena.Anaphora.Studies.HaugDalrymple2020

/-!
# Beck (2001): Reciprocals are Definites
@cite{beck-2001}

*Natural Language Semantics* 9(1): 69–138. doi:10.1023/A:1012203407127.

The Heim-Lasnik-May (1991) analysis of reciprocals — *each other* means
"the other ones among them" — is recast as a special kind of relational
plural. Interpretational variability across the six known reciprocal
readings (Strong Reciprocity, Partitioned Strong Reciprocity, Intermediate
Reciprocity, Weak Reciprocity, One-way Weak Reciprocity, Inclusive
Alternative Ordering) is derived not from ambiguity of the reciprocal
itself but from the standard mechanisms of plural predication: the `*`
distribution operator (Link 1983), the `**` cumulation operator
(Beck-Sauerland 2000), Schwarzschild (1996) covers, QR, and the addition
of contextual information. The reciprocal expression is **uniformly**
"the other ones among them" — the variability is at the plural-predication
layer.

## What is formalized

A scope-bounded slice of the paper:

| Paper § | Topic                                  | Lean encoding              |
|---------|----------------------------------------|----------------------------|
| §2      | Four Bool-valued reciprocal readings   | Bool predicates over `(A, R)` |
| §2.6    | Entailment lattice (eq 28)             | Implication theorems       |
| §3.3    | HLM "the other ones among them" (eq 76) | `otherOnesAmongThem`       |
| §4.1    | Sternefeld 1998's `**`-based WR (eq 98) | Connection to `cumulativeOp` |
| §4.3.2  | Distinctness as presupposition         | Convergence-with-H&D-2020 note |

The two readings whose definitions involve unbounded existentials —
**Partitioned SR** (paper eq 12, ∃ partition) and **Intermediate
Reciprocity** (paper eq 17, ∃ chain) — are documented in prose but
defined as `Prop` only with no entailment theorems against the Bool
readings; the Bool ↔ Prop bridge is deferred until a downstream
consumer needs it.

Sections out of scope for a study-file size budget:
- The full §3 plural-predication machinery (`*`, `**`, covers,
  QR-based LF) — substrate-deferred to `Plurality.{Distributivity,
  Cumulativity, Cover}.lean` and consumed at the predicate level here.
- §4.2's Sternefeld critique (negation interaction, distinct subgroups
  effect) — would require formalising Sternefeld 1998 itself.
- §5 intermediate reciprocity via salient relations.
- §6 SMH application — synthesised SMH refutation already in
  `Reciprocals.lean`'s `SMH_diverges_from_relational`.

## Connection to H&D 2020

@cite{haug-dalrymple-2020} formalises reciprocity in PPCDRT (plural
partial CDRT) — a fundamentally different framework from Beck's HLM +
plural-predication apparatus. Despite the framework difference, both
papers **converge on the presuppositional treatment of distinctness**
(paper §4.3.2 ↔ H&D 2020 eq 41) — both agree against Sternefeld 1998's
asserted treatment.

The two papers diverge on the derivation method:
- **Beck**: HLM "the other ones among them" + `**` cumulation + covers
  + QR. WR derives from `**` applied to the HLM-denoted reciprocal.
- **H&D**: anaphoric relations (binding, group identity, reciprocity)
  in PPCDRT. WR is the basic reading; SR derives from Maximize Anaphora.

Beck's pluralization machinery (`*`, `**`, covers) and H&D's anaphoric
relations are not in tension — they are different abstractions of the
same empirical landscape. A formal H&D ↔ Beck convergence theorem at
the level of derived truth conditions would require encoding Beck's
LF mechanics; deferred.

## Substrate connection

Beck's `**` is the same `cumulativeOp` consumed by
`Theories/Semantics/Dynamic/PPCDRT/Cumulativity.lean`'s
`groupIdentityCond_iff_cumulativeOp_eq` bridge. Beck's reciprocity-as-
cumulation analysis (paper §4.3 / eq 120) and H&D's reciprocity-as-
sum-dref-equality analysis (H&D paper eq 41) therefore consume a
shared operator — making the cumulation bridge **bidirectional**
(linglib's interconnection-density goal).
-/

namespace Beck2001

open Semantics.Plurality.Cumulativity
open Semantics.Reference.Reciprocals
open Theories.Semantics.Dynamic.PPCDRT

-- ════════════════════════════════════════════════════════════════
-- § 1: Four Bool-Valued Reciprocal Readings (paper §2)
-- ════════════════════════════════════════════════════════════════

/-! Each reading is a Bool predicate over `(A : Finset α, R : α → α → Bool)`.
    α is constrained to `Type` (universe 0) for compatibility with
    `cumulativeOp` (which is monomorphic). -/

variable {α : Type} [DecidableEq α]

/-- **Strong Reciprocity** (paper eq 10): `∀x ∈ A. ∀y ∈ A. y ≠ x → xRy`.
    Every distinct pair is in the relation. -/
def stronglyReciprocal (A : Finset α) (R : α → α → Bool) : Bool :=
  decide (∀ x ∈ A, ∀ y ∈ A, y ≠ x → R x y = true)

/-- **Weak Reciprocity** (paper eq 20, Langendoen 1978): for each x in A,
    some y is R-related to x, and for each y in A, some x is R-related
    to y. Captures "the prisoners released each other" / "the children
    give each other a present". -/
def weaklyReciprocal (A : Finset α) (R : α → α → Bool) : Bool :=
  decide (∀ x ∈ A, ∃ y ∈ A, R x y = true ∧ x ≠ y) &&
  decide (∀ y ∈ A, ∃ x ∈ A, R x y = true ∧ x ≠ y)

/-- **One-way Weak Reciprocity** (paper eq 25): only the first direction
    is required. "The pirates are staring at each other" — pirate 6 is
    not stared at by anybody, but everyone stares at someone. -/
def onewayWeaklyReciprocal (A : Finset α) (R : α → α → Bool) : Bool :=
  decide (∀ x ∈ A, ∃ y ∈ A, R x y = true ∧ x ≠ y)

/-- **Inclusive Alternative Ordering** (paper eq 27, Kanski 1987): each
    member of A participates in the relation as either first or second
    argument. "The plates are stacked on top of each other" — each plate
    is on top of one or has one on top of itself. -/
def inclusiveAlternativeOrdering (A : Finset α) (R : α → α → Bool) : Bool :=
  decide (∀ x ∈ A, ∃ y ∈ A, x ≠ y ∧ (R x y = true ∨ R y x = true))

-- ════════════════════════════════════════════════════════════════
-- § 1.5: Two Prop-valued readings (definitions only)
-- ════════════════════════════════════════════════════════════════

/-- **Partitioned Strong Reciprocity** (paper eq 12, Fiengo & Lasnik 1973):
    there is a partition `PART` of A such that SR holds within each cell.
    "The men are hitting each other" can be true if the men team up in
    pairs that stand in the hit-relation. -/
def partitionedStronglyReciprocal (A : Finset α) (R : α → α → Bool) : Prop :=
  ∃ PART : Finset (Finset α),
    (∀ X ∈ PART, X ⊆ A) ∧
    (∀ a ∈ A, ∃ X ∈ PART, a ∈ X) ∧
    (∀ X ∈ PART, ∀ x ∈ X, ∀ y ∈ X, y ≠ x → R x y = true)

/-- **Intermediate Reciprocity** (paper eq 17): any two members of A
    are connected by a chain of elements that stand in the reciprocal
    relation. "Five Boston pitchers sat alongside each other." -/
def intermediatelyReciprocal (A : Finset α) (R : α → α → Bool) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
    ∃ chain : List α, chain.head? = some x ∧ chain.getLast? = some y ∧
      (∀ z ∈ chain, z ∈ A) ∧
      chain.Chain' (fun a b => R a b = true)

-- ════════════════════════════════════════════════════════════════
-- § 2: Entailment Lattice for the Four Bool Readings (paper eq 28)
-- ════════════════════════════════════════════════════════════════

/-! Beck's entailment lattice (paper eq 28):

    ```
      SR  →  IR  →  WR  →  OWR  →  IAO
        ↘    ↗
         PartSR
    ```

    The Bool fragment we prove here: `SR → WR → OWR → IAO`. -/

/-- A finite set of cardinality ≥ 2 contains, for any element, another
    distinct element. -/
private theorem exists_other (A : Finset α) (x : α)
    (hne : 2 ≤ A.card) : ∃ y ∈ A, y ≠ x := by
  by_contra h
  push_neg at h
  have hAsub : A ⊆ {x} := fun y hy => by
    rw [Finset.mem_singleton]; exact h y hy
  have : A.card ≤ 1 := by
    calc A.card ≤ ({x} : Finset α).card := Finset.card_le_card hAsub
      _ = 1 := Finset.card_singleton x
  omega

/-- SR implies WR (paper eq 28). -/
theorem SR_implies_WR (A : Finset α) (R : α → α → Bool) (hne : 2 ≤ A.card)
    (hSR : stronglyReciprocal A R = true) :
    weaklyReciprocal A R = true := by
  unfold stronglyReciprocal at hSR
  unfold weaklyReciprocal
  rw [decide_eq_true_iff] at hSR
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  all_goals (rw [decide_eq_true_iff]; intro x hx)
  · obtain ⟨y, hy, hxy⟩ := exists_other A x hne
    exact ⟨y, hy, hSR x hx y hy hxy, hxy.symm⟩
  · obtain ⟨y, hy, hxy⟩ := exists_other A x hne
    exact ⟨y, hy, hSR y hy x hx hxy.symm, hxy⟩

/-- WR implies OWR: bidirectional coverage entails one-direction
    coverage. -/
theorem WR_implies_OWR (A : Finset α) (R : α → α → Bool)
    (hWR : weaklyReciprocal A R = true) :
    onewayWeaklyReciprocal A R = true := by
  unfold weaklyReciprocal at hWR
  unfold onewayWeaklyReciprocal
  rw [Bool.and_eq_true] at hWR
  exact hWR.1

/-- OWR implies IAO: one-direction coverage entails the disjunctive
    `xRy ∨ yRx` form. -/
theorem OWR_implies_IAO (A : Finset α) (R : α → α → Bool)
    (hOWR : onewayWeaklyReciprocal A R = true) :
    inclusiveAlternativeOrdering A R = true := by
  unfold onewayWeaklyReciprocal at hOWR
  unfold inclusiveAlternativeOrdering
  rw [decide_eq_true_iff] at hOWR ⊢
  intro x hx
  obtain ⟨y, hy, hRxy, hxy⟩ := hOWR x hx
  exact ⟨y, hy, hxy, Or.inl hRxy⟩

/-- Composition: SR → IAO via the chain SR → WR → OWR → IAO. -/
theorem SR_implies_IAO (A : Finset α) (R : α → α → Bool) (hne : 2 ≤ A.card)
    (hSR : stronglyReciprocal A R = true) :
    inclusiveAlternativeOrdering A R = true :=
  OWR_implies_IAO A R (WR_implies_OWR A R (SR_implies_WR A R hne hSR))

-- ════════════════════════════════════════════════════════════════
-- § 3: Beck's HLM Denotation for *each other* (paper eq 76)
-- ════════════════════════════════════════════════════════════════

/-- Paper eq 76: `each other = max(*λz[¬z∘x₁ ∧ z ≤ x₃ ∧ Cov(z)])` —
    "the other ones among them" via the maximum of the (covered) parts
    of the antecedent group that are not (overlapping) the contrast
    argument.

    Skipping the full LF (the `*` operator, the cover variable Cov, the
    QR-introduced trace x₁), the denotation reduces to: given an
    antecedent group `A` and a contrast individual `x`, return the
    maximal subgroup of A that does not include x. For singularity parts
    (the simplest case, paper p. 92), this is `A \ {x}`. -/
def otherOnesAmongThem (A : Finset α) (x : α) : Finset α :=
  A.erase x

/-- The reciprocal denotation excludes the contrast argument. -/
theorem otherOnesAmongThem_excludes (A : Finset α) (x : α) :
    x ∉ otherOnesAmongThem A x := by
  unfold otherOnesAmongThem; exact Finset.notMem_erase x A

/-- The reciprocal denotation is a subgroup of the antecedent. -/
theorem otherOnesAmongThem_subset (A : Finset α) (x : α) :
    otherOnesAmongThem A x ⊆ A := by
  unfold otherOnesAmongThem; exact Finset.erase_subset x A

/-- For an antecedent group with at least 2 members, the
    `otherOnesAmongThem` denotation is non-empty for any element. -/
theorem otherOnesAmongThem_nonempty (A : Finset α) (x : α)
    (hne : 2 ≤ A.card) : (otherOnesAmongThem A x).Nonempty := by
  obtain ⟨y, hy, hyx⟩ := exists_other A x hne
  refine ⟨y, ?_⟩
  unfold otherOnesAmongThem
  exact Finset.mem_erase.mpr ⟨hyx, hy⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: WR via Cumulation (paper §4.3 / eq 120)
-- ════════════════════════════════════════════════════════════════

/-! Beck adopts Sternefeld 1998's insight that WR derives from `**`
    (cumulation) applied to the reciprocal relation. The `**` operator
    is `cumulativeOp` from `Theories/Semantics/Plurality/Cumulativity.lean`
    — the SAME operator H&D's
    `Theories/Semantics/Dynamic/PPCDRT/Cumulativity.lean`'s
    `groupIdentityCond_iff_cumulativeOp_eq` bridge consumes. Beck's WR
    derivation and H&D's reciprocal group identity therefore share
    machinery at the substrate level. -/

/-- **Beck's `**` underwrites WR's bidirectional coverage** (paper §4.3,
    forward direction). The cumulative `**(R)(A, A)` holds if WR's
    bidirectional coverage holds — modulo the distinctness clause.
    WR explicitly requires `x ≠ y` for the witnesses; `cumulativeOp`
    captures the bidirectional coverage component of WR's truth
    conditions, with distinctness handled separately at the
    presupposition layer (Beck §4.3.2; see `§5` below). -/
theorem WR_implies_cumulativeOp (A : Finset α) (R : α → α → Bool)
    (hWR : weaklyReciprocal A R = true) :
    cumulativeOp R A A = true := by
  unfold weaklyReciprocal at hWR
  unfold cumulativeOp
  rw [Bool.and_eq_true] at hWR ⊢
  obtain ⟨hLR, hRL⟩ := hWR
  rw [decide_eq_true_iff] at hLR hRL
  refine ⟨?_, ?_⟩
  · rw [decide_eq_true_iff]
    intro x hx
    obtain ⟨y, hy, hRxy, _⟩ := hLR x hx
    exact ⟨y, hy, hRxy⟩
  · rw [decide_eq_true_iff]
    intro y hy
    obtain ⟨x, hx, hRxy, _⟩ := hRL y hy
    exact ⟨x, hx, hRxy⟩

-- ════════════════════════════════════════════════════════════════
-- § 5: Cross-framework Convergence with H&D 2020
-- (paper §4.3.2 ↔ H&D 2020 eq 41)
-- ════════════════════════════════════════════════════════════════

/-! Beck §4.3.2 (paper p. 105, eq 121d) and Haug & Dalrymple 2020 eq 41
    (PPCDRT paper p. 18) **converge** on the presuppositional treatment
    of reciprocal distinctness — both reject Sternefeld 1998's asserted
    distinctness on empirical grounds (negation interaction, distinct
    subgroups effect, downward-monotone operators).

    Beck's argument (paper §4.3.2): the distinctness condition `x ≠ y`
    must project as a presupposition (paper eq 121d marks distinctness
    as `@(x ≠ y)`), NOT be part of the asserted content. Otherwise we
    mispredict a tautological reading for "they don't like each other"
    (paper eq 100). The presuppositional analysis correctly predicts
    the distinct-subgroups effect.

    H&D 2020's analysis (eq 41): `[[each other]] = λP. [u | ∂(∪u =
    ∪𝒜(u)), ∂(u ≠ 𝒜(u))]; P(u)`. The `∂` wrapper makes BOTH the group
    identity condition and the distinctness condition presuppositional.

    Both papers therefore agree that distinctness is presuppositional;
    they disagree on the framework (Beck: HLM + `**` + covers; H&D:
    PPCDRT). The `∂` substrate that would let this convergence be a
    Lean theorem (rather than a meta-comment) is currently trimmed from
    PPCDRT (see HD2020 docstring); landing it is queued as Tier-3 work. -/

/-- **Convergence note**: Beck (this paper, §4.3.2) and H&D 2020 both
    factor reciprocity into a *non-presuppositional* coverage component
    (group identity / `**` cumulativity) and a *presuppositional*
    distinctness component. This is exhibited *structurally* by the
    parallel:

    - Beck eq 121d: `**(λyλx[R(x,y) ∧ @(x ≠ y)])(A,A)` — `@` marks
      the distinctness as presupposition.
    - H&D eq 41: `[u | ∂(∪u = ∪𝒜(u)), ∂(u ≠ 𝒜(u))]` — `∂` marks
      both group-identity AND distinctness as presupposition.

    Both treat distinctness as a separable, projecting condition.
    Theorem-level realisation requires `∂` substrate (PPCDRT operator
    set was trimmed in 0.230.781; re-adding `∂` is the natural follow-on
    to Beck's full formalisation). -/
theorem distinctness_presupposition_agreement_with_HD2020 :
    -- Meta-level claim about the literature; substrate-level realisation
    -- pending. The Lean witness is at the *consumption* level: both
    -- Beck's eq 120 (`**` + distinctness) and H&D's `reciprocityCond`
    -- (groupIdentityCond + distinctness) factor reciprocity into a
    -- coverage-plus-distinctness shape.
    True := trivial

/-- **Divergence with Sternefeld 1998** (paper §4.2): Sternefeld asserts
    distinctness, leading to wrong predictions for "they don't like each
    other" (tautological reading). Beck and H&D 2020 both reject this in
    favour of the presuppositional analysis.

    This is a *meta-fact* about the literature, not a Lean theorem
    (Sternefeld 1998 is not formalised in linglib — see Tier-3 of the
    cross-framework auditor's recommendation list). -/
theorem sternefeld_distinctness_dispute :
    -- Beck and H&D agree against Sternefeld; placeholder until
    -- Sternefeld 1998 is formalised as a sibling Studies file.
    True := trivial

end Beck2001
