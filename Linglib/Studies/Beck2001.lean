import Mathlib.Data.Finset.Card
import Linglib.Semantics.Plurality.Cumulativity
import Linglib.Semantics.Plurality.Reciprocal
import Linglib.Semantics.Dynamic.PPCDRT.Cumulativity

/-!
# Beck (2001): Reciprocals are Definites
[beck-2001]

*Natural Language Semantics* 9(1): 69–138. doi:10.1023/A:1012203407127.

The [heim-lasnik-may-1991] analysis of reciprocals — *each other*
means "the other ones among them" — is recast as a special kind of
relational plural. Interpretational variability across the six known
reciprocal readings (Strong Reciprocity, Partitioned Strong Reciprocity,
Intermediate Reciprocity, Weak Reciprocity, One-way Weak Reciprocity,
Inclusive Alternative Ordering) is derived not from ambiguity of the
reciprocal itself but from the standard mechanisms of plural predication:
the `*` distribution operator ([link-1983]), the `**` cumulation
operator ([beck-sauerland-2000]), [schwarzschild-1996] covers,
QR, and the addition of contextual information. The reciprocal expression
is **uniformly** "the other ones among them" — the variability is at the
plural-predication layer.

## What is formalized

A scope-bounded slice of the paper:

| Paper § | Topic                                  | Lean encoding              |
|---------|----------------------------------------|----------------------------|
| §2      | Four reciprocal readings               | Prop predicates over `(A, R)` |
| §2.6    | Entailment lattice (eq 28)             | Implication theorems       |
| §3.3    | HLM "the other ones among them" (eq 76) | `otherOnesAmongThem`       |
| §4.3    | Bare `**(R)(A,A)` coverage forward dir | `weaklyReciprocal_implies_cumulative_R` |
| §4.3.2  | Beck eq 120 = [sternefeld-1998] eq 26b (bivalent) | `Plurality.Reciprocal.weakReciprocity_iff_cumulative_strict` |
| §4.3.2  | Distinctness as presupposition         | Bridge to H&D 2020         |

The two readings whose definitions involve unbounded existentials —
**Partitioned SR** (paper eq 12, ∃ partition) and **Intermediate
Reciprocity** (paper eq 17, ∃ chain) — are documented in prose but
defined as `Prop` only with no entailment theorems against the four
basic readings.

Sections out of scope for a study-file size budget:
- The full §3 plural-predication machinery (`*`, `**`, covers,
  QR-based LF) — substrate-deferred to `Plurality.{Distributivity,
  Cumulativity, Cover}.lean` and consumed at the predicate level here.
- §4.2's [sternefeld-1998] critique (negation interaction, distinct
  subgroups effect) — would require formalising Sternefeld 1998 itself.
- §5 intermediate reciprocity via salient relations.
- §6 SMH application — synthesised SMH refutation already in
  `Reciprocals.lean`'s `SMH_diverges_from_relational`.

## Connection to H&D 2020

[haug-dalrymple-2020] formalises reciprocity in PPCDRT (plural
partial CDRT) — a fundamentally different framework from Beck's HLM +
plural-predication apparatus. Despite the framework difference, both
papers **converge on the presuppositional treatment of distinctness**
(paper §4.3.2 ↔ H&D 2020 eq 41) — both agree against
[sternefeld-1998]'s asserted treatment.

The two papers diverge on the derivation method:
- **Beck**: HLM "the other ones among them" + `**` cumulation + covers
  + QR. WR derives from `**` applied to the HLM-denoted reciprocal.
- **H&D**: anaphoric relations (binding, group identity, reciprocity)
  in PPCDRT. WR is the basic reading; SR derives from Maximize Anaphora.

The §6 cross-paper bridge `beck_cumulativity_on_equality_iff_HD_groupIdentity`
makes the convergence visible at the type level: H&D's group identity is
Beck-Sauerland `**` applied to *equality* on the sum-dref value-sets, while
Beck applies `**` to the verb relation. Both consume the same machinery —
[langendoen-1978]'s reciprocity-as-cumulativity is the shared insight.

Note on imports: this file does **not** import
`HaugDalrymple2020.lean` directly — per the convention used by
`DalrympleHaug2024.lean` and `Rakosi2019.lean`, cross-paper references
are made via `[key]` in docstrings while substrate-level theorems
chain through `PPCDRT/Cumulativity.lean` (which both papers consume).
-/

namespace Beck2001

open Semantics.Plurality.Cumulativity
open Semantics.Plurality.Reciprocal
open PPCDRT

-- ════════════════════════════════════════════════════════════════
-- § 1: Four Basic Reciprocal Readings (paper §2)
-- ════════════════════════════════════════════════════════════════

variable {α : Type*} [DecidableEq α]

/-! ### § 1-2: Reciprocal schemes + entailment lattice

The six DKMPK / Langendoen 1978 reciprocal schemes and Beck's
entailment lattice (paper eq 28) now live in
`Plurality/Reciprocal.lean`. See `StrongReciprocity`, `WeakReciprocity`,
`OneWayWeakReciprocity`, `InclusiveAlternativeOrdering`,
`PartitionedStrongReciprocity`, `IntermediateReciprocity` for the
predicates, and `strong_imp_weak`, `weak_imp_oneWay`,
`oneWay_imp_inclusiveAlternative`, `strong_imp_inclusiveAlternative`
for the right-hand-spine entailments. -/

/-! ### § 3: Beck's HLM Denotation for *each other* (paper eq 76) -/

/-- Paper eq 76: `each other = max(*λz[¬z∘x₁ ∧ z ≤ x₃ ∧ Cov(z)])` —
    "the other ones among them" via the maximum of the (covered) parts
    of the antecedent group that are not (overlapping) the contrast
    argument.

    Skipping the full LF (the `*` operator, the cover variable Cov, the
    QR-introduced trace x₁), the denotation reduces to: given an
    antecedent group `A` and a contrast individual `x`, return the
    maximal subgroup of A that does not include x. For singularity parts
    (the simplest case, paper p. 92), this is `A \ {x}`.

    *Layered-grounding gap*: the full eq 76 invokes Sharvy max
    (`Semantics/Definiteness/Maximality.lean` provides the substrate) and Link `*`
    (`Plurality/Algebra.lean`); current `A.erase x` is the simplest
    case. Promoting `otherOnesAmongThem` to consume `Nominal/Maximality`
    is queued (Tier-4 of the cross-framework auditor's recommendation
    list). -/
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
    (hne : 1 < A.card) : (otherOnesAmongThem A x).Nonempty := by
  obtain ⟨y, hy, hyx⟩ := A.exists_mem_ne hne x
  refine ⟨y, ?_⟩
  unfold otherOnesAmongThem
  exact Finset.mem_erase.mpr ⟨hyx, hy⟩

/-! ### § 4: WR via Cumulation — [sternefeld-1998] eq 26b vs Beck eq 120

The substrate-level bridge `WeakReciprocity R A ↔
Cumulative (fun a b => R a b ∧ a ≠ b) A A` and the forward weakening
`WeakReciprocity → Cumulative` both live in `Plurality/Reciprocal.lean`
(`weakReciprocity_iff_cumulative_strict`, `weakReciprocity_imp_cumulative`).
They formalise the bivalent collapse of [sternefeld-1998] eq 26b
and [beck-2001] eq 120 (both papers keep the distinctness clause
`x ≠ y` inside the `**`'s relation argument; they differ only at the
trivalent layer, where Sternefeld asserts distinctness and Beck
presupposes it). The cross-paper trivalent divergence is *only*
visible in trivalent semantics: Sternefeld returns false when R holds
with x = y; Beck returns "undefined" (presupposition failure). See
`Studies/Sternefeld1998.lean` for the cross-paper bridges. -/

-- ════════════════════════════════════════════════════════════════
-- § 5: Cross-framework Bridge to H&D 2020
-- (paper §4.3.2 ↔ [haug-dalrymple-2020] eq 41)
-- ════════════════════════════════════════════════════════════════

/-! Beck §4.3.2 (paper p. 105, eq 121d) and [haug-dalrymple-2020]
    eq 41 (PPCDRT paper p. 18) **converge** on the *presuppositional*
    treatment of reciprocal distinctness. [sternefeld-1998]
    eq 26b also has distinctness inside the `**`'s relation argument
    but treats it as asserted, not presupposed — the Beck/H&D
    refinement is the assertion → presupposition status change.

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
    PPCDRT). Below we make the substrate-level convergence visible at
    the type level. -/

/-- **Beck-shaped cumulativity coverage on equality reduces to H&D 2020
    group identity.** Both Beck (paper §4.3, eq 120) and
    [haug-dalrymple-2020] (eq 41) invoke `**` (`Cumulative`); they
    differ in the relation argument. Beck applies `**` to the verb
    relation `R` (yielding WR coverage); H&D's group identity is what
    you get when you apply `**` to *equality* on the sum-dref value-sets.
    The two analyses therefore consume the same machinery; this theorem
    makes the convergence visible at the type level.

    [langendoen-1978]'s reciprocity-as-cumulativity is the shared
    insight; this is its first true cross-paper realization in linglib. -/
theorem beck_cumulativity_on_equality_iff_HD_groupIdentity
    {E : Type} [DecidableEq E]
    (uAnaph uAnt : Nat) (S : Core.PluralAssign E)
    (xa xb : Finset E)
    (hxa : ∀ d, d ∈ xa ↔ d ∈ Core.PluralAssign.sumDref S uAnaph)
    (hxb : ∀ d, d ∈ xb ↔ d ∈ Core.PluralAssign.sumDref S uAnt) :
    Cumulative (fun a b : E => a = b) xa xb ↔
    groupIdentityCond uAnaph uAnt S ∅ :=
  (groupIdentityCond_iff_cumulative_eq uAnaph uAnt S xa xb hxa hxb).symm

/-- **(Coverage, distinctness) factorization theorem** — replaces the
    previous-session `True := trivial` placeholder with a real typed
    statement of the cross-paper convergence.

    Both Beck eq 120 and [haug-dalrymple-2020] `reciprocityCond`
    factor reciprocity into a *coverage* component plus a *distinctness*
    component. The coverage components are bridged by
    `groupIdentityCond_iff_cumulative_eq` (chained as
    `beck_cumulativity_on_equality_iff_HD_groupIdentity` above) — Beck's
    `**`-on-equality is H&D's group identity. The distinctness components
    are pointwise per-state distinctness on either side.

    Concretely: a Beck-shaped pair `(coverage on equality, distinctness)`
    over the value-sets matches an H&D `reciprocityCond` over the same
    plural state. -/
theorem reciprocity_factors_as_coverage_and_distinctness
    {E : Type} [DecidableEq E]
    (uAnaph uAnt : Nat) (S : Core.PluralAssign E)
    (xa xb : Finset E)
    (hxa : ∀ d, d ∈ xa ↔ d ∈ Core.PluralAssign.sumDref S uAnaph)
    (hxb : ∀ d, d ∈ xb ↔ d ∈ Core.PluralAssign.sumDref S uAnt) :
    -- Beck-shape: cumulativity-on-equality + per-state distinctness
    (Cumulative (fun a b : E => a = b) xa xb ∧
     ∀ s ∈ S, ∀ d_a d_b, s uAnaph = some d_a → s uAnt = some d_b → d_a ≠ d_b)
    ↔
    -- H&D-shape: reciprocityCond
    reciprocityCond uAnaph uAnt S ∅ := by
  unfold reciprocityCond
  rw [beck_cumulativity_on_equality_iff_HD_groupIdentity uAnaph uAnt S xa xb hxa hxb]

/-! **Divergence with [sternefeld-1998]** is *only* visible in
    trivalent semantics. In bivalent encoding, Sternefeld eq 26b and
    Beck eq 120 produce the same predicate — formally witnessed by
    `Sternefeld1998.sternefeldWR_iff_WeakReciprocity` (chained
    through `Plurality.Reciprocal.weakReciprocity_iff_cumulative_strict`).
    The presupposition-vs-assertion divergence on truth-value
    gaps when `R` holds with `x = y` requires `∂` substrate (PPCDRT
    operator set was trimmed in 0.230.781; queued).

    Originally this section housed a `True := trivial` placeholder
    citing eq 98 of Sternefeld; that attribution was wrong (Sternefeld
    1998 has only ~70 numbered equations, the highest-numbered being
    eq 70 on p. 335). The actual Sternefeld WR analysis (eq 26b)
    coincides with Beck's eq 120 in bivalent encoding; the structural
    equivalence is now witnessed by the Sternefeld1998.lean bridge. -/

end Beck2001
