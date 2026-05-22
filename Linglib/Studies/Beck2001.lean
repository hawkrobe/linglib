import Mathlib.Data.Finset.Card
import Linglib.Theories.Semantics.Plurality.Cumulativity
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Cumulativity

/-!
# Beck (2001): Reciprocals are Definites
@cite{beck-2001}

*Natural Language Semantics* 9(1): 69–138. doi:10.1023/A:1012203407127.

The @cite{heim-lasnik-may-1991} analysis of reciprocals — *each other*
means "the other ones among them" — is recast as a special kind of
relational plural. Interpretational variability across the six known
reciprocal readings (Strong Reciprocity, Partitioned Strong Reciprocity,
Intermediate Reciprocity, Weak Reciprocity, One-way Weak Reciprocity,
Inclusive Alternative Ordering) is derived not from ambiguity of the
reciprocal itself but from the standard mechanisms of plural predication:
the `*` distribution operator (@cite{link-1983}), the `**` cumulation
operator (@cite{beck-sauerland-2000}), @cite{schwarzschild-1996} covers,
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
| §4.3.2  | Beck eq 120 = @cite{sternefeld-1998} eq 26b (bivalent) | `weaklyReciprocal_iff_cumulative_with_distinctness` |
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
- §4.2's @cite{sternefeld-1998} critique (negation interaction, distinct
  subgroups effect) — would require formalising Sternefeld 1998 itself.
- §5 intermediate reciprocity via salient relations.
- §6 SMH application — synthesised SMH refutation already in
  `Reciprocals.lean`'s `SMH_diverges_from_relational`.

## Connection to H&D 2020

@cite{haug-dalrymple-2020} formalises reciprocity in PPCDRT (plural
partial CDRT) — a fundamentally different framework from Beck's HLM +
plural-predication apparatus. Despite the framework difference, both
papers **converge on the presuppositional treatment of distinctness**
(paper §4.3.2 ↔ H&D 2020 eq 41) — both agree against
@cite{sternefeld-1998}'s asserted treatment.

The two papers diverge on the derivation method:
- **Beck**: HLM "the other ones among them" + `**` cumulation + covers
  + QR. WR derives from `**` applied to the HLM-denoted reciprocal.
- **H&D**: anaphoric relations (binding, group identity, reciprocity)
  in PPCDRT. WR is the basic reading; SR derives from Maximize Anaphora.

The §6 cross-paper bridge `beck_cumulativity_on_equality_iff_HD_groupIdentity`
makes the convergence visible at the type level: H&D's group identity is
Beck-Sauerland `**` applied to *equality* on the sum-dref value-sets, while
Beck applies `**` to the verb relation. Both consume the same machinery —
@cite{langendoen-1978}'s reciprocity-as-cumulativity is the shared insight.

Note on imports: this file does **not** import
`HaugDalrymple2020.lean` directly — per the convention used by
`DalrympleHaug2024.lean` and `Rakosi2019.lean`, cross-paper references
are made via `@cite{}` in docstrings while substrate-level theorems
chain through `PPCDRT/Cumulativity.lean` (which both papers consume).
-/

namespace Beck2001

open Semantics.Plurality.Cumulativity
open Theories.Semantics.Dynamic.PPCDRT

-- ════════════════════════════════════════════════════════════════
-- § 1: Four Basic Reciprocal Readings (paper §2)
-- ════════════════════════════════════════════════════════════════

variable {α : Type*} [DecidableEq α]

/-- **Strong Reciprocity** (paper eq 10): `∀x ∈ A. ∀y ∈ A. y ≠ x → xRy`.
    Every distinct pair is in the relation. -/
def stronglyReciprocal (A : Finset α) (R : α → α → Prop) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, y ≠ x → R x y

instance stronglyReciprocal.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (stronglyReciprocal A R) := by
  unfold stronglyReciprocal; infer_instance

/-- **Weak Reciprocity** (paper eq 20, @cite{langendoen-1978}): for each
    x in A, some y is R-related to x, and for each y in A, some x is
    R-related to y. Captures "the prisoners released each other" / "the
    children give each other a present". -/
def weaklyReciprocal (A : Finset α) (R : α → α → Prop) : Prop :=
  (∀ x ∈ A, ∃ y ∈ A, R x y ∧ x ≠ y) ∧ (∀ y ∈ A, ∃ x ∈ A, R x y ∧ x ≠ y)

instance weaklyReciprocal.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (weaklyReciprocal A R) := by
  unfold weaklyReciprocal; infer_instance

/-- **One-way Weak Reciprocity** (paper eq 25): only the first direction
    is required. "The pirates are staring at each other" — pirate 6 is
    not stared at by anybody, but everyone stares at someone. -/
def onewayWeaklyReciprocal (A : Finset α) (R : α → α → Prop) : Prop :=
  ∀ x ∈ A, ∃ y ∈ A, R x y ∧ x ≠ y

instance onewayWeaklyReciprocal.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (onewayWeaklyReciprocal A R) := by
  unfold onewayWeaklyReciprocal; infer_instance

/-- **Inclusive Alternative Ordering** (paper eq 27, Kanski 1987 — no
    bib entry yet): each member of A participates in the relation as
    either first or second argument. "The plates are stacked on top of
    each other" — each plate is on top of one or has one on top of
    itself. -/
def inclusiveAlternativeOrdering (A : Finset α) (R : α → α → Prop) : Prop :=
  ∀ x ∈ A, ∃ y ∈ A, x ≠ y ∧ (R x y ∨ R y x)

instance inclusiveAlternativeOrdering.instDecidable
    (A : Finset α) (R : α → α → Prop) [∀ a b, Decidable (R a b)] :
    Decidable (inclusiveAlternativeOrdering A R) := by
  unfold inclusiveAlternativeOrdering; infer_instance

-- ════════════════════════════════════════════════════════════════
-- § 1.5: Two readings with unbounded quantification
-- ════════════════════════════════════════════════════════════════

/-- **Partitioned Strong Reciprocity** (paper eq 12, Fiengo & Lasnik 1973
    — no bib entry yet): there is a partition `PART` of A such that SR
    holds within each cell. "The men are hitting each other" can be true
    if the men team up in pairs that stand in the hit-relation. -/
def partitionedStronglyReciprocal (A : Finset α) (R : α → α → Prop) : Prop :=
  ∃ PART : Finset (Finset α),
    (∀ X ∈ PART, X ⊆ A) ∧
    (∀ a ∈ A, ∃ X ∈ PART, a ∈ X) ∧
    (∀ X ∈ PART, ∀ x ∈ X, ∀ y ∈ X, y ≠ x → R x y)

/-- **Intermediate Reciprocity** (paper eq 17): any two members of A
    are connected by a chain of elements that stand in the reciprocal
    relation. "Five Boston pitchers sat alongside each other." -/
def intermediatelyReciprocal (A : Finset α) (R : α → α → Prop) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
    ∃ chain : List α, chain.head? = some x ∧ chain.getLast? = some y ∧
      (∀ z ∈ chain, z ∈ A) ∧
      chain.IsChain R

-- ════════════════════════════════════════════════════════════════
-- § 2: Entailment Lattice for the Basic Readings (paper eq 28)
-- ════════════════════════════════════════════════════════════════

/-! Beck's entailment lattice (paper eq 28) is a Hasse diagram with
    parallel weakening from SR:

    ```
            SR
           /  \
          IR  PartSR
           \  /
            WR
            |
           OWR
            |
           IAO
    ```

    SR weakens *in parallel* into IR and PartSR; both reconverge at WR.
    Below WR the lattice is a chain (WR → OWR → IAO).

    The fragment we prove here covers the **right-hand spine** of the
    diagram: SR → WR (the SR-to-WR shortcut, which equally bypasses
    the IR and PartSR intermediates) plus WR → OWR → IAO. -/

/-- SR implies WR (paper eq 28, right-hand spine). -/
theorem SR_implies_WR (A : Finset α) (R : α → α → Prop) (hne : 1 < A.card)
    (hSR : stronglyReciprocal A R) :
    weaklyReciprocal A R := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := A.exists_mem_ne hne x
    exact ⟨y, hy, hSR x hx y hy hxy, hxy.symm⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := A.exists_mem_ne hne x
    exact ⟨y, hy, hSR y hy x hx hxy.symm, hxy⟩

/-- WR implies OWR: bidirectional coverage entails one-direction
    coverage. -/
theorem WR_implies_OWR (A : Finset α) (R : α → α → Prop)
    (hWR : weaklyReciprocal A R) :
    onewayWeaklyReciprocal A R :=
  hWR.1

/-- OWR implies IAO: one-direction coverage entails the disjunctive
    `xRy ∨ yRx` form. -/
theorem OWR_implies_IAO (A : Finset α) (R : α → α → Prop)
    (hOWR : onewayWeaklyReciprocal A R) :
    inclusiveAlternativeOrdering A R := by
  intro x hx
  obtain ⟨y, hy, hRxy, hxy⟩ := hOWR x hx
  exact ⟨y, hy, hxy, Or.inl hRxy⟩

/-- Composition: SR → IAO via the right-hand spine SR → WR → OWR → IAO. -/
theorem SR_implies_IAO (A : Finset α) (R : α → α → Prop) (hne : 1 < A.card)
    (hSR : stronglyReciprocal A R) :
    inclusiveAlternativeOrdering A R :=
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
    (the simplest case, paper p. 92), this is `A \ {x}`.

    *Layered-grounding gap*: the full eq 76 invokes Sharvy max
    (`Core/Nominal/Maximality.lean` provides the substrate) and Link `*`
    (`Plurality/Link1983.lean`); current `A.erase x` is the simplest
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

-- ════════════════════════════════════════════════════════════════
-- § 4: WR via Cumulation — @cite{sternefeld-1998} eq 26b vs Beck eq 120
-- ════════════════════════════════════════════════════════════════

/-! Beck (paper §4.3) extends @cite{sternefeld-1998}'s reciprocity-as-
    cumulativity analysis with one refinement: distinctness is marked
    as **presupposition** rather than assertion. Reading
    @cite{sternefeld-1998} directly (eq 26b, p. 316), the distinctness
    clause `x ≠ y` is INSIDE the `**`'s relation argument in BOTH
    analyses — `⟨A,A⟩ ∈ **λxy[R(x,y) ∧ x ≠ y]` for Sternefeld vs
    `**(λxλy.[R(x,y) ∧ @(x ≠ y)])(A,A)` for Beck eq 120. The two
    differ only in the trivalent assertion-vs-presupposition status of
    `x ≠ y` (visible only when R holds with x = y).

    In bivalent encoding both collapse to `weaklyReciprocal` — see
    `weaklyReciprocal_iff_cumulative_with_distinctness` below. The
    bare-`**(R)(A,A)` shape (without inner distinctness) is what
    NEITHER paper proposes; the forward direction
    `weaklyReciprocal → Cumulative R` is just a structural weakening,
    not a faithful analysis of either. -/

/-- **Forward weakening**: WR truth conditions entail bare
    Beck-Sauerland `**(R)(A,A)` coverage of the verb relation
    (without inner distinctness). This is *strictly weaker* than
    either @cite{sternefeld-1998} eq 26b or @cite{beck-2001} eq 120
    — both of those put the distinctness clause `x ≠ y` INSIDE the
    relation argument (see `weaklyReciprocal_iff_cumulative_with_distinctness`).
    Forward direction holds because WR's `R(x,y) ∧ x ≠ y` witnesses
    are *a fortiori* `R(x,y)` witnesses. -/
theorem weaklyReciprocal_implies_cumulative_R
    (A : Finset α) (R : α → α → Prop)
    (hWR : weaklyReciprocal A R) :
    Cumulative R A A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hRxy, _⟩ := hWR.1 x hx
    exact ⟨y, hy, hRxy⟩
  · intro y hy
    obtain ⟨x, hx, hRxy, _⟩ := hWR.2 y hy
    exact ⟨x, hx, hRxy⟩

/-- **@cite{sternefeld-1998} eq 26b ↔ @cite{beck-2001} eq 120 (bivalent
    collapse)**: WR truth conditions are exactly `**(λxλy.[R(x,y) ∧
    x ≠ y])(A,A)` — Beck-Sauerland cumulation applied to the relation
    `R` *strengthened by per-witness distinctness*. The `@`
    presupposition marker of Beck eq 120 collapses to assertion in
    bivalent encoding, yielding the same predicate as Sternefeld
    eq 26b's asserted `R(x,y) ∧ x ≠ y`.

    The Sternefeld 1998 ↔ Beck 2001 divergence is therefore *only*
    visible in trivalent semantics: Sternefeld returns false when R
    holds with x = y; Beck returns "undefined" (presupposition
    failure). See `Studies/Sternefeld1998.lean` for the cross-paper
    bridge `sternefeldWR_iff_weaklyReciprocal`. -/
theorem weaklyReciprocal_iff_cumulative_with_distinctness
    (A : Finset α) (R : α → α → Prop) :
    weaklyReciprocal A R ↔
    Cumulative (fun x y => R x y ∧ x ≠ y) A A := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § 5: Cross-framework Bridge to H&D 2020
-- (paper §4.3.2 ↔ @cite{haug-dalrymple-2020} eq 41)
-- ════════════════════════════════════════════════════════════════

/-! Beck §4.3.2 (paper p. 105, eq 121d) and @cite{haug-dalrymple-2020}
    eq 41 (PPCDRT paper p. 18) **converge** on the *presuppositional*
    treatment of reciprocal distinctness. @cite{sternefeld-1998}
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
    @cite{haug-dalrymple-2020} (eq 41) invoke `**` (`Cumulative`); they
    differ in the relation argument. Beck applies `**` to the verb
    relation `R` (yielding WR coverage); H&D's group identity is what
    you get when you apply `**` to *equality* on the sum-dref value-sets.
    The two analyses therefore consume the same machinery; this theorem
    makes the convergence visible at the type level.

    @cite{langendoen-1978}'s reciprocity-as-cumulativity is the shared
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

    Both Beck eq 120 and @cite{haug-dalrymple-2020} `reciprocityCond`
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

/-! **Divergence with @cite{sternefeld-1998}** is *only* visible in
    trivalent semantics. In bivalent encoding, Sternefeld eq 26b and
    Beck eq 120 produce the same predicate — formally witnessed by
    `Sternefeld1998.sternefeldWR_iff_weaklyReciprocal` (chained
    through `weaklyReciprocal_iff_cumulative_with_distinctness`
    above). The presupposition-vs-assertion divergence on truth-value
    gaps when `R` holds with `x = y` requires `∂` substrate (PPCDRT
    operator set was trimmed in 0.230.781; queued).

    Originally this section housed a `True := trivial` placeholder
    citing eq 98 of Sternefeld; that attribution was wrong (Sternefeld
    1998 has only ~70 numbered equations, the highest-numbered being
    eq 70 on p. 335). The actual Sternefeld WR analysis (eq 26b)
    coincides with Beck's eq 120 in bivalent encoding; the structural
    equivalence is now witnessed by the Sternefeld1998.lean bridge. -/

end Beck2001
