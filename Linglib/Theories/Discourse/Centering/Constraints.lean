import Linglib.Theories.Discourse.Centering.Basic

/-!
# Centering Theory — Constraint 1 and Its Decomposition
@cite{poesio-stevenson-eugenio-hitzeman-2004} @cite{grosz-joshi-weinstein-1995}

@cite{grosz-joshi-weinstein-1995} stated Constraint 1 (sometimes called
the "uniqueness" or "entity coherence" constraint) as a single claim:
**every utterance after the first has exactly one CB**.
@cite{poesio-stevenson-eugenio-hitzeman-2004} §5.3.2 (p. 356-357)
propose unpacking this into two separate, independently testable
claims:

> *We feel this work has greatly helped our understanding of the
> theory and believe that it would be similarly useful to unpack
> Constraint 1 into two separate claims, as well: one about
> uniqueness of the CB, and one about entity coherence.*

Specifically:

* **CB Uniqueness**: utterances have **at most one** CB.
* **(Entity) Continuity**: `CF(U_{i-1}) ∩ CF(U_i) ≠ ∅`.

In their own notation:
- Strong C1 = CB Uniqueness ∧ Continuity (= "exactly one CB")
- Weak C1 = CB Uniqueness alone (= "at most one CB")

This file formalizes both predicates as length-properties of `cbAll`
(`Basic.lean` §4) and proves the decomposition theorem. The `length`
formulation makes the decomposition trivial — it falls out by `omega`
once the predicates are stated in their canonical list-arithmetic form.

**Why list arithmetic and not separate `Prop`s.** The mathlib idiom
encodes "at most one X" via the type system (`Option`, `List.length ≤ 1`,
`Subsingleton`) rather than a parallel `Unique` predicate. Per the
audit, `cb : prev → cur → Option E` already encodes uniqueness by type
(at most one), and `cbAll : prev → cur → List E` exposes the multi-CB
case PSDH study; the constraint-1 decomposition is then list arithmetic.

**Total-ranking hypothesis**. CB Uniqueness fails under partial
rankings (PSDH §5.3.4 (10)): two realizations tied at the highest rank
both qualify as CBs, so `(cbAll prev cur).length = 2`. Under a total
ranking, ties cannot occur, so CB Uniqueness holds by construction.
The unconditional decomposition theorem holds at the *length* level
(`length = 1 ↔ length ≤ 1 ∧ length ≥ 1`), independent of the ranking;
the empirical content of PSDH's analysis is **which `CenteringConfig`
instantiations make CB Uniqueness empirically high** — that lives in
the PoesioEtAl2004 study file, not in this substrate file.
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. CB Uniqueness, Entity Continuity, Strong C1
-- ════════════════════════════════════════════════════

/-- **CB Uniqueness** (@cite{poesio-stevenson-eugenio-hitzeman-2004}
    §5.3.2 p. 357): the utterance pair `(prev, cur)` admits *at most
    one* candidate CB. Phrased as `(cbAll prev cur).length ≤ 1`.

    Holds by construction under a total Cf-ranker. Fails under partial
    rankings when two realizations tie at the highest rank and both
    are realized in `cur` (PSDH §5.3.4 example (10)). -/
def CBUniqueness [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length ≤ 1

/-- **Entity Continuity** (@cite{poesio-stevenson-eugenio-hitzeman-2004}
    §5.3.2 p. 357): the utterance pair `(prev, cur)` shares at least
    one CF entity — there exists a candidate CB. Phrased as
    `(cbAll prev cur).length ≥ 1`.

    PSDH equivalently formulate this as `CF(U_{i-1}) ∩ CF(U_i) ≠ ∅`;
    the `cbAll` formulation is the one consistent with `cb`'s
    "highest-ranked realized" semantics. -/
def EntityContinuity [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length ≥ 1

/-- **Strong Constraint 1** (@cite{grosz-joshi-weinstein-1995} §3,
    @cite{poesio-stevenson-eugenio-hitzeman-2004} §5.3.2): the pair
    has *exactly one* CB. Equivalently: CB Uniqueness ∧ Entity
    Continuity (the decomposition PSDH advocate). -/
def Constraint1Strong [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length = 1

/-- **Weak Constraint 1**: only CB Uniqueness; @cite{poesio-stevenson-eugenio-hitzeman-2004}
    §5.3.2 cite Walker, Joshi & Prince 1998 footnote 2 page 3 as the
    source for separating this from Strong C1. -/
def Constraint1Weak [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  CBUniqueness prev cur

-- ════════════════════════════════════════════════════
-- § 2. Decidability
-- ════════════════════════════════════════════════════

instance CBUniqueness.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (CBUniqueness prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length ≤ 1))

instance EntityContinuity.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (EntityContinuity prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length ≥ 1))

instance Constraint1Strong.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (Constraint1Strong prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length = 1))

-- ════════════════════════════════════════════════════
-- § 3. PSDH §5.3.2 decomposition theorem
-- ════════════════════════════════════════════════════

/-- **PSDH §5.3.2 decomposition** (p. 356-357): Strong Constraint 1 is
    equivalent to the conjunction of CB Uniqueness and Entity
    Continuity. The proof falls out by `omega` from the canonical
    `length = 1 ↔ length ≤ 1 ∧ length ≥ 1` arithmetic on `Nat`.

    PSDH propose this decomposition as a theoretical clarification:
    earlier work treated Constraint 1 as a single empirical claim,
    while in their corpus evaluation the two clauses behave
    differently — Weak C1 (CB Uniqueness alone) is verified by 82.7%
    of utterances under the vanilla instantiation, while Strong C1
    holds for only 34.4% (PSDH Table 2, p. 328). -/
theorem strongC1_iff_uniqueness_and_continuity
    [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) :
    Constraint1Strong prev cur ↔ CBUniqueness prev cur ∧ EntityContinuity prev cur := by
  unfold Constraint1Strong CBUniqueness EntityContinuity
  omega

/-- Weak Constraint 1 is exactly CB Uniqueness — by definition. -/
theorem weakC1_eq_uniqueness [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Constraint1Weak prev cur ↔ CBUniqueness prev cur := Iff.rfl

/-- Strong implies Weak: a unique CB implies at most one CB. -/
theorem strong_implies_weak [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] {prev : Utterance E R} {cur : U}
    (h : Constraint1Strong prev cur) : Constraint1Weak prev cur := by
  unfold Constraint1Strong at h
  unfold Constraint1Weak CBUniqueness
  omega

end Discourse.Centering
