import Linglib.Core.IntensionalLogic.Lumping

/-!
# Kratzer 2012 Premise-Semantic Counterfactuals

@cite{kratzer-2012}

Truth conditions for "would"- and "might"-counterfactuals from
@cite{kratzer-2012} §5.4.4 ("The formal definitions", p. 132–133),
built on top of the lumping API in `Core.IntensionalLogic.Lumping`.

## §5.4.4 in brief

A counterfactual `p □→ q` is evaluated at a world `w` against a
*Base Set* `Fw : Set (Set F.Index)` — a privileged collection of true
propositions characterizing the facts of `w`. Kratzer lists five
admissibility conditions for `Fw` (truth, persistence, cognitive
viability, non-redundancy, completeness — pp. 132–133); we treat `Fw`
as an input parameter here and leave admissibility checks for
downstream consumers (cognitive viability is, in Kratzer's own words,
"the big unknown").

Pairing a Base Set `Fw` with a proposition `p`, the **Crucial Set**
`F_{w,p}` is the set of subsets `A ⊆ Fw ∪ {p}` satisfying:

> (i)   `A` is consistent
> (ii)  `p ∈ A`
> (iii) `A` is closed under lumping in `w`: for all `q ∈ A` and
>       `r ∈ Fw`, if `q` lumps `r` in `w`, then `r ∈ A`.

The truth conditions are then:

- **`p □→ q`** is true at `w` iff for every `A ∈ F_{w,p}` there is
  a superset `A' ∈ F_{w,p}` such that `A'` logically implies `q`
  (i.e., `Follows A' q` in the @cite{kratzer-2012} §5.3.3 sense).
- **`p ◇→ q`** is true at `w` iff there is an `A ∈ F_{w,p}` such
  that `q` is compatible with all its supersets in `F_{w,p}`.

## Architectural placement

This is the **first** formal consumer of the `Lumps` API in
`Core/IntensionalLogic/Lumping.lean` — closing the orphan-API problem
flagged in earlier reviews. The crucial-set closure condition
(condition (iii)) literally calls `Lumps q r w`, so the operator
cannot exist without the lumping API; conversely, the API earns its
keep by enabling this operator.

This is also the **fourth** counterfactual operator in linglib,
joining `universalCounterfactual` (Lewis/Stalnaker minimal-change),
`selectionalCounterfactual` (Stalnaker selection + supervaluation),
and `homogeneityCounterfactual` (von Fintel/Križ presupposition) — all
in `Theories/Semantics/Conditionals/Counterfactual.lean`. Unlike those
three, the lumping CF does NOT use `SimilarityOrdering` /
`closestWorlds`; it works directly on premise sets.

## What this file does NOT do

- **Admissibility checks for Base Sets** (§5.4.4 conditions (ii)–(v))
  are not formalized. Cognitive Viability in particular is, per
  @cite{kratzer-2012} p. 133, "the big unknown" — a question for
  empirical cognitive science, not formal semantics.
- **Testing on the @cite{ciardelli-zhang-champollion-2018} switches
  scenario**: a worlds-only switches model is too coarse for
  non-trivial lumping behaviour; the operator is genuinely tested in
  partial-situation models where lumping closure has bite (see the
  Paula apple-buying instantiation under @cite{kratzer-2012} §5.4.3,
  formalized in a sibling `Studies/` file).
- **Predicting the falsified `¬(A ∧ B) > OFF` judgment** of
  @cite{ciardelli-zhang-champollion-2018} from this operator: open
  question raised by that paper. The result that drops out of a
  worlds-only switches lift (lumping CF predicts `¬(A ∧ B) > OFF`
  false, but also predicts `aDn > OFF` false — a failure mode disjoint
  from minimal-change semantics) is documented separately.
-/

namespace Semantics.Conditionals.PremiseSemantic

open Core.IntensionalLogic
open Core.IntensionalLogic.Lumping (Lumps IsConsistent IsCompatible Follows)

variable {F : SituationFrame}

/-- **Predicate version of the Crucial Set membership condition**
    (@cite{kratzer-2012} §5.4.4, p. 133): a subset `A` of `Fw ∪ {p}`
    counts as a Crucial Set member at world `w` iff it contains the
    antecedent, is consistent, and is closed under lumping in `w`.

    Bundled as a `structure` (mirrors mathlib's `IsLUB`/`IsGreatest`
    pattern) so that consumers project out clauses by name (`hA.consistent`,
    `hA.lumping_closed`) rather than by `.2.2.1`-style chains. -/
structure IsCrucialSet (Fw : Set (Set F.Index)) (w : F.Index)
    (p : Set F.Index) (A : Set (Set F.Index)) : Prop where
  /-- (Carrier) `A` is a subset of `Fw ∪ {p}`. -/
  subset_insert : A ⊆ insert p Fw
  /-- (ii) The antecedent is in `A`. -/
  antecedent_mem : p ∈ A
  /-- (i) `A` is consistent (some world satisfies all of its members). -/
  consistent : IsConsistent A
  /-- (iii) `A` is closed under lumping in `w`: every Base-Set member
      lumped at `w` by something already in `A` must be in `A`. -/
  lumping_closed : ∀ q ∈ A, ∀ r ∈ Fw, Lumps q r w → r ∈ A

/-- **Crucial Set** (@cite{kratzer-2012} §5.4.4, p. 133): for any world
    `w`, Base Set `Fw`, and antecedent `p`, the set of subsets of
    `Fw ∪ {p}` that contain `p`, are consistent, and are closed under
    lumping at `w`. -/
def CrucialSet (Fw : Set (Set F.Index)) (w : F.Index) (p : Set F.Index) :
    Set (Set (Set F.Index)) :=
  { A | IsCrucialSet Fw w p A }

@[simp] theorem mem_crucialSet_iff {Fw : Set (Set F.Index)} {w : F.Index}
    {p : Set F.Index} {A : Set (Set F.Index)} :
    A ∈ CrucialSet Fw w p ↔ IsCrucialSet Fw w p A := Iff.rfl

/-- **"Would"-counterfactual** (@cite{kratzer-2012} §5.4.4, p. 133):
    given world `w` and admissible Base Set `Fw`, `p □→ q` is true at
    `w` iff for every `A` in the Crucial Set `F_{w,p}`, there exists a
    superset `A' ∈ F_{w,p}` such that `A'` logically implies `q`.

    The hypothesis `Fw` is the Base Set (assumed admissible by the
    caller; admissibility is not checked here, see file-level docstring).

    Note the quantifier alternation `∀ A ∈ F_{w,p}, ∃ A' ⊇ A`: this is
    *not* the maximization-of-consistency pattern that
    @cite{ciardelli-zhang-champollion-2018} §1.2 falsifies for ordering
    semantics — whether the lumping CF inherits the falsification on
    the switches scenario is open. -/
def wouldCF (Fw : Set (Set F.Index)) (w : F.Index) (p q : Set F.Index) :
    Prop :=
  ∀ A ∈ CrucialSet Fw w p, ∃ A' ∈ CrucialSet Fw w p, A ⊆ A' ∧ Follows A' q

/-- **"Might"-counterfactual** (@cite{kratzer-2012} §5.4.4, p. 133):
    `p ◇→ q` is true at `w` iff there is an `A` in `F_{w,p}` such that
    `q` is compatible with every superset of `A` in `F_{w,p}`. -/
def mightCF (Fw : Set (Set F.Index)) (w : F.Index) (p q : Set F.Index) :
    Prop :=
  ∃ A ∈ CrucialSet Fw w p,
    ∀ A' ∈ CrucialSet Fw w p, A ⊆ A' → IsCompatible q A'

/-! ## Basic API -/

/-- **Vacuous truth case**: if the Crucial Set is empty (e.g., the
    antecedent is incompatible with every lumping-closed extension of
    `Fw`), the would-counterfactual is vacuously true. -/
theorem wouldCF_of_crucialSet_empty {Fw : Set (Set F.Index)} {w : F.Index}
    {p q : Set F.Index} (h : CrucialSet Fw w p = ∅) :
    wouldCF Fw w p q := by
  intro A hA
  exact ((Set.mem_empty_iff_false A).mp (h ▸ hA)).elim

/-- **Vacuous failure case**: if the Crucial Set is empty, the
    might-counterfactual is vacuously false. -/
theorem not_mightCF_of_crucialSet_empty {Fw : Set (Set F.Index)}
    {w : F.Index} {p q : Set F.Index} (h : CrucialSet Fw w p = ∅) :
    ¬ mightCF Fw w p q := by
  rintro ⟨A, hA, _⟩
  exact (Set.mem_empty_iff_false A).mp (h ▸ hA)

/-- **Might/would duality** (@cite{kratzer-2012} p. 125):
    "'Might'-counterfactuals are interpreted as duals of the
    corresponding 'would'-counterfactuals." Whether
    `mightCF Fw w p q ↔ ¬ wouldCF Fw w p qᶜ` follows from our §5.4.4
    encoding is non-trivial: the would-CF quantifier is `∀ A ∃ A' ⊇ A`
    and the might-CF quantifier is `∃ A ∀ A' ⊇ A`, so duality requires
    that `Follows A' qᶜ ↔ ¬ IsCompatible q A'` *uniformly across A'* —
    which holds only when the Crucial Set is upward-directed. We leave
    the bridge as future work. -/
theorem mightCF_iff_not_wouldCF_compl {Fw : Set (Set F.Index)} {w : F.Index}
    {p q : Set F.Index} :
    mightCF Fw w p q ↔ ¬ wouldCF Fw w p qᶜ := by
  sorry  -- TODO: requires upward-directedness of CrucialSet; see docstring

end Semantics.Conditionals.PremiseSemantic
