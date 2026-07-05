import Linglib.Syntax.Minimalist.SyntacticObject.Derivation
import Linglib.Syntax.Minimalist.Agree.Checking
import Linglib.Core.Order.PullbackPreorder
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Derivational Economy
[chomsky-1991] [chomsky-1995] [boskovic-1997] [collins-2001]
[citko-gracanin-yuksek-2025]

Economy compares competing derivations that converge on the same PF
string and LF interpretation, selecting the one with fewest operations
and lexical resources.

## Two principles

- **Least Effort**: Pareto-minimize on lexical items / Merge ops / Agree
  ops / E-feature deletions. Drawn from [chomsky-1991],
  [chomsky-1995], [boskovic-1997]; the **global**
  transderivational variant per [citko-gracanin-yuksek-2025] fn 3.
  The local-economy alternative ([collins-2001]) is not formalized.

- **Pronunciation Economy** ([citko-gracanin-yuksek-2025] p. 27): no
  PF-affecting operation is vacuous. Checked **per operation**, not on
  whole-derivation PF before/after — see `pronunciationEconomy`'s
  docstring for why a whole-derivation `≠` check under-rejects.

## Headline (§3): well-foundedness via Dickson's lemma

`instance : WellFoundedLT DerivationCost` lifts `Pi.wellFoundedLT` on
`Fin 4 → Nat` (= Dickson 1913 applied to `Nat^n`) through the order
embedding `DerivationCost.profileEmbedding`. This is what makes "economy
selects an optimum from the reference set" mathematically *coherent*:
without WF, an infinite chain of ever-more-economical derivations could
exist and "the economy winner" would be ill-defined. WF is a
precondition for the linguistic content, not a corollary.

The load-bearing corollary `economy_admits_winner` says any non-empty
`R : Set DerivationCost` admits a Pareto-minimum. Consumers identifying
a *specific* winner of a binary reference set (the common C&G-Y pattern)
use the `economy_winner_of_pair` helper.

## Architectural realization

`DerivationCost` is a 4-Nat record. Its preorder is the pullback of
`Pi.preorder` on `Fin 4 → Nat` through `DerivationCost.profile`,
realized via `Core.Order.PullbackPreorder.ofProj`. Same shape as
`Core/Optimization/Pareto.lean`'s `paretoPullbackPreorder` (used for OT/HG
candidate comparison); the OT side wraps in `ConstraintSystem` with
candidate set + decoder, but Minimalist economy needs neither, so we
register `Preorder DerivationCost` directly. `coarsen_via_monotone` from
`Core/Order/PullbackPreorder.lean` is then available for free.

## Removed (for git history)

Pre-Phase principles (Procrastinate, Last Resort, Greed) and `overtOps`
field were removed at 0.230.574 — Bool-identity wrappers and a cost
field no producer populated. Future consumers wanting Phase-Theoretic
analogues should formalize against actual `Step`/`Phase` infrastructure.
-/

namespace Minimalist

section DerivationCost

/-- 4-dimensional cost of a syntactic derivation, measured by operation
    and resource counts. The dimensions are exactly those
    [citko-gracanin-yuksek-2025] (p. 3) compares when arguing
    multidominance is more economical than ellipsis: lexical items drawn
    from the numeration, Merge operations, Agree operations, and
    E-feature triggered PF deletions. -/
structure DerivationCost where
  lexicalItems : Nat
  mergeOps : Nat
  agreeOps : Nat
  ellipsisOps : Nat
  deriving Repr, DecidableEq

namespace DerivationCost

/-- The 4-vector projection: `profile c i` is the i-th cost dimension
    (0 = lexicalItems, 1 = mergeOps, 2 = agreeOps, 3 = ellipsisOps).
    Feature map for the `Core.Order.PullbackPreorder` instance. -/
def profile (c : DerivationCost) : Fin 4 → Nat
  | ⟨0, _⟩ => c.lexicalItems
  | ⟨1, _⟩ => c.mergeOps
  | ⟨2, _⟩ => c.agreeOps
  | ⟨3, _⟩ => c.ellipsisOps

@[simp] theorem profile_zero (c : DerivationCost) : c.profile 0 = c.lexicalItems := rfl
@[simp] theorem profile_one (c : DerivationCost) : c.profile 1 = c.mergeOps := rfl
@[simp] theorem profile_two (c : DerivationCost) : c.profile 2 = c.agreeOps := rfl
@[simp] theorem profile_three (c : DerivationCost) : c.profile 3 = c.ellipsisOps := rfl

/-- Cost-comparison preorder via `PullbackPreorder.ofProj` pullback
    through `profile`, with `Pi.preorder` (pointwise ≤) on the
    `Fin 4 → Nat` feature space.

    See module docstring § "Architectural realization" for the parallel
    with `Core/Optimization/Pareto.lean`'s `paretoPullbackPreorder`. -/
def pullbackPreorder : Core.Order.PullbackPreorder DerivationCost (Fin 4 → Nat) :=
  Core.Order.PullbackPreorder.ofProj profile (fun a a' =>
    decidable_of_iff (∀ i, a.profile i ≤ a'.profile i) Iff.rfl)

instance : Preorder DerivationCost := pullbackPreorder.toPreorder

end DerivationCost

/-- Extract cost from a core `Derivation` (step-based model).

    `lexicalItems`: each `emL`/`emR`/`wlm` step draws one lexical item
    from the numeration. (Wholesale Late Merger
    [takahashi-hulsey-2009] introduces a restrictor — also a
    numeration draw.)
    `mergeOps`: total step count.
    `agreeOps`/`ellipsisOps`: not tracked by the step-based model. -/
def SyntacticObject.Derivation.cost (d : Derivation) : DerivationCost where
  lexicalItems :=
    d.steps.filter
      (match · with | .emL _ | .emR _ => true | _ => false)
      |>.length
  mergeOps := d.steps.length
  agreeOps := 0
  ellipsisOps := 0

end DerivationCost

section EconomyComparison

/-- Componentwise Pareto: `c1` is at-least-as-economical as `c2` iff every
    cost dimension is no worse. Linguistic-named alias for the underlying
    `Preorder.le` from `DerivationCost.pullbackPreorder`.

    NB: this is **not** a flat sum. Earlier revisions used `totalOps :=
    mergeOps + agreeOps + ellipsisOps` followed by 2-tuple
    `(totalOps, lexicalItems)` comparison, which lets a derivation with
    `agreeOps=0, mergeOps=100` "beat" one with `agreeOps=10, mergeOps=50`
    purely on the sum (110 vs 60) — a comparison
    [citko-gracanin-yuksek-2025] (p. 3) explicitly does not endorse:
    they argue MD is more economical than ellipsis on the *each-dimension*
    reading (fewer lexical items AND fewer Merge AND fewer Agree). -/
def atLeastAsEconomical (c1 c2 : DerivationCost) : Prop :=
  c1.lexicalItems ≤ c2.lexicalItems ∧
  c1.mergeOps ≤ c2.mergeOps ∧
  c1.agreeOps ≤ c2.agreeOps ∧
  c1.ellipsisOps ≤ c2.ellipsisOps

instance (c1 c2 : DerivationCost) : Decidable (atLeastAsEconomical c1 c2) := by
  unfold atLeastAsEconomical; infer_instance

/-- Strict Pareto: at-least-as-economical AND strictly better on at least
    one dimension. Equivalent to `<` from the `Preorder` instance
    (cf. `strictlyMoreEconomical_iff_lt`), but not definitionally equal. -/
def strictlyMoreEconomical (c1 c2 : DerivationCost) : Prop :=
  atLeastAsEconomical c1 c2 ∧
  (c1.lexicalItems < c2.lexicalItems ∨ c1.mergeOps < c2.mergeOps ∨
   c1.agreeOps < c2.agreeOps ∨ c1.ellipsisOps < c2.ellipsisOps)

instance (c1 c2 : DerivationCost) : Decidable (strictlyMoreEconomical c1 c2) := by
  unfold strictlyMoreEconomical; infer_instance

/-- The linguistic alias agrees with `≤` from the `PullbackPreorder` pullback
    componentwise. Tagged `@[simp]` so consumers can rewrite freely between
    the linguistic and order-theoretic forms. -/
@[simp] theorem atLeastAsEconomical_iff_le (c1 c2 : DerivationCost) :
    atLeastAsEconomical c1 c2 ↔ c1 ≤ c2 := by
  refine ⟨fun ⟨h0, h1, h2, h3⟩ i => ?_, fun h => ?_⟩
  · match i with
    | ⟨0, _⟩ => exact h0
    | ⟨1, _⟩ => exact h1
    | ⟨2, _⟩ => exact h2
    | ⟨3, _⟩ => exact h3
  · exact ⟨h ⟨0, by decide⟩, h ⟨1, by decide⟩, h ⟨2, by decide⟩, h ⟨3, by decide⟩⟩

/-- Strict economy is the strict order of the `Preorder` instance:
    `at-least-as-economical AND strictly better on at least one dimension`
    iff `c1 ≤ c2 ∧ ¬ c2 ≤ c1`. -/
theorem strictlyMoreEconomical_iff_lt (c1 c2 : DerivationCost) :
    strictlyMoreEconomical c1 c2 ↔ c1 < c2 := by
  rw [lt_iff_le_not_ge, ← atLeastAsEconomical_iff_le, ← atLeastAsEconomical_iff_le]
  unfold strictlyMoreEconomical atLeastAsEconomical
  refine ⟨fun ⟨⟨hl, hm, ha, he⟩, hstrict⟩ =>
    ⟨⟨hl, hm, ha, he⟩, fun ⟨hl', hm', ha', he'⟩ => ?_⟩,
    fun ⟨⟨hl, hm, ha, he⟩, hnot⟩ => ⟨⟨hl, hm, ha, he⟩, ?_⟩⟩
  · rcases hstrict with h | h | h | h <;> omega
  · by_contra hbad
    push Not at hbad
    obtain ⟨hl', hm', ha', he'⟩ := hbad
    exact hnot ⟨by omega, by omega, by omega, by omega⟩

end EconomyComparison

section WellFoundedness

/-! ### Well-Foundedness — the headline (Dickson's lemma) -/

namespace DerivationCost

/-- `profile` is injective: a derivation cost is determined by its 4
    components. Foundational fact for the `OrderEmbedding` and
    `PartialOrder` instances below. -/
theorem profile_injective : Function.Injective profile := by
  intro c1 c2 h
  cases c1; cases c2
  congr 1
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

/-- Order embedding of `DerivationCost` into the 4-vector Pareto preorder
    on `Fin 4 → Nat`. `map_rel_iff'` is `Iff.rfl` because the
    `Preorder DerivationCost` instance is `pullbackPreorder.toPreorder =
    Preorder.lift profile` (`≤` is *definitionally* `profile a ≤
    profile b`). -/
def profileEmbedding : DerivationCost ↪o (Fin 4 → Nat) where
  toFun := profile
  inj' := profile_injective
  map_rel_iff' := Iff.rfl

end DerivationCost

/-- `DerivationCost` is a `PartialOrder`, not just a `Preorder`:
    antisymmetry from componentwise `Nat.le_antisymm` lifted by
    `profile_injective`. Mathlib's order algebra (`IsAntichain`,
    `Maximal`, `Minimal`) gets the partial-order flavor for free. -/
instance : PartialOrder DerivationCost where
  __ := (inferInstance : Preorder DerivationCost)
  le_antisymm a b hab hba := DerivationCost.profile_injective <| by
    funext i
    exact le_antisymm (hab i) (hba i)

/-- **The headline (Dickson's lemma applied to derivational economy)**:
    the Pareto-strict order on `DerivationCost` is well-founded.

    Lifted from `Pi.wellFoundedLT` on `Fin 4 → Nat` — which IS Dickson's
    lemma applied to `Nat^n` — through the order embedding
    `DerivationCost.profileEmbedding` via `OrderEmbedding.wellFounded`.

    **Structural significance**: this is what makes the [chomsky-1995]
    / [citko-gracanin-yuksek-2025] claim that "economy selects an
    optimum from the reference set" *coherent*. Without well-foundedness,
    an infinite chain `c₀ > c₁ > c₂ > …` of ever-more-economical
    derivations could exist, and "the economy winner" would be
    ill-defined. The well-foundedness theorem is a *precondition* for the
    linguistic content, not a corollary of it.

    Mathematically: Dickson 1913, foundational for the Robbiano-Buchberger
    Gröbner basis termination argument and Hilbert's basis theorem on
    monomial ideals. The classical statement "every monomial ideal in
    `k[x₁, …, xₙ]` is finitely generated" reduces to exactly this
    well-foundedness on `Nat^n` under the divisibility order, which is
    the Pareto-componentwise order on exponent vectors. -/
instance : WellFoundedLT DerivationCost :=
  ⟨DerivationCost.profileEmbedding.wellFounded
    (Function.wellFoundedLT (α := Nat)).wf⟩

/-- **Existence of economy winners**: any non-empty set `R` of derivation
    costs admits at least one Pareto-minimum — a "winner" not strictly
    dominated by any other element of `R`.

    Direct corollary of `WellFoundedLT DerivationCost` via mathlib's
    `WellFounded.has_min`, with the `<` ↔ `strictlyMoreEconomical`
    translation through `strictlyMoreEconomical_iff_lt`.

    Linguistically: the [citko-gracanin-yuksek-2025] selection
    procedure is mathematically well-defined; whatever else economy +
    Pronunciation Economy + MWF do to break ties among winners, the set
    of winners is non-empty for any non-empty reference set. -/
theorem economy_admits_winner {R : Set DerivationCost} (hR : R.Nonempty) :
    ∃ winner ∈ R, ∀ alt ∈ R, ¬ strictlyMoreEconomical alt winner := by
  obtain ⟨winner, hwR, hmin⟩ := wellFounded_lt.has_min R hR
  exact ⟨winner, hwR, fun alt haltR hsme =>
    hmin alt haltR ((strictlyMoreEconomical_iff_lt _ _).mp hsme)⟩

/-- **Consumer-friendly form**: in a 2-element reference set `{c, c'}`
    where `c` strictly beats `c'`, `c` is the economy winner. The common
    pattern in [citko-gracanin-yuksek-2025]-style cost-comparison
    arguments: pair MD-cost vs ellipsis-cost, prove MD beats ellipsis,
    conclude MD is the winner.

    Discharges via `lt_irrefl` (anti-self-domination) + asymmetry of `<`. -/
theorem economy_winner_of_pair {c c' : DerivationCost}
    (h : strictlyMoreEconomical c c') :
    ∀ alt ∈ ({c, c'} : Set DerivationCost), ¬ strictlyMoreEconomical alt c := by
  have hlt : c < c' := (strictlyMoreEconomical_iff_lt _ _).mp h
  rintro alt (rfl | rfl) halt_lt
  · exact lt_irrefl _ ((strictlyMoreEconomical_iff_lt _ _).mp halt_lt)
  · exact lt_asymm hlt ((strictlyMoreEconomical_iff_lt _ _).mp halt_lt)

end WellFoundedness

section PronunciationEconomy

/-- A single PF-affecting operation: PF state immediately before vs
    immediately after the op fires. Used to express
    [citko-gracanin-yuksek-2025]'s **per-operation** vacuity check
    (paper p. 27 ex (39); §3 PF reduction).

    Whole-derivation Pronunciation Economy is the conjunction of per-op
    economy across all PF-affecting operations in the derivation. -/
structure PFOperation where
  pfBefore : List String
  pfAfter : List String
  deriving Repr, DecidableEq

/-- A PF operation is *vacuous* iff it has no effect on the PF string —
    e.g., the deletion targets material already unpronounced because a
    prior deletion removed it (paper p. 32 ex (45c)). -/
def PFOperation.isVacuous (op : PFOperation) : Prop := op.pfBefore = op.pfAfter

instance (op : PFOperation) : Decidable op.isVacuous := by
  unfold PFOperation.isVacuous; infer_instance

/-- **Pronunciation Economy** ([citko-gracanin-yuksek-2025] p. 27,
    ex (39)): no PF-affecting operation in the derivation is vacuous.

    Crucially **per-operation**, not on whole-derivation PF before/after.
    A whole-derivation `pfBefore ≠ pfAfter` check under-rejects: any
    derivation containing one non-vacuous deletion plus N vacuous ones
    would pass, because the non-vacuous deletion alone ensures the whole
    derivation's PF changes. The paper's centerpiece argument (p. 32
    ex (45c)) needs to ban exactly that configuration: a CWH structure
    where a shared C with E-feature deletes two TPs, the second of which
    is vacuous. -/
def pronunciationEconomy (ops : List PFOperation) : Prop :=
  ∀ op ∈ ops, ¬ op.isVacuous

instance (ops : List PFOperation) : Decidable (pronunciationEconomy ops) := by
  unfold pronunciationEconomy; infer_instance

/-- Pronunciation Economy holds iff no individual operation is vacuous. -/
theorem pronunciationEconomy_iff_no_vacuous (ops : List PFOperation) :
    pronunciationEconomy ops ↔ ¬ ∃ op ∈ ops, op.isVacuous := by
  simp only [pronunciationEconomy, not_exists, not_and]

/-- A derivation with any vacuous op violates Pronunciation Economy. -/
theorem pronunciationEconomy_violated_of_vacuous {op : PFOperation}
    {ops : List PFOperation} (hmem : op ∈ ops) (hvac : op.isVacuous) :
    ¬ pronunciationEconomy ops := by
  intro h; exact h op hmem hvac

end PronunciationEconomy

end Minimalist
