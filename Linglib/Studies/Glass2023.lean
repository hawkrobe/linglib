import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Studies.NadathurLauer2020

/-!
# Glass 2023: Anna Karenina Principle and *cause*
[glass-2023b]

Using the Anna Karenina Principle to explain why *cause* favors
negative-sentiment complements. Semantics and Pragmatics 16, Article 6.

## Core contributions

1. Cross-cuts necessity/sufficiency into **local** (∃ background) vs
   **global** (∀ backgrounds) variants.

2. Shows that **global sufficiency licenses inference under uncertainty**
   while global necessity does not — the key asymmetry (Table 2).

3. Proposes that *cause* **entails** local sufficiency and only
   **implicates** local necessity — reversing [nadathur-lauer-2020]'s
   assignment where *cause* entails necessity.

4. Links the asymmetry to sentiment via the **Anna Karenina Principle**
   (Diamond 1997): desirable outcomes get conjunctive models
   (multiple necessary factors), undesirable outcomes get disjunctive
   models (single sufficient factors), so *C causes E* is true in
   more contexts when *E* is bad.

## V2 substrate

This file uses V2 `BoolSEM` directly. The legacy `CausalDynamics`-based
formalization (576 LOC including conjunctive/disjunctive helper lemmas
and the Anna Karenina sentiment theorems) was deleted in Phase D-H; the
core local/global concepts are re-stated here over `BoolSEM`. The
sentiment-asymmetry theorems are recoverable from this scaffolding when
needed.
-/

namespace Glass2023

open Semantics.Causation Semantics.Causation.Mechanism Semantics.Causation.SEM

/-! ## Local vs Global Sufficiency / Necessity (defs 8–11)

Glass's quartet of distinctions over `BoolSEM`:

- `GloballySufficient`: setting cause = true develops effect = true
  in every background where cause and effect are undetermined.
- `LocallySufficient`: there exists some such background.
- `GloballyNecessary`: in every background where cause and effect
  are undetermined, effect does NOT develop.
- `LocallyNecessary`: there exists some such background.

The local/global distinction matters because Glass argues that *cause*
asserts only local sufficiency but pragmatically implicates the
stronger global form. -/

/-- **Globally sufficient** ([glass-2023b] def 11). -/
noncomputable def GloballySufficient {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause effect : V) : Prop :=
  ∀ bg : Valuation (fun _ : V => Bool),
    bg.get cause = none → bg.get effect = none →
    (M.developDet (bg.extend cause true)).hasValue effect true

/-- **Locally sufficient** ([glass-2023b] def 10). -/
noncomputable def LocallySufficient {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause effect : V) : Prop :=
  ∃ bg : Valuation (fun _ : V => Bool),
    bg.get effect = none ∧
    (M.developDet (bg.extend cause true)).hasValue effect true

/-- **Globally necessary** ([glass-2023b] def 9). -/
noncomputable def GloballyNecessary {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause effect : V) : Prop :=
  ∀ bg : Valuation (fun _ : V => Bool),
    bg.get cause = none → bg.get effect = none →
    ¬ (M.developDet bg).hasValue effect true

/-- **Locally necessary** ([glass-2023b] def 8). -/
noncomputable def LocallyNecessary {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause effect : V) : Prop :=
  ∃ bg : Valuation (fun _ : V => Bool),
    bg.get cause = none ∧ bg.get effect = none ∧
    ¬ (M.developDet bg).hasValue effect true

/-! ## Entailment: Global → Local

Both global → local entailments are immediate: instantiate the universal
with `Valuation.empty`, which trivially has cause and effect undetermined. -/

/-- Global sufficiency entails local sufficiency ([glass-2023b] (22a)). -/
theorem global_sufficient_implies_local {V : Type*} [Fintype V] [DecidableEq V]
    {M : BoolSEM V} [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    {cause effect : V} (h : GloballySufficient M cause effect) :
    LocallySufficient M cause effect :=
  ⟨Valuation.empty, rfl, h Valuation.empty rfl rfl⟩

/-- Global necessity entails local necessity ([glass-2023b] (21a)). -/
theorem global_necessary_implies_local {V : Type*} [Fintype V] [DecidableEq V]
    {M : BoolSEM V} [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    {cause effect : V} (h : GloballyNecessary M cause effect) :
    LocallyNecessary M cause effect :=
  ⟨Valuation.empty, rfl, rfl, h Valuation.empty rfl rfl⟩

/-! ## Glass's *cause* (def 12)

Glass argues that *cause* truth-conditionally requires only LOCAL
sufficiency — `causeSemGlass` collapses to `BoolSEM.causallySufficient`.
This is truth-conditionally identical to [nadathur-lauer-2020]'s
*make*; the difference is that Glass relegates necessity to pragmatic
implicature. -/

/-- Glass's proposed truth condition for "C causes E" ([glass-2023b]
    def 12): C is causally sufficient for E in the actual background. -/
abbrev causeSemGlass {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  Semantics.Causation.BoolSEM.causallySufficient M bg cause effect

/-- Glass's *cause* is truth-conditionally identical to N&L's *make*
    (`causallySufficient`). The difference is pragmatic. -/
theorem glass_cause_is_causallySufficient {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation (fun _ : V => Bool)) (cause effect : V) :
    causeSemGlass M bg cause effect ↔
      Semantics.Causation.BoolSEM.causallySufficient M bg cause effect := Iff.rfl

/-- **Glass vs N&L diverge on the Bus scenario**: "Ava's training caused
    Lia to take the bus" is true on Glass's sufficiency-based *cause* but
    false on [nadathur-lauer-2020]'s necessity-based *cause* — the same
    verb, the same scenario, opposite predictions. The two conjuncts are
    [nadathur-lauer-2020]'s own (33a)/(33b) verdicts, repackaged as the
    rival-accounts comparison this paper draws. -/
theorem glass_nl_diverge_on_bus :
    causeSemGlass NadathurLauer2020.Bus.busSEM NadathurLauer2020.Bus.s_b .Tr .Bs ∧
    ¬ Necessity.causeSem NadathurLauer2020.Bus.busSEM NadathurLauer2020.Bus.s_b
        .Tr true .Bs true :=
  ⟨SEM.causallySufficient_of_causallyEntails
      NadathurLauer2020.Bus.make_felicitous_for_bus.2,
   NadathurLauer2020.Bus.cause_infelicitous_for_bus⟩

end Glass2023
