import Linglib.Semantics.Attitudes.Preference
import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Presupposition.Basic
import Linglib.Core.Order.Satisfaction
import Linglib.Core.Order.SimilarityOrdering
import Linglib.Core.Probability.Decision.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Desire semantics

Rival semantics for desire ascriptions (*want*, *wish*, *hope*),
collected so their predictions about conflicting desires — ⌜S wants p⌝
together with ⌜S wants ¬p⌝ against one belief state — can be compared:

1. **Heim** ([heim-1992]) — `WantHeimNaive`, her (27), the
   Hintikka-style baseline she rejects; `WantHeim`, the (37/39)
   comparative-belief semantics restricted to the doxastic base; and
   her (40) definedness amendment `WantHeimDefined`.
2. **von Fintel** ([von-fintel-1999]) — `WantVonFintel`: every
   undominated belief-world is a p-world, under the world ordering
   induced by which desires each world satisfies — [kratzer-1981]'s
   `atLeastAsGoodAs` over the projected desire propositions
   (`WorldAtLeastAsGood`).
3. **Phillips-Brown** ([phillips-brown-2025]) — `WantQuestionBased`:
   every best answer in Q_c-Bel_S entails p, for a contextual question
   Q_c, with the paper's metasemantic constraints (`IsConsidered`,
   `IsDiverse`, `IsAntiDeckstacking`, `IsBelSensitive`) and its §3.4
   simulation result: on the finest question the semantics is von
   Fintel's (`wantQuestionBased_finestPartition_iff_WantVonFintel`).
4. **Condoravdi & Lauer** ([condoravdi-lauer-2011],
   [condoravdi-lauer-2012], [lauer-2013], [lauer-condoravdi-2014],
   [condoravdi-lauer-2016]) — *want* over a *preferential background*
   `P : Agent → W → PreferenceStructure W`, their analog of a Kratzerian
   conversational background: some maximal preference stands in a
   designated relation to the complement. The relation is the locus of
   variation among the three readings of their eq. 71: equality
   (`WantExactMatch`, the canonical reading, eq. 69), reverse inclusion
   (`WantSuccessOriented` — satisfied *if* the complement is true), and
   inclusion (`WantQuineHintikka` — satisfied *only if*).
5. **Lassiter** ([lassiter-2017] apparatus; [lassiter-2011] want
   application) — `Lassiter.Want`: conditional expected value above a
   threshold, with Sloman's Principle added in the full account
   (`Lassiter.WantWithSloman`).

On conflicting desires: the belief-based semantics block simultaneous
`want(p)` and `want(¬p)` (`wantHeim_no_conflict`,
`wantVonFintel_no_conflict`); Condoravdi & Lauer's exact-match want
over a consistent background blocks it too
(`PreferenceStructure.maxElts_pair_belief_compatible` applied to
`WantExactMatch` facts — the agent's designated *effective* preference
function, their (68), is a background pointwise `consistent` with the
belief state); Phillips-Brown evades the blockage by varying Q_c;
Lassiter's bare threshold admits it outright
(`Lassiter.threshold_admits_conflict_witness`) while his full account
does not (`Lassiter.wantWithSloman_blocks_conflict`). The
belief-based-*class* packaging of this argument is
[phillips-brown-2025]'s own §2 thesis and lives in
`Studies/PhillipsBrown2025.lean`.
-/

namespace Desire

open Semantics.Presupposition (PartialProp)
open Core.Order (SatisfactionOrdering)

section

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Comparative-belief semantics ([heim-1992])

The paper develops three successive truth conditions for *want*, each
repairing a defect of the previous:

* (27), §3 p. 192 — the naive Hintikka-style condition: every bouletic
  alternative is a φ-world (`WantHeimNaive`). Rejected via Asher's
  Concorde counterexample at (32), p. 194.
* (31), §4.1 p. 193 — the canonical comparative-belief condition: for
  every doxastic alternative w', every φ-world maximally similar to w'
  is more desirable than any ¬φ-world maximally similar to w'.
* (37/39), §4.2.2 p. 197 — the CCP rephrasal (`WantHeim`): the same
  comparison with the proposition restricted to the doxastic base
  first. The (40) amendment (`WantHeimDefined`, §4.2.3 p. 198) makes
  the ascription undefined when the agent already believes φ or
  already believes ¬φ.

Heim's ordering apparatus is a [lewis-1973]/[stalnaker-1968]
similarity ordering on worlds together with a primitive comparative
desirability relation — not a Kratzer ordering source, and not derived
from a desire list the way von Fintel's ordering is. -/

/-- Heim's (27), the naive Hintikka-style baseline: every belief-world
    is a p-world (the bouletic/doxastic distinction is collapsed).
    Heim rejects it via Asher's Concorde counterexample, her (32). -/
def WantHeimNaive (belS p : Set W) : Prop :=
  ∀ w, belS w → p w

instance (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] :
    Decidable (WantHeimNaive belS p) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- Parameters for Heim 1992's desire semantics: a similarity ordering
    on worlds (for `Sim_w(p)` = closest p-worlds to w) and a comparative
    desirability relation `pref w_eval x y` saying "at evaluation world
    w_eval, world x is at least as desirable as world y". -/
structure HeimDesireParams (W : Type*) where
  /-- The Lewis–Stalnaker similarity ordering on worlds. -/
  sim : Core.Order.SimilarityOrdering W
  /-- Comparative desirability `pref w_eval x y`: at `w_eval`, `x` is
      more desirable than `y`. The agent argument is suppressed
      (single-agent setup). -/
  pref : W → W → W → Prop
  /-- Decidability of the desirability relation. -/
  prefDec : ∀ w x y, Decidable (pref w x y)

instance (params : HeimDesireParams W) (w x y : W) :
    Decidable (params.pref w x y) :=
  params.prefDec w x y

/-- Sim_w(p) restricted to `belS ∩ p`: the closest worlds in
    `belS ∩ p` to `w` under the similarity ordering. Heim's (37)
    restricts the proposition argument of `Sim` to the doxastic base,
    which is what makes the Limit Assumption automatic on a finite
    model. -/
def heimSim (params : HeimDesireParams W)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] (w : W) : Finset W :=
  params.sim.closestWorlds w
    (Finset.univ.filter (fun z => belS z ∧ p z))

/-- Heim's (37/39), the canonical comparative-belief semantics:
    "α wants φ" at `w_eval` iff for every doxastic alternative
    `w' ∈ belS`, every closest `belS ∩ φ`-world to `w'` is at least as
    desirable as every closest `belS ∩ ¬φ`-world to `w'`. -/
def WantHeim (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] : Prop :=
  ∀ w' ∈ (Finset.univ : Finset W).filter belS,
    ∀ x ∈ heimSim params belS p w',
      ∀ y ∈ heimSim params belS (fun z => ¬ p z) w',
        params.pref w_eval x y

instance (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] :
    Decidable (WantHeim belS params w_eval p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Heim's (40) amendment: ⟦α wants φ⟧ is defined only when the agent
    neither already believes φ nor already believes ¬φ — both
    `belS ∩ φ` and `belS ∩ ¬φ` are non-empty. -/
def WantHeimDefined (belS p : Set W) : Prop :=
  (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)

instance (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] :
    Decidable (WantHeimDefined belS p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Comparative belief blocks conflicting desires -/

/-- `heimSim` is non-empty whenever `belS ∩ p` is — Heim's Limit
    Assumption, automatic on a finite model via
    `SimilarityOrdering.closestWorlds_nonempty`. -/
theorem heimSim_nonempty (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (p : Set W) [DecidablePred p]
    (w' : W) (hNE : ∃ z, belS z ∧ p z) :
    (heimSim params belS p w').Nonempty := by
  unfold heimSim
  apply Core.Order.SimilarityOrdering.closestWorlds_nonempty
  obtain ⟨z, hzBel, hzp⟩ := hNE
  exact ⟨z, by simp [Finset.mem_filter, hzBel, hzp]⟩

/-- Under the (40) definedness amendment and an antisymmetric
    desirability relation, Heim's semantics cannot make `want(p)` and
    `want(¬p)` simultaneously true. Antisymmetry is a hypothesis
    rather than structure so the theorem applies to strict and
    partial-order desirability alike. -/
theorem wantHeim_no_conflict
    (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p]
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y)
    (h : WantHeimDefined belS p) :
    ¬ (WantHeim belS params w_eval p ∧
       WantHeim belS params w_eval (fun w => ¬ p w)) := by
  rintro ⟨hp, hnp⟩
  obtain ⟨⟨wp, hwp_bel, hwp_p⟩, ⟨wn, hwn_bel, hwn_np⟩⟩ := h
  -- The negation argument's heimSim has a double-negation that needs
  -- reduction: heimSim belS (¬¬p) = heimSim belS p extensionally.
  have hSim_negneg :
      heimSim params belS (fun z => ¬ (fun w => ¬ p w) z) wp
        = heimSim params belS p wp := by
    unfold heimSim
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Decidable.not_not]
  -- Pick w' = wp (any belS-world; we use the p-witness).
  have hwp_filter : wp ∈ (Finset.univ : Finset W).filter belS := by
    simp [Finset.mem_filter, hwp_bel]
  obtain ⟨x, hx⟩ := heimSim_nonempty belS params p wp ⟨wp, hwp_bel, hwp_p⟩
  obtain ⟨y, hy⟩ := heimSim_nonempty belS params (fun z => ¬ p z) wp ⟨wn, hwn_bel, hwn_np⟩
  have hxy : params.pref w_eval x y := hp wp hwp_filter x hx y hy
  -- Use hSim_negneg to convert hx : x ∈ heimSim params belS p wp into the
  -- form expected by hnp (which has heimSim ... (¬¬p) ...).
  have hx' : x ∈ heimSim params belS (fun z => ¬ (fun w => ¬ p w) z) wp :=
    hSim_negneg ▸ hx
  have hyx : params.pref w_eval y x := hnp wp hwp_filter y hy x hx'
  have hxy_eq : x = y := hAsym x y hxy hyx
  -- x ∈ heimSim params belS p wp ⊆ {z | belS z ∧ p z}, so p x.
  have hxp : p x := by
    have := Core.Order.SimilarityOrdering.closestWorlds_subset _ _ _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hynp : ¬ p y := by
    have := Core.Order.SimilarityOrdering.closestWorlds_subset _ _ _ hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  exact hynp (hxy_eq ▸ hxp)

end

section

variable {W : Type*}

/-! ## Ordering semantics ([von-fintel-1999])

Every undominated belief-world is a p-world, under the world ordering
induced by which desires each world satisfies — [kratzer-1981]'s
`atLeastAsGoodAs` over the projected desire propositions. -/

/-- World ordering induced by a desire list: `w ≤ z` iff every desire
    in `GS` satisfied at `z` is also satisfied at `w` — [kratzer-1981]'s
    `atLeastAsGoodAs` over the projected proposition list, by
    definition. -/
def WorldAtLeastAsGood (GS : List (Finset W)) (w z : W) : Prop :=
  Modality.Kratzer.atLeastAsGoodAs (GS.map (fun s w => w ∈ s)) w z

/-- The ordering in its membership form: every listed desire satisfied
    at `z` is satisfied at `w`. -/
theorem worldAtLeastAsGood_iff_mem (GS : List (Finset W)) (w z : W) :
    WorldAtLeastAsGood GS w z ↔ ∀ s ∈ GS, z ∈ s → w ∈ s := by
  show (∀ p ∈ GS.map (fun s w => w ∈ s), p z → p w) ↔ _
  constructor
  · intro h a ha hz
    exact h _ (List.mem_map.mpr ⟨a, ha, rfl⟩) hz
  · intro h q hq hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact h a ha hz

instance [DecidableEq W] (GS : List (Finset W)) (w z : W) :
    Decidable (WorldAtLeastAsGood GS w z) :=
  decidable_of_iff _ (worldAtLeastAsGood_iff_mem GS w z).symm

/-- von Fintel's *want*: every undominated belief-world is a
    p-world. -/
def WantVonFintel (belS : Set W) (GS : List (Finset W)) (p : Set W) : Prop :=
  ∀ w, belS w →
    (∀ z, belS z → ¬ (WorldAtLeastAsGood GS z w ∧ ¬ WorldAtLeastAsGood GS w z)) →
    p w

instance [Fintype W] [DecidableEq W] (belS : Set W) [DecidablePred belS]
    (GS : List (Finset W)) (p : Set W) [DecidablePred p] :
    Decidable (WantVonFintel belS GS p) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- If some belief-world is undominated, `WantVonFintel` cannot hold
    of both `p` and `¬p` — the no-go [phillips-brown-2025] §2.1 runs
    against belief-based semantics. -/
theorem wantVonFintel_no_conflict
    (belS : Set W) (GS : List (Finset W)) (p : Set W)
    (h : ∃ w, belS w ∧
      ∀ z, belS z → ¬ (WorldAtLeastAsGood GS z w ∧ ¬ WorldAtLeastAsGood GS w z)) :
    ¬ (WantVonFintel belS GS p ∧ WantVonFintel belS GS (fun w => ¬ p w)) := by
  rintro ⟨hp, hnp⟩
  obtain ⟨w, hw, hund⟩ := h
  exact (hnp w hw hund) (hp w hw hund)

/-- `WantVonFintel` is upward monotonic in the complement — the
    [villalta-2008] doxastic-closure problem that motivates the
    question-based approach ([phillips-brown-2025] §4.1). -/
theorem wantVonFintel_upward_monotonic (belS : Set W)
    (GS : List (Finset W)) (p q : Set W)
    (hpq : ∀ w, p w → q w) (h : WantVonFintel belS GS p) :
    WantVonFintel belS GS q :=
  fun w hw hund => hpq w (h w hw hund)

end

section

variable {W : Type*} [DecidableEq W]

/-! ## Question-based semantics ([phillips-brown-2025])

⟦S wants p⟧^c is evaluated against a contextual question Q_c: the
answers compatible with S's beliefs (`questionRelativeBelief`, §3.3)
are ordered by which desires they entail (`propositionOrdering`,
§3.5), and the ascription is true iff every undominated answer
entails p (`WantQuestionBased`). Definedness is governed by four
metasemantic constraints (§3.6–§4.2), and on the finest question the
semantics is von Fintel's (§3.4,
`wantQuestionBased_finestPartition_iff_WantVonFintel`). -/

/-! ### Answer preference (§3.5)

S prefers answer `a` to `a'` iff the desires `a'` satisfies are a
strict subset of those `a` satisfies:

  {p ∈ G_S : a' ⊆ p} ⊊ {p ∈ G_S : a ⊆ p}

The weak relation is `SatisfactionOrdering.ofCriteria`, the strict one
`SatisfactionOrdering.strictlyBetter`; the paper's "best answers" are
the Pareto-undominated elements (§3.5, p. 11:21). -/

/-- Answer ordering: `a ≤ a'` iff every desire in `GS` that `a'`
    entails, `a` also entails. -/
def propositionOrdering (GS : List (Finset W)) :
    SatisfactionOrdering (Finset W) (Finset W) :=
  SatisfactionOrdering.ofCriteria (fun a p => decide (a ⊆ p)) GS

/-- Best (= Pareto-undominated) answers among a candidate list. -/
abbrev undominatedAnswers (GS answers : List (Finset W)) : List (Finset W) :=
  (propositionOrdering GS).undominated answers

/-- Q_c-Bel_S (§3.3): the cells of `answers` compatible with `belS`. -/
def questionRelativeBelief (answers : List (Finset W))
    (belS : Set W) [DecidablePred belS] : List (Finset W) :=
  answers.filter fun a => decide (∃ w ∈ a, belS w)

/-- ⟦S wants p⟧^c (§3.5): every undominated answer in Q_c-Bel_S
    entails p. -/
def WantQuestionBased (belS : Set W) [DecidablePred belS]
    (GS answers : List (Finset W)) (p : Set W) : Prop :=
  ∀ a ∈ undominatedAnswers GS (questionRelativeBelief answers belS),
    ∀ w ∈ a, p w

instance (belS : Set W) [DecidablePred belS]
    (GS answers : List (Finset W)) (p : Set W) [DecidablePred p] :
    Decidable (WantQuestionBased belS GS answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Metasemantic constraints (§3.6–§4.2) -/

/-- The Considering Constraint (§3.6): every cell of Q_c either
    entails p or entails ¬p — over partition cells, p is a union of
    cells. -/
def IsConsidered (answers : List (Finset W)) (p : Set W) : Prop :=
  ∀ a ∈ answers, (∀ w ∈ a, p w) ∨ (∀ w ∈ a, ¬ p w)

instance (answers : List (Finset W)) (p : Set W) [DecidablePred p] :
    Decidable (IsConsidered answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The Diversity Constraint (§3.7, attributed to [condoravdi-2002]):
    Q_c contains both p-cells and ¬p-cells; without it ⟦want p⟧ is
    vacuously true (or false). -/
def IsDiverse (answers : List (Finset W)) (p : Set W) : Prop :=
  (∃ a ∈ answers, ∀ w ∈ a, p w) ∧
  (∃ a ∈ answers, ∀ w ∈ a, ¬ p w)

instance (answers : List (Finset W)) (p : Set W) [DecidablePred p] :
    Decidable (IsDiverse answers p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Anti-deckstacking (§3.7)

The paper quantifies over all propositions q: if some cell entails q,
then q must itself be considered. Over a finite model the unrestricted
`∀ q : Set W` fails on gerrymandered unions of part-cells — artifacts
of the encoding, not of the question — so the constraint is
parameterized on a test set of salient propositions that each concrete
model declares. -/

/-- The Anti-deckstacking Constraint (§3.7) over the test set
    `naturalProps`: any test proposition entailed by some cell must be
    considered. The empty test set satisfies the constraint trivially,
    so concrete models must opt in by listing their basic
    propositions. -/
def IsAntiDeckstacking (naturalProps answers : List (Finset W)) : Prop :=
  ∀ q ∈ naturalProps, (∃ a ∈ answers, a ⊆ q) → IsConsidered answers (· ∈ q)

instance (naturalProps answers : List (Finset W)) :
    Decidable (IsAntiDeckstacking naturalProps answers) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The Belief-sensitivity Constraint (§4.2, building on
    [yalcin-2018]'s question-sensitive belief): `belS` discriminates
    among the cells of Q_c — at least one answer is compatible with
    the beliefs and at least one is not. Blocks ascriptions whose
    question the agent cannot grasp (the paper's William III /
    nuclear-war case). -/
def IsBelSensitive (belS : Set W) [DecidablePred belS]
    (answers : List (Finset W)) : Prop :=
  let live := questionRelativeBelief answers belS
  live ≠ [] ∧ live.length ≠ answers.length

instance (belS : Set W) [DecidablePred belS] (answers : List (Finset W)) :
    Decidable (IsBelSensitive belS answers) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Full definedness for ⟦S wants p⟧^c: Considering, Diversity,
    Anti-deckstacking, and Belief-sensitivity jointly. -/
def WantDefined (belS : Set W) [DecidablePred belS]
    (naturalProps answers : List (Finset W)) (p : Set W) : Prop :=
  IsConsidered answers p ∧ IsDiverse answers p ∧
  IsAntiDeckstacking naturalProps answers ∧ IsBelSensitive belS answers

instance (belS : Set W) [DecidablePred belS]
    (naturalProps answers : List (Finset W)) (p : Set W) [DecidablePred p] :
    Decidable (WantDefined belS naturalProps answers p) := by
  unfold WantDefined; infer_instance

/-- Question-based *want* as a `PartialProp`: presupposition = full
    definedness, assertion = question-based truth. Both are
    world-independent because Q_c is fixed contextually prior to
    evaluation. -/
def wantPartialProp (belS : Set W) [DecidablePred belS]
    (GS naturalProps answers : List (Finset W)) (p : Set W) :
    PartialProp W where
  presup _ := WantDefined belS naturalProps answers p
  assertion _ := WantQuestionBased belS GS answers p

/-- Question-based *want* is Strawson upward monotonic (§4.2): given
    `p ⊆ q` and the Considering presupposition for `q`, `want(p)`
    entails `want(q)`. The presupposition is what blocks the naive
    monotonicity that would derive "wants Avoid-nuclear-war" from
    "wants Avoid-war". -/
theorem wantQuestionBased_strawson_upward_monotonic
    (belS : Set W) [DecidablePred belS]
    (GS answers : List (Finset W)) (p q : Set W)
    (hpq : ∀ w, p w → q w) (_hCons : IsConsidered answers q)
    (h : WantQuestionBased belS GS answers p) :
    WantQuestionBased belS GS answers q :=
  fun a ha w hw => hpq w (h a ha w hw)

/-! ### The finest question simulates von Fintel (§3.4)

On the finest partition — one singleton cell per world — the
question-based semantics is von Fintel's. The construction is
parameterized on an explicit world list so concrete models can
`decide` it. -/

/-- The finest partition over an explicit world list: one singleton
    cell per listed world. -/
def finestPartition (worlds : List W) : List (Finset W) :=
  worlds.map ({·})

/-- Singleton-cell preference under `propositionOrdering` reduces to
    single-world preference under `WorldAtLeastAsGood`: `{w} ≤ {z}` in
    the proposition ordering iff `WorldAtLeastAsGood GS w z`. -/
private theorem singleton_le_iff_world (GS : List (Finset W)) (w z : W) :
    (propositionOrdering GS).le {w} {z} ↔ WorldAtLeastAsGood GS w z := by
  rw [worldAtLeastAsGood_iff_mem]
  unfold propositionOrdering SatisfactionOrdering.ofCriteria
  show (∀ q ∈ GS.filter (fun q => decide (({z} : Finset W) ⊆ q)),
          decide (({w} : Finset W) ⊆ q) = true) ↔
       (∀ s ∈ GS, z ∈ s → w ∈ s)
  simp only [decide_eq_true_eq, Finset.singleton_subset_iff]
  constructor
  · intro h q hq hqz
    exact h q (by rw [List.mem_filter]; exact ⟨hq, by simpa using hqz⟩)
  · intro h q hqf
    rw [List.mem_filter] at hqf
    exact h q hqf.1 (by simpa using hqf.2)

omit [DecidableEq W] in
/-- The singleton cell `{w}` is in `questionRelativeBelief
    (finestPartition worlds) belS` iff `w ∈ worlds` and `belS w`. -/
private theorem singleton_mem_questionRelativeBelief_finestPartition
    (belS : Set W) [DecidablePred belS] (worlds : List W) (w : W) :
    ({w} : Finset W) ∈ questionRelativeBelief (finestPartition worlds) belS ↔
      w ∈ worlds ∧ belS w := by
  simp [questionRelativeBelief, finestPartition, List.mem_filter,
    Finset.singleton_inj]

/-- On the finest partition over an exhaustive world list,
    question-based want is von Fintel's ([phillips-brown-2025]
    §3.4). -/
theorem wantQuestionBased_finestPartition_iff_WantVonFintel
    (belS : Set W) [DecidablePred belS] (GS : List (Finset W))
    (worlds : List W) (hUniv : ∀ w, w ∈ worlds)
    (p : Set W) [DecidablePred p] :
    WantQuestionBased belS GS (finestPartition worlds) p ↔ WantVonFintel belS GS p := by
  unfold WantQuestionBased WantVonFintel undominatedAnswers SatisfactionOrdering.undominated
  refine ⟨fun hLHS w hw hUnd => ?_, fun hRHS a ha => ?_⟩
  · -- LHS → RHS: pick the cell {w}, show it is undominated, apply
    have hcell_mem : ({w} : Finset W) ∈
        questionRelativeBelief (finestPartition worlds) belS :=
      (singleton_mem_questionRelativeBelief_finestPartition belS worlds w).mpr ⟨hUniv w, hw⟩
    have hcell_undom : ({w} : Finset W) ∈
        ((propositionOrdering GS).undominated
          (questionRelativeBelief (finestPartition worlds) belS)) := by
      unfold SatisfactionOrdering.undominated
      rw [List.mem_filter]
      refine ⟨hcell_mem, ?_⟩
      simp only [decide_eq_true_eq]
      rintro ⟨c, hc_mem, hc_strict⟩
      -- c is a question-relative belief cell, so c = {z} for some z with
      -- belS z; translate hc_strict to the world ordering and contradict hUnd.
      have hc_in_fp : c ∈ finestPartition worlds := by
        unfold questionRelativeBelief at hc_mem
        exact (List.mem_filter.mp hc_mem).1
      obtain ⟨z, _hz_mem, hz_eq⟩ := List.mem_map.mp hc_in_fp
      have hz_bel : belS z := by
        rw [← hz_eq] at hc_mem
        exact ((singleton_mem_questionRelativeBelief_finestPartition belS worlds z).mp hc_mem).2
      rw [← hz_eq] at hc_strict
      have hzw : WorldAtLeastAsGood GS z w := (singleton_le_iff_world GS z w).mp hc_strict.1
      have hnwz : ¬ WorldAtLeastAsGood GS w z := fun h =>
        hc_strict.2 ((singleton_le_iff_world GS w z).mpr h)
      exact hUnd z hz_bel ⟨hzw, hnwz⟩
    exact hLHS _ hcell_undom w (Finset.mem_singleton_self w)
  · -- RHS → LHS: a is an undominated question-relative belief cell
    rw [List.mem_filter] at ha
    obtain ⟨ha_mem, ha_min⟩ := ha
    -- extract w with a = {w}, w ∈ worlds, belS w
    have ha_in_fp : a ∈ finestPartition worlds := by
      unfold questionRelativeBelief at ha_mem
      exact (List.mem_filter.mp ha_mem).1
    obtain ⟨w, _hw_mem, hw_eq⟩ := List.mem_map.mp ha_in_fp
    -- Substitute a := {w} throughout
    subst hw_eq
    have hbelw : belS w :=
      ((singleton_mem_questionRelativeBelief_finestPartition belS worlds w).mp ha_mem).2
    -- ha_min: no question-relative belief cell is strictly better than {w}
    simp only [decide_eq_true_eq] at ha_min
    have hUnd : ∀ z, belS z → ¬ (WorldAtLeastAsGood GS z w ∧
                                  ¬ WorldAtLeastAsGood GS w z) := by
      intro z hz_bel ⟨hzw, hnwz⟩
      apply ha_min
      refine ⟨{z}, ?_, ?_⟩
      · exact (singleton_mem_questionRelativeBelief_finestPartition belS worlds z).mpr ⟨hUniv z, hz_bel⟩
      · exact ⟨(singleton_le_iff_world GS z w).mpr hzw,
               fun h => hnwz ((singleton_le_iff_world GS w z).mp h)⟩
    have hpw : p w := hRHS w hbelw hUnd
    intro x hx
    exact (Finset.mem_singleton.mp hx) ▸ hpw

end

/-! ## Effective-preference readings ([condoravdi-lauer-2016])

The inferential profile is fixed by the choice of relation:
success-oriented want is downward-entailing in the complement,
Quine-Hintikka want upward-entailing, exact-match want neither. The conflicting-desires
blockage for exact-match want over a consistent background is
`PreferenceStructure.maxElts_pair_belief_compatible` directly,
prosecuted in `Studies/CondoravdiLauer2016.lean`; the anankastic
ordering source `max[EP(Ad, w)]` (their eq. 88) is
`fun w => (P Ad w).maxElts`. -/

section EffectivePreferenceReadings

variable {Agent W : Type*} (P : Agent → W → PreferenceStructure W)

/-- Exact-match want: some maximal preference in the preferential
    background `P` is `φ` itself: `φ ∈ max[P(a, w)]`. The canonical
    reading. -/
def WantExactMatch (a : Agent) (φ : Set W) (w : W) : Prop :=
  φ ∈ (P a w).maxElts

/-- Success-oriented want: some maximal preference is entailed by `φ`
    — a preference satisfied if `φ` is true. -/
def WantSuccessOriented (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, φ ⊆ p

/-- Quine-Hintikka want: some maximal preference entails `φ` — a
    preference satisfied only if `φ` is true. -/
def WantQuineHintikka (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, p ⊆ φ

variable {P}

/-- Exact match implies the success-oriented reading. -/
theorem wantSuccessOriented_of_exactMatch {a : Agent} {φ : Set W} {w : W}
    (h : WantExactMatch P a φ w) : WantSuccessOriented P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-- Exact match implies the Quine-Hintikka reading. -/
theorem wantQuineHintikka_of_exactMatch {a : Agent} {φ : Set W} {w : W}
    (h : WantExactMatch P a φ w) : WantQuineHintikka P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-- Success-oriented want is downward-entailing in the complement. -/
theorem wantSuccessOriented_downward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    WantSuccessOriented P a ψ w → WantSuccessOriented P a φ w :=
  fun ⟨p, hp, hψp⟩ => ⟨p, hp, hφψ.trans hψp⟩

/-- Quine-Hintikka want is upward-entailing in the complement. -/
theorem wantQuineHintikka_upward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    WantQuineHintikka P a φ w → WantQuineHintikka P a ψ w :=
  fun ⟨p, hp, hpφ⟩ => ⟨p, hp, hpφ.trans hφψ⟩

end EffectivePreferenceReadings

/-! ## Expected-value semantics ([lassiter-2017]; [lassiter-2011])

[lassiter-2017] ch.7 ("Scalar goodness") develops an expected-value
semantics for evaluative gradable predicates:
`E_V(φ) = Σ_{w ∈ φ ∩ D} V(w) · prob({w} | φ ∩ D)` (eq. 7.22, p.187),
with the positive form the threshold reading `μ(φ) > θ` (§8.14
eq. 8.72a, p.253). The extension to *want* is §8.13 (p.249) — "*want*
behaves as a gradable verb like *like, matter, care, need*" — with the
detailed account in [lassiter-2011] ch.6.

The bare threshold admits simultaneous `want(p) ∧ want(¬p)`
(`threshold_admits_conflict_witness`), so Lassiter escapes the
belief-based no-go by a different route than Phillips-Brown:
probabilistic gradability rather than question-sensitivity. The full
account adds Sloman's Principle, which blocks single-value conflict
(`wantWithSloman_blocks_conflict`); per §8.11 (pp.243–245), genuine
conflicting wants come from multiple sources of value with weighted
aggregation, not from threshold-tuning on one value function. -/

namespace Lassiter

variable {W : Type*}

/-! ### Expected value -/

/-- Conditional expected value of `p` given belief state `belS` under
    prior `pr` and value function `V` (eq. 7.22):

      E_V(p) = (Σ pr·V over (p ∩ belS)) / (Σ pr over (p ∩ belS))

    Indicator-style sums keep the definition `decide`-friendly for
    concrete witness models. Returns `0` when the denominator is zero
    (Lassiter leaves E_V undefined for the empty proposition,
    p.187 fn.). -/
def expectedValue [Fintype W]
    (pr : W → ℚ) (V : W → ℚ)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : ℚ :=
  if (∑ w, (if belS w ∧ p w then pr w else 0)) = 0 then 0
  else (∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
       (∑ w, (if belS w ∧ p w then pr w else 0))

/-- Positive-form *want*: the conditional expected value of `p` given
    S's beliefs exceeds the threshold `θ` — the scalar reading
    `μ_ought(φ) > θ_ought` of §8.14 eq. 8.72a, extended to *want* per
    §8.13 and [lassiter-2011] ch.6. -/
def Want [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p] : Prop :=
  expectedValue pr V belS p > θ

instance [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p] :
    Decidable (Want belS pr V θ p) :=
  inferInstanceAs (Decidable (_ > θ))

/-! ### Sloman's Principle ([lassiter-2017] §8.6)

`ought(φ) → [∀ψ ∈ ALT(φ) : ψ ≠ φ → φ >_good ψ]`

The wanted proposition strictly dominates every other alternative on
the value scale. This is the constraint Lassiter adopts to block
simultaneous truth of `ought(φ) ∧ ought(¬φ)` when both are in the
alternative set. -/

/-- Sloman's Principle: `p` strictly dominates every other listed
    alternative on the expected-value scale. -/
def SlomanPrinciple [Fintype W] [DecidableEq W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ)
    (alts : List (Finset W)) (p : Finset W) : Prop :=
  ∀ entry ∈ alts, entry ≠ p →
    expectedValue pr V belS (· ∈ p) > expectedValue pr V belS (· ∈ entry)

/-- Lassiter's full account: the bare threshold and Sloman's
    Principle. This is the account Lassiter defends in §8; the bare
    `Want` operator alone is apparatus, not the position. -/
def WantWithSloman [Fintype W] [DecidableEq W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (alts : List (Finset W)) (p : Finset W) : Prop :=
  Want belS pr V θ (· ∈ p) ∧ SlomanPrinciple belS pr V alts p

/-! ### Bridge to decision theory

`expectedValue` is the proposition-conditional analog of
`Core.DecisionTheory.DecisionProblem.condExpectedUtility`; wrapping
the value function as a unit-action utility makes the bridge
explicit. -/

/-- Wrap a Lassiter `(prior, value)` pair as a unit-action
    `DecisionProblem`. -/
def toDecisionProblem (pr : W → ℚ) (V : W → ℚ) :
    Core.DecisionTheory.DecisionProblem ℚ W Unit where
  utility w _ := V w
  prior := pr

/-! ### Conflict witness for the bare threshold

A 4-world model demonstrating that the *bare* `want` operator (without
Sloman) admits simultaneous `want(p) ∧ want(¬p)`. Uniform prior 1/4 over
`Fin 4`; asymmetric value `V = (10, 4, 4, 0)`; threshold `θ = 3/2`;
`p = {w₀, w₁}`. Then `E_V(p) = 7 > 3/2` and `E_V(¬p) = 2 > 3/2`.

This is Lassiter Table 8.4 p.239 — Lassiter's reconstruction of the
Weakening-failure pattern [cariani-2016] attacks within actualism,
applied to the EV semantics. Cariani 2016's own counter-model
(p.405) uses an actualist closeness ordering, not EV. Lassiter's
*response* is to add Sloman's Principle, which excludes the witness
(`wantWithSloman_blocks_conflict`; the witness-model instance is in
`Studies/Lassiter2017.lean`). -/

/-- The bare threshold admits simultaneous `want(p)` and `want(¬p)`. -/
theorem threshold_admits_conflict_witness :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (belS : Set W) (_ : DecidablePred belS)
      (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
      (p : Set W) (_ : DecidablePred p),
      Want belS pr V θ p ∧
      Want belS pr V θ (fun w => ¬ p w) := by
  refine ⟨Fin 4, inferInstance, inferInstance,
          (fun _ => True), inferInstance,
          (fun _ => 1/4),
          (fun w => match w with
            | 0 => 10 | 1 => 4 | 2 => 4 | 3 => 0),
          3/2,
          (fun w => w = 0 ∨ w = 1), inferInstance,
          ?_, ?_⟩
  all_goals
    show Want _ _ _ _ _
    unfold Want expectedValue
    simp [Fin.sum_univ_succ]
    norm_num

/-! ### Sloman's Principle blocks the conflict

On the witness model with `alts = [p, pᶜ]`, Sloman holds for `p`
(E_V(p) = 7 > 2 = E_V(pᶜ)) and fails for `pᶜ`, so `WantWithSloman`
makes only `p` wanted — Lassiter's §8.11 (p.245) position that
single-value conflict is excluded by his own constraints, with
genuine conflicting wants coming from multi-source aggregation. -/

/-- `WantWithSloman` cannot hold of both `p` and its complement when
    both are among the alternatives. -/
theorem wantWithSloman_blocks_conflict
    [Fintype W] [DecidableEq W] (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (alts : List (Finset W)) (p : Finset W)
    (hp : p ∈ alts) (hpc : pᶜ ∈ alts) (hne : p ≠ pᶜ) :
    ¬ (WantWithSloman belS pr V θ alts p ∧
       WantWithSloman belS pr V θ alts pᶜ) := by
  rintro ⟨⟨_, hSlomanP⟩, ⟨_, hSlomanPc⟩⟩
  exact absurd (lt_trans (hSlomanPc p hp hne) (hSlomanP pᶜ hpc hne.symm))
    (lt_irrefl _)

/-! ### Intermediacy of expected value ([lassiter-2017] §7.5–§7.6)

Lassiter §7.5 establishes that `S_good` is an *intermediate* scale: the
goodness of `φ ∨ ψ` is between the goodness of `φ` and the goodness of
`ψ` (rather than maximal — equal to the better of the two — or
positive — strictly above both). In §7.6 (p.188), the disjoint union
formula

  E_V(φ ∨ ψ) = (E_V(φ)·prob(φ) + E_V(ψ)·prob(ψ)) / (prob(φ) + prob(ψ))

shows E_V is a weighted average over disjoint propositions, hence
intermediate.

Formalized here in the disjoint case: for disjoint p, q with
positive belief mass,
`min(E_V(p), E_V(q)) ≤ E_V(p ∪ q) ≤ max(E_V(p), E_V(q))` — the scalar
property underlying Weakening below. -/

/-- `p` carries positive prior mass inside the belief state. -/
def HasPositiveBeliefMass [Fintype W]
    (pr : W → ℚ) (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : Prop :=
  (∑ w, (if belS w ∧ p w then pr w else 0)) > 0

/-- Intermediacy of E_V, disjoint case: for disjoint p, q with
    positive belief mass, the disjoint-union expectation is the
    mediant `(E(p)·μ(p) + E(q)·μ(q)) / (μ(p) + μ(q))` — a weighted
    average, hence between `min(E_V(p), E_V(q))` and the `max`. -/
theorem expectedValue_intermediate_disjoint [Fintype W]
    (pr : W → ℚ) (V : W → ℚ)
    (belS : Set W) [DecidablePred belS]
    (p q : Set W) [DecidablePred p] [DecidablePred q]
    (hPosP : HasPositiveBeliefMass pr belS p)
    (hPosQ : HasPositiveBeliefMass pr belS q)
    (hDisjoint : ∀ w, ¬ (p w ∧ q w)) :
    min (expectedValue pr V belS p) (expectedValue pr V belS q)
      ≤ expectedValue pr V belS (fun w => p w ∨ q w) ∧
    expectedValue pr V belS (fun w => p w ∨ q w)
      ≤ max (expectedValue pr V belS p) (expectedValue pr V belS q) := by
  unfold HasPositiveBeliefMass at hPosP hPosQ
  have hsplit : ∀ f : W → ℚ,
      (∑ w, (if belS w ∧ (p w ∨ q w) then f w else 0)) =
      (∑ w, (if belS w ∧ p w then f w else 0)) +
      (∑ w, (if belS w ∧ q w then f w else 0)) := by
    intro f
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hb : belS w
    · by_cases hp : p w
      · have hq : ¬ q w := fun hq => hDisjoint w ⟨hp, hq⟩
        simp [hb, hp, hq]
      · by_cases hq : q w <;> simp [hb, hp, hq]
    · simp [hb]
  have hEp : expectedValue pr V belS p =
      (∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
      (∑ w, (if belS w ∧ p w then pr w else 0)) := by
    unfold expectedValue; rw [if_neg (ne_of_gt hPosP)]
  have hEq : expectedValue pr V belS q =
      (∑ w, (if belS w ∧ q w then pr w * V w else 0)) /
      (∑ w, (if belS w ∧ q w then pr w else 0)) := by
    unfold expectedValue; rw [if_neg (ne_of_gt hPosQ)]
  have hSpq : (0 : ℚ) < (∑ w, (if belS w ∧ p w then pr w else 0)) +
      (∑ w, (if belS w ∧ q w then pr w else 0)) := add_pos hPosP hPosQ
  have hEpq : expectedValue pr V belS (fun w => p w ∨ q w) =
      ((∑ w, (if belS w ∧ p w then pr w * V w else 0)) +
       (∑ w, (if belS w ∧ q w then pr w * V w else 0))) /
      ((∑ w, (if belS w ∧ p w then pr w else 0)) +
       (∑ w, (if belS w ∧ q w then pr w else 0))) := by
    unfold expectedValue
    rw [hsplit pr, hsplit (fun w => pr w * V w), if_neg (ne_of_gt hSpq)]
  rw [hEp, hEq, hEpq]
  constructor
  · refine (le_div_iff₀ hSpq).mpr ?_
    have h1 := (le_div_iff₀ hPosP).mp
      (min_le_left ((∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ p w then pr w else 0)))
        ((∑ w, (if belS w ∧ q w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ q w then pr w else 0))))
    have h2 := (le_div_iff₀ hPosQ).mp
      (min_le_right ((∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ p w then pr w else 0)))
        ((∑ w, (if belS w ∧ q w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ q w then pr w else 0))))
    nlinarith [h1, h2]
  · refine (div_le_iff₀ hSpq).mpr ?_
    have h1 := (div_le_iff₀ hPosP).mp
      (le_max_left ((∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ p w then pr w else 0)))
        ((∑ w, (if belS w ∧ q w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ q w then pr w else 0))))
    have h2 := (div_le_iff₀ hPosQ).mp
      (le_max_right ((∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ p w then pr w else 0)))
        ((∑ w, (if belS w ∧ q w then pr w * V w else 0)) /
          (∑ w, (if belS w ∧ q w then pr w else 0))))
    nlinarith [h1, h2]

/-! ### Weakening from intermediacy

[lassiter-2017] eq. 8.54 collects three constraints on *ought*: Sloman
(formalized above as `SlomanPrinciple`), Smith (restricted
agglomeration, whose derivation requires more structure than
intermediacy and is not formalized here), and Weakening
(`ought(φ) ∧ ought(ψ) → ought(φ ∨ ψ)`, the name due to [cariani-2016],
who defends the principle). Lassiter derives Weakening from the
intermediacy of expected value (§8.14);
`want_satisfies_weakening_disjoint` reproduces the derivation in the
disjoint case, so Weakening is derived from the underlying scalar
property rather than stipulated. -/

/-- Weakening from intermediacy, disjoint case: when disjoint `p`
    and `q` both exceed the threshold, so does their disjunction —
    `E_V(p ∨ q) ≥ min(E_V(p), E_V(q)) > θ`, Lassiter's §8.14
    eq. (8.78) derivation. -/
theorem want_satisfies_weakening_disjoint [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p q : Set W) [DecidablePred p] [DecidablePred q]
    (hPosP : HasPositiveBeliefMass pr belS p)
    (hPosQ : HasPositiveBeliefMass pr belS q)
    (hDisjoint : ∀ w, ¬ (p w ∧ q w))
    (hp : Want belS pr V θ p) (hq : Want belS pr V θ q) :
    Want belS pr V θ (fun w => p w ∨ q w) := by
  unfold Want at hp hq ⊢
  have ⟨hMin, _hMax⟩ :=
    expectedValue_intermediate_disjoint pr V belS p q hPosP hPosQ hDisjoint
  exact lt_of_lt_of_le (lt_min hp hq) hMin

end Lassiter

end Desire
