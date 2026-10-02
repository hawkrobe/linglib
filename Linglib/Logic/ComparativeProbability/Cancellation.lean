module

public import Linglib.Logic.ComparativeProbability.Representability
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cancellation conditions

A pair of event sequences is *balanced* when every state lies in equally many events on each
side. Finite cancellation, Scott's reformulation of the condition of Kraft, Pratt and
Seidenberg, says that when the premise comparisons of a balanced pair hold, the head
comparison holds reversed; it characterizes representability by a single additive measure.
Ríos Insua and Alon and Lehrer strengthen it to generalized finite cancellation, which allows
the head pair to repeat and characterizes representability by a nonempty set of measures.
Harrison-Trainor, Holliday and Icard show that the strengthening is strict for incomplete
relations; under totality the two coincide.

`Scott.lean` proves Scott's theorem in the sign-vector form of the condition and shows the two
forms agree (`ComparativeProbability.cancellation_iff_finiteCancellation`). This file holds the
definitions, the derived properties of a cancellation order, and the soundness directions:
measures induce cancellation orders, and representable qualitative probability orders satisfy
finite cancellation.

## Main definitions

* `BalancedSeqs`, `FiniteCancellation`, `GeneralizedFiniteCancellation`: balance and the two
  cancellation conditions.
* `CancellationOrder`: reflexivity, positivity, non-triviality and generalized finite
  cancellation, bundled without totality.

## Main statements

* `FiniteCancellation.of_generalized`, `CancellationOrder.trans`, `CancellationOrder.mono`,
  `CancellationOrder.complRev`: the order properties derived from cancellation.
* `CancellationOrder.ofMeasure`, `Representable.finiteCancellation`: soundness.

## References

* [scott-1964]
* [kraft-pratt-seidenberg-1959]
* [rios-insua-1992]
* [alon-lehrer-2014]
* [harrison-trainor-holliday-icard-2016]
-/

@[expose] public section

namespace ComparativeProbability

variable {W : Type*}

open scoped Classical in
/-- `seqCount s Es` counts the events of `Es` that contain `s`. -/
noncomputable def seqCount (s : W) (Es : List (Set W)) : ℕ :=
  (Es.map (fun E => if s ∈ E then (1 : ℕ) else 0)).sum

@[simp] theorem seqCount_nil (s : W) : seqCount s [] = 0 := rfl

open scoped Classical in
@[simp] theorem seqCount_cons (s : W) (E : Set W) (Es : List (Set W)) :
    seqCount s (E :: Es) = (if s ∈ E then 1 else 0) + seqCount s Es := by
  simp [seqCount]

/-- Two event sequences are **balanced** when every state lies in equally many events on the
    left as on the right. -/
def BalancedSeqs (Es Fs : List (Set W)) : Prop := ∀ s : W, seqCount s Es = seqCount s Fs

/-- **Finite cancellation** holds when `Y ≿ X` for every balanced pair `⟨…, X⟩` / `⟨…, Y⟩`
    whose premise comparisons all hold. Here `prem` carries the paired premise events and
    `X`, `Y` are the heads. -/
def FiniteCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W),
    BalancedSeqs (X :: prem.map Prod.fst) (Y :: prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- **Generalized finite cancellation** is `FiniteCancellation` with the head pair repeated
    `r ≥ 1` times. -/
def GeneralizedFiniteCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W) (r : ℕ), 1 ≤ r →
    BalancedSeqs (List.replicate r X ++ prem.map Prod.fst)
             (List.replicate r Y ++ prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- Generalized finite cancellation implies finite cancellation, as its `r = 1` instance. -/
theorem FiniteCancellation.of_generalized {ge : Set W → Set W → Prop}
    (h : GeneralizedFiniteCancellation ge) : FiniteCancellation ge :=
  fun prem X Y hbal hprem => h prem X Y 1 le_rfl (by simpa [List.replicate_one] using hbal) hprem

/-- A **cancellation order** is a reflexive, positive, non-trivial relation satisfying
    generalized finite cancellation. On a finite state space these are the orders represented
    by a nonempty set of additive probability measures (`E ≿ F ↔ ∀ μ ∈ P, μ E ≥ μ F`).
    Totality is not assumed; transitivity, monotonicity and complement reversal are derived
    (`CancellationOrder.trans`, `mono`, `complRev`). -/
structure CancellationOrder (W : Type*) where
  /-- `ge A B` says that `A` is at least as likely as `B`. -/
  ge : Set W → Set W → Prop
  /-- Every proposition is at least as likely as itself. -/
  refl : ∀ A, ge A A
  /-- Every proposition is at least as likely as the contradiction. -/
  positivity : ∀ A, ge A ∅
  /-- The contradiction is not at least as likely as the tautology. -/
  nonTriviality : ¬ ge ∅ Set.univ
  /-- The relation satisfies generalized finite cancellation. -/
  gfc : GeneralizedFiniteCancellation ge

section

variable (G : CancellationOrder W)

/-- A cancellation order satisfies finite cancellation. -/
theorem CancellationOrder.fc : FiniteCancellation G.ge := FiniteCancellation.of_generalized G.gfc

/-- Transitivity is derived from cancellation (balanced sequence `⟨A,B,C⟩`/`⟨B,C,A⟩`). -/
theorem CancellationOrder.trans {A B C : Set W} (hAB : G.ge A B) (hBC : G.ge B C) : G.ge A C := by
  refine G.fc [(A, B), (B, C)] C A (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hAB
    · exact hBC

/-- Monotonicity is derived from positivity and cancellation
    (balanced sequence `⟨B∖A, A⟩`/`⟨∅, B⟩`). -/
theorem CancellationOrder.mono {A B : Set W} (hAB : A ⊆ B) : G.ge B A := by
  refine G.fc [(B \ A, ∅)] A B (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_empty_iff_false, ite_false, Set.mem_sdiff]
    by_cases hsA : s ∈ A
    · simp [hsA, hAB hsA]
    · by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact G.positivity _

/-- Complement reversal is derived from cancellation
    (balanced sequence `⟨A, Aᶜ⟩`/`⟨B, Bᶜ⟩`). -/
theorem CancellationOrder.complRev {A B : Set W} (hAB : G.ge A B) : G.ge Bᶜ Aᶜ := by
  refine G.fc [(A, B)] Aᶜ Bᶜ (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_compl_iff]
    by_cases hsA : s ∈ A <;> by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hAB

end

/-! ### Measures induce cancellation orders -/

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype W] (m : FinAddMeasure K W)

open scoped Classical in
private lemma mu_eq_sum_ite (E : Set W) :
    m E = ∑ s, if s ∈ E then m {s} else 0 := by
  classical
  have h : m E = ∑ i ∈ E.toFinset, m {i} := by
    rw [m.sum_mu_singleton, Set.coe_toFinset]
  rw [h, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext s; simp [Set.mem_toFinset]

private lemma mu_listSum (L : List (Set W)) :
    (L.map m).sum = ∑ s, m {s} * (seqCount s L : K) := by
  classical
  induction L with
  | nil => simp [seqCount]
  | cons E L ih =>
    rw [List.map_cons, List.sum_cons, ih, mu_eq_sum_ite m E, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hsc : seqCount s (E :: L) = (if s ∈ E then 1 else 0) + seqCount s L := by
      simp [seqCount]
    rw [hsc]; push_cast
    by_cases hs : s ∈ E
    · simp only [hs, ite_true]; rw [mul_add, mul_one]
    · simp [hs]

private lemma mu_listSum_eq_of_balanced {L₁ L₂ : List (Set W)} (h : BalancedSeqs L₁ L₂) :
    (L₁.map m).sum = (L₂.map m).sum := by
  rw [mu_listSum m L₁, mu_listSum m L₂]
  exact Finset.sum_congr rfl (fun s _ => by rw [h s])

omit [Fintype W] in
private lemma mu_sum_mono {prem : List (Set W × Set W)}
    (hprem : ∀ p ∈ prem, m.inducedGe p.1 p.2) :
    ((prem.map Prod.snd).map m).sum ≤ ((prem.map Prod.fst).map m).sum := by
  induction prem with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hprem p (List.mem_cons_self ..))
      (ih (fun q hq => hprem q (List.mem_cons_of_mem _ hq)))

/-- Every finitely additive measure induces a cancellation order, the soundness direction of
    the representation, since a single measure `μ` is the nonempty set `{μ}`. -/
def CancellationOrder.ofMeasure : CancellationOrder W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  positivity := fun A => by
    simpa [FinAddMeasure.inducedGe, m.mu_empty] using m.nonneg A
  nonTriviality := by
    simp only [FinAddMeasure.inducedGe, m.mu_empty, m.total, not_le]; exact one_pos
  gfc := by
    intro prem X Y r hr hbal hprem
    have hsum := mu_listSum_eq_of_balanced m hbal
    simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul] at hsum
    have hr0 : (0 : K) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    show m X ≤ m Y
    have hkey : (r : K) * m X ≤ (r : K) * m Y := by nlinarith [mu_sum_mono m hprem]
    exact le_of_mul_le_mul_left hkey hr0

end

/-- A representable qualitative probability order satisfies finite cancellation
    (the soundness half of Scott's theorem, in balanced-sequence form). -/
theorem Representable.finiteCancellation [Fintype W] {sys : QualitativeProbability (Set W)}
    (h : Representable sys) : FiniteCancellation sys.ge := by
  obtain ⟨m, hm⟩ := h
  have hfc := (CancellationOrder.ofMeasure m).fc
  intro prem X Y hbal hprem
  exact (hm X Y).mpr (hfc prem X Y hbal fun p hp => (hm p.2 p.1).mp (hprem p hp))

end ComparativeProbability
