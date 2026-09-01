import Linglib.Logic.ComparativeProbability.Systems
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# [harrison-trainor-holliday-icard-2016]: Cancellation axioms for comparative probability

The cancellation theory of precise and imprecise (multi-prior) comparative
probability, as assembled by [harrison-trainor-holliday-icard-2016]: a pair of
event-sequences is *balanced* when every state lies in equally many events on
each side; **Finite Cancellation** ([scott-1964]'s reformulation of
[kraft-pratt-seidenberg-1959]) and its **Generalized** strengthening
([rios-insua-1992]; [alon-lehrer-2014]) are the cancellation axioms whose
`Reflexivity + Positivity + Non-triviality` companions characterize, on a
finite state space, representability by a single additive probability measure,
resp. by a nonempty *set* of such measures.

The note's own result — GFC is strictly stronger than FC for incomplete
relations (its Propositions 1 and 2) — is not yet formalized. This file states
the axioms, derives the properties cancellation makes redundant (transitivity,
monotonicity, and complement reversal follow from the four GFC-order axioms),
and proves the soundness direction of the representation: a finitely additive
measure's induced order is a GFC order.

## Main definitions

* `Balanced`, `FiniteCancellation`, `GeneralizedFiniteCancellation` — the
  cancellation axioms.
* `GFCOrder` — reflexivity, positivity, non-triviality, and generalized finite
  cancellation, bundled.

## Main statements

* `FiniteCancellation.of_generalized` — GFC implies FC.
* `GFCOrder.trans`/`mono`/`complRev` — derived from cancellation, not
  stipulated.
* `GFCOrder.ofMeasure` — a finitely additive measure induces a GFC order.

## References

[harrison-trainor-holliday-icard-2016], [scott-1964],
[kraft-pratt-seidenberg-1959], [rios-insua-1992], [alon-lehrer-2014]
-/

namespace HarrisonTrainorHollidayIcard2016

open ComparativeProbability

variable {W : Type*}

open scoped Classical in
/-- Indicator count of a state across an event sequence. -/
noncomputable def seqCount (s : W) (Es : List (Set W)) : ℕ :=
  (Es.map (fun E => if s ∈ E then (1 : ℕ) else 0)).sum

/-- A **balanced** pair of event-sequences: every state lies in equally many
    events on the left as on the right. -/
def Balanced (Es Fs : List (Set W)) : Prop := ∀ s : W, seqCount s Es = seqCount s Fs

/-- **Finite Cancellation** ([scott-1964]'s axiom, reformulating
    [kraft-pratt-seidenberg-1959]): for every balanced pair `⟨…, X⟩` / `⟨…, Y⟩`
    whose premise comparisons all hold, `Y ≿ X`. (`prem` carries the paired
    premise events; `X`/`Y` are the heads.) -/
def FiniteCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W),
    Balanced (X :: prem.map Prod.fst) (Y :: prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- **Generalized Finite Cancellation** ([rios-insua-1992]; [alon-lehrer-2014]):
    like `FiniteCancellation`, but the distinguished pair may be repeated
    `r ≥ 1` times. Strictly stronger than `FiniteCancellation` for incomplete
    relations (the note's Propositions 1 and 2); equivalent under totality. -/
def GeneralizedFiniteCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W) (r : ℕ), 1 ≤ r →
    Balanced (List.replicate r X ++ prem.map Prod.fst)
             (List.replicate r Y ++ prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- GFC implies FC (the `r = 1` instance). -/
theorem FiniteCancellation.of_generalized {ge : Set W → Set W → Prop}
    (h : GeneralizedFiniteCancellation ge) : FiniteCancellation ge :=
  fun prem X Y hbal hprem => h prem X Y 1 le_rfl (by simpa [List.replicate_one] using hbal) hprem

/-- A **GFC order**: reflexivity, positivity, non-triviality, and generalized
    finite cancellation. On a finite state space these four axioms characterize
    representability by a nonempty set of additive probability measures
    (`E ≿ F ↔ ∀ μ ∈ P, μ E ≥ μ F`; [rios-insua-1992], [alon-lehrer-2014]).
    Transitivity, monotonicity, and complement reversal are *derived* from
    cancellation (`GFCOrder.trans`/`mono`/`complRev`), not stipulated. -/
structure GFCOrder (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Reflexivity. -/
  refl : ∀ A, ge A A
  /-- Positivity: every proposition is at least as likely as the contradiction. -/
  positivity : ∀ A, ge A ∅
  /-- Non-triviality: the contradiction is not at least as likely as the tautology. -/
  nonTriviality : ¬ ge ∅ Set.univ
  /-- Generalized finite cancellation. -/
  gfc : GeneralizedFiniteCancellation ge

section

variable (G : GFCOrder W)

/-- A GFC order satisfies finite cancellation. -/
theorem GFCOrder.fc : FiniteCancellation G.ge := FiniteCancellation.of_generalized G.gfc

/-- Transitivity is derived from cancellation (balanced sequence `⟨A,B,C⟩`/`⟨B,C,A⟩`). -/
theorem GFCOrder.trans {A B C : Set W} (hAB : G.ge A B) (hBC : G.ge B C) : G.ge A C := by
  refine G.fc [(A, B), (B, C)] C A (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hAB
    · exact hBC

/-- Monotonicity is derived from positivity + cancellation
    (balanced sequence `⟨B∖A, A⟩`/`⟨∅, B⟩`). -/
theorem GFCOrder.mono {A B : Set W} (hAB : A ⊆ B) : G.ge B A := by
  refine G.fc [(B \ A, ∅)] A B (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_empty_iff_false, if_false, Set.mem_sdiff]
    by_cases hsA : s ∈ A
    · simp [hsA, hAB hsA]
    · by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact G.positivity _

/-- Complement reversal is derived from cancellation
    (balanced sequence `⟨A, Aᶜ⟩`/`⟨B, Bᶜ⟩`). -/
theorem GFCOrder.complRev {A B : Set W} (hAB : G.ge A B) : G.ge Bᶜ Aᶜ := by
  refine G.fc [(A, B)] Aᶜ Bᶜ (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_compl_iff]
    by_cases hsA : s ∈ A <;> by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hAB

end

/-! ### Measures induce GFC orders -/

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
    · simp only [hs, if_true]; rw [mul_add, mul_one]
    · simp [hs]

private lemma mu_listSum_eq_of_balanced {L₁ L₂ : List (Set W)} (h : Balanced L₁ L₂) :
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

/-- Every finitely additive measure's induced order is a GFC order — the
    soundness direction of the representation (a single measure `μ` is the
    nonempty set `{μ}`). -/
def GFCOrder.ofMeasure : GFCOrder W where
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

end HarrisonTrainorHollidayIcard2016
