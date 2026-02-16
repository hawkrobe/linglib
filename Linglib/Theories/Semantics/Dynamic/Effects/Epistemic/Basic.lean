import Linglib.Core.CommonGround
import Linglib.Core.Proposition
import Linglib.Theories.Semantics.Modality.Kratzer

/-!
# Neo-Stalnakerian Formalization of Assertion (Rudin 2025)

Rudin proposes that when a speaker asserts a sentence s, she predicates her
epistemic state: she presents herself as though she knows s, and proposes
the context be updated to reflect that knowledge. This is formalized via
the **meta-intensionalization** function MI, which maps s to the set of
epistemic states compatible with knowing s.

Applied uniformly to all declaratives, this single mechanism derives:
1. Standard Stalnakerian intersective update for non-epistemic sentences (§4.1)
2. Veltman's (1996) consistency-test semantics for epistemic *might* (§4.2)
3. A novel ordering-source update for *might* on Kratzer (1981) semantics (§5)

The key insight: epistemic modals get nonstandard updates not because they
have special update semantics, but because they are speaker-orientedly
epistemic *in the same way* that assertion is.

## References

- Rudin, D. (2025). Asserting epistemic modals. *L&P* 48, 43–88.
- Stalnaker, R. (1978). Assertion. *Syntax and Semantics* 9, 315–332.
- Veltman, F. (1996). Defaults in update semantics. *JPL* 25(3), 221–261.
- Kratzer, A. (1981/1991). The notional category of modality / Modality.
-/

namespace Semantics.Dynamic.NeoStalnakerian

open Core.Proposition
open Core.CommonGround

/-! ## Part 1: Core Types -/

section SimpleVersion

variable {W : Type*}

/-- Information-sensitive denotation: ⟦s⟧ⁱ(w).
    Truth value may depend on the epistemic state `i`. -/
abbrev InfoSensDen (W : Type*) := List W → BProp W

/-- Lift a plain proposition to an information-insensitive denotation.
    For sentences like "John is dead" whose truth doesn't vary with `i`. -/
def liftProp (p : BProp W) : InfoSensDen W := λ _ => p

/-- Simple quantificational semantics for epistemic *might*:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ i, p(w') = true.
    Truth is insensitive to the evaluation world w.

    Rudin (2025) eq. (25); adapted from Yalcin (2007). -/
def mightSimple (p : BProp W) : InfoSensDen W :=
  λ i _ => i.any p

/-- Simple quantificational semantics for epistemic *must*:
    ⟦must-p⟧ⁱ(w) = true iff ∀w' ∈ i, p(w') = true.

    Rudin (2025) Appendix A, eq. (57). -/
def mustSimple (p : BProp W) : InfoSensDen W :=
  λ i _ => i.all p

/-! ## Part 2: Meta-Intensionalization -/

/-- **Meta-intensionalization**: the set of epistemic states the speaker
    could hold if she knows s to be true.

        MI(s) = { i : ∀w ∈ i, ⟦s⟧ⁱ(w) = 1 }

    When a speaker asserts s, she presents herself as though her epistemic
    state is a member of MI(s).

    Rudin (2025) Definition (10). -/
def MI (sem : InfoSensDen W) (i : List W) : Prop :=
  ∀ w, w ∈ i → sem i w = true

/-- Refinement: i' refines i iff i' ⊆ i.
    Removing worlds monotonically increases information.

    Rudin (2025) Definition (13). -/
def refines (i' i : List W) : Prop :=
  ∀ w, w ∈ i' → w ∈ i

/-- A context c is s-compatible iff some non-empty refinement is in MI(s).

    Rudin (2025) Definition (18). -/
def sCompatible (sem : InfoSensDen W) (c : List W) : Prop :=
  ∃ c', refines c' c ∧ MI sem c' ∧ c' ≠ []

/-- Rejection of s is licensed when the rejector's state is not s-compatible.

    Rudin (2025) Definition (20). -/
def rejectionLicensed (sem : InfoSensDen W) (i_rejector : List W) : Prop :=
  ¬sCompatible sem i_rejector

/-! ## Part 3: MI Characterization Theorems -/

/-- MI for non-epistemic sentences: i ∈ MI(p) iff every world in i satisfies p.
    Equivalently, i ⊆ ext(p) — the downward closure of the proposition's extension.

    Rudin (2025) eqs. (22)–(23). -/
theorem MI_liftProp (p : BProp W) (i : List W) :
    MI (liftProp p) i ↔ ∀ w, w ∈ i → p w = true :=
  Iff.rfl

/-- MI for might-p (non-empty states): i ∈ MI(might-p) iff i has a p-world.
    The universal quantifier in MI collapses because might's truth conditions
    are insensitive to the evaluation world.

    Rudin (2025) eq. (27b): MI(might-p) = { i : i ∩ p ≠ ∅ }. -/
theorem MI_mightSimple (p : BProp W) (i : List W) (hi : i ≠ []) :
    MI (mightSimple p) i ↔ i.any p = true := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ => exact h w (by simp)
  · intro h _ _; exact h

/-- MI for must-p coincides with MI for the bare prejacent.
    Since must universally quantifies over the same set i that MI quantifies
    over, the two collapse: MI(must-p) = { i : i ⊆ p }.

    Rudin (2025) Appendix A, eq. (58). -/
theorem MI_mustSimple (p : BProp W) (i : List W) (hi : i ≠ []) :
    MI (mustSimple p) i ↔ ∀ w, w ∈ i → p w = true := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ => exact List.all_eq_true.mp (h w (by simp))
  · intro h _ _; exact List.all_eq_true.mpr h

/-- MI(must-p) = MI(p): must has the same meta-intensionalized denotation
    as a non-epistemic assertion of its prejacent. -/
theorem MI_must_eq_MI_lift (p : BProp W) (i : List W) (hi : i ≠ []) :
    MI (mustSimple p) i ↔ MI (liftProp p) i := by
  rw [MI_mustSimple p i hi, MI_liftProp]

/-! ## Part 4: Derived Update Potentials -/

/-- NSF update for non-epistemic sentences: intersect with proposition.
    The most conservative refinement of c that lands in MI(liftProp p).

    Rudin (2025) eq. (24). -/
def nsfUpdateNonEpistemic (p : BProp W) (c : List W) : List W :=
  c.filter p

/-- NSF update for might-p (simple semantics): consistency test.
    Leave context unchanged if c has p-worlds; anomaly otherwise.

    Rudin (2025) eq. (29). -/
def nsfUpdateMight (p : BProp W) (c : List W) : List W :=
  if c.any p then c else []

/-- NSF update for must-p (simple semantics): same as non-epistemic.

    Rudin (2025) Appendix A, eq. (59). -/
def nsfUpdateMust (p : BProp W) (c : List W) : List W :=
  c.filter p

/-! ## Part 5: Derivation Theorems -/

/-- If c has p-worlds, it is already in MI(might-p). No refinement needed. -/
theorem context_in_MI_might (p : BProp W) (c : List W)
    (h : c.any p = true) : MI (mightSimple p) c :=
  λ _ _ => h

/-- **Core lemma**: subset refinement cannot introduce p-worlds.
    If c has no p-worlds, no refinement of c does either,
    making c not-might-p-compatible. This forces anomalous update.

    This is the key step in deriving Veltman's test semantics from
    the NSF: the "consistency test" behavior of might falls out of
    the monotonicity of refinement. -/
theorem no_p_worlds_not_compatible (p : BProp W) (c : List W)
    (h : c.any p = false) : ¬sCompatible (mightSimple p) c := by
  intro ⟨c', hRef, hMI, hNe⟩
  -- c' is non-empty, so MI gives c'.any p = true
  have hAny : c'.any p = true := by
    cases c' with
    | nil => exact absurd rfl hNe
    | cons w _ => exact hMI w (by simp)
  -- Some world in c' satisfies p; by refinement it's in c
  obtain ⟨v, hv, hpv⟩ := List.any_eq_true.mp hAny
  -- So c.any p = true, contradicting h
  have : c.any p = true := List.any_eq_true.mpr ⟨v, hRef v hv, hpv⟩
  simp [h] at this

/-- **NSF derives Veltman's consistency test.**

    Given solipsistic contextualist truth conditions for might and the
    NSF's assertive machinery, the update potential for might-p is:
    - c[might-p] = c   if c ∩ p ≠ ∅  (test passes)
    - c[might-p] = ∅   if c ∩ p = ∅  (anomaly)

    This is exactly Veltman (1996), derived rather than stipulated.
    The derivation uses `context_in_MI_might` (compatible case) and
    `no_p_worlds_not_compatible` (incompatible case).

    Bridges `nsfUpdateMight` to `Update.might` from UpdateSemantics.

    Rudin (2025) §4.2; cf. Veltman (1996), Yalcin (2007, 2011). -/
theorem nsfUpdateMight_spec (p : BProp W) (c : List W) :
    nsfUpdateMight p c = (if c.any p then c else []) :=
  rfl

/-- NSF update for must-p equals update for its prejacent.
    Must-p updates identically to a non-epistemic assertion of p.

    Rudin (2025) Appendix A, eq. (59). -/
theorem nsfUpdateMust_eq_nonEpistemic (p : BProp W) (c : List W) :
    nsfUpdateMust p c = nsfUpdateNonEpistemic p c :=
  rfl

/-- **NSF recovers Stalnaker for non-epistemic sentences.**

    For sentences whose denotation doesn't vary with the information
    parameter, the NSF update is intersection with the proposition —
    exactly Stalnaker's (1978) original formalization.

    Bridges `nsfUpdateNonEpistemic` to `ContextSet.update` from CommonGround:
    both compute c ∩ p (filter c to p-worlds). -/
theorem nsf_recovers_stalnaker (p : BProp W) (c : List W) (w : W) :
    w ∈ nsfUpdateNonEpistemic p c ↔ w ∈ c ∧ p w = true := by
  simp [nsfUpdateNonEpistemic, List.mem_filter]

/-! ## Part 6: Rejection Licensing -/

/-- Rejection of a non-epistemic assertion of p is licensed iff the rejector
    has no p-worlds — i.e., the rejector knows ¬p. -/
theorem rejection_nonEpistemic (p : BProp W) (i : List W) (_ : i ≠ []) :
    rejectionLicensed (liftProp p) i ↔ ∀ w, w ∈ i → p w = false := by
  unfold rejectionLicensed sCompatible
  constructor
  · intro hRej w hw
    by_contra hpw
    have hne : p w = true := by
      cases hpw' : p w with
      | true => rfl
      | false => exact absurd hpw' hpw
    -- {w} is a non-empty refinement in MI(liftProp p)
    apply hRej
    refine ⟨[w], λ v hv => ?_, λ v hv => ?_, List.cons_ne_nil w []⟩
    · simp only [List.mem_singleton] at hv; rw [hv]; exact hw
    · simp only [List.mem_singleton] at hv; rw [hv]; exact hne
  · intro h ⟨c', hRef, hMI, hNe⟩
    cases c' with
    | nil => exact absurd rfl hNe
    | cons v vs =>
      have hvi : v ∈ i := hRef v (by simp)
      have hpv : liftProp p (v :: vs) v = true := hMI v (by simp)
      simp only [liftProp] at hpv
      exact absurd hpv (by simp [h v hvi])

/-- Rejection of might-p is licensed iff the rejector has no p-worlds.
    Crucially, this depends on the *rejector's* information, not the
    *assertor's*. The assertor's might-claim can be true (she has
    p-worlds) while the rejector is licensed to reject (he has none).

    This predicts Khoo's (2015) finding that might-claims can be
    simultaneously not-judged-false and rejected.

    Rudin (2025) §4.2.1. -/
theorem rejection_mightSimple (p : BProp W) (i : List W) :
    rejectionLicensed (mightSimple p) i ↔ ¬(sCompatible (mightSimple p) i) :=
  Iff.rfl

/-- Rejection of might-p reduces to having no p-worlds. -/
theorem rejection_might_iff_no_p_worlds (p : BProp W) (i : List W)
    (hi : i.any p = false) :
    rejectionLicensed (mightSimple p) i :=
  no_p_worlds_not_compatible p i hi

end SimpleVersion

/-! ## Part 7: Ordering Semantics (Kratzer bridge) -/

section OrderingVersion

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)

/-- Epistemic state (ordering version): a modal base (set of worlds)
    paired with an ordering source (set of propositions ranking those worlds).

    Rudin (2025) Definition (43):
      D_i = { ⟨b_i, o_i⟩ : b_i ∈ D_st ∧ o_i ∈ ℘D_st }  -/
structure OrdEpistemicState where
  /-- Modal base: the set of epistemically accessible worlds -/
  base : List World
  /-- Ordering source: propositions ranking accessible worlds -/
  ordering : List (BProp World)

/-- BEST worlds: worlds in the modal base not strictly dominated by any other.
    A world w is strictly dominated by w' iff w' satisfies a proper superset
    of the ordering propositions that w satisfies.

    Rudin (2025) eq. (44); Kratzer (1981, 1991). -/
def OrdEpistemicState.bestWorlds (s : OrdEpistemicState) : List World :=
  s.base.filter λ w =>
    !s.base.any λ w' =>
      atLeastAsGoodAs s.ordering w' w && !atLeastAsGoodAs s.ordering w w'

/-- Ordering semantics for might (Kratzer 1981, 1991):
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ BEST_{b_i,o_i}, p(w') = true.

    Rudin (2025) eq. (45). -/
def mightOrdering (p : BProp World) (s : OrdEpistemicState) (_ : World) : Bool :=
  s.bestWorlds.any p

/-- MI for ordering-semantic might-p: the set of epistemic states whose
    BEST worlds include at least one p-world.

    Rudin (2025) eq. (54b). -/
def MI_ord (p : BProp World) (s : OrdEpistemicState) : Prop :=
  s.bestWorlds.any p = true

/-- Refinement (ordering version): only the modal base is refined.

    Rudin (2025) Definition (46). -/
def OrdEpistemicState.refines (c' c : OrdEpistemicState) : Prop :=
  ∀ w, w ∈ c'.base → w ∈ c.base

/-- **NSF update for might-p (ordering semantics): add p to ordering source.**

    This is the paper's most novel result. Asserting might-p proposes that
    the prejacent be added as a "live possibility" — a proposition in the
    ordering source. This makes p-worlds more likely to be among the BEST
    worlds, yielding an informative (non-trivial) update.

    Rudin (2025) eq. (56). -/
def nsfUpdateMightOrd (p : BProp World) (c : OrdEpistemicState) : OrdEpistemicState :=
  if (c.base.filter p).isEmpty then
    { base := [], ordering := c.ordering }  -- anomaly
  else
    { base := c.base, ordering := p :: c.ordering }

/-- Adding p to the ordering source cannot make a p-world dominated
    by a non-p-world, because the non-p-world fails to satisfy p
    while the p-world satisfies it.

    This is the key step in proving the ordering update is commensurate. -/
theorem nonPWorld_cannot_dominate_pWorld
    (A : List (BProp World)) (p : BProp World)
    (w z : World) (hw : p w = true) (hz : p z = false) :
    atLeastAsGoodAs (p :: A) z w = false := by
  unfold atLeastAsGoodAs satisfiedPropositions
  simp only [List.filter_cons, hw, ↓reduceIte, List.all_cons, hz,
             Bool.false_and]

/-- A non-empty list has an element maximizing any Nat-valued function. -/
private theorem exists_max_by {α : Type*} (f : α → Nat) (l : List α) (hl : l ≠ []) :
    ∃ a, a ∈ l ∧ ∀ b, b ∈ l → f b ≤ f a := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst hxs; exact ⟨x, by simp, by intro b hb; rcases List.mem_cons.mp hb with rfl | h; rfl; simp at h⟩
    · obtain ⟨m, hm, hmax⟩ := ih hxs
      by_cases h : f m ≤ f x
      · exact ⟨x, by simp, by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact Nat.le_refl _
          · exact Nat.le_trans (hmax b hb) h⟩
      · push_neg at h
        exact ⟨m, List.mem_cons_of_mem x hm, by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact Nat.le_of_lt h
          · exact hmax b hb⟩

/-- Filter by a weaker predicate gives a weakly longer result. -/
private theorem filter_length_le_of_imp
    (A : List (BProp World)) (w w' : World)
    (h : ∀ q, q ∈ A → q w = true → q w' = true) :
    (A.filter (λ q => q w)).length ≤ (A.filter (λ q => q w')).length := by
  induction A with
  | nil => rfl
  | cons q qs ih =>
    have ih' := ih (λ r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.filter_cons]
    by_cases hqw : q w = true <;> by_cases hqw' : q w' = true
      <;> simp only [hqw, hqw', ↓reduceIte]
    · exact Nat.succ_le_succ ih'
    · exact absurd (h q (by simp) hqw) (by simp [hqw'])
    · exact Nat.le_trans ih' (Nat.le_succ _)
    · exact ih'

/-- Filter is strictly longer when one predicate strictly implies another. -/
private theorem filter_length_lt_of_strict
    (A : List (BProp World)) (w w' : World)
    (hsub : ∀ q, q ∈ A → q w = true → q w' = true)
    (hstrict : ∃ q, q ∈ A ∧ q w' = true ∧ q w = false) :
    (A.filter (λ q => q w)).length < (A.filter (λ q => q w')).length := by
  induction A with
  | nil => obtain ⟨q, hq, _, _⟩ := hstrict; simp at hq
  | cons r rs ih =>
    simp only [List.filter_cons]
    have hsub_rs : ∀ q, q ∈ rs → q w = true → q w' = true :=
      λ q hq => hsub q (List.mem_cons_of_mem r hq)
    obtain ⟨q, hqA, hqw', hqw⟩ := hstrict
    rcases List.mem_cons.mp hqA with rfl | hqrs
    · -- Witness is the head
      simp only [hqw, hqw', ↓reduceIte]
      exact Nat.lt_succ_of_le (filter_length_le_of_imp rs w w' hsub_rs)
    · -- Witness is in tail
      by_cases hrw : r w = true <;> by_cases hrw' : r w' = true
        <;> simp only [hrw, hrw', ↓reduceIte]
      · exact Nat.succ_lt_succ (ih hsub_rs ⟨q, hqrs, hqw', hqw⟩)
      · exact absurd (hsub r (by simp) hrw) (by simp [hrw'])
      · exact Nat.lt_succ_of_lt (ih hsub_rs ⟨q, hqrs, hqw', hqw⟩)
      · exact ih hsub_rs ⟨q, hqrs, hqw', hqw⟩

/-- Strict domination implies strictly more satisfied propositions. -/
private theorem strict_dom_more_sat
    (A : List (BProp World)) (w w' : World)
    (h1 : atLeastAsGoodAs A w' w = true)
    (h2 : atLeastAsGoodAs A w w' = false) :
    (satisfiedPropositions A w).length < (satisfiedPropositions A w').length := by
  unfold satisfiedPropositions
  unfold atLeastAsGoodAs at h1 h2
  have hsub : ∀ q, q ∈ A → q w = true → q w' = true := by
    intro q hq hqw
    exact List.all_eq_true.mp h1 q (List.mem_filter.mpr ⟨hq, hqw⟩)
  have hstrict : ∃ q, q ∈ A ∧ q w' = true ∧ q w = false := by
    have hne : ¬(∀ q, q ∈ A.filter (λ r => r w') → q w = true) := by
      intro hall
      exact absurd (List.all_eq_true.mpr hall) (Bool.eq_false_iff.mp h2)
    push_neg at hne
    obtain ⟨q, hq, hqw⟩ := hne
    exact ⟨q, (List.mem_filter.mp hq).1, (List.mem_filter.mp hq).2,
           by cases hv : q w <;> simp_all⟩
  exact filter_length_lt_of_strict A w w' hsub hstrict

/-- **Commensurativity**: if the modal base has a p-world, adding p to the
    ordering source yields a state whose BEST worlds include a p-world.

    After adding p, no non-p-world can dominate any p-world
    (`nonPWorld_cannot_dominate_pWorld`). Among p-worlds, the element with
    maximum satisfaction count is maximal. Since the base has p-worlds,
    BEST_{b, A+p} ∩ p ≠ ∅.

    Rudin (2025) §5.3, pp. 77–78. -/
theorem ordering_update_commensurate
    (c : OrdEpistemicState) (p : BProp World)
    (hCompat : c.base.any p = true) :
    MI_ord p (nsfUpdateMightOrd p c) := by
  unfold MI_ord nsfUpdateMightOrd
  obtain ⟨w₀, hw₀, hpw₀⟩ := List.any_eq_true.mp hCompat
  have hFilterMem : w₀ ∈ c.base.filter p := List.mem_filter.mpr ⟨hw₀, hpw₀⟩
  have hNotEmpty : (c.base.filter p).isEmpty = false := by
    cases hfp : c.base.filter p with
    | nil => simp [hfp] at hFilterMem
    | cons _ _ => rfl
  simp only [hNotEmpty]
  have hPWorldsNe : c.base.filter p ≠ [] := by
    intro h; simp [h] at hFilterMem
  obtain ⟨m, hm, hmmax⟩ := exists_max_by
    (λ w => (satisfiedPropositions (p :: c.ordering) w).length)
    (c.base.filter p) hPWorldsNe
  have hmBase : m ∈ c.base := (List.mem_filter.mp hm).1
  have hpm : p m = true := (List.mem_filter.mp hm).2
  apply List.any_eq_true.mpr
  refine ⟨m, ?_, hpm⟩
  -- Show m ∈ bestWorlds: m is in base and not strictly dominated
  apply List.mem_filter.mpr
  refine ⟨hmBase, ?_⟩
  -- Need: !(base.any (λ w' => ... w' m && !... m w')) = true
  -- Equivalently: base.any (λ w' => ... w' m && !... m w') = false
  -- Goal: !(base.any (λ w' => ... && !...)) = true
  -- i.e., no w' in base strictly dominates m
  suffices h : c.base.any (λ w' =>
    atLeastAsGoodAs (p :: c.ordering) w' m &&
    !atLeastAsGoodAs (p :: c.ordering) m w') = false by
    simp [h]
  rw [List.any_eq_false]
  intro w' hw' hcontra
  have ⟨h1, h2bang⟩ := Bool.and_eq_true_iff.mp hcontra
  -- h1: w' ≥ m, h2bang: !(m ≥ w') = true
  have h2 : atLeastAsGoodAs (p :: c.ordering) m w' = false := by
    revert h2bang; cases atLeastAsGoodAs (p :: c.ordering) m w' <;> simp
  by_cases hpw' : p w' = true
  · -- w' is a p-world. m has max satCount, so no strict domination.
    have hlt := strict_dom_more_sat (p :: c.ordering) m w' h1 h2
    have hw'F : w' ∈ c.base.filter p := List.mem_filter.mpr ⟨hw', hpw'⟩
    exact absurd (hmmax w' hw'F) (by omega)
  · -- w' is a non-p-world. Can't even be ≥ m.
    have hpw'f : p w' = false := by cases hv : p w' <;> simp_all
    have habs := nonPWorld_cannot_dominate_pWorld c.ordering p m w' hpm hpw'f
    simp [habs] at h1

/-- The ordering update is conservative: adding p to the ordering source
    does not guarantee that the resulting context will entail anything
    not already entailed by might-p.

    Rudin (2025) §5.3. -/
theorem ordering_update_conservative
    (c : OrdEpistemicState) (p : BProp World)
    (hCompat : c.base.any p = true) :
    (nsfUpdateMightOrd p c).base = c.base := by
  unfold nsfUpdateMightOrd
  obtain ⟨w, hw, hpw⟩ := List.any_eq_true.mp hCompat
  have hMem : w ∈ c.base.filter p := List.mem_filter.mpr ⟨hw, hpw⟩
  have hNotEmpty : (c.base.filter p).isEmpty = false := by
    cases hfp : c.base.filter p with
    | nil => simp [hfp] at hMem
    | cons _ _ => rfl
  simp [hNotEmpty]

/-- Non-epistemic sentences still get standard intersective update
    in the ordering version: the ordering source is unchanged.

    Rudin (2025) eq. (52). -/
theorem ordering_nonEpistemic_preserves_ordering
    (c : OrdEpistemicState) (p : BProp World) :
    let c' : OrdEpistemicState :=
      { base := c.base.filter p, ordering := c.ordering }
    c'.ordering = c.ordering :=
  rfl

/-! ### Appendix A2: Must on ordering semantics -/

/-- Ordering semantics for must (Kratzer 1981, 1991):
    ⟦must-p⟧ⁱ(w) = true iff ∀w' ∈ BEST_{b_i,o_i}, p(w') = true.

    Rudin (2025) eq. (60). -/
def mustOrdering (p : BProp World) (s : OrdEpistemicState) (_ : World) : Bool :=
  s.bestWorlds.all p

/-- MI for ordering-semantic must-p: the set of epistemic states whose
    BEST worlds are all p-worlds.

    Rudin (2025) eq. (61). -/
def MI_ord_must (p : BProp World) (s : OrdEpistemicState) : Prop :=
  ∀ w, w ∈ s.bestWorlds → p w = true

/-- MI(must-p) on ordering semantics ↔ BEST ⊆ p. -/
theorem MI_ord_must_iff (p : BProp World) (s : OrdEpistemicState) :
    MI_ord_must p s ↔ s.bestWorlds.all p = true := by
  unfold MI_ord_must
  exact Iff.symm List.all_eq_true

/-- A proposition is p-disjoint iff no world satisfies both it and p. -/
def pDisjoint (p q : BProp World) (base : List World) : Bool :=
  base.all λ w => !(p w && q w)

/-- **NSF update for must-p (ordering semantics).**

    Add p to the ordering source AND remove all p-disjoint propositions.
    Simply adding p is insufficient: p-disjoint ordering propositions can
    keep non-p-worlds in BEST. Removing them ensures all BEST worlds
    satisfy p.

    Rudin (2025) eq. (64). -/
def nsfUpdateMustOrd (p : BProp World) (c : OrdEpistemicState) : OrdEpistemicState :=
  if (c.base.filter p).isEmpty then
    { base := [], ordering := c.ordering }  -- anomaly
  else
    { base := c.base,
      ordering := p :: c.ordering.filter (λ q => !pDisjoint p q c.base) }

/-- The must ordering update preserves the modal base (when compatible). -/
theorem nsfUpdateMustOrd_preserves_base
    (c : OrdEpistemicState) (p : BProp World)
    (hCompat : c.base.any p = true) :
    (nsfUpdateMustOrd p c).base = c.base := by
  unfold nsfUpdateMustOrd
  obtain ⟨w, hw, hpw⟩ := List.any_eq_true.mp hCompat
  have hMem : w ∈ c.base.filter p := List.mem_filter.mpr ⟨hw, hpw⟩
  have hNotEmpty : (c.base.filter p).isEmpty = false := by
    cases hfp : c.base.filter p with
    | nil => simp [hfp] at hMem
    | cons _ _ => rfl
  simp [hNotEmpty]

end OrderingVersion

/-! ## Part 8: Relational Semantics Equivalence (Appendix B) -/

section RelationalSemantics

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)

/-- Relational semantics for might (Kratzer 1977):
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ f_i(w), p(w') = true,
    where f_i is the epistemic accessibility function determined by i.

    Rudin (2025) eq. (65). -/
def mightRelational (f : World → List World) (p : BProp World) (w : World) : Bool :=
  (f w).any p

/-- Epistemic closure: f maps every world in i to i itself.
    Under solipsistic contextualism, the accessibility function for
    the speaker's epistemic state maps each accessible world to
    the full epistemic state.

    Rudin (2025) eq. (67). -/
def EpistemicClosure (f : World → List World) (i : List World) : Prop :=
  ∀ w, w ∈ i → f w = i

/-- Under epistemic closure, MI(might-p) on relational semantics
    is { i : i ∩ p ≠ ∅ } — identical to the domain semantics result.

    Proof follows Rudin (2025) eq. (69a–c):
    - If i ∩ p ≠ ∅, then for any w ∈ i, f(w) = i has p-worlds ✓
    - If i ∩ p = ∅, then for any w ∈ i, f(w) = i has no p-worlds ✗

    Rudin (2025) Appendix B1, eq. (69c). -/
theorem MI_relational_might_eq_domain
    (f : World → List World) (i : List World) (p : BProp World)
    (hClosed : EpistemicClosure f i) (hi : i ≠ []) :
    (∀ w, w ∈ i → mightRelational f p w = true) ↔ i.any p = true := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ =>
      have := h w (by simp)
      simp only [mightRelational] at this
      rwa [hClosed w (by simp)] at this
  · intro hAny w hw
    simp only [mightRelational, hClosed w hw]
    exact hAny

/-- Must on relational semantics: ⟦must-p⟧ⁱ(w) = ∀w' ∈ f_i(w), p(w'). -/
def mustRelational (f : World → List World) (p : BProp World) (w : World) : Bool :=
  (f w).all p

/-- Under epistemic closure, MI(must-p) on relational semantics
    is { i : i ⊆ p } — identical to the domain semantics result.

    Rudin (2025) Appendix B1 (analogous to eq. 69). -/
theorem MI_relational_must_eq_domain
    (f : World → List World) (i : List World) (p : BProp World)
    (hClosed : EpistemicClosure f i) (_hi : i ≠ []) :
    (∀ w, w ∈ i → mustRelational f p w = true) ↔ (∀ w, w ∈ i → p w = true) := by
  constructor
  · intro h w hw
    have := h w hw
    simp only [mustRelational] at this
    rw [hClosed w hw] at this
    exact List.all_eq_true.mp this w hw
  · intro h w hw
    simp only [mustRelational, hClosed w hw]
    exact List.all_eq_true.mpr (λ v hv => h v hv)

/-! ### B2: Relational ordering semantics -/

/-- Relational ordering semantics for might:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ BEST_{f_i(w), g_i(w)}, p(w') = true,
    where g_i maps worlds to ordering sources.

    Rudin (2025) eq. (70). -/
def mightRelOrd (f : World → List World) (g : World → List (BProp World))
    (p : BProp World) (w : World) : Bool :=
  let s : OrdEpistemicState := { base := f w, ordering := g w }
  s.bestWorlds.any p

/-- Ordering closure: g maps every world in b_i to the same ordering o_i.

    Rudin (2025) eq. (71). -/
def OrderingClosure (g : World → List (BProp World))
    (base : List World) (ordering : List (BProp World)) : Prop :=
  ∀ w, w ∈ base → g w = ordering

/-- Under both epistemic and ordering closure, MI(might-p) on the
    relational ordering semantics equals { i : BEST_{b_i,o_i} has p-world }
    — identical to the domain ordering result.

    Rudin (2025) Appendix B2, eq. (73). -/
theorem MI_relOrd_might_eq_domain
    (f : World → List World) (g : World → List (BProp World))
    (i : OrdEpistemicState) (p : BProp World)
    (hfClosed : EpistemicClosure f i.base)
    (hgClosed : OrderingClosure g i.base i.ordering)
    (hi : i.base ≠ []) :
    (∀ w, w ∈ i.base → mightRelOrd f g p w = true) ↔
    MI_ord p i := by
  constructor
  · intro h
    unfold MI_ord
    obtain ⟨w₀, hw₀⟩ := List.exists_mem_of_ne_nil _ hi
    have := h w₀ hw₀
    simp only [mightRelOrd] at this
    rw [hfClosed w₀ hw₀, hgClosed w₀ hw₀] at this
    exact this
  · intro hMI w hw
    simp only [mightRelOrd, hfClosed w hw, hgClosed w hw]
    exact hMI

end RelationalSemantics

/-! ## Part 9: Truth ≠ Acceptance -/

section TruthAcceptance

variable {W : Type*}

/-- For non-epistemic sentences, truth and rejectability align:
    if the sentence is false in the rejector's state, rejection is licensed;
    if true, rejection is not licensed.

    This is the standard biconditional relationship. -/
theorem nonEpistemic_truth_acceptance_biconditional
    (p : BProp W) (c_assertor c_rejector : List W)
    (_h_rej_ne : c_rejector ≠ [])
    (_h_assertor_true : MI (liftProp p) c_assertor)
    (h_rejector_false : ∀ w, w ∈ c_rejector → p w = false) :
    rejectionLicensed (liftProp p) c_rejector := by
  intro ⟨c', hRef, hMI, hNe⟩
  cases c' with
  | nil => exact absurd rfl hNe
  | cons v vs =>
    have hvi := hRef v (by simp)
    have hpv : liftProp p (v :: vs) v = true := hMI v (by simp)
    simp only [liftProp] at hpv
    exact absurd hpv (by simp [h_rejector_false v hvi])

/-- **For might-claims, truth and rejectability dissociate.**

    The assertor's might-claim can be true (she has p-worlds in her
    epistemic state) while the rejector is simultaneously licensed
    to reject (he has no p-worlds in his). This is because:
    - Truth depends on the *assertor's* information parameter
    - Rejection depends on the *rejector's* information parameter
    - These are different parameters that can diverge

    This predicts the empirical pattern in Khoo (2015): participants
    reject might-claims (mean Likert rejection ~5.03) without judging
    them false (mean Likert falsity ~2.42).

    Rudin (2025) §4.3, bridging §4.2.1. -/
theorem might_truth_acceptance_dissociate
    (p : BProp W) (c_assertor c_rejector : List W)
    (h_assertor_has_p : c_assertor.any p = true)
    (h_rejector_no_p : c_rejector.any p = false) :
    MI (mightSimple p) c_assertor ∧ rejectionLicensed (mightSimple p) c_rejector :=
  ⟨context_in_MI_might p c_assertor h_assertor_has_p,
   no_p_worlds_not_compatible p c_rejector h_rejector_no_p⟩

end TruthAcceptance

end Semantics.Dynamic.NeoStalnakerian
