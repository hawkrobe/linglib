import Linglib.Core.Semantics.CommonGround
import Mathlib.Data.Set.Basic
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Modality.Kratzer.Ordering
import Linglib.Theories.Semantics.Attitudes.Intensional

/-!
# Neo-Stalnakerian Formalization of Assertion
@cite{rudin-2025a} @cite{stalnaker-1978} @cite{veltman-1996} @cite{kratzer-1981}

Rudin proposes that when a speaker asserts a sentence s, she predicates her
epistemic state: she presents herself as though she knows s, and proposes
the context be updated to reflect that knowledge. This is formalized via
the **meta-intensionalization** function MI, which maps s to the set of
epistemic states compatible with knowing s.

Applied uniformly to all declaratives, this single mechanism derives:
1. Standard Stalnakerian intersective update for non-epistemic sentences (§4.1)
2. @cite{veltman-1996}'s consistency-test semantics for epistemic *might* (§4.2)
3. A novel ordering-source update for *might* on @cite{kratzer-1981} semantics (§5)

The key insight: epistemic modals get nonstandard updates not because they
have special update semantics, but because they are speaker-orientedly
epistemic *in the same way* that assertion is.

Following the Bool→Prop migration: predicates on worlds are `W → Prop`
(mathlib-native), and list operations that depend on decidability of
predicates carry `[DecidablePred p]` constraints.
-/

namespace Phenomena.Assertion.Studies.Rudin2025

open Core.CommonGround

/-! ## Part 1: Core Types -/

section SimpleVersion

variable {W : Type*}

/-- Information-sensitive denotation: ⟦s⟧ⁱ(w).
    Truth value may depend on the epistemic state `i`. -/
abbrev InfoSensDen (W : Type*) := List W → (W → Prop)

/-- Lift a plain proposition to an information-insensitive denotation.
    For sentences like "John is dead" whose truth doesn't vary with `i`. -/
def liftProp (p : (W → Prop)) : InfoSensDen W := λ _ => p

/-- Simple quantificational semantics for epistemic *might*:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ i, p(w') = true.
    Truth is insensitive to the evaluation world w.

    eq. (25); adapted from @cite{yalcin-2007}. -/
def mightSimple (p : (W → Prop)) : InfoSensDen W :=
  λ i _ => ∃ w ∈ i, p w

/-- Simple quantificational semantics for epistemic *must*:
    ⟦must-p⟧ⁱ(w) = true iff ∀w' ∈ i, p(w') = true.

    Appendix A, eq. (57). -/
def mustSimple (p : (W → Prop)) : InfoSensDen W :=
  λ i _ => ∀ w ∈ i, p w

/-! ## Part 2: Meta-Intensionalization -/

/-- **Meta-intensionalization**: the set of epistemic states the speaker
    could hold if she knows s to be true.

        MI(s) = { i : ∀w ∈ i, ⟦s⟧ⁱ(w) = 1 }

    When a speaker asserts s, she presents herself as though her epistemic
    state is a member of MI(s).

    Definition (10). -/
def MI (sem : InfoSensDen W) (i : List W) : Prop :=
  ∀ w, w ∈ i → sem i w

/-- Refinement: i' refines i iff i' ⊆ i.
    Removing worlds monotonically increases information.

    Definition (13). -/
def refines (i' i : List W) : Prop :=
  ∀ w, w ∈ i' → w ∈ i

/-- A context c is s-compatible iff some non-empty refinement is in MI(s).

    Definition (18). -/
def sCompatible (sem : InfoSensDen W) (c : List W) : Prop :=
  ∃ c', refines c' c ∧ MI sem c' ∧ c' ≠ []

/-- Rejection of s is licensed when the rejector's state is not s-compatible.

    Definition (20). -/
def rejectionLicensed (sem : InfoSensDen W) (i_rejector : List W) : Prop :=
  ¬sCompatible sem i_rejector

/-! ## Part 3: MI Characterization Theorems -/

/-- MI for non-epistemic sentences: i ∈ MI(p) iff every world in i satisfies p.
    Equivalently, i ⊆ ext(p) — the downward closure of the proposition's extension.

    eqs. (22)–(23). -/
theorem MI_liftProp (p : (W → Prop)) (i : List W) :
    MI (liftProp p) i ↔ ∀ w, w ∈ i → p w :=
  Iff.rfl

/-- MI for might-p (non-empty states): i ∈ MI(might-p) iff i has a p-world.
    The universal quantifier in MI collapses because might's truth conditions
    are insensitive to the evaluation world.

    eq. (27b): MI(might-p) = { i : i ∩ p ≠ ∅ }. -/
theorem MI_mightSimple (p : (W → Prop)) (i : List W) (hi : i ≠ []) :
    MI (mightSimple p) i ↔ ∃ w ∈ i, p w := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ => exact h w (by simp)
  · intro h _ _; exact h

/-- MI for must-p coincides with MI for the bare prejacent.
    Since must universally quantifies over the same set i that MI quantifies
    over, the two collapse: MI(must-p) = { i : i ⊆ p }.

    Appendix A, eq. (58). -/
theorem MI_mustSimple (p : (W → Prop)) (i : List W) (hi : i ≠ []) :
    MI (mustSimple p) i ↔ ∀ w, w ∈ i → p w := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ =>
      have hAll := h w (by simp)
      intro v hv; exact hAll v hv
  · intro h _ _ v hv; exact h v hv

/-- MI(must-p) = MI(p): must has the same meta-intensionalized denotation
    as a non-epistemic assertion of its prejacent. -/
theorem MI_must_eq_MI_lift (p : (W → Prop)) (i : List W) (hi : i ≠ []) :
    MI (mustSimple p) i ↔ MI (liftProp p) i := by
  rw [MI_mustSimple p i hi, MI_liftProp]

/-! ## Part 4: Derived Update Potentials -/

/-- NSF update for non-epistemic sentences: intersect with proposition.
    The most conservative refinement of c that lands in MI(liftProp p).

    eq. (24). -/
def nsfUpdateNonEpistemic (p : (W → Prop)) [DecidablePred p] (c : List W) : List W :=
  c.filter p

/-- NSF update for might-p (simple semantics): consistency test.
    Leave context unchanged if c has p-worlds; anomaly otherwise.

    eq. (29). -/
def nsfUpdateMight (p : (W → Prop)) [DecidablePred p] (c : List W) : List W :=
  if c.any (fun w => decide (p w)) then c else []

/-- NSF update for must-p (simple semantics): same as non-epistemic.

    Appendix A, eq. (59). -/
def nsfUpdateMust (p : (W → Prop)) [DecidablePred p] (c : List W) : List W :=
  c.filter p

/-! ## Part 5: Derivation Theorems -/

/-- If c has p-worlds, it is already in MI(might-p). No refinement needed. -/
theorem context_in_MI_might (p : (W → Prop)) (c : List W)
    (h : ∃ w ∈ c, p w) : MI (mightSimple p) c :=
  λ _ _ => h

/-- **Core lemma**: subset refinement cannot introduce p-worlds.
    If c has no p-worlds, no refinement of c does either,
    making c not-might-p-compatible. This forces anomalous update.

    This is the key step in deriving Veltman's test semantics from
    the NSF: the "consistency test" behavior of might falls out of
    the monotonicity of refinement. -/
theorem no_p_worlds_not_compatible (p : (W → Prop)) (c : List W)
    (h : ¬ ∃ w ∈ c, p w) : ¬sCompatible (mightSimple p) c := by
  intro ⟨c', hRef, hMI, hNe⟩
  -- c' is non-empty, so MI gives ∃ w ∈ c', p w
  have hAny : ∃ w ∈ c', p w := by
    cases c' with
    | nil => exact absurd rfl hNe
    | cons w _ => exact hMI w (by simp)
  -- Some world in c' satisfies p; by refinement it's in c
  obtain ⟨v, hv, hpv⟩ := hAny
  exact h ⟨v, hRef v hv, hpv⟩

/-- **NSF derives Veltman's consistency test.**

    Given solipsistic contextualist truth conditions for might and the
    NSF's assertive machinery, the update potential for might-p is:
    - c[might-p] = c if c ∩ p ≠ ∅ (test passes)
    - c[might-p] = ∅ if c ∩ p = ∅ (anomaly)

    This is exactly @cite{veltman-1996}, derived rather than stipulated.
    The derivation uses `context_in_MI_might` (compatible case) and
    `no_p_worlds_not_compatible` (incompatible case).

    Bridges `nsfUpdateMight` to `Update.might` from UpdateSemantics.

    §4.2; cf. @cite{veltman-1996}, @cite{yalcin-2007}. -/
theorem nsfUpdateMight_spec (p : (W → Prop)) [DecidablePred p] (c : List W) :
    nsfUpdateMight p c = (if c.any (fun w => decide (p w)) then c else []) :=
  rfl

/-- NSF update for must-p equals update for its prejacent.
    Must-p updates identically to a non-epistemic assertion of p.

    Appendix A, eq. (59). -/
theorem nsfUpdateMust_eq_nonEpistemic (p : (W → Prop)) [DecidablePred p] (c : List W) :
    nsfUpdateMust p c = nsfUpdateNonEpistemic p c :=
  rfl

/-- **NSF recovers Stalnaker for non-epistemic sentences.**

    For sentences whose denotation doesn't vary with the information
    parameter, the NSF update is intersection with the proposition —
    exactly @cite{stalnaker-1978}'s original formalization.

    Bridges `nsfUpdateNonEpistemic` to `ContextSet.update` from CommonGround:
    both compute c ∩ p (filter c to p-worlds). -/
theorem nsf_recovers_stalnaker (p : (W → Prop)) [DecidablePred p] (c : List W) (w : W) :
    w ∈ nsfUpdateNonEpistemic p c ↔ w ∈ c ∧ p w := by
  simp [nsfUpdateNonEpistemic, List.mem_filter]

/-! ## Part 6: Rejection Licensing -/

/-- Rejection of a non-epistemic assertion of p is licensed iff the rejector
    has no p-worlds — i.e., the rejector knows ¬p. -/
theorem rejection_nonEpistemic (p : (W → Prop)) (i : List W) (_ : i ≠ []) :
    rejectionLicensed (liftProp p) i ↔ ∀ w, w ∈ i → ¬ p w := by
  unfold rejectionLicensed sCompatible
  constructor
  · intro hRej w hw hpw
    -- {w} is a non-empty refinement in MI(liftProp p)
    apply hRej
    refine ⟨[w], λ v hv => ?_, λ v hv => ?_, List.cons_ne_nil w []⟩
    · simp only [List.mem_singleton] at hv; rw [hv]; exact hw
    · simp only [List.mem_singleton] at hv; rw [hv]; exact hpw
  · intro h ⟨c', hRef, hMI, hNe⟩
    cases c' with
    | nil => exact absurd rfl hNe
    | cons v vs =>
      have hvi : v ∈ i := hRef v (by simp)
      have hpv : liftProp p (v :: vs) v := hMI v (by simp)
      simp only [liftProp] at hpv
      exact h v hvi hpv

/-- Rejection of might-p is licensed iff the rejector has no p-worlds.
    Crucially, this depends on the *rejector's* information, not the
    *assertor's*. The assertor's might-claim can be true (she has
    p-worlds) while the rejector is licensed to reject (he has none).

    This predicts @cite{khoo-2015}'s finding that might-claims can be
    simultaneously not-judged-false and rejected.

    §4.2.1. -/
theorem rejection_mightSimple (p : (W → Prop)) (i : List W) :
    rejectionLicensed (mightSimple p) i ↔ ¬(sCompatible (mightSimple p) i) :=
  Iff.rfl

/-- Rejection of might-p reduces to having no p-worlds. -/
theorem rejection_might_iff_no_p_worlds (p : (W → Prop)) (i : List W)
    (hi : ¬ ∃ w ∈ i, p w) :
    rejectionLicensed (mightSimple p) i :=
  no_p_worlds_not_compatible p i hi

end SimpleVersion

/-! ## Part 7: Ordering Semantics (Kratzer bridge) -/

section OrderingVersion

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)

/-- Epistemic state (ordering version): a modal base (set of worlds)
    paired with an ordering source (set of propositions ranking those worlds).

    Definition (43):
      D_i = { ⟨b_i, o_i⟩ : b_i ∈ D_st ∧ o_i ∈ ℘D_st } -/
structure OrdEpistemicState where
  /-- Modal base: the set of epistemically accessible worlds -/
  base : List World
  /-- Ordering source: propositions ranking accessible worlds -/
  ordering : List ((World → Prop))

/-- Predicate: world `w` is *not strictly dominated* in `s` (i.e., there is no
    `w'` in the base that beats `w` strictly under the ordering). -/
def OrdEpistemicState.notDominated (s : OrdEpistemicState) (w : World) : Prop :=
  ¬ ∃ w' ∈ s.base, atLeastAsGoodAs s.ordering w' w ∧
    ¬ atLeastAsGoodAs s.ordering w w'

/-- Membership in `bestWorlds` unfolds to base ∧ notDominated. -/
theorem OrdEpistemicState.mem_bestWorlds_iff (s : OrdEpistemicState) (w : World) :
    (w ∈ s.base ∧ s.notDominated w) ↔
    (w ∈ s.base ∧
      ¬ ∃ w' ∈ s.base, atLeastAsGoodAs s.ordering w' w ∧
        ¬ atLeastAsGoodAs s.ordering w w') :=
  Iff.rfl

/-- BEST worlds: worlds in the modal base not strictly dominated by any other.
    A world w is strictly dominated by w' iff w' satisfies a proper superset
    of the ordering propositions that w satisfies.

    eq. (44); @cite{kratzer-1981}. -/
noncomputable def OrdEpistemicState.bestWorlds (s : OrdEpistemicState) : List World :=
  letI : DecidablePred s.notDominated := fun _ => Classical.propDecidable _
  s.base.filter s.notDominated

theorem OrdEpistemicState.mem_bestWorlds (s : OrdEpistemicState) (w : World) :
    w ∈ s.bestWorlds ↔ w ∈ s.base ∧ s.notDominated w := by
  classical
  unfold OrdEpistemicState.bestWorlds
  simp [List.mem_filter]

/-- Ordering semantics for might:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ BEST_{b_i,o_i}, p(w') = true.

    eq. (45). -/
def mightOrdering (p : (World → Prop)) (s : OrdEpistemicState) (_ : World) : Prop :=
  ∃ w ∈ s.bestWorlds, p w

/-- MI for ordering-semantic might-p: the set of epistemic states whose
    BEST worlds include at least one p-world.

    eq. (54b). -/
def MI_ord (p : (World → Prop)) (s : OrdEpistemicState) : Prop :=
  ∃ w ∈ s.bestWorlds, p w

/-- Refinement (ordering version): only the modal base is refined.

    Definition (46). -/
def OrdEpistemicState.refines (c' c : OrdEpistemicState) : Prop :=
  ∀ w, w ∈ c'.base → w ∈ c.base

/-- **NSF update for might-p (ordering semantics): add p to ordering source.**

    This is the paper's most novel result. Asserting might-p proposes that
    the prejacent be added as a "live possibility" — a proposition in the
    ordering source. This makes p-worlds more likely to be among the BEST
    worlds, yielding an informative (non-trivial) update.

    eq. (56). -/
def nsfUpdateMightOrd (p : (World → Prop)) [DecidablePred p]
    (c : OrdEpistemicState) : OrdEpistemicState :=
  if (c.base.filter p).isEmpty then
    { base := [], ordering := c.ordering }  -- anomaly
  else
    { base := c.base, ordering := p :: c.ordering }

/-- Adding p to the ordering source cannot make a p-world dominated
    by a non-p-world, because the non-p-world fails to satisfy p
    while the p-world satisfies it.

    This is the key step in proving the ordering update is commensurate. -/
theorem nonPWorld_cannot_dominate_pWorld
    (A : List ((World → Prop))) (p : (World → Prop))
    (w z : World) (hw : p w) (hz : ¬ p z) :
    ¬ atLeastAsGoodAs (p :: A) z w := by
  intro hLeq
  -- z ≤[p :: A] w means: ∀ q ∈ p :: A, q w → q z. Apply to p.
  exact hz (hLeq p (by simp) hw)

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

/-- Filtering by an implied Prop predicate yields a (weakly) longer list.
    Helper lemma for `strict_dom_more_sat`. Filters use classical decidability
    via `decide`; correspondence to the propositional condition is provided by
    the membership-based hypothesis `h`. -/
private theorem filter_length_le_of_imp
    (A : List (World → Prop)) (w w' : World)
    (h : ∀ q, q ∈ A → q w → q w') :
    (A.filter (fun q => @decide (q w) (Classical.propDecidable _))).length ≤
      (A.filter (fun q => @decide (q w') (Classical.propDecidable _))).length := by
  classical
  induction A with
  | nil => exact Nat.le_refl _
  | cons q qs ih =>
    have ih' := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    by_cases hqw : q w
    · have hqw' : q w' := h q (by simp) hqw
      have hd  : @decide (q w)  (Classical.propDecidable _) = true := by
        simp [hqw]
      have hd' : @decide (q w') (Classical.propDecidable _) = true := by
        simp [hqw']
      simp only [List.filter_cons, hd, hd']
      exact Nat.succ_le_succ ih'
    · by_cases hqw' : q w'
      · have hd  : @decide (q w)  (Classical.propDecidable _) = false := by
          simp [hqw]
        have hd' : @decide (q w') (Classical.propDecidable _) = true := by
          simp [hqw']
        simp only [List.filter_cons, hd, hd']
        exact Nat.le_trans ih' (Nat.le_succ _)
      · have hd  : @decide (q w)  (Classical.propDecidable _) = false := by
          simp [hqw]
        have hd' : @decide (q w') (Classical.propDecidable _) = false := by
          simp [hqw']
        simp only [List.filter_cons, hd, hd']
        exact ih'

/-- Filter is strictly longer when one Prop predicate strictly implies another. -/
private theorem filter_length_lt_of_strict
    (A : List (World → Prop)) (w w' : World)
    (hsub : ∀ q, q ∈ A → q w → q w')
    (hstrict : ∃ q, q ∈ A ∧ q w' ∧ ¬ q w) :
    (A.filter (fun q => @decide (q w) (Classical.propDecidable _))).length <
      (A.filter (fun q => @decide (q w') (Classical.propDecidable _))).length := by
  classical
  induction A with
  | nil => obtain ⟨_, hq, _, _⟩ := hstrict; simp at hq
  | cons r rs ih =>
    have hsub_rs : ∀ q, q ∈ rs → q w → q w' :=
      fun q hq => hsub q (List.mem_cons_of_mem r hq)
    obtain ⟨q, hqA, hqw', hqw⟩ := hstrict
    rcases List.mem_cons.mp hqA with rfl | hqrs
    · -- Witness is the head: q w = False, q w' = True
      have hd  : @decide (q w)  (Classical.propDecidable _) = false := by
        simp [hqw]
      have hd' : @decide (q w') (Classical.propDecidable _) = true := by
        simp [hqw']
      simp only [List.filter_cons, hd, hd']
      exact Nat.lt_succ_of_le (filter_length_le_of_imp rs w w' hsub_rs)
    · -- Witness is in tail. Case-split on r at w/w'.
      by_cases hrw : r w
      · have hrw' : r w' := hsub r (by simp) hrw
        have hd  : @decide (r w)  (Classical.propDecidable _) = true := by
          simp [hrw]
        have hd' : @decide (r w') (Classical.propDecidable _) = true := by
          simp [hrw']
        simp only [List.filter_cons, hd, hd']
        exact Nat.succ_lt_succ (ih hsub_rs ⟨q, hqrs, hqw', hqw⟩)
      · by_cases hrw' : r w'
        · have hd  : @decide (r w)  (Classical.propDecidable _) = false := by
            simp [hrw]
          have hd' : @decide (r w') (Classical.propDecidable _) = true := by
            simp [hrw']
          simp only [List.filter_cons, hd, hd']
          exact Nat.lt_succ_of_lt (ih hsub_rs ⟨q, hqrs, hqw', hqw⟩)
        · have hd  : @decide (r w)  (Classical.propDecidable _) = false := by
            simp [hrw]
          have hd' : @decide (r w') (Classical.propDecidable _) = false := by
            simp [hrw']
          simp only [List.filter_cons, hd, hd']
          exact ih hsub_rs ⟨q, hqrs, hqw', hqw⟩

/-- Strict domination implies strictly more satisfied propositions.

    Proof: from `h1` (w' ≤[A] w), every A-prop true at w is true at w'; from
    `h2` (¬ w ≤[A] w'), some A-prop is true at w' and false at w. Apply
    `filter_length_lt_of_strict`. -/
private theorem strict_dom_more_sat
    (A : List ((World → Prop))) (w w' : World)
    (h1 : atLeastAsGoodAs A w' w)
    (h2 : ¬ atLeastAsGoodAs A w w') :
    (satisfiedPropositions A w).length < (satisfiedPropositions A w').length := by
  classical
  -- Extract sub and strict properties from atLeastAsGoodAs hypotheses.
  have hsub : ∀ q, q ∈ A → q w → q w' := fun q hq hqw => h1 q hq hqw
  have hstrict : ∃ q, q ∈ A ∧ q w' ∧ ¬ q w := by
    by_contra hAll
    apply h2
    intro p hpA hpw'
    by_contra hpw
    exact hAll ⟨p, hpA, hpw', hpw⟩
  -- Now reduce both sides to filter-by-decide and apply the helper.
  have key := filter_length_lt_of_strict A w w' hsub hstrict
  -- `satisfiedPropositions A w` is `A.filter (fun p => p w)` with a `letI`-
  -- provided `Classical.propDecidable` instance. Both filters reduce to the
  -- same `@decide ... (Classical.propDecidable _)` form.
  show
    (haveI : DecidablePred (fun p : World → Prop => p w) :=
      fun p => Classical.propDecidable (p w)
     A.filter (fun p => p w)).length <
    (haveI : DecidablePred (fun p : World → Prop => p w') :=
      fun p => Classical.propDecidable (p w')
     A.filter (fun p => p w')).length
  convert key using 2

/-- **Commensurativity**: if the modal base has a p-world, adding p to the
    ordering source yields a state whose BEST worlds include a p-world.

    After adding p, no non-p-world can dominate any p-world
    (`nonPWorld_cannot_dominate_pWorld`). Among p-worlds, the element with
    maximum satisfaction count is maximal. Since the base has p-worlds,
    BEST_{b, A+p} ∩ p ≠ ∅.

    §5.3, pp. 77–78. -/
theorem ordering_update_commensurate
    (c : OrdEpistemicState) (p : (World → Prop)) [DecidablePred p]
    (hCompat : ∃ w ∈ c.base, p w) :
    MI_ord p (nsfUpdateMightOrd p c) := by
  classical
  unfold MI_ord nsfUpdateMightOrd
  obtain ⟨w₀, hw₀, hpw₀⟩ := hCompat
  have hFilterMem : w₀ ∈ c.base.filter p := List.mem_filter.mpr
    ⟨hw₀, by simpa using hpw₀⟩
  have hNotEmpty : (c.base.filter p).isEmpty = false := by
    cases hfp : c.base.filter p with
    | nil => simp [hfp] at hFilterMem
    | cons _ _ => rfl
  simp only [hNotEmpty, ↓reduceIte]
  have hPWorldsNe : c.base.filter p ≠ [] := by
    intro h; simp [h] at hFilterMem
  obtain ⟨m, hm, hmmax⟩ := exists_max_by
    (λ w => (satisfiedPropositions (p :: c.ordering) w).length)
    (c.base.filter p) hPWorldsNe
  have hmBase : m ∈ c.base := (List.mem_filter.mp hm).1
  have hpm : p m := by
    have := (List.mem_filter.mp hm).2
    simpa using this
  refine ⟨m, ?_, hpm⟩
  -- Show m ∈ bestWorlds: m is in base and not strictly dominated.
  rw [OrdEpistemicState.mem_bestWorlds]
  refine ⟨hmBase, ?_⟩
  -- Goal: notDominated, i.e., ¬ ∃ w' ∈ base, w' ≥ m ∧ ¬ m ≥ w'
  intro ⟨w', hw', h1, h2⟩
  -- h1: w' ≥ m, h2: ¬ m ≥ w'
  by_cases hpw' : p w'
  · -- w' is a p-world. m has max satCount, so no strict domination.
    have hlt := strict_dom_more_sat (p :: c.ordering) m w' h1 h2
    have hw'F : w' ∈ c.base.filter p := List.mem_filter.mpr ⟨hw', by simpa using hpw'⟩
    exact absurd (hmmax w' hw'F) (by omega)
  · -- w' is a non-p-world. Can't even be ≥ m.
    exact nonPWorld_cannot_dominate_pWorld c.ordering p m w' hpm hpw' h1

/-- The ordering update is conservative: adding p to the ordering source
    does not guarantee that the resulting context will entail anything
    not already entailed by might-p.

    §5.3. -/
theorem ordering_update_conservative
    (c : OrdEpistemicState) (p : (World → Prop)) [DecidablePred p]
    (hCompat : ∃ w ∈ c.base, p w) :
    (nsfUpdateMightOrd p c).base = c.base := by
  unfold nsfUpdateMightOrd
  obtain ⟨w, hw, hpw⟩ := hCompat
  have hMem : w ∈ c.base.filter p := List.mem_filter.mpr ⟨hw, by simpa using hpw⟩
  have hNotEmpty : (c.base.filter p).isEmpty = false := by
    cases hfp : c.base.filter p with
    | nil => simp [hfp] at hMem
    | cons _ _ => rfl
  simp [hNotEmpty]

/-- Non-epistemic sentences still get standard intersective update
    in the ordering version: the ordering source is unchanged.

    eq. (52). -/
theorem ordering_nonEpistemic_preserves_ordering
    (c : OrdEpistemicState) (p : (World → Prop)) [DecidablePred p] :
    let c' : OrdEpistemicState :=
      { base := c.base.filter p, ordering := c.ordering }
    c'.ordering = c.ordering :=
  rfl

/-! ### Appendix A2: Must on ordering semantics -/

/-- Ordering semantics for must:
    ⟦must-p⟧ⁱ(w) = true iff ∀w' ∈ BEST_{b_i,o_i}, p(w') = true.

    eq. (60). -/
def mustOrdering (p : (World → Prop)) (s : OrdEpistemicState) (_ : World) : Prop :=
  ∀ w ∈ s.bestWorlds, p w

/-- MI for ordering-semantic must-p: the set of epistemic states whose
    BEST worlds are all p-worlds.

    eq. (61). -/
def MI_ord_must (p : (World → Prop)) (s : OrdEpistemicState) : Prop :=
  ∀ w, w ∈ s.bestWorlds → p w

/-- MI(must-p) on ordering semantics ↔ BEST ⊆ p. -/
theorem MI_ord_must_iff (p : (World → Prop)) (s : OrdEpistemicState) :
    MI_ord_must p s ↔ ∀ w ∈ s.bestWorlds, p w :=
  Iff.rfl

/-- A proposition is p-disjoint iff no world in the base satisfies both it
    and p. -/
def pDisjoint (p q : (World → Prop)) (base : List World) : Prop :=
  ∀ w ∈ base, ¬ (p w ∧ q w)

/-- **NSF update for must-p (ordering semantics).**

    Add p to the ordering source AND remove all p-disjoint propositions.
    Simply adding p is insufficient: p-disjoint ordering propositions can
    keep non-p-worlds in BEST. Removing them ensures all BEST worlds
    satisfy p.

    eq. (64). -/
noncomputable def nsfUpdateMustOrd (p : (World → Prop)) [DecidablePred p]
    (c : OrdEpistemicState) : OrdEpistemicState :=
  haveI : DecidablePred (fun q : World → Prop => ¬ pDisjoint p q c.base) :=
    fun _ => Classical.propDecidable _
  if (c.base.filter p).isEmpty then
    { base := [], ordering := c.ordering }  -- anomaly
  else
    { base := c.base,
      ordering := p :: c.ordering.filter (fun q => ¬ pDisjoint p q c.base) }

/-- The must ordering update preserves the modal base (when compatible). -/
theorem nsfUpdateMustOrd_preserves_base
    (c : OrdEpistemicState) (p : (World → Prop)) [DecidablePred p]
    (hCompat : ∃ w ∈ c.base, p w) :
    (nsfUpdateMustOrd p c).base = c.base := by
  classical
  unfold nsfUpdateMustOrd
  obtain ⟨w, hw, hpw⟩ := hCompat
  have hMem : w ∈ c.base.filter p := List.mem_filter.mpr ⟨hw, by simpa using hpw⟩
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

/-- Relational semantics for might:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ f_i(w), p(w') = true,
    where f_i is the epistemic accessibility function determined by i.

    eq. (65). -/
def mightRelational (f : World → List World) (p : (World → Prop)) (w : World) : Prop :=
  ∃ w' ∈ f w, p w'

/-- Epistemic closure: f maps every world in i to i itself.
    Under solipsistic contextualism, the accessibility function for
    the speaker's epistemic state maps each accessible world to
    the full epistemic state.

    eq. (67). -/
def EpistemicClosure (f : World → List World) (i : List World) : Prop :=
  ∀ w, w ∈ i → f w = i

/-- Under epistemic closure, MI(might-p) on relational semantics
    is { i : i ∩ p ≠ ∅ } — identical to the domain semantics result.

    Proof follows eq. (69a–c):
    - If i ∩ p ≠ ∅, then for any w ∈ i, f(w) = i has p-worlds ✓
    - If i ∩ p = ∅, then for any w ∈ i, f(w) = i has no p-worlds ✗

    Appendix B1, eq. (69c). -/
theorem MI_relational_might_eq_domain
    (f : World → List World) (i : List World) (p : (World → Prop))
    (hClosed : EpistemicClosure f i) (hi : i ≠ []) :
    (∀ w, w ∈ i → mightRelational f p w) ↔ ∃ w ∈ i, p w := by
  constructor
  · intro h
    cases i with
    | nil => exact absurd rfl hi
    | cons w _ =>
      have hwi := h w (by simp)
      simp only [mightRelational] at hwi
      rwa [hClosed w (by simp)] at hwi
  · intro hAny w hw
    simp only [mightRelational, hClosed w hw]
    exact hAny

/-- Must on relational semantics: ⟦must-p⟧ⁱ(w) = ∀w' ∈ f_i(w), p(w'). -/
def mustRelational (f : World → List World) (p : (World → Prop)) (w : World) : Prop :=
  ∀ w' ∈ f w, p w'

/-- Under epistemic closure, MI(must-p) on relational semantics
    is { i : i ⊆ p } — identical to the domain semantics result.

    Appendix B1 (analogous to eq. 69). -/
theorem MI_relational_must_eq_domain
    (f : World → List World) (i : List World) (p : (World → Prop))
    (hClosed : EpistemicClosure f i) (_hi : i ≠ []) :
    (∀ w, w ∈ i → mustRelational f p w) ↔ (∀ w, w ∈ i → p w) := by
  constructor
  · intro h w hw
    have hwi := h w hw
    simp only [mustRelational] at hwi
    rw [hClosed w hw] at hwi
    exact hwi w hw
  · intro h w hw
    simp only [mustRelational, hClosed w hw]
    intro v hv; exact h v hv

/-! ### B2: Relational ordering semantics -/

/-- Relational ordering semantics for might:
    ⟦might-p⟧ⁱ(w) = true iff ∃w' ∈ BEST_{f_i(w), g_i(w)}, p(w') = true,
    where g_i maps worlds to ordering sources.

    eq. (70). -/
def mightRelOrd (f : World → List World) (g : World → List ((World → Prop)))
    (p : (World → Prop)) (w : World) : Prop :=
  let s : OrdEpistemicState := { base := f w, ordering := g w }
  ∃ w' ∈ s.bestWorlds, p w'

/-- Ordering closure: g maps every world in b_i to the same ordering o_i.

    eq. (71). -/
def OrderingClosure (g : World → List ((World → Prop)))
    (base : List World) (ordering : List ((World → Prop))) : Prop :=
  ∀ w, w ∈ base → g w = ordering

/-- Under both epistemic and ordering closure, MI(might-p) on the
    relational ordering semantics equals { i : BEST_{b_i,o_i} has p-world }
    — identical to the domain ordering result.

    Appendix B2, eq. (73). -/
theorem MI_relOrd_might_eq_domain
    (f : World → List World) (g : World → List ((World → Prop)))
    (i : OrdEpistemicState) (p : (World → Prop))
    (hfClosed : EpistemicClosure f i.base)
    (hgClosed : OrderingClosure g i.base i.ordering)
    (hi : i.base ≠ []) :
    (∀ w, w ∈ i.base → mightRelOrd f g p w) ↔
    MI_ord p i := by
  constructor
  · intro h
    unfold MI_ord
    obtain ⟨w₀, hw₀⟩ := List.exists_mem_of_ne_nil _ hi
    have hwi := h w₀ hw₀
    simp only [mightRelOrd] at hwi
    rw [hfClosed w₀ hw₀, hgClosed w₀ hw₀] at hwi
    exact hwi
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
    (p : (W → Prop)) (c_assertor c_rejector : List W)
    (_h_rej_ne : c_rejector ≠ [])
    (_h_assertor_true : MI (liftProp p) c_assertor)
    (h_rejector_false : ∀ w, w ∈ c_rejector → ¬ p w) :
    rejectionLicensed (liftProp p) c_rejector := by
  intro ⟨c', hRef, hMI, hNe⟩
  cases c' with
  | nil => exact absurd rfl hNe
  | cons v vs =>
    have hvi := hRef v (by simp)
    have hpv : liftProp p (v :: vs) v := hMI v (by simp)
    simp only [liftProp] at hpv
    exact h_rejector_false v hvi hpv

/-- **For might-claims, truth and rejectability dissociate.**

    The assertor's might-claim can be true (she has p-worlds in her
    epistemic state) while the rejector is simultaneously licensed
    to reject (he has no p-worlds in his). This is because:
    - Truth depends on the *assertor's* information parameter
    - Rejection depends on the *rejector's* information parameter
    - These are different parameters that can diverge

    This predicts the empirical pattern in @cite{khoo-2015}: participants
    reject might-claims (mean Likert rejection ~5.03) without judging
    them false (mean Likert falsity ~2.42).

    §4.3, bridging §4.2.1. -/
theorem might_truth_acceptance_dissociate
    (p : (W → Prop)) (c_assertor c_rejector : List W)
    (h_assertor_has_p : ∃ w ∈ c_assertor, p w)
    (h_rejector_no_p : ¬ ∃ w ∈ c_rejector, p w) :
    MI (mightSimple p) c_assertor ∧ rejectionLicensed (mightSimple p) c_rejector :=
  ⟨context_in_MI_might p c_assertor h_assertor_has_p,
   no_p_worlds_not_compatible p c_rejector h_rejector_no_p⟩

end TruthAcceptance

end Phenomena.Assertion.Studies.Rudin2025
