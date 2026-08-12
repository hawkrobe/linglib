import Linglib.Logic.Modal.Kripke
import Linglib.Logic.Team.Algebra

/-!
# Bisimulation for modal team logics

This file defines bounded-depth world bisimulation between pointed
`KripkeModel`s and its lift to teams, and proves the transport lemmas
(image unions, team splits, witness teams) that each team-semantic
logic's invariance theorem consumes at its modal and split cases.
Nothing here mentions a formula type: each logic states its own
`bisim_invariant_eval` against its own evaluation, recursing through
these carrier lemmas.

## Main declarations

* `WorldBisim k M w M' w'`: bounded `k`-bisimulation between pointed worlds.
* `StateBisim k M s M' s'`: its lift to teams, by back/forth partnership.
* `StateBisim.biUnionAccess`, `StateBisim.splitPreserve`,
  `StateBisim.possWitness`: the transport lemmas.

## References

* [aloni-anttila-yang-2024] — Definitions 3.1 and 3.6, Lemma 3.7
* [vaananen-2008] — modal dependence logic, the (T8)/(T9) modal clauses
* [anttila-2025] — nonemptiness in team semantics
-/

namespace ModalLogic

variable {W W' Atom : Type*}

/-! ### World bisimulation -/

/-- Bounded-depth bisimulation between pointed worlds across two
    `KripkeModel`s (Definition 3.1 of [aloni-anttila-yang-2024]). At
    depth 0, requires only that atoms match. At depth `k+1`, additionally
    requires the standard back/forth conditions on accessibility relating
    depth-`k` bisimilar successors. -/
def WorldBisim : ℕ → KripkeModel W Atom → W → KripkeModel W' Atom → W' → Prop
  | 0,     M, w, M', w' => ∀ p : Atom, M.val p w = M'.val p w'
  | k + 1, M, w, M', w' =>
      (∀ p : Atom, M.val p w = M'.val p w') ∧
      (∀ v ∈ M.access w, ∃ v' ∈ M'.access w', WorldBisim k M v M' v') ∧
      (∀ v' ∈ M'.access w', ∃ v ∈ M.access w, WorldBisim k M v M' v')

/-- World bisimulation is reflexive at every depth. -/
theorem WorldBisim.refl (k : ℕ) (M : KripkeModel W Atom) (w : W) :
    WorldBisim k M w M w := by
  induction k generalizing w with
  | zero => intro _; rfl
  | succ k ih =>
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · intro v hv; exact ⟨v, hv, ih v⟩
    · intro v hv; exact ⟨v, hv, ih v⟩

/-- World bisimulation is symmetric (swap models). -/
theorem WorldBisim.symm {k : ℕ} {M : KripkeModel W Atom} {w : W}
    {M' : KripkeModel W' Atom} {w' : W'} :
    WorldBisim k M w M' w' → WorldBisim k M' w' M w := by
  induction k generalizing w w' with
  | zero => intro h p; exact (h p).symm
  | succ k ih =>
    intro h
    obtain ⟨hp, hforth, hback⟩ := h
    refine ⟨fun p => (hp p).symm, ?_, ?_⟩
    · intro v' hv'
      obtain ⟨v, hv, hbisim⟩ := hback v' hv'
      exact ⟨v, hv, ih hbisim⟩
    · intro v hv
      obtain ⟨v', hv', hbisim⟩ := hforth v hv
      exact ⟨v', hv', ih hbisim⟩

/-- Bisimilarity at depth `k+1` implies bisimilarity at depth `k`:
    higher depths are stricter. -/
theorem WorldBisim.mono_succ {k : ℕ} {M : KripkeModel W Atom} {w : W}
    {M' : KripkeModel W' Atom} {w' : W'} :
    WorldBisim (k + 1) M w M' w' → WorldBisim k M w M' w' := by
  induction k generalizing w w' with
  | zero =>
    intro h; exact h.1
  | succ n ih =>
    intro h
    obtain ⟨hp, hforth, hback⟩ := h
    refine ⟨hp, ?_, ?_⟩
    · intro v hv
      obtain ⟨v', hv', hbisim⟩ := hforth v hv
      exact ⟨v', hv', ih hbisim⟩
    · intro v' hv'
      obtain ⟨v, hv, hbisim⟩ := hback v' hv'
      exact ⟨v, hv, ih hbisim⟩

/-- Bisimilarity is monotone in depth: `m ≤ n → WorldBisim n → WorldBisim m`. -/
theorem WorldBisim.mono_le {m n : ℕ} (hmn : m ≤ n)
    {M : KripkeModel W Atom} {w : W} {M' : KripkeModel W' Atom} {w' : W'} :
    WorldBisim n M w M' w' → WorldBisim m M w M' w' := by
  induction hmn with
  | refl => exact id
  | step _ ih => exact fun h => ih h.mono_succ

/-! ### State bisimulation -/

/-- State bisimulation (Definition 3.6 of [aloni-anttila-yang-2024]):
    every world in `s` is `k`-bisimilar to some world in `s'`, and every
    world in `s'` is `k`-bisimilar to some world in `s`. Lifts world
    bisimulation from points to teams. -/
def StateBisim (k : ℕ) (M : KripkeModel W Atom) (s : Finset W)
    (M' : KripkeModel W' Atom) (s' : Finset W') : Prop :=
  (∀ w ∈ s, ∃ w' ∈ s', WorldBisim k M w M' w') ∧
  (∀ w' ∈ s', ∃ w ∈ s, WorldBisim k M w M' w')

theorem StateBisim.refl (k : ℕ) (M : KripkeModel W Atom) (s : Finset W) :
    StateBisim k M s M s :=
  ⟨fun w hw => ⟨w, hw, WorldBisim.refl k M w⟩,
   fun w hw => ⟨w, hw, WorldBisim.refl k M w⟩⟩

theorem StateBisim.symm {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'} :
    StateBisim k M s M' s' → StateBisim k M' s' M s :=
  fun ⟨hforth, hback⟩ =>
    ⟨fun w' hw' => let ⟨w, hw, hb⟩ := hback w' hw'; ⟨w, hw, hb.symm⟩,
     fun w hw => let ⟨w', hw', hb⟩ := hforth w hw; ⟨w', hw', hb.symm⟩⟩

theorem StateBisim.mono_succ {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'} :
    StateBisim (k + 1) M s M' s' → StateBisim k M s M' s' :=
  fun ⟨hforth, hback⟩ =>
    ⟨fun w hw => let ⟨w', hw', hb⟩ := hforth w hw; ⟨w', hw', hb.mono_succ⟩,
     fun w' hw' => let ⟨w, hw, hb⟩ := hback w' hw'; ⟨w, hw, hb.mono_succ⟩⟩

theorem StateBisim.mono_le {m n : ℕ} (hmn : m ≤ n)
    {M : KripkeModel W Atom} {s : Finset W} {M' : KripkeModel W' Atom}
    {s' : Finset W'} :
    StateBisim n M s M' s' → StateBisim m M s M' s' := by
  induction hmn with
  | refl => exact id
  | step _ ih => exact fun h => ih h.mono_succ

/-! ### Helpers for the invariance theorems -/

/-- World bisimilarity at any depth preserves atom valuations. -/
theorem WorldBisim.val_eq {k : ℕ} {M : KripkeModel W Atom} {w : W}
    {M' : KripkeModel W' Atom} {w' : W'}
    (h : WorldBisim k M w M' w') (p : Atom) :
    M.val p w = M'.val p w' :=
  match k, h with
  | 0, h => h p
  | _ + 1, ⟨h, _, _⟩ => h p

/-- World bisim at depth `k+1` yields state bisim of the accessibility
    images at depth `k` — the singleton form of Lemma 3.7(i). -/
theorem WorldBisim.accessStateBisim {k : ℕ} {M : KripkeModel W Atom} {w : W}
    {M' : KripkeModel W' Atom} {w' : W'}
    (h : WorldBisim (k + 1) M w M' w') :
    StateBisim k M (M.access w) M' (M'.access w') :=
  ⟨fun v hv => h.2.1 v hv, fun v' hv' => h.2.2 v' hv'⟩

/-- State bisim preserves nonemptiness. -/
theorem StateBisim.nonempty_iff {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') : s.Nonempty ↔ s'.Nonempty :=
  ⟨fun ⟨w, hw⟩ => let ⟨w', hw', _⟩ := h.1 w hw; ⟨w', hw'⟩,
   fun ⟨w', hw'⟩ => let ⟨w, hw, _⟩ := h.2 w' hw'; ⟨w, hw⟩⟩

/-- State bisim preserves emptiness. -/
theorem StateBisim.eq_empty_iff {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') : s = ∅ ↔ s' = ∅ := by
  simp only [← Finset.not_nonempty_iff_eq_empty, h.nonempty_iff]

/-- Given `s ⇌_k s'` and a sub-team `t ⊆ s`, there is a sub-team
    `t' ⊆ s'` with `t ⇌_k t'`; non-emptiness transfers. -/
theorem StateBisim.exists_image_subset {k : ℕ} {M : KripkeModel W Atom}
    {s t : Finset W} {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') (hsub : t ⊆ s) :
    ∃ t' : Finset W', t' ⊆ s' ∧ (t.Nonempty → t'.Nonempty) ∧
      StateBisim k M t M' t' := by
  classical
  let t' : Finset W' :=
    s'.filter (fun w' => ∃ w ∈ t, WorldBisim k M w M' w')
  refine ⟨t', ?_, ?_, ?_, ?_⟩
  · intro w' hw'; exact (Finset.mem_filter.mp hw').1
  · rintro ⟨w, hw⟩
    obtain ⟨w', hw', hbisim⟩ := h.1 w (hsub hw)
    exact ⟨w', Finset.mem_filter.mpr ⟨hw', w, hw, hbisim⟩⟩
  · intro w hw
    obtain ⟨w', hw', hbisim⟩ := h.1 w (hsub hw)
    exact ⟨w', Finset.mem_filter.mpr ⟨hw', w, hw, hbisim⟩, hbisim⟩
  · intro w' hw'
    obtain ⟨_, w, hw, hbisim⟩ := Finset.mem_filter.mp hw'
    exact ⟨w, hw, hbisim⟩

/-! ### Lemma 3.7: state bisimulation preserves modal step and team splits -/

variable [DecidableEq W] [DecidableEq W']

/-- Lemma 3.7(i): state bisim at depth `k+1` yields state bisim of the
    unions of accessibility images at depth `k`. -/
theorem StateBisim.biUnionAccess {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim (k + 1) M s M' s') :
    StateBisim k M (s.biUnion M.access) M' (s'.biUnion M'.access) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    obtain ⟨w', hw', hbw⟩ := h.1 w hw
    obtain ⟨v', hv', hbv⟩ := hbw.accessStateBisim.1 v hvw
    exact ⟨v', Finset.mem_biUnion.mpr ⟨w', hw', hv'⟩, hbv⟩
  · intro v' hv'
    rw [Finset.mem_biUnion] at hv'
    obtain ⟨w', hw', hvw'⟩ := hv'
    obtain ⟨w, hw, hbw⟩ := h.2 w' hw'
    obtain ⟨v, hv, hbv⟩ := hbw.accessStateBisim.2 v' hvw'
    exact ⟨v, Finset.mem_biUnion.mpr ⟨w, hw, hv⟩, hbv⟩

/-- Lemma 3.7(ii): state bisim preserves binary team splits. Given
    `s = t ∪ u` and `s ⇌_k s'`, there are `t'`, `u'` with `s' = t' ∪ u'`,
    `t ⇌_k t'`, and `u ⇌_k u'`. -/
theorem StateBisim.splitPreserve {k : ℕ} {M : KripkeModel W Atom}
    {s t u : Finset W} {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') (hsplit : Team.splitsAs s t u)
    (htsub : t ⊆ s) (husub : u ⊆ s) :
    ∃ t' u' : Finset W',
      Team.splitsAs s' t' u' ∧
      StateBisim k M t M' t' ∧ StateBisim k M u M' u' := by
  classical
  let t' : Finset W' := s'.filter (fun w' => ∃ w ∈ t, WorldBisim k M w M' w')
  let u' : Finset W' := s'.filter (fun w' => ∃ w ∈ u, WorldBisim k M w M' w')
  refine ⟨t', u', ?_, ?_, ?_⟩
  · apply Finset.Subset.antisymm
    · intro w' hw'
      rcases Finset.mem_union.mp hw' with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    · intro w' hw'
      obtain ⟨w, hw, hbisim⟩ := h.2 w' hw'
      have hwtu : w ∈ t ∪ u := hsplit ▸ hw
      rcases Finset.mem_union.mp hwtu with hwt | hwu
      · refine Finset.mem_union.mpr (Or.inl ?_)
        exact Finset.mem_filter.mpr ⟨hw', w, hwt, hbisim⟩
      · refine Finset.mem_union.mpr (Or.inr ?_)
        exact Finset.mem_filter.mpr ⟨hw', w, hwu, hbisim⟩
  · refine ⟨?_, ?_⟩
    · intro w hw
      obtain ⟨w', hw', hbisim⟩ := h.1 w (htsub hw)
      refine ⟨w', ?_, hbisim⟩
      exact Finset.mem_filter.mpr ⟨hw', w, hw, hbisim⟩
    · intro w' hw'
      obtain ⟨_, w, hw, hbisim⟩ := Finset.mem_filter.mp hw'
      exact ⟨w, hw, hbisim⟩
  · refine ⟨?_, ?_⟩
    · intro w hw
      obtain ⟨w', hw', hbisim⟩ := h.1 w (husub hw)
      refine ⟨w', ?_, hbisim⟩
      exact Finset.mem_filter.mpr ⟨hw', w, hw, hbisim⟩
    · intro w' hw'
      obtain ⟨_, w, hw, hbisim⟩ := Finset.mem_filter.mp hw'
      exact ⟨w, hw, hbisim⟩

/-! ### Single-witness modal step (Väänänen-style ◇) -/

/-- Single-witness team transport: given `s ⇌_{k+1} s'` and a witness team
    `Y` inside the image union that every world in `s` reaches, there is a
    `Y'` that every world in `s'` reaches, with `Y ⇌_k Y'` — the Lemma 3.7
    analogue for the single-witness `◇`-support clause. -/
theorem StateBisim.possWitness {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim (k + 1) M s M' s') {Y : Finset W}
    (hYsub : Y ⊆ s.biUnion M.access)
    (hwit : ∀ w ∈ s, ∃ y ∈ Y, y ∈ M.access w) :
    ∃ Y' : Finset W', Y' ⊆ s'.biUnion M'.access ∧
      (∀ w' ∈ s', ∃ y' ∈ Y', y' ∈ M'.access w') ∧
      StateBisim k M Y M' Y' := by
  classical
  let Y' : Finset W' :=
    (s'.biUnion M'.access).filter (fun y' => ∃ y ∈ Y, WorldBisim k M y M' y')
  refine ⟨Y', ?_, ?_, ?_, ?_⟩
  · intro y' hy'; exact (Finset.mem_filter.mp hy').1
  · -- every w' ∈ s' reaches some y' ∈ Y'
    intro w' hw'
    obtain ⟨w, hw, hbw⟩ := h.2 w' hw'
    obtain ⟨y, hyY, hyw⟩ := hwit w hw
    obtain ⟨y', hy'w', hby⟩ := hbw.2.1 y hyw
    have hy'mem : y' ∈ Y' :=
      Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w', hw', hy'w'⟩, y, hyY, hby⟩
    exact ⟨y', hy'mem, hy'w'⟩
  · -- forth: every y ∈ Y has a partner in Y'
    intro y hyY
    obtain ⟨w, hw, hyw⟩ := Finset.mem_biUnion.mp (hYsub hyY)
    obtain ⟨w', hw', hbw⟩ := h.1 w hw
    obtain ⟨y', hy'w', hby⟩ := hbw.2.1 y hyw
    exact ⟨y', Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨w', hw', hy'w'⟩, y, hyY, hby⟩, hby⟩
  · -- back: every y' ∈ Y' has a partner in Y
    intro y' hy'
    obtain ⟨_, y, hyY, hby⟩ := Finset.mem_filter.mp hy'
    exact ⟨y, hyY, hby⟩

end ModalLogic
