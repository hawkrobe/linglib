import Linglib.Core.Logic.Modal.Kripke
import Linglib.Core.Logic.Team.Algebra

/-!
# Bisimulation for modal team logics

[aloni-anttila-yang-2024] [anttila-2025] [vaananen-2008]

Bisimulation is the canonical equivalence relation on Kripke models that
abstracts away from the choice of world-carrier and identifies models no
modal formula can distinguish. This file provides the **carrier-level**
bisimulation substrate shared by every team-semantic modal logic in
`Core/Logic/Modal/`: bounded-depth world bisimulation (Definition 3.1 of
[aloni-anttila-yang-2024]), state bisimulation lifted to teams
(Definition 3.6), and the structural lemmas (Lemma 3.7) that each logic's
*invariance theorem* (BSML Theorem 3.8, the MDL analogue, …) consumes.

Nothing here mentions a `Formula` type or an `eval` relation — everything
is stated over the bare `KripkeModel` carrier (`access` + `val`). Each
logic states its own `bisim_invariant_eval` against its own evaluation,
recursing through these carrier lemmas at the modal step. This file is the
genus-level home the per-logic invariance proofs were extracted to once a
second consumer (MDL) landed; see `Core/Logic/Modal/README.md`.

## Main declarations

* `WorldBisim k M w M' w'` — bounded `k`-bisimulation between pointed worlds.
* `StateBisim k M s M' s'` — state bisimulation lifting it to teams.
* `WorldBisim.refl` / `.symm` / `.mono_succ` / `.mono_le` and the `StateBisim`
  analogues — the equivalence-relation and depth-monotonicity properties.
* `WorldBisim.val_eq`, `WorldBisim.accessStateBisim` — valuation and
  accessibility-image transfer.
* `StateBisim.eq_empty_iff`, `StateBisim.nonempty_iff` — emptiness transfer.
* `StateBisim.accessImage` — Lemma 3.7(i): per-world accessibility-image bisim.
* `StateBisim.splitPreserve` — Lemma 3.7(ii): team-split preservation.
* `StateBisim.exists_image_subset` — sub-team transport (BSML's per-world ◇).
* `StateBisim.biUnionAccess` — union-of-images preservation (MDL's anti-◇).
* `StateBisim.possWitness` — single-witness team transport (MDL's ◇-support).

## Implementation notes

`WorldBisim` recurses on `k`: base case is atom invariance, inductive case
adds back/forth on accessibility. The split- and witness-transport lemmas
(`splitPreserve`, `exists_image_subset`, `possWitness`) construct the
other-side team by `Finset.filter` over the bisim's existential witnesses,
using `Classical.choice` only inside pure-`Prop` existentials.
-/

namespace Core.Logic.Modal

variable {W W' : Type*} [DecidableEq W] [Fintype W] [DecidableEq W'] [Fintype W']
variable {Atom : Type*}

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
    StateBisim k M s M' s' → StateBisim k M' s' M s := by
  intro h
  obtain ⟨hforth, hback⟩ := h
  refine ⟨?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, hbisim⟩ := hback w' hw'
    exact ⟨w, hw, hbisim.symm⟩
  · intro w hw
    obtain ⟨w', hw', hbisim⟩ := hforth w hw
    exact ⟨w', hw', hbisim.symm⟩

theorem StateBisim.mono_succ {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'} :
    StateBisim (k + 1) M s M' s' → StateBisim k M s M' s' := by
  intro h
  obtain ⟨hforth, hback⟩ := h
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨w', hw', hbisim⟩ := hforth w hw
    exact ⟨w', hw', hbisim.mono_succ⟩
  · intro w' hw'
    obtain ⟨w, hw, hbisim⟩ := hback w' hw'
    exact ⟨w, hw, hbisim.mono_succ⟩

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
    images at depth `k`. -/
theorem WorldBisim.accessStateBisim {k : ℕ} {M : KripkeModel W Atom} {w : W}
    {M' : KripkeModel W' Atom} {w' : W'}
    (h : WorldBisim (k + 1) M w M' w') :
    StateBisim k M (M.access w) M' (M'.access w') :=
  ⟨fun v hv => h.2.1 v hv, fun v' hv' => h.2.2 v' hv'⟩

/-- State bisim preserves emptiness: `s = ∅ ↔ s' = ∅`. The back/forth
    conditions force any worlds on one side to have partners on the
    other, so emptiness is mutually determined. -/
theorem StateBisim.eq_empty_iff {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') : s = ∅ ↔ s' = ∅ := by
  refine ⟨?_, ?_⟩
  · intro hs
    apply Finset.eq_empty_of_forall_notMem
    intro w' hw'
    obtain ⟨w, hw, _⟩ := h.2 w' hw'
    exact absurd hw (hs ▸ Finset.notMem_empty w)
  · intro hs'
    apply Finset.eq_empty_of_forall_notMem
    intro w hw
    obtain ⟨w', hw', _⟩ := h.1 w hw
    exact absurd hw' (hs' ▸ Finset.notMem_empty w')

/-- State bisim preserves nonemptiness. -/
theorem StateBisim.nonempty_iff {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') : s.Nonempty ↔ s'.Nonempty := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    obtain ⟨w', hw', _⟩ := h.1 w hw
    exact ⟨w', hw'⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨w, hw, _⟩ := h.2 w' hw'
    exact ⟨w, hw⟩

/-- Given `s ⇌_k s'` and a sub-team `t ⊆ s`, there exists a corresponding
    sub-team `t' ⊆ s'` such that `t ⇌_k t'`. Non-emptiness transfers.
    Used by the per-world `poss`-support case of BSML's invariance proof. -/
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

/-- Lemma 3.7(i) of [aloni-anttila-yang-2024]: at depth `k+1`, state
    bisim provides for each `w ∈ s` a witness `w' ∈ s'` such that the
    accessibility images `R[w]` and `R'[w']` are state-bisimilar at
    depth `k`. -/
theorem StateBisim.accessImage {k : ℕ} {M : KripkeModel W Atom} {s : Finset W}
    {M' : KripkeModel W' Atom} {s' : Finset W'} {w : W}
    (h : StateBisim (k + 1) M s M' s') (hw : w ∈ s) :
    ∃ w' ∈ s', StateBisim k M (M.access w) M' (M'.access w') := by
  obtain ⟨w', hw', hbisim⟩ := h.1 w hw
  obtain ⟨_, hforth, hback⟩ := hbisim
  refine ⟨w', hw', ?_, ?_⟩
  · intro v hv
    obtain ⟨v', hv', hbv⟩ := hforth v hv
    exact ⟨v', hv', hbv⟩
  · intro v' hv'
    obtain ⟨v, hv, hbv⟩ := hback v' hv'
    exact ⟨v, hv, hbv⟩

/-- Lemma 3.7(ii) of [aloni-anttila-yang-2024]: state bisim preserves
    binary team splits. Given `s = t ∪ u` and `s ⇌_k s'`, there exist
    `t', u' ⊆ s'` with `s' = t' ∪ u'`, `t ⇌_k t'`, and `u ⇌_k u'`.

    Constructed via classical choice over the bisim's existential
    witnesses: `t'` collects all of `s'`'s witnesses for `t`, and `u'`
    likewise for `u`. -/
theorem StateBisim.splitPreserve {k : ℕ} {M : KripkeModel W Atom}
    {s t u : Finset W} {M' : KripkeModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') (hsplit : Core.Logic.Team.splitsAs s t u)
    (htsub : t ⊆ s) (husub : u ⊆ s) :
    ∃ t' u' : Finset W',
      Core.Logic.Team.splitsAs s' t' u' ∧
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

/-! ### Single-relation modal step (Väänänen-style ◇)

The MDL modality uses the union of accessibility images (anti-support) and
a single witness team (support), rather than BSML's per-world sub-witness.
These two lemmas are the Lemma 3.7 analogues for that modality. -/

/-- State bisim at depth `k+1` preserves the **union of accessibility images**
    at depth `k`: `s.biUnion R ⇌_k s'.biUnion R'`. The MDL anti-`◇` clause
    ([vaananen-2008] (T9)) evaluates the inner formula on this union. -/
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

/-- **Single-witness team transport.** Given `s ⇌_{k+1} s'` and a witness team
    `Y ⊆ s.biUnion R` that every world in `s` reaches (`∀ w ∈ s, ∃ y ∈ Y ∩
    R[w]`), there is a corresponding `Y' ⊆ s'.biUnion R'` that every world in
    `s'` reaches, with `Y ⇌_k Y'`. This is the Lemma 3.7 analogue for the MDL
    `◇`-support clause ([vaananen-2008] (T8)). The `Y ⊆ s.biUnion R`
    hypothesis is supplied by the caller via downward closure (shrinking a raw
    witness to its reachable part). -/
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

end Core.Logic.Modal
