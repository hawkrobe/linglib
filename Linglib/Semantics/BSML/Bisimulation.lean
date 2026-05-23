import Linglib.Semantics.BSML.Defs

/-!
# Bisimulation for BSML

@cite{aloni-anttila-yang-2024} @cite{anttila-2025}

Bisimulation is the canonical equivalence relation on Kripke models that
abstracts away from the choice of world-carrier and identifies models no
modal formula can distinguish. This file provides the BSML-family
bisimulation substrate: bounded-depth world bisimulation (Definition 3.1
of @cite{aloni-anttila-yang-2024}), state bisimulation lifted to teams
(Definition 3.6), and the headline invariance theorem (Theorem 3.8) for
BSML's bilateral evaluation.

## Main declarations

* `WorldBisim k M w M' w'` — bounded `k`-bisimulation between pointed
  worlds, defined by recursion on `k` (atom invariance at depth 0; atom
  + back/forth on accessibility at higher depths).
* `StateBisim k M s M' s'` — state bisimulation: every world in `s` is
  `k`-bisimilar to a world in `s'` and vice versa.
* `BSMLFormula.modalDepth` — modal depth (page 9): atoms/NE are 0,
  `conj`/`disj` take max, `poss` increments.
* `WorldBisim.refl` / `.symm` / `.mono_succ` and the `StateBisim`
  analogues — equivalence-relation properties.
* `StateBisim.accessImage` — Lemma 3.7(i): state bisim at depth `k+1`
  preserves accessibility images at depth `k`.
* `StateBisim.splitPreserve` — Lemma 3.7(ii): state bisim preserves team
  splits (existence via classical choice).
* `bisim_invariant_eval` — Theorem 3.8 for BSML: `k`-bisimilar states
  agree on `eval` for all formulas of modal depth `≤ k`, for both
  polarities.

## Implementation notes

Bisimulation is recursive in `k`. `WorldBisim` uses Lean's definitional
recursion on `Nat`; the base case is atom invariance (`∀ p, M.val p w =
M'.val p w'`), and the inductive case adds back/forth on
`M.access w` / `M'.access w'`.

Lemma 3.7(ii) (split preservation) requires constructing witness
sub-teams on the other side; we use `Classical.choose` rather than
introducing a decidability assumption on bisimulation. The choice is
hidden behind a pure-Prop existential — consumers see only the existence
claim, not the chosen splits.

The bisim-invariance proof inducts on the formula, handling both
polarities (`eval M b φ s`) jointly at each step. The negation case
flips polarity without changing depth; the modal case uses Lemma 3.7(i)
to recurse at depth `k`. Conjunction and disjunction use Lemma 3.7(ii)
for the split-existential clauses (conj-antiSupport and disj-support).

## Todo

* Hennessy-Milner direction (Theorem 3.3): `k`-equivalence implies
  `k`-bisimilarity, via Hintikka formulas. Requires a finite atom set
  hypothesis (`[Fintype Atom]`) for the characteristic-formula
  construction. Deferred — Theorem 3.8 alone is enough for the
  expressive-completeness side of @cite{aloni-anttila-yang-2024} §3.
* Bisim invariance for `BSMLOr.eval` and `BSMLEmpty.eval`. Same shape
  with one new case each (`gdisj` is structurally like `support_conj` at
  the team level; `empt` reduces to support of the inner formula or `s
  = ∅`, both bisim-preserved).
-/

namespace Semantics.BSML

variable {W W' : Type*} [DecidableEq W] [Fintype W] [DecidableEq W'] [Fintype W']
variable {Atom : Type*}

/-! ### World bisimulation -/

/-- Bounded-depth bisimulation between pointed worlds across two
    `BSMLModel`s (Definition 3.1 of @cite{aloni-anttila-yang-2024}). At
    depth 0, requires only that atoms match. At depth `k+1`, additionally
    requires the standard back/forth conditions on accessibility
    relating depth-`k` bisimilar successors. -/
def WorldBisim : ℕ → BSMLModel W Atom → W → BSMLModel W' Atom → W' → Prop
  | 0,     M, w, M', w' => ∀ p : Atom, M.val p w = M'.val p w'
  | k + 1, M, w, M', w' =>
      (∀ p : Atom, M.val p w = M'.val p w') ∧
      (∀ v ∈ M.access w, ∃ v' ∈ M'.access w', WorldBisim k M v M' v') ∧
      (∀ v' ∈ M'.access w', ∃ v ∈ M.access w, WorldBisim k M v M' v')

/-- World bisimulation is reflexive at every depth. -/
theorem WorldBisim.refl (k : ℕ) (M : BSMLModel W Atom) (w : W) :
    WorldBisim k M w M w := by
  induction k generalizing w with
  | zero => intro _; rfl
  | succ k ih =>
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · intro v hv; exact ⟨v, hv, ih v⟩
    · intro v hv; exact ⟨v, hv, ih v⟩

/-- World bisimulation is symmetric (swap models). -/
theorem WorldBisim.symm {k : ℕ} {M : BSMLModel W Atom} {w : W}
    {M' : BSMLModel W' Atom} {w' : W'} :
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
theorem WorldBisim.mono_succ {k : ℕ} {M : BSMLModel W Atom} {w : W}
    {M' : BSMLModel W' Atom} {w' : W'} :
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
    {M : BSMLModel W Atom} {w : W} {M' : BSMLModel W' Atom} {w' : W'} :
    WorldBisim n M w M' w' → WorldBisim m M w M' w' := by
  induction hmn with
  | refl => exact id
  | step _ ih => exact fun h => ih h.mono_succ

/-! ### State bisimulation -/

/-- State bisimulation (Definition 3.6 of @cite{aloni-anttila-yang-2024}):
    every world in `s` is `k`-bisimilar to some world in `s'`, and every
    world in `s'` is `k`-bisimilar to some world in `s`. Lifts world
    bisimulation from points to teams. -/
def StateBisim (k : ℕ) (M : BSMLModel W Atom) (s : Finset W)
    (M' : BSMLModel W' Atom) (s' : Finset W') : Prop :=
  (∀ w ∈ s, ∃ w' ∈ s', WorldBisim k M w M' w') ∧
  (∀ w' ∈ s', ∃ w ∈ s, WorldBisim k M w M' w')

theorem StateBisim.refl (k : ℕ) (M : BSMLModel W Atom) (s : Finset W) :
    StateBisim k M s M s :=
  ⟨fun w hw => ⟨w, hw, WorldBisim.refl k M w⟩,
   fun w hw => ⟨w, hw, WorldBisim.refl k M w⟩⟩

theorem StateBisim.symm {k : ℕ} {M : BSMLModel W Atom} {s : Finset W}
    {M' : BSMLModel W' Atom} {s' : Finset W'} :
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

theorem StateBisim.mono_succ {k : ℕ} {M : BSMLModel W Atom} {s : Finset W}
    {M' : BSMLModel W' Atom} {s' : Finset W'} :
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
    {M : BSMLModel W Atom} {s : Finset W} {M' : BSMLModel W' Atom}
    {s' : Finset W'} :
    StateBisim n M s M' s' → StateBisim m M s M' s' := by
  induction hmn with
  | refl => exact id
  | step _ ih => exact fun h => ih h.mono_succ

/-! ### Helpers for the invariance theorem -/

/-- World bisimilarity at any depth preserves atom valuations. -/
theorem WorldBisim.val_eq {k : ℕ} {M : BSMLModel W Atom} {w : W}
    {M' : BSMLModel W' Atom} {w' : W'}
    (h : WorldBisim k M w M' w') (p : Atom) :
    M.val p w = M'.val p w' :=
  match k, h with
  | 0, h => h p
  | _ + 1, ⟨h, _, _⟩ => h p

/-- World bisim at depth `k+1` yields state bisim of the accessibility
    images at depth `k`. -/
theorem WorldBisim.accessStateBisim {k : ℕ} {M : BSMLModel W Atom} {w : W}
    {M' : BSMLModel W' Atom} {w' : W'}
    (h : WorldBisim (k + 1) M w M' w') :
    StateBisim k M (M.access w) M' (M'.access w') :=
  ⟨fun v hv => h.2.1 v hv, fun v' hv' => h.2.2 v' hv'⟩

/-- State bisim preserves emptiness: `s = ∅ ↔ s' = ∅`. The back/forth
    conditions force any worlds on one side to have partners on the
    other, so emptiness is mutually determined. -/
theorem StateBisim.eq_empty_iff {k : ℕ} {M : BSMLModel W Atom} {s : Finset W}
    {M' : BSMLModel W' Atom} {s' : Finset W'}
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
theorem StateBisim.nonempty_iff {k : ℕ} {M : BSMLModel W Atom} {s : Finset W}
    {M' : BSMLModel W' Atom} {s' : Finset W'}
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
    Used by the `poss`-support case of the bisim-invariance proof to
    transport witness sub-teams across models. -/
theorem StateBisim.exists_image_subset {k : ℕ} {M : BSMLModel W Atom}
    {s t : Finset W} {M' : BSMLModel W' Atom} {s' : Finset W'}
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

/-! ### Modal depth -/

/-- Modal depth of a `BSMLFormula` (page 9 of @cite{aloni-anttila-yang-2024}).
    Atoms and `NE` are 0; `neg` preserves depth; `conj` and `disj` take
    the max; `poss` increments. -/
def BSMLFormula.modalDepth : BSMLFormula Atom → ℕ
  | .atom _ => 0
  | .ne => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Lemma 3.7: state bisimulation preserves modal step and team splits -/

/-- Lemma 3.7(i) of @cite{aloni-anttila-yang-2024}: at depth `k+1`, state
    bisim provides for each `w ∈ s` a witness `w' ∈ s'` such that the
    accessibility images `R[w]` and `R'[w']` are state-bisimilar at
    depth `k`. -/
theorem StateBisim.accessImage {k : ℕ} {M : BSMLModel W Atom} {s : Finset W}
    {M' : BSMLModel W' Atom} {s' : Finset W'} {w : W}
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

/-- Lemma 3.7(ii) of @cite{aloni-anttila-yang-2024}: state bisim preserves
    binary team splits. Given `s = t ∪ u` and `s ⇌_k s'`, there exist
    `t', u' ⊆ s'` with `s' = t' ∪ u'`, `t ⇌_k t'`, and `u ⇌_k u'`.

    Constructed via classical choice over the bisim's existential
    witnesses: `t'` collects all of `s'`'s witnesses for `t`, and `u'`
    likewise for `u`. -/
theorem StateBisim.splitPreserve {k : ℕ} {M : BSMLModel W Atom}
    {s t u : Finset W} {M' : BSMLModel W' Atom} {s' : Finset W'}
    (h : StateBisim k M s M' s') (hsplit : Core.Logic.Team.splitsAs s t u)
    (htsub : t ⊆ s) (husub : u ⊆ s) :
    ∃ t' u' : Finset W',
      Core.Logic.Team.splitsAs s' t' u' ∧
      StateBisim k M t M' t' ∧ StateBisim k M u M' u' := by
  classical
  -- Define t' as the worlds in s' that are bisim-partners of some world in t.
  -- u' is the complement-within-s'.
  let t' : Finset W' := s'.filter (fun w' => ∃ w ∈ t, WorldBisim k M w M' w')
  let u' : Finset W' := s'.filter (fun w' => ∃ w ∈ u, WorldBisim k M w M' w')
  refine ⟨t', u', ?_, ?_, ?_⟩
  · -- t' ∪ u' = s'. ⊆ direction: each is a subset of s'. ⊇ direction:
    -- every w' ∈ s' has a bisim partner w ∈ s; w is in t or u by the split;
    -- so w' lands in t' or u'.
    apply Finset.Subset.antisymm
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
  · -- t ⇌_k t'. Forth: every w ∈ t has a bisim partner w' ∈ s' (via h),
    -- and w' ∈ t' by construction. Back: every w' ∈ t' has a bisim partner
    -- w by construction.
    refine ⟨?_, ?_⟩
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

/-! ### Theorem 3.8: bisimulation invariance for BSML -/

/-- **Theorem 3.8** of @cite{aloni-anttila-yang-2024} specialised to BSML:
    if `s ⇌_k s'` and `φ : BSMLFormula Atom` has modal depth `≤ k`, then
    `eval M b φ s ↔ eval M' b φ s'` for both polarities.

    Proved by structural induction on `φ`, with both polarities handled
    jointly at each step. The `neg` case flips polarity without changing
    depth; the `poss` case uses Lemma 3.7(i) to recurse at depth `k`;
    conjunction and disjunction use Lemma 3.7(ii) for the split-existential
    clauses (conj-antiSupport and disj-support). -/
theorem bisim_invariant_eval (φ : BSMLFormula Atom) :
    ∀ {k : ℕ}, φ.modalDepth ≤ k →
    ∀ {M : BSMLModel W Atom} {M' : BSMLModel W' Atom}
      {s : Finset W} {s' : Finset W'},
    StateBisim k M s M' s' →
    ∀ b : Bool, eval M b φ s ↔ eval M' b φ s' := by
  induction φ with
  | atom p =>
    intro k _ M M' s s' hbisim b
    -- For both polarities: each side of the iff uses the bisim partner's
    -- valuation, related by `WorldBisim.val_eq`.
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | ne =>
    intro k _ M M' s s' hbisim b
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    intro k hd M M' s s' hbisim b
    cases b
    · -- antiSupport (neg ψ) = support ψ
      exact ih hd hbisim true
    · -- support (neg ψ) = antiSupport ψ
      exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k :=
      le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k :=
      le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport (conj ψ₁ ψ₂): ∃ t u, splitsAs ∧ antiSupport ψ₁ t ∧ antiSupport ψ₂ u
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁,
               (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm false).mpr h₁
        · exact (ih₂ hd₂ hbu.symm false).mpr h₂
    · -- support (conj ψ₁ ψ₂) = support ψ₁ ∧ support ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mp h₁, (ih₂ hd₂ hbisim true).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mpr h₁, (ih₂ hd₂ hbisim true).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k :=
      le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k :=
      le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport (disj ψ₁ ψ₂) = antiSupport ψ₁ ∧ antiSupport ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · -- support (disj ψ₁ ψ₂): ∃ t u, splitsAs ∧ support ψ₁ t ∧ support ψ₂ u
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁,
               (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm true).mpr h₁
        · exact (ih₂ hd₂ hbu.symm true).mpr h₂
  | poss ψ ih =>
    intro k hd M M' s s' hbisim b
    -- modalDepth (poss ψ) = ψ.modalDepth + 1, so we need k = succ for accessImage
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => exact absurd hd (by simp [BSMLFormula.modalDepth])
      | succ k => exact ⟨k, rfl⟩
    have hdψ : ψ.modalDepth ≤ k := by
      have := hd
      simp only [BSMLFormula.modalDepth] at this
      omega
    cases b
    · -- antiSupport (poss ψ): ∀ w ∈ s, antiSupport ψ (M.access w).
      -- For each side, find the bisim-partner world and use IH at the
      -- accessibility-image state bisim.
      constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        exact (ih hdψ hbw.accessStateBisim false).mp (h w hw)
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        exact (ih hdψ hbw.accessStateBisim false).mpr (h w' hw')
    · -- support (poss ψ): ∀ w ∈ s, ∃ t ⊆ R[w], t.Nonempty ∧ support ψ t.
      -- The witness sub-team `t` of the access image transports across
      -- models via `exists_image_subset`.
      constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        obtain ⟨t, htsub, htne, htsupp⟩ := h w hw
        obtain ⟨t', ht'sub, ht'ne, htbisim⟩ :=
          hbw.accessStateBisim.exists_image_subset htsub
        exact ⟨t', ht'sub, ht'ne htne, (ih hdψ htbisim true).mp htsupp⟩
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        obtain ⟨t', ht'sub, ht'ne, ht'supp⟩ := h w' hw'
        obtain ⟨t, htsub, htne, htbisim⟩ :=
          hbw.accessStateBisim.symm.exists_image_subset ht'sub
        exact ⟨t, htsub, htne ht'ne, (ih hdψ htbisim.symm true).mpr ht'supp⟩

end Semantics.BSML
