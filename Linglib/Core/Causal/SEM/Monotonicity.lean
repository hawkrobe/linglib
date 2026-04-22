import Linglib.Core.Causal.SEM.Defs
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate

/-!
# SEM: Information-monotone fixpoint via well-founded recursion
@cite{fitting-1985} @cite{schulz-2011} @cite{nadathur-2024} @cite{nadathur-lauer-2020}

`normalDevelopment` iterates `applyLawsOnce` to a fixpoint. Termination is
via well-founded recursion on the count of undetermined inner variables —
a measure that strictly decreases on every non-fixpoint step because
info-monotone `apply` (in `Defs.lean`) only transitions variables from
`none` to `some _`, never the reverse.

No polarity restriction: dynamics with negative preconditions like
`COM := MSG ∧ ¬BRK` (Schulz @cite{schulz-2011}'s "potential obstacle"
pattern) terminate just as cleanly as classical Pearl SEMs with
all-positive preconditions. The measure proof uses only
information-monotonicity, never the law's polarity.

This is the Lean realization of @cite{schulz-2011} footnote 7: T_D is
info-extensive (`s ≤ T_D(s)`) but not order-monotone (so Knaster–Tarski
of @cite{fitting-1985} §6 does not apply); termination still holds via
finite-state exhaustion, which we make explicit via `Nat`-valued
`countP isNone` measure.
-/

namespace Core.Causal

private abbrev trueLE := Situation.trueLE

-- ════════════════════════════════════════════════════
-- § Information-monotonicity primitives
-- ════════════════════════════════════════════════════

/-- Once a variable is determined, no `apply` overwrites it. -/
theorem CausalLaw.apply_preserves_determined (law : CausalLaw) (s : Situation)
    (v : Variable) (h : s.get v ≠ none) :
    (law.apply s).get v ≠ none := by
  unfold CausalLaw.apply
  cases hg : s.get law.effect with
  | none =>
    by_cases hMet : law.preconditionsMet s
    · simp only [hMet, if_true]
      by_cases hve : v = law.effect
      · rw [hve, Situation.extend_get_same]; simp
      · rw [Situation.extend_get_ne hve]; exact h
    · simp [hMet]; exact h
  | some b => exact h

/-- `apply` preserves `hasValue`: once `s.hasValue v val`, the law can't
    overwrite it (info-monotonicity). -/
theorem CausalLaw.apply_preserves_hasValue (law : CausalLaw) (s : Situation)
    (v : Variable) (val : Bool) (h : s.hasValue v val) :
    (law.apply s).hasValue v val := by
  -- s.hasValue v val means s.valuation v = some val, so v is determined
  unfold Situation.hasValue at h ⊢
  unfold CausalLaw.apply
  cases hg : s.get law.effect with
  | none =>
    by_cases hMet : law.preconditionsMet s
    · simp only [hMet, if_true]
      by_cases hve : v = law.effect
      · -- v = effect; s.valuation v = some val, but s.get effect = none — contradiction
        subst hve
        rw [show s.valuation law.effect = s.get law.effect from rfl, hg] at h
        cases h
      · show (s.extend law.effect law.effectValue).valuation v = some val
        rw [show (s.extend law.effect law.effectValue).valuation v
              = (s.extend law.effect law.effectValue).get v from rfl,
            Situation.extend_get_ne hve]
        exact h
    · simp [hMet]; exact h
  | some b => exact h

/-- `applyLawsOnce` preserves `hasValue` (folded version). -/
theorem applyLawsOnce_preserves_hasValue (dyn : CausalDynamics) (s : Situation)
    (v : Variable) (val : Bool) (h : s.hasValue v val) :
    (applyLawsOnce dyn s).hasValue v val := by
  show (dyn.laws.foldl _ s).hasValue v val
  induction dyn.laws generalizing s with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (hd.apply s) (CausalLaw.apply_preserves_hasValue hd s v val h)

/-- `applyLawsOnce` preserves determined-ness (folded info-monotonicity). -/
theorem applyLawsOnce_preserves_determined (dyn : CausalDynamics) (s : Situation)
    (v : Variable) (h : s.get v ≠ none) :
    (applyLawsOnce dyn s).get v ≠ none := by
  show (dyn.laws.foldl _ s).get v ≠ none
  induction dyn.laws generalizing s with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (hd.apply s) (CausalLaw.apply_preserves_determined hd s v h)

/-- `applyLawsOnce` is `trueLE`-extensive: every truth in `s` is preserved.
    Follows from info-monotonicity. -/
theorem applyLawsOnce_grows (dyn : CausalDynamics) (s : Situation) :
    trueLE s (applyLawsOnce dyn s) :=
  fun v hv => applyLawsOnce_preserves_hasValue dyn s v true hv

/-- `applyLawsOnce` preserves `(s.get v).isNone = false` (Bool-valued
    convenience for the strict-decrease measure). -/
private theorem applyLawsOnce_preserves_isNone_eq_false (dyn : CausalDynamics)
    (s : Situation) (v : Variable) (h : (s.get v).isNone = false) :
    ((applyLawsOnce dyn s).get v).isNone = false := by
  have hSome : s.get v ≠ none := by
    cases hg : s.get v with
    | none => rw [hg] at h; simp at h
    | some _ => intro hh; cases hh
  have : (applyLawsOnce dyn s).get v ≠ none :=
    applyLawsOnce_preserves_determined dyn s v hSome
  cases hg : (applyLawsOnce dyn s).get v with
  | none => exact absurd hg this
  | some _ => rfl

-- ════════════════════════════════════════════════════
-- § Strict-decrease: undetermined-count drops on non-fixpoint step
-- ════════════════════════════════════════════════════

/-- List counting: pointwise implication gives `countP P ≤ countP Q`. -/
private theorem countP_le_of_imp {α : Type*}
    {P Q : α → Bool} (hMono : ∀ x, P x = true → Q x = true) :
    ∀ (l : List α), l.countP P ≤ l.countP Q
  | [] => Nat.le_refl _
  | hd :: tl => by
    cases hPhd : P hd
    · cases hQhd : Q hd
      · simp [hPhd, hQhd]; exact countP_le_of_imp hMono tl
      · simp [hPhd, hQhd]; exact Nat.le_succ_of_le (countP_le_of_imp hMono tl)
    · have hQhd : Q hd = true := hMono hd hPhd
      simp [hPhd, hQhd]; exact countP_le_of_imp hMono tl

/-- List counting: strict variant. -/
private theorem countP_lt_of_imp_of_witness {α : Type*}
    {P Q : α → Bool} (hMono : ∀ x, P x = true → Q x = true)
    {l : List α} {x : α} (hx : x ∈ l) (hQx : Q x = true) (hPx : P x = false) :
    l.countP P < l.countP Q := by
  induction l with
  | nil => cases hx
  | cons hd tl ih =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hxtl
    · simp [hPx, hQx]; exact Nat.lt_succ_of_le (countP_le_of_imp hMono tl)
    · cases hPhd : P hd
      · cases hQhd : Q hd
        · simp [hPhd, hQhd]; exact ih hxtl
        · simp [hPhd, hQhd]; exact Nat.lt_succ_of_lt (ih hxtl)
      · have hQhd : Q hd = true := hMono hd hPhd
        simp [hPhd, hQhd]; exact ih hxtl

/-- After folding `apply` over laws, if law `L` had met preconditions and
    undetermined effect at the start, its effect ends up determined. -/
private theorem foldl_determines_witness :
    ∀ (laws : List CausalLaw) (s : Situation) (L : CausalLaw),
    L ∈ laws →
    L.preconditionsMet s →
    s.get L.effect = none →
    (laws.foldl (fun s' law => law.apply s') s).get L.effect ≠ none
  | [], _, _, hMem, _, _ => by simp at hMem
  | hd :: tl, s, L, hMem, hMet, hNone => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hMem with hLhd | hmemtl
    · -- L = hd: applies first → effect determined; preserved through tail
      have hMetHd : hd.preconditionsMet s := hLhd ▸ hMet
      have hNoneHd : s.get hd.effect = none := hLhd ▸ hNone
      rw [CausalLaw.apply_of_met_undetermined hMetHd hNoneHd]
      have hDet : (s.extend hd.effect hd.effectValue).get L.effect ≠ none := by
        rw [hLhd, Situation.extend_get_same]; simp
      exact applyLawsOnce_preserves_determined ⟨tl⟩ _ L.effect hDet
    · -- L is in tail; track L's preconditions through hd.apply
      have hMet' : L.preconditionsMet (hd.apply s) := by
        intro p hp
        exact CausalLaw.apply_preserves_hasValue hd s p.1 p.2 (hMet p hp)
      by_cases hHdEffL : L.effect = hd.effect
      · -- hd's effect = L's effect; if hd fires, L.effect becomes determined
        rw [hHdEffL] at hNone
        by_cases hMetHd : hd.preconditionsMet s
        · rw [CausalLaw.apply_of_met_undetermined hMetHd hNone]
          have hDet : (s.extend hd.effect hd.effectValue).get L.effect ≠ none := by
            rw [hHdEffL, Situation.extend_get_same]; simp
          exact applyLawsOnce_preserves_determined ⟨tl⟩ _ L.effect hDet
        · rw [CausalLaw.apply_of_not_met hMetHd]
          rw [← hHdEffL] at hNone
          exact foldl_determines_witness tl s L hmemtl hMet hNone
      · -- hd's effect ≠ L's effect; L.effect stays `none` after hd.apply
        have hNone' : (hd.apply s).get L.effect = none := by
          unfold CausalLaw.apply
          cases hg : s.get hd.effect with
          | none =>
            by_cases hMetHd : hd.preconditionsMet s
            · simp only [hMetHd, if_true]
              exact (Situation.extend_get_ne hHdEffL).trans hNone
            · simp [hMetHd]; exact hNone
          | some b => exact hNone
        exact foldl_determines_witness tl (hd.apply s) L hmemtl hMet' hNone'

/-- **Strict-decrease lemma**: if `s` is not a fixpoint, `applyLawsOnce`
    strictly decreases the count of undetermined inner variables.

    No positivity needed: works for arbitrary dynamics, including those
    with negative preconditions. -/
theorem applyLawsOnce_strict_decrease
    (dyn : CausalDynamics) (s : Situation) (hNotFix : ¬ isFixpoint dyn s) :
    (innerVariables dyn).countP (fun v => ((applyLawsOnce dyn s).get v).isNone) <
    (innerVariables dyn).countP (fun v => (s.get v).isNone) := by
  -- Extract witness law L₀ from non-fixpoint
  unfold isFixpoint at hNotFix
  push Not at hNotFix
  obtain ⟨L₀, hL₀mem, hMet, hNone⟩ := hNotFix
  -- L₀.effect ∈ innerVariables
  have hMemInner : L₀.effect ∈ innerVariables dyn :=
    effect_mem_innerVariables dyn L₀ hL₀mem
  -- After applyLawsOnce: L₀.effect determined
  have hAfter : (applyLawsOnce dyn s).get L₀.effect ≠ none :=
    foldl_determines_witness dyn.laws s L₀ hL₀mem hMet hNone
  refine countP_lt_of_imp_of_witness ?_ hMemInner ?_ ?_
  · -- monotonicity
    intro v hAfterIsNone
    cases hSb : (s.get v).isNone
    · -- determined in s; preserved through applyLawsOnce
      have := applyLawsOnce_preserves_isNone_eq_false dyn s v hSb
      rw [this] at hAfterIsNone; exact hAfterIsNone
    · rfl
  · rw [hNone]; rfl
  · cases hg : (applyLawsOnce dyn s).get L₀.effect with
    | none => exact absurd hg hAfter
    | some _ => rfl

-- ════════════════════════════════════════════════════
-- § normalDevelopment via well-founded recursion
-- ════════════════════════════════════════════════════

/-- The `Nat`-valued termination measure: count of undetermined inner
    variables. Strictly decreases on non-fixpoint steps under info-monotone
    `applyLawsOnce` (the substantive content is `applyLawsOnce_strict_decrease`). -/
private def measure (dyn : CausalDynamics) (s : Situation) : ℕ :=
  (innerVariables dyn).countP (fun v => (s.get v).isNone)

/-- Generic missing-from-mathlib piece: if a `ℕ`-valued measure strictly
    decreases on non-stopping points, iterating `f` eventually reaches a
    stopping point. After this, "iterate to fixed point" is `f^[Nat.find ...] x`
    in pure mathlib. (Inlined here as a private lemma; promote to a
    standalone file if a second consumer materializes.) -/
private theorem _root_.Function.exists_iterate_satisfies {α : Type*} (f : α → α)
    {Stop : α → Prop} [DecidablePred Stop]
    (m : α → ℕ) (h : ∀ x, ¬ Stop x → m (f x) < m x) (x : α) :
    ∃ n, Stop (f^[n] x) := by
  induction hk : m x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases hStop : Stop x
    · exact ⟨0, by simpa using hStop⟩
    · have hLt : m (f x) < k := hk ▸ h x hStop
      obtain ⟨n, hn⟩ := ih (m (f x)) hLt (f x) rfl
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- **Normal Causal Development** (@cite{nadathur-lauer-2020} Definition 15;
    Schulz @cite{schulz-2011} Definition 4 of `s_Σ^*`).

    `(applyLawsOnce dyn)^[k] s` for the smallest `k` reaching a fixpoint —
    expressed via `Function.iterate` and `Nat.find` (no new combinator).
    Termination of the search is `Function.exists_iterate_satisfies` applied
    to the strict-decrease measure on undetermined inner variables. -/
def normalDevelopment (dyn : CausalDynamics) (s : Situation) : Situation :=
  (applyLawsOnce dyn)^[Nat.find (Function.exists_iterate_satisfies (applyLawsOnce dyn)
    (measure dyn) (applyLawsOnce_strict_decrease dyn) s)] s

/-- `normalDevelopment` reaches a fixpoint — directly from `Nat.find_spec`. -/
theorem normalDevelopment_isFixpoint (dyn : CausalDynamics) (s : Situation) :
    isFixpoint dyn (normalDevelopment dyn s) :=
  Nat.find_spec (Function.exists_iterate_satisfies (applyLawsOnce dyn)
    (measure dyn) (applyLawsOnce_strict_decrease dyn) s)

/-- mathlib bridge: `normalDevelopment dyn s` is a fixed point of
    `applyLawsOnce dyn` (`Mathlib.Dynamics.FixedPoints.Basic`). -/
theorem normalDevelopment_isFixedPt (dyn : CausalDynamics) (s : Situation) :
    Function.IsFixedPt (applyLawsOnce dyn) (normalDevelopment dyn s) :=
  applyLawsOnce_of_fixpoint (normalDevelopment_isFixpoint dyn s)

/-- Fixpoint case unfolds to identity — `Nat.find` returns 0. -/
theorem normalDevelopment_of_fixpoint {dyn : CausalDynamics} {s : Situation}
    (h : isFixpoint dyn s) : normalDevelopment dyn s = s := by
  unfold normalDevelopment
  rw [Nat.find_eq_zero _ |>.mpr h]
  rfl

/-- Step case unfolds via `Nat.find_eq_iff` and `iterate_succ_apply`. -/
theorem normalDevelopment_of_not_fixpoint {dyn : CausalDynamics} {s : Situation}
    (h : ¬ isFixpoint dyn s) :
    normalDevelopment dyn s = normalDevelopment dyn (applyLawsOnce dyn s) := by
  unfold normalDevelopment
  -- Want: f^[Nat.find P_s] s = f^[Nat.find P_(fs)] (f s)
  -- where P_s n := isFixpoint dyn (f^[n] s); similarly P_(fs).
  -- Key: P_s (n+1) = P_(fs) n (since f^[n+1] s = f^[n] (f s)).
  -- So Nat.find P_s = Nat.find P_(fs) + 1.
  set k := Nat.find (Function.exists_iterate_satisfies (applyLawsOnce dyn)
    (measure dyn) (applyLawsOnce_strict_decrease dyn) (applyLawsOnce dyn s))
  have key : Nat.find (Function.exists_iterate_satisfies (applyLawsOnce dyn)
      (measure dyn) (applyLawsOnce_strict_decrease dyn) s) = k + 1 := by
    apply (Nat.find_eq_iff _).mpr
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply]
      exact Nat.find_spec (Function.exists_iterate_satisfies (applyLawsOnce dyn)
        (measure dyn) (applyLawsOnce_strict_decrease dyn) (applyLawsOnce dyn s))
    · intro j hj hPj
      match j with
      | 0 => exact h hPj
      | j' + 1 =>
        rw [Function.iterate_succ_apply] at hPj
        exact Nat.find_min (Function.exists_iterate_satisfies (applyLawsOnce dyn)
          (measure dyn) (applyLawsOnce_strict_decrease dyn) (applyLawsOnce dyn s))
          (Nat.lt_of_succ_lt_succ hj) hPj
  rw [key, Function.iterate_succ_apply]

/-- One-step convergence: if `applyLawsOnce dyn s` is a fixpoint, then
    `normalDevelopment dyn s = applyLawsOnce dyn s`. -/
theorem normalDevelopment_eq_applyLawsOnce_of_fixpoint
    (dyn : CausalDynamics) (s : Situation)
    (hFix : isFixpoint dyn (applyLawsOnce dyn s)) :
    normalDevelopment dyn s = applyLawsOnce dyn s := by
  by_cases hSFix : isFixpoint dyn s
  · rw [normalDevelopment_of_fixpoint hSFix, applyLawsOnce_of_fixpoint hSFix]
  · rw [normalDevelopment_of_not_fixpoint hSFix,
        normalDevelopment_of_fixpoint hFix]

/-- **n-step closed form**: if any specific iterate `(applyLawsOnce dyn)^[n] s`
    is a fixpoint, that iterate equals `normalDevelopment dyn s`. The
    consumer chooses `n` (often 1, 2, or 3 for small SEMs) and discharges
    `isFixpoint` via `decide` — no `native_decide` needed.

    Proof: `Nat.find ≤ n` (Nat.find_le on the fixpoint witness), and
    iterating past the fixpoint is no-op (`Function.IsFixedPt.iterate`). -/
theorem normalDevelopment_eq_iterate_of_fixpoint
    (dyn : CausalDynamics) (s : Situation) (n : ℕ)
    (hFix : isFixpoint dyn ((applyLawsOnce dyn)^[n] s)) :
    normalDevelopment dyn s = (applyLawsOnce dyn)^[n] s := by
  unfold normalDevelopment
  set findN := Nat.find (Function.exists_iterate_satisfies (applyLawsOnce dyn)
    (measure dyn) (applyLawsOnce_strict_decrease dyn) s)
  have hLe : findN ≤ n := Nat.find_le hFix
  have hFixFind : Function.IsFixedPt (applyLawsOnce dyn)
      ((applyLawsOnce dyn)^[findN] s) :=
    applyLawsOnce_of_fixpoint (Nat.find_spec
      (Function.exists_iterate_satisfies (applyLawsOnce dyn)
        (measure dyn) (applyLawsOnce_strict_decrease dyn) s))
  conv_rhs => rw [show n = (n - findN) + findN from (Nat.sub_add_cancel hLe).symm,
                  Function.iterate_add_apply]
  exact (hFixFind.iterate _).symm

-- ════════════════════════════════════════════════════
-- § Closure properties
-- ════════════════════════════════════════════════════

/-- **Inflationary**: every truth in `s` is preserved by normal development.
    Follows directly from `applyLawsOnce_grows` lifted along
    `Function.iterate` (every iterate of a `trueLE`-extensive op is
    `trueLE`-extensive). -/
theorem normalDevelopment_grows (dyn : CausalDynamics) (s : Situation) :
    trueLE s (normalDevelopment dyn s) := by
  -- More general fact: every iterate is trueLE-extensive
  suffices h : ∀ k (s : Situation), trueLE s ((applyLawsOnce dyn)^[k] s) from h _ _
  intro k
  induction k with
  | zero => intro s; exact Situation.trueLE_refl s
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    exact Situation.trueLE_trans (applyLawsOnce_grows dyn s) (ih (applyLawsOnce dyn s))

/-- **Strong inflation**: every determined value (true *or* false) in `s`
    is preserved by normal development. The Bool-valued strengthening of
    `normalDevelopment_grows`, lifted from `applyLawsOnce_preserves_hasValue`
    along `Function.iterate`. -/
theorem normalDevelopment_preserves_hasValue (dyn : CausalDynamics) (s : Situation)
    (v : Variable) (val : Bool) (h : s.hasValue v val) :
    (normalDevelopment dyn s).hasValue v val := by
  suffices haux : ∀ k (s : Situation), s.hasValue v val →
      ((applyLawsOnce dyn)^[k] s).hasValue v val from haux _ _ h
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ n ih =>
    intro s hs
    rw [Function.iterate_succ_apply]
    exact ih (applyLawsOnce dyn s) (applyLawsOnce_preserves_hasValue dyn s v val hs)

end Core.Causal
