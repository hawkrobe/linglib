import Linglib.Theories.Semantics.Dynamic.Connectives.CCP

/-!
# Update Semantics
@cite{veltman-1996}

In Update Semantics:
- Information states are sets of worlds (not assignments)
- Sentences update states by eliminating incompatible worlds
- "Might φ" is a TEST: passes if some φ-worlds remain
- No discourse referents (simpler than DRT/DPL)

⟦φ⟧ : State → State where State = Set World

-/

namespace Semantics.Dynamic.UpdateSemantics

open Classical

/--
Update Semantics state: a set of possible worlds.

Unlike DPL/DRT, no assignment component - US focuses on propositional content.
-/
abbrev State (W : Type*) := Set W

/--
Update function: how a sentence modifies a state.
-/
def Update (W : Type*) := State W → State W

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop {W : Type*} (φ : W → Prop) : Update W :=
  λ s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧

Delegates to `Core.CCP.seq`.
-/
def Update.conj {W : Type*} (φ ψ : Update W) : Update W :=
  Core.CCP.seq φ ψ

/--
Negation: test and possibly fail.

⟦¬φ⟧(s) = s if ⟦φ⟧(s) = ∅, else ∅

Delegates to `Core.CCP.neg`.
-/
noncomputable def Update.neg {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.neg φ

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

Delegates to `Core.CCP.might`.
-/
noncomputable def Update.might {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.might φ

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

Delegates to `Core.CCP.must`.
-/
noncomputable def Update.must {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.must φ

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem might_is_test {W : Type*} (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) :
    Update.might φ s = s := by
  simp [Update.might, Core.CCP.might, h]

/--
Order matters for epistemic might.

"It's raining and it might not be raining" is contradictory:
after learning rain, the might-not-rain test fails (no ¬rain worlds remain).
But "it might not be raining and it's raining" can succeed:
the might test passes on the initial state, then learning eliminates ¬rain worlds.

Requires `Nontrivial W`: for empty or singleton W, no state has both
p-worlds and ¬p-worlds, making the second conjunct unsatisfiable. -/
theorem might_order_matters {W : Type*} [DecidableEq W] [Nontrivial W] :
    ∃ (p : W → Prop) (_ : DecidablePred p) (s : State W),
      Update.conj (Update.prop p) (Update.might (Update.prop fun w => ¬p w)) s = ∅ ∧
      (Update.conj (Update.might (Update.prop fun w => ¬p w)) (Update.prop p) s).Nonempty := by
  obtain ⟨w₁, w₂, hne⟩ := exists_pair_ne W
  refine ⟨fun w => w = w₁, inferInstance, {w₁, w₂}, ?_, ?_⟩
  · -- "p and might(not p)" fails: after learning p, only w₁ remains, and ¬p w₁ is false
    simp only [Update.conj, Core.CCP.seq, Update.prop, Update.might, Core.CCP.might]
    have h_not_nonempty :
        ¬({w ∈ {w ∈ ({w₁, w₂} : Set W) | w = w₁} | ¬w = w₁}).Nonempty := by
      rintro ⟨w, ⟨_, hw_p⟩, hw_np⟩; exact hw_np hw_p
    simp only [h_not_nonempty, ↓reduceIte]
  · -- "might(not p) and p" succeeds: might test passes on {w₁, w₂}, then p keeps w₁
    simp only [Update.conj, Core.CCP.seq, Update.prop, Update.might, Core.CCP.might]
    have h_nonempty : ({w ∈ ({w₁, w₂} : Set W) | ¬w = w₁}).Nonempty :=
      ⟨w₂, Or.inr rfl, hne.symm⟩
    simp only [h_nonempty, ↓reduceIte]
    exact ⟨w₁, ⟨Or.inl rfl, rfl⟩⟩

/--
State s supports φ iff updating with φ doesn't change s.

s ⊨ φ iff ⟦φ⟧(s) = s
-/
def supports {W : Type*} (s : State W) (φ : Update W) : Prop :=
  φ s = s

/--
State s accepts φ iff updating with φ yields a non-empty state.

s accepts φ iff ⟦φ⟧(s) ≠ ∅
-/
def accepts {W : Type*} (s : State W) (φ : Update W) : Prop :=
  (φ s).Nonempty


-- ═══ Three Notions of Validity (§1.2) ═══

/-- **Validity₁**: updating the minimal state **0** with the premises
    in order yields a state that supports the conclusion.

    ψ₁,...,ψₙ ⊩₁ φ  iff  **0**[ψ₁]⋯[ψₙ] ⊨ φ

    @cite{veltman-1996}, §1.2. This is the notion Veltman concentrates on:
    it captures the fact that default conclusions depend on exactly what
    information is available. -/
def valid₁ {W : Type*} (premises : List (Update W)) (conclusion : Update W) : Prop :=
  supports (premises.foldl (fun s u => u s) Set.univ) conclusion

/-- **Validity₂**: for *every* state σ, updating with the premises
    in order yields a state that supports the conclusion.

    ψ₁,...,ψₙ ⊩₂ φ  iff  ∀σ, σ[ψ₁]⋯[ψₙ] ⊨ φ -/
def valid₂ {W : Type*} (premises : List (Update W)) (conclusion : Update W) : Prop :=
  ∀ σ : State W, supports (premises.foldl (fun s u => u s) σ) conclusion

/-- **Validity₃**: one cannot accept all premises without accepting
    the conclusion. Closest to the classical notion.

    ψ₁,...,ψₙ ⊩₃ φ  iff  ∀σ, (σ ⊨ ψ₁ ∧ ... ∧ σ ⊨ ψₙ) → σ ⊨ φ -/
def valid₃ {W : Type*} (premises : List (Update W)) (conclusion : Update W) : Prop :=
  ∀ σ : State W, (∀ p ∈ premises, supports σ p) → supports σ conclusion

/-- Validity₂ implies validity₁: specializing σ = **0**.

    @cite{veltman-1996}, Proposition 1.3 (one direction, unconditional). -/
theorem valid₂_imp_valid₁ {W : Type*}
    (premises : List (Update W)) (conclusion : Update W) :
    valid₂ premises conclusion → valid₁ premises conclusion :=
  fun h => h Set.univ

/-- Validity₃ is monotonic: adding premises preserves validity.

    @cite{veltman-1996}, §1.2: validity₃ is the only notion that is
    both left and right monotonic. -/
theorem valid₃_monotone {W : Type*}
    (premises extra : List (Update W)) (conclusion : Update W) :
    valid₃ premises conclusion → valid₃ (premises ++ extra) conclusion :=
  fun h σ hsup => h σ (fun p hp => hsup p (List.mem_append_left extra hp))

-- ═══ Presuppositional Updates (§2.3 of @cite{yagi-2025}) ═══

/-- The designated undefined state: update failure.

    @cite{yagi-2025} Definition 5: when a presupposition is not satisfied,
    the update yields ∗. We model ∗ as `none` via `Option (State W)`. -/
abbrev PState (W : Type*) := Option (State W)

/-- Presuppositional update: update by φ_p is defined only when the
    presupposition p is supported (i.e. `s[p] = s`).

    @cite{yagi-2025} Definition 5:
      s[φ_p] = ∗  if s[p] ≠ s
             = s[φ]  otherwise

    @cite{heim-1982} @cite{beaver-2001} @cite{veltman-1996} -/
noncomputable def PUpdate.presup {W : Type*} (p φ : W → Prop) : PState W → PState W
  | none => none
  | some s =>
    if Update.prop p s = s then
      some (Update.prop φ s)
    else
      none

/-- Negation extended to PState: s[¬φ] = s/s[φ].

    @cite{yagi-2025} Definition 4: s[¬φ] = s \ s[φ]. -/
noncomputable def PUpdate.neg {W : Type*} (φ : W → Prop) : PState W → PState W
  | none => none
  | some s => some (s \ Update.prop φ s)

/-- Disjunction extended to PState: s[φ ∨ ψ] = s[φ] ∪ s[¬φ][ψ].

    @cite{yagi-2025} Definition 4, @cite{heim-1982}.
    Extended with ∗ ∪ s = s ∪ ∗ = ∗. -/
noncomputable def PUpdate.disj {W : Type*} (φ ψ : W → Prop) :
    PState W → PState W
  | none => none
  | some s =>
    let left := Update.prop φ s
    let negLeft := s \ left
    let right := Update.prop ψ negLeft
    some (left ∪ right)

/-- Presuppositional disjunction: s[φ_p ∨ ψ_q].
    Apply presupposition checks to each disjunct.

    This is the standard Heim/Beaver definition:
      s[φ_p ∨ ψ_q] = s[φ_p] ∪ s[¬φ_p][ψ_q]

    Both presuppositional updates must be defined for the result to be
    defined: s[φ_p] requires s ⊨ p, and s[¬φ_p][ψ_q] requires s[¬φ_p] ⊨ q. -/
noncomputable def PUpdate.disjPresup {W : Type*} (p φ q ψ : W → Prop) :
    PState W → PState W
  | none => none
  | some s =>
    -- Left disjunct: s[φ_p]
    let left := PUpdate.presup p φ (some s)
    -- Right context: s[¬φ_p] — but ¬φ_p requires negating the presuppositional φ
    -- Following Yagi: s[¬φ_p] = s \ s[φ_p], but s[φ_p] may be ∗
    match left with
    | none => none  -- left undefined → whole disjunction undefined
    | some leftResult =>
      let negLeftCtx := s \ leftResult
      -- Right disjunct: s[¬φ_p][ψ_q]
      let right := PUpdate.presup q ψ (some negLeftCtx)
      match right with
      | none => none
      | some rightResult => some (leftResult ∪ rightResult)

/-- **Flexible accommodation disjunction** (dynamic version).

    @cite{yagi-2025} (13) / @cite{geurts-2005} / @cite{aloni-2022}:
      s[φ ∨ ψ] = s[χ][φ] ∪ s[ω][ψ], where s[χ] ∪ s[ω] = s

    The propositions χ and ω *split* the state s into two substates.
    By default χ = ω = ⊤ (both tautological), but when the default
    violates genuineness (@cite{zimmermann-2000}), the split becomes
    non-trivial: χ = ¬q and ω = ¬p for conflicting presuppositions. -/
noncomputable def PUpdate.disjFlex {W : Type*}
    (χ φ_presup φ ω ψ_presup ψ : W → Prop)
    (_h_split : ∀ s : State W, Update.prop χ s ∪ Update.prop ω s = s) :
    PState W → PState W
  | none => none
  | some s =>
    let leftCtx := Update.prop χ s
    let rightCtx := Update.prop ω s
    let left := PUpdate.presup φ_presup φ (some leftCtx)
    let right := PUpdate.presup ψ_presup ψ (some rightCtx)
    match left, right with
    | some l, some r => some (l ∪ r)
    | _, _ => none  -- ∗ poisons: if either side is undefined, result is ∗


-- ═══ Yagi's Core Observations (Dynamic) ═══

/-- Presuppositional disjunction update is uninformative when both
    presuppositions are already supported: if s ⊨ p and s ⊨ q and the
    disjunction φ ∨ ψ is already true throughout s, the update returns
    s unchanged.

    Note: this applies to **non-conflicting** presuppositions. When
    p ∧ q = ⊥, the hypotheses hp and hq are jointly unsatisfiable
    (unless s = ∅). For the conflicting case, see
    `update_yields_undefined` in the Yagi2025 study, which shows the
    update is undefined (∗) rather than uninformative. -/
theorem presup_disj_uninformative_when_supported {W : Type*}
    (p φ q ψ : W → Prop) (s : State W)
    (hp : Update.prop p s = s) (hq : Update.prop q s = s)
    (h_or : ∀ w, w ∈ s → (φ w ∨ ψ w)) :
    PUpdate.disjPresup p φ q ψ (some s) = some s := by
  unfold PUpdate.disjPresup PUpdate.presup
  -- Helper: q holds at every world in s (from hq)
  have hq_at : ∀ w, w ∈ s → q w := by
    intro w hw
    have : w ∈ Update.prop q s := hq.symm ▸ hw
    exact this.2
  -- Helper: q is supported on any subset of s
  have hq_sub : ∀ t : State W, t ⊆ s → Update.prop q t = t := by
    intro t ht; ext w
    exact ⟨fun h => h.1, fun hw => ⟨hw, hq_at w (ht hw)⟩⟩
  -- Helper: ψ holds everywhere in s \ Update.prop φ s (by h_or + φ failure)
  have hψ_sub : ∀ w, w ∈ s \ Update.prop φ s → ψ w := by
    intro w ⟨hw, hnφ⟩
    cases h_or w hw with
    | inl h => exact absurd (show w ∈ Update.prop φ s from ⟨hw, h⟩) hnφ
    | inr h => exact h
  have h_q_neg : Update.prop q (s \ Update.prop φ s) = s \ Update.prop φ s :=
    hq_sub _ (fun _ h => h.1)
  simp only [hp, ↓reduceIte, h_q_neg]
  -- Result: Update.prop φ s ∪ Update.prop ψ (s \ Update.prop φ s) = s
  suffices h : Update.prop φ s ∪ Update.prop ψ (s \ Update.prop φ s) = s by
    exact congrArg some h
  apply Set.Subset.antisymm
  · intro w hw
    cases hw with
    | inl h => exact h.1
    | inr h => exact h.1.1
  · intro w hw
    by_cases hφ : φ w
    · exact Set.mem_union_left _ ⟨hw, hφ⟩
    · exact Set.mem_union_right _ ⟨⟨hw, fun h => hφ h.2⟩, hψ_sub w ⟨hw, fun h => hφ h.2⟩⟩

end Semantics.Dynamic.UpdateSemantics
