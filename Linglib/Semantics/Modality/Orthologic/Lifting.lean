import Linglib.Semantics.Modality.Orthologic.RegularProp

/-!
# Constructing possibilities from worlds

[holliday-mandelkern-2024] §5 — the *epistemic extension* of a Boolean algebra. From
a Boolean algebra `B` of non-modal propositions we build a compatibility frame `Bᵉ`
whose possibilities are pairs `(truth, info)` of propositions with `0 ≠ truth ≤ info`
(Def 5.1): `truth` says what *is* the case, `info` what *must* be the case. The
regular propositions of `Bᵉ` form an epistemic ortholattice into which `B` embeds via
`e_B(a) = {(b,i) | b ≤ a}` (Theorem 5.7.2).

This gives possibility-semantics models a concrete construction from familiar
possible-worlds models (take `B = ℘(W)`), showing the framework is "ontologically
innocent": anyone comfortable with worlds can build the whole system on them.

## Main results
* `Possibility`, `epistemicFrame` — the frame `Bᵉ` (Def 5.1, Thm 5.7.1).
* `eBset_regular`, `eB` — the embedding `e_B : B → O(Bᵉ)` (Thm 5.7.2): `e_B(a)` is a
  regular proposition.
-/

namespace Orthologic

variable {B : Type*} [BooleanAlgebra B]

/-- A *possibility* of a Boolean algebra `B` ([holliday-mandelkern-2024] Def 5.1):
    a pair `(truth, info)` with `0 ≠ truth ≤ info`. The first component says what is
    the case, the second what must be the case. -/
structure Possibility (B : Type*) [BooleanAlgebra B] where
  /-- What is the case at this possibility. -/
  truth : B
  /-- What must be the case at this possibility. -/
  info : B
  truth_ne_bot : truth ≠ ⊥
  truth_le_info : truth ≤ info

namespace Possibility

/-- Compatibility ◊ ([holliday-mandelkern-2024] Def 5.1.2): their truths overlap, and
    each truth is entailed by the other's information. -/
def Compat (p q : Possibility B) : Prop :=
  p.truth ⊓ q.truth ≠ ⊥ ∧ p.truth ≤ q.info ∧ q.truth ≤ p.info

/-- Epistemic accessibility R ([holliday-mandelkern-2024] Def 5.1.3). -/
def Access (p q : Possibility B) : Prop :=
  p.truth ≤ q.truth ∧ q.info ≤ p.info

theorem access_refl (p : Possibility B) : p.Access p := ⟨le_refl _, le_refl _⟩

theorem access_trans {p q r : Possibility B} (h₁ : p.Access q) (h₂ : q.Access r) :
    p.Access r := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

end Possibility

/-- The *epistemic frame* `Bᵉ` of a Boolean algebra ([holliday-mandelkern-2024]
    Def 5.1, Theorem 5.7.1): possibilities under compatibility `◊`, a `CompatFrame`
    (`◊` is reflexive and symmetric). -/
def epistemicFrame (B : Type*) [BooleanAlgebra B] : CompatFrame (Possibility B) where
  compat := Possibility.Compat
  compat_refl :=
    ⟨fun p => ⟨by rw [inf_idem]; exact p.truth_ne_bot, p.truth_le_info, p.truth_le_info⟩⟩
  compat_symm := ⟨fun _ _ h => ⟨by rw [inf_comm]; exact h.1, h.2.2, h.2.1⟩⟩

/-- The embedding's underlying set `e_B(a) = {(b,i) | b ≤ a}`
    ([holliday-mandelkern-2024] Theorem 5.7.2). -/
def eBset (a : B) : Set (Possibility B) := {q | q.truth ≤ a}

/-- `e_B(a)` is a regular proposition of `Bᵉ` ([holliday-mandelkern-2024] Thm 5.7.2):
    if `b ≰ a` then the possibility `(b ⊓ aᶜ, i)` is a `◊`-witness none of whose
    compatible possibilities support `e_B(a)`. -/
theorem eBset_regular (a : B) : IsRegular (epistemicFrame B) (eBset a) := by
  intro x
  by_cases hx : x.truth ≤ a
  · exact Or.inl hx
  · right
    have hb' : x.truth ⊓ aᶜ ≠ ⊥ :=
      fun h => hx (disjoint_compl_right_iff.mp (disjoint_iff.mpr h))
    refine ⟨⟨x.truth ⊓ aᶜ, x.info, hb', inf_le_left.trans x.truth_le_info⟩, ?_, ?_⟩
    · exact ⟨by rwa [← inf_assoc, inf_idem], x.truth_le_info,
        inf_le_left.trans x.truth_le_info⟩
    · intro z hz hza
      exact hz.1 (le_bot_iff.mp ((inf_le_inf inf_le_right hza).trans (compl_inf_self a).le))

/-- The embedding `e_B : B → O(Bᵉ)` ([holliday-mandelkern-2024] Theorem 5.7.2) as a
    regular proposition. -/
def eB (a : B) : (epistemicFrame B).Regular := (epistemicFrame B).regOf (eBset a) (eBset_regular a)

@[simp] theorem mem_eB (a : B) (q : Possibility B) : q ∈ (eB a : Set _) ↔ q.truth ≤ a :=
  Iff.rfl

@[simp] theorem coe_eB (a : B) : (eB a : Set (Possibility B)) = eBset a := rfl

/-! ### `e_B` is an order-embedding preserving `⊓`, `⊤`, `⊥` (Theorem 5.7.2) -/

theorem eB_mono {a a' : B} (h : a ≤ a') : eB a ≤ eB a' :=
  fun _ hq => le_trans hq h

/-- `e_B` reflects order, hence is an embedding: the possibility `(a, ⊤)` witnesses
    `a ≤ a'` whenever `e_B a ≤ e_B a'`. -/
theorem eB_le_iff {a a' : B} : eB a ≤ eB a' ↔ a ≤ a' := by
  refine ⟨fun h => ?_, eB_mono⟩
  rcases eq_or_ne a ⊥ with rfl | ha
  · exact bot_le
  · exact @h ⟨a, ⊤, ha, le_top⟩ (le_refl a)

theorem eB_injective : Function.Injective (eB : B → (epistemicFrame B).Regular) :=
  fun _ _ h => le_antisymm (eB_le_iff.mp h.le) (eB_le_iff.mp h.ge)

theorem eB_top : eB (⊤ : B) = ⊤ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_top]
  ext q; simp [eBset]

theorem eB_bot : eB (⊥ : B) = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_bot]
  ext q; simp [eBset, le_bot_iff, q.truth_ne_bot]

theorem eB_inf (a a' : B) : eB (a ⊓ a') = eB a ⊓ eB a' := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_inf, coe_eB, coe_eB]
  ext q; simp [eBset, le_inf_iff]

/-- `e_B` preserves complement ([holliday-mandelkern-2024] Thm 5.7.2): the orthonegation
    of `e_B(a)` is `e_B(aᶜ)`. The `←` direction reuses the witness `(q ⊓ a, q.info)`. -/
theorem eB_compl (a : B) : eB aᶜ = (eB a)ᶜ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_compl, coe_eB]
  ext q
  simp only [eBset, Set.mem_setOf_eq, mem_orthoNeg]
  constructor
  · intro hq y hcompat hya
    exact hcompat.1 (le_bot_iff.mp ((inf_le_inf hq hya).trans (compl_inf_self a).le))
  · intro hq
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    by_contra hcon
    exact hq ⟨q.truth ⊓ a, q.info, hcon, inf_le_left.trans q.truth_le_info⟩
      ⟨by rwa [← inf_assoc, inf_idem], q.truth_le_info, inf_le_left.trans q.truth_le_info⟩
      inf_le_right

/-- `e_B` preserves joins (from `⊓`- and complement-preservation via De Morgan),
    completing the Boolean-algebra embedding ([holliday-mandelkern-2024] Thm 5.7.2). -/
theorem eB_sup (a a' : B) : eB (a ⊔ a') = eB a ⊔ eB a' := by
  rw [show a ⊔ a' = (aᶜ ⊓ a'ᶜ)ᶜ by rw [_root_.compl_inf, compl_compl, compl_compl],
      eB_compl, eB_inf, eB_compl, eB_compl,
      LatticeWithInvolution.compl_inf, LatticeWithInvolution.compl_compl,
      LatticeWithInvolution.compl_compl]

end Orthologic
