import Linglib.Semantics.Modality.Orthologic.Modal
import Linglib.Semantics.Modality.Orthologic.RegularProp
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The epistemic frame of a Boolean algebra

The construction of [holliday-mandelkern-2024] that lifts a possible-worlds model to a
possibility model for epistemic modals: the possibilities of the *epistemic frame* of a Boolean
algebra `B` are the pairs `(a, i)` with `⊥ ≠ a ≤ i`, `a` recording how things are and might be
and `i` what must be the case; `(a, i)` is compatible with `(a', i')` when `a ⊓ a' ≠ ⊥`, `a ≤ i'`
and `a' ≤ i`, and accesses `(a', i')` when `a ≤ a'` and `i' ≤ i`. The result is an epistemic
compatibility frame (`epistemicFrame`), refinement is componentwise (`refines_iff`), and the
map `embed b = {(a, i) | a ≤ b}` sends `b` to a regular proposition whose box and diamond are
read off the two components (`mem_box_embed`, `mem_diamond_embed`): `b` must be the case at
`(a, i)` iff `i ≤ b`, and might be iff `a ⊓ b ≠ ⊥`. As a map `eB` into the regular
propositions the embedding is an injective order embedding preserving `⊤`, `⊥`, meets and
complements, and the diamond of a nontrivial embedded proposition does not collapse to it
(`not_diamond_embed_subset`).

## References

* [holliday-mandelkern-2024]
-/

namespace Orthologic

variable {B : Type*} [BooleanAlgebra B]

/-- A possibility of the epistemic frame of `B`: a pair `(a, i)` with `⊥ ≠ a ≤ i`.
[holliday-mandelkern-2024] Definition 5.1. -/
abbrev Possibility (B : Type*) [BooleanAlgebra B] : Type _ :=
  {p : B × B // p.1 ≠ ⊥ ∧ p.1 ≤ p.2}

namespace Possibility

variable (x y : Possibility B)

/-- How things are and might be according to the possibility. -/
abbrev truth : B := x.1.1

/-- What must be the case according to the possibility. -/
abbrev info : B := x.1.2

theorem truth_ne_bot : x.truth ≠ ⊥ := x.2.1

theorem truth_le_info : x.truth ≤ x.info := x.2.2

theorem info_ne_bot : x.info ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot x.truth_le_info

/-- Compatibility: the two truths overlap and each lies within the other's information.
[holliday-mandelkern-2024] Definition 5.1.2. -/
def compat : Prop := x.truth ⊓ y.truth ≠ ⊥ ∧ x.truth ≤ y.info ∧ y.truth ≤ x.info

/-- Epistemic access: both components of the target lie in the interval between the components
of the source. [holliday-mandelkern-2024] Definition 5.1.3. -/
def access : Prop := x.truth ≤ y.truth ∧ y.info ≤ x.info

instance [DecidableEq B] [DecidableLE B] : Decidable (compat x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq B] [DecidableLE B] : Decidable (access x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The possibility `(a, a)` that knows everything it settles. -/
def diag (a : B) (ha : a ≠ ⊥) : Possibility B := ⟨(a, a), ha, le_rfl⟩

@[simp] theorem diag_truth (a : B) (ha : a ≠ ⊥) : (diag a ha).truth = a := rfl

@[simp] theorem diag_info (a : B) (ha : a ≠ ⊥) : (diag a ha).info = a := rfl

theorem compat_diag_truth : compat x (diag x.truth x.truth_ne_bot) :=
  ⟨by simp only [diag_truth, inf_idem]; exact x.truth_ne_bot, le_rfl, x.truth_le_info⟩

theorem compat_diag_info : compat x (diag x.info x.info_ne_bot) :=
  ⟨by simp only [diag_truth, inf_of_le_left x.truth_le_info]; exact x.truth_ne_bot,
    x.truth_le_info, le_rfl⟩

theorem access_diag_info : access x (diag x.info x.info_ne_bot) := ⟨x.truth_le_info, le_rfl⟩

end Possibility

open Possibility

/-- The epistemic frame of `B`: an epistemic compatibility frame on `Possibility B`. R-regularity
is witnessed by `(a ⊔ d, a ⊔ d)` and Knowability by `(a, a)`.
[holliday-mandelkern-2024] Definition 5.1 and Theorem 5.7.1. -/
def epistemicFrame (B : Type*) [BooleanAlgebra B] : EpistemicCompatFrame (Possibility B) where
  compat := compat
  compat_refl := ⟨λ x => ⟨by rw [inf_idem]; exact x.truth_ne_bot, x.truth_le_info,
    x.truth_le_info⟩⟩
  compat_symm := ⟨λ _ _ h => ⟨by rw [inf_comm]; exact h.1, h.2.2, h.2.1⟩⟩
  access := access
  access_refl := ⟨λ _ => ⟨le_rfl, le_rfl⟩⟩
  rRegular := by
    rintro x y' y ⟨hab, hki⟩ ⟨_, hbl, hdk⟩
    have hne : x.truth ⊔ y.truth ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot le_sup_left
    refine ⟨diag _ hne, ⟨?_, le_sup_left, sup_le x.truth_le_info (hdk.trans hki)⟩,
      λ x'' ⟨_, hx', hx''⟩ => ⟨diag _ hne, ⟨hx'', hx'⟩, ?_, sup_le (hab.trans hbl)
        y.truth_le_info, le_sup_right⟩⟩
    · simp only [diag_truth, inf_sup_self]; exact x.truth_ne_bot
    · simp only [diag_truth, inf_of_le_right (le_sup_right : y.truth ≤ x.truth ⊔ y.truth)]
      exact y.truth_ne_bot
  knowable := λ x => ⟨diag x.truth x.truth_ne_bot, λ z ⟨haz, hza⟩ w ⟨hzw, hzw', hwz⟩ => by
    have hz : z.truth = x.truth := le_antisymm (z.truth_le_info.trans hza) haz
    exact ⟨by rwa [← hz], hz ▸ hzw', hwz.trans (hza.trans x.truth_le_info)⟩⟩

section Decidable

variable [DecidableEq B] [DecidableLE B]

instance : DecidableRel (epistemicFrame B).toCompatFrame.compat :=
  inferInstanceAs (DecidableRel (compat (B := B)))

instance : DecidableRel (epistemicFrame B).compat :=
  inferInstanceAs (DecidableRel (compat (B := B)))

instance : DecidableRel (epistemicFrame B).access :=
  inferInstanceAs (DecidableRel (access (B := B)))

instance : DecidableRel (epistemicFrame B).toModalCompatFrame.access :=
  inferInstanceAs (DecidableRel (access (B := B)))

end Decidable

/-- Refinement in the epistemic frame is componentwise: `(a, i) ⊑ (a', i')` iff `a = a'` and
`i ≤ i'`. [holliday-mandelkern-2024] Lemma 5.2. -/
theorem refines_iff (y x : Possibility B) :
    refines (epistemicFrame B).toCompatFrame y x ↔ y.truth = x.truth ∧ y.info ≤ x.info := by
  constructor
  · intro h
    by_contra hne
    rcases not_and_or.mp hne with hne | hii
    · rcases not_and_or.mp (mt (λ h : y.truth ≤ x.truth ∧ x.truth ≤ y.truth =>
          le_antisymm h.1 h.2) hne) with hyx | hxy
      · have hne' : y.truth ⊓ x.truthᶜ ≠ ⊥ := by rwa [← sdiff_eq, Ne, sdiff_eq_bot_iff]
        refine (h ⟨(y.truth ⊓ x.truthᶜ, y.truth), hne', inf_le_left⟩
          ⟨?_, le_rfl, inf_le_left.trans y.truth_le_info⟩).1 ?_
        · show y.truth ⊓ (y.truth ⊓ x.truthᶜ) ≠ ⊥
          rwa [inf_of_le_right inf_le_left]
        · show x.truth ⊓ (y.truth ⊓ x.truthᶜ) = ⊥
          rw [inf_comm y.truth, ← inf_assoc, inf_compl_eq_bot, bot_inf_eq]
      · exact hxy (h (diag y.truth y.truth_ne_bot) y.compat_diag_truth).2.1
    · exact hii (h (diag y.info y.info_ne_bot) y.compat_diag_info).2.2
  · rintro ⟨ha, hi⟩ z ⟨hz, hz', hz''⟩
    exact ⟨by rwa [← ha], ha ▸ hz', hz''.trans hi⟩

/-- The underlying set of the embedding `e_B`: the possibilities whose truth entails `b`.
[holliday-mandelkern-2024] Theorem 5.7.2. -/
def embed (b : B) : Set (Possibility B) := {x | x.truth ≤ b}

@[simp] theorem mem_embed {b : B} {x : Possibility B} : x ∈ embed b ↔ x.truth ≤ b := Iff.rfl

instance [DecidableLE B] (b : B) : DecidablePred (· ∈ embed b) :=
  λ x => inferInstanceAs (Decidable (x.truth ≤ b))

instance [DecidableLE B] (b : B) : DecidablePred (embed b) :=
  λ x => inferInstanceAs (Decidable (x.truth ≤ b))

/-- `b` must be the case at `(a, i)` iff `i ≤ b`. [holliday-mandelkern-2024] Lemma 5.8.2. -/
theorem mem_box_embed {b : B} {x : Possibility B} :
    x ∈ box (epistemicFrame B).toModalCompatFrame (embed b) ↔ x.info ≤ b :=
  ⟨λ h => h _ x.access_diag_info, λ h y hy => (y.truth_le_info.trans hy.2).trans h⟩

/-- `b` might be the case at `(a, i)` iff `a ⊓ b ≠ ⊥`. [holliday-mandelkern-2024] Lemma 5.8.3. -/
theorem mem_diamond_embed {b : B} {x : Possibility B} :
    x ∈ diamond (epistemicFrame B).toModalCompatFrame (embed b) ↔ x.truth ⊓ b ≠ ⊥ := by
  constructor
  · intro h
    have := h _ x.compat_diag_truth
    simp only [mem_box, not_forall] at this
    obtain ⟨y', ⟨-, hy'a⟩, hy'⟩ := this
    simp only [mem_orthoNeg, not_forall, not_not] at hy'
    obtain ⟨y'', ⟨hne, -, -⟩, hy''⟩ := hy'
    exact ne_bot_of_le_ne_bot hne (inf_le_inf (y'.truth_le_info.trans hy'a) hy'')
  · intro h x' ⟨_, hx', _⟩ hbox
    have hle : x.truth ⊓ b ≤ x'.info := inf_le_left.trans hx'
    refine hbox ⟨(x'.truth ⊔ x.truth ⊓ b, x'.info), ne_bot_of_le_ne_bot x'.truth_ne_bot
      le_sup_left, sup_le x'.truth_le_info hle⟩ ⟨le_sup_left, le_rfl⟩
      ⟨(x.truth ⊓ b, x'.info), h, hle⟩ ⟨?_, sup_le x'.truth_le_info hle, hle⟩ inf_le_right
    show (x'.truth ⊔ x.truth ⊓ b) ⊓ (x.truth ⊓ b) ≠ ⊥
    rwa [inf_of_le_right le_sup_right]

/-- Embedded propositions are regular: the witness for `(a, i) ∉ e(b)` is `(a ⊓ bᶜ, i)`.
[holliday-mandelkern-2024] Theorem 5.7.2. -/
theorem embed_isRegular (b : B) : IsRegular (epistemicFrame B).toCompatFrame (embed b) := by
  intro x
  by_cases hx : x.truth ≤ b
  · exact Or.inl hx
  · right
    have hne : x.truth ⊓ bᶜ ≠ ⊥ := by rwa [← sdiff_eq, Ne, sdiff_eq_bot_iff]
    refine ⟨⟨(x.truth ⊓ bᶜ, x.info), hne, inf_le_left.trans x.truth_le_info⟩,
      ⟨?_, x.truth_le_info, inf_le_left.trans x.truth_le_info⟩, λ z ⟨hz, _, _⟩ hzb => hz ?_⟩
    · show x.truth ⊓ (x.truth ⊓ bᶜ) ≠ ⊥
      rwa [inf_of_le_right inf_le_left]
    · show x.truth ⊓ bᶜ ⊓ z.truth = ⊥
      have : bᶜ ⊓ z.truth = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_left _ hzb).trans compl_inf_eq_bot.le)
      rw [inf_assoc, this, inf_bot_eq]

/-- The embedding sends complements to orthocomplements.
[holliday-mandelkern-2024] Theorem 5.7.2. -/
theorem embed_compl (b : B) :
    embed bᶜ = orthoNeg (epistemicFrame B).toCompatFrame (embed b) := by
  ext x
  simp only [mem_embed, mem_orthoNeg]
  constructor
  · intro hx y ⟨hne, _, _⟩ hy
    exact hne (le_bot_iff.mp ((inf_le_inf hx hy).trans compl_inf_eq_bot.le))
  · intro h
    by_contra hx
    have hne : x.truth ⊓ b ≠ ⊥ := by
      rwa [← compl_compl b, ← sdiff_eq, Ne, sdiff_eq_bot_iff]
    refine h ⟨(x.truth ⊓ b, x.info), hne, inf_le_left.trans x.truth_le_info⟩
      ⟨?_, x.truth_le_info, inf_le_left.trans x.truth_le_info⟩ inf_le_right
    show x.truth ⊓ (x.truth ⊓ b) ≠ ⊥
    rwa [inf_of_le_right inf_le_left]

/-- The embedding preserves meets. [holliday-mandelkern-2024] Theorem 5.7.2. -/
theorem embed_inf (b c : B) : embed (b ⊓ c) = embed b ∩ embed c := by
  ext x; exact le_inf_iff

/-- Inheritance for embedded propositions: what is the case and compatible with `c` is
compatible with both. [holliday-mandelkern-2024] Proposition 5.12.3. -/
theorem embed_inter_diamond_embed_subset (b c : B) :
    embed b ∩ diamond (epistemicFrame B).toModalCompatFrame (embed c) ⊆
      diamond (epistemicFrame B).toModalCompatFrame (embed (b ⊓ c)) := by
  rintro x ⟨hb, hc⟩
  rw [mem_diamond_embed] at hc ⊢
  rwa [← inf_assoc, inf_of_le_left hb]

/-! ### The embedding into the regular propositions -/

/-- The embedding `e_B : B → O(Bᵉ)` as a regular proposition.
[holliday-mandelkern-2024] Theorem 5.7.2. -/
def eB (b : B) : (epistemicFrame B).toCompatFrame.Regular :=
  (epistemicFrame B).toCompatFrame.regOf (embed b) (embed_isRegular b)

@[simp] theorem coe_eB (b : B) : (eB b : Set (Possibility B)) = embed b := rfl

theorem eB_mono {b c : B} (h : b ≤ c) : eB b ≤ eB c := λ _ hx => le_trans hx h

/-- `e_B` reflects order: the possibility `(b, ⊤)` witnesses `b ≤ c` from `e_B b ≤ e_B c`. -/
theorem eB_le_iff {b c : B} : eB b ≤ eB c ↔ b ≤ c := by
  refine ⟨λ h => ?_, eB_mono⟩
  rcases eq_or_ne b ⊥ with rfl | hb
  · exact bot_le
  · exact @h ⟨(b, ⊤), hb, le_top⟩ le_rfl

theorem eB_injective : Function.Injective (eB : B → (epistemicFrame B).toCompatFrame.Regular) :=
  λ _ _ h => le_antisymm (eB_le_iff.mp h.le) (eB_le_iff.mp h.ge)

theorem eB_top : eB (⊤ : B) = ⊤ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_top]
  ext x; simp [embed]

theorem eB_bot : eB (⊥ : B) = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_bot]
  ext x; simp [embed, le_bot_iff, x.truth_ne_bot]

theorem eB_inf (b c : B) : eB (b ⊓ c) = eB b ⊓ eB c := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_inf, coe_eB, coe_eB, embed_inf]

theorem eB_compl (b : B) : eB bᶜ = (eB b)ᶜ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_compl, coe_eB, embed_compl]

/-- The diamond of an embedded proposition strictly extends it unless the proposition is
trivial: `(⊤, ⊤)` lies in `◇e(b)` but not in `e(b)`.
[holliday-mandelkern-2024] Theorem 5.7.4. -/
theorem not_diamond_embed_subset {b : B} (hb : b ≠ ⊥) (hb' : b ≠ ⊤) :
    ¬ diamond (epistemicFrame B).toModalCompatFrame (embed b) ⊆ embed b := by
  intro h
  have htop : (⊤ : B) ≠ ⊥ := ne_bot_of_le_ne_bot hb le_top
  have := h (a := ⟨(⊤, ⊤), htop, le_rfl⟩) (mem_diamond_embed.mpr (by rwa [top_inf_eq]))
  exact hb' (top_le_iff.mp this)

end Orthologic
