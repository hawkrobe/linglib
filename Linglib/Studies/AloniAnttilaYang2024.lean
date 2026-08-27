import Linglib.Logic.Team.BSML.Properties
import Linglib.Logic.Team.BSML.Bisimulation
import Linglib.Logic.Bilateral.Defs
import Linglib.Logic.Team.Closure
import Linglib.Studies.Aloni2022

/-!
# Aloni, Anttila and Yang (2024): state-based modal logics for free choice

Two extensions of bilateral state-based modal logic: BSML⨼ adds the global
(inquisitive) disjunction, supported when either disjunct is; BSML⊘ adds the
emptiness operator, supported when the argument is or the state is empty.
The closure profile of the three logics comes from two connectives alone
(Fact 2.7): NE is the only obstruction to downward closure and the empty-state
property, ⨼ the only obstruction to union closure. All three logics are
invariant under bounded state bisimulation (Theorem 3.8), and BSML, though
union closed, cannot express every union-closed bisimulation-invariant
property (Fact 3.19).

Here the three logics are the fragments of one syntax: `Formula` carries ⊥,
NE, ⨼ and ⊘ together, and `NEFree`, `GDFree`, `EmptFree` cut out the
languages, so each closure property is a single theorem under its fragment
hypothesis. The §2 equivalences between the new connectives are stated
(`support_empt_iff_gdisj_bot`, `support_poss_gdisj`, the distributions of ∧
and ∨ over ⨼), Lemma 3.18 and the counterexample of Fact 3.19 are proved on a
two-world model, ⊘ is shown to cancel pragmatic enrichment, and narrow-scope
free choice transfers from [aloni-2022] along the embedding of BSML.
Expressive completeness (Theorems 3.15, 3.17) and the natural-deduction
systems of §4 are not formalised here; the BSML system of Definition 4.33
lives in `Logic/Team/BSML/NaturalDeduction`.

## References

* [aloni-anttila-yang-2024]
* [aloni-2022]
* [anttila-2025]
-/

namespace AloniAnttilaYang2024

variable {W W' : Type*} [DecidableEq W] [DecidableEq W'] {Atom : Type*}

open ModalLogic (KripkeModel StateBisim WorldBisim)

/-! ### Syntax and semantics -/

/-- The joint syntax of BSML, BSML⨼ and BSML⊘ (Definition 2.1): BSML with the weak
    contradiction `⊥`, the global disjunction `⨼` and the emptiness operator `⊘`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  /-- Weak contradiction `⊥`, supported by the empty state only. -/
  | bot
  /-- Nonemptiness atom `NE`. -/
  | ne
  | neg (φ : Formula Atom)
  | conj (φ ψ : Formula Atom)
  /-- Tensor (local) disjunction. -/
  | disj (φ ψ : Formula Atom)
  /-- Global disjunction `⨼`. -/
  | gdisj (φ ψ : Formula Atom)
  /-- Emptiness operator `⊘`. -/
  | empt (φ : Formula Atom)
  | poss (φ : Formula Atom)
  deriving Repr, DecidableEq

namespace Formula

/-- `□φ := ¬◇¬φ`. -/
def nec (φ : Formula Atom) : Formula Atom := .neg (.poss (.neg φ))

/-- No occurrence of `NE`. -/
def NEFree : Formula Atom → Prop
  | .ne => False
  | .neg φ | .empt φ | .poss φ => φ.NEFree
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => φ.NEFree ∧ ψ.NEFree
  | _ => True

/-- No occurrence of `⨼`: the BSML⊘ fragment. -/
def GDFree : Formula Atom → Prop
  | .gdisj _ _ => False
  | .neg φ | .empt φ | .poss φ => φ.GDFree
  | .conj φ ψ | .disj φ ψ => φ.GDFree ∧ ψ.GDFree
  | _ => True

/-- No occurrence of `⊘`: the BSML⨼ fragment. -/
def EmptFree : Formula Atom → Prop
  | .empt _ => False
  | .neg φ | .poss φ => φ.EmptFree
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => φ.EmptFree ∧ ψ.EmptFree
  | _ => True

instance : (φ : Formula Atom) → Decidable φ.NEFree
  | .atom _ | .bot => isTrue trivial
  | .ne => isFalse id
  | .neg φ | .empt φ | .poss φ => by unfold NEFree; exact instDecidableNEFree φ
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => by
    unfold NEFree; exact @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)

instance : (φ : Formula Atom) → Decidable φ.GDFree
  | .atom _ | .bot | .ne => isTrue trivial
  | .gdisj _ _ => isFalse id
  | .neg φ | .empt φ | .poss φ => by unfold GDFree; exact instDecidableGDFree φ
  | .conj φ ψ | .disj φ ψ => by
    unfold GDFree; exact @instDecidableAnd _ _ (instDecidableGDFree φ) (instDecidableGDFree ψ)

instance : (φ : Formula Atom) → Decidable φ.EmptFree
  | .atom _ | .bot | .ne => isTrue trivial
  | .empt _ => isFalse id
  | .neg φ | .poss φ => by unfold EmptFree; exact instDecidableEmptFree φ
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => by
    unfold EmptFree; exact @instDecidableAnd _ _ (instDecidableEmptFree φ) (instDecidableEmptFree ψ)

end Formula

/-- Bilateral evaluation (Definition 2.3): `eval M true φ t` is support, `eval M false φ t`
    anti-support. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true, .atom p, t => ∀ w ∈ t, M.val p w = true
  | false, .atom p, t => ∀ w ∈ t, M.val p w = false
  | true, .bot, t => t = ∅
  | false, .bot, _ => True
  | true, .ne, t => t.Nonempty
  | false, .ne, t => t = ∅
  | true, .neg ψ, t => eval M false ψ t
  | false, .neg ψ, t => eval M true ψ t
  | true, .conj ψ₁ ψ₂, t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂, t =>
    ∃ t₁ t₂ : Finset W, Team.splitsAs t t₁ t₂ ∧ eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true, .disj ψ₁ ψ₂, t =>
    ∃ t₁ t₂ : Finset W, Team.splitsAs t t₁ t₂ ∧ eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂, t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true, .gdisj ψ₁ ψ₂, t => eval M true ψ₁ t ∨ eval M true ψ₂ t
  | false, .gdisj ψ₁ ψ₂, t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true, .empt ψ, t => eval M true ψ t ∨ t = ∅
  | false, .empt ψ, t => eval M false ψ t
  | true, .poss ψ, t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ, t => ∀ w ∈ t, eval M false ψ (M.access w)

abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

variable (M : KripkeModel W Atom) (φ ψ χ : Formula Atom) (t : Finset W)

@[simp] theorem support_neg : support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl
@[simp] theorem antiSupport_neg : antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl
@[simp] theorem support_bot : support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl
@[simp] theorem antiSupport_bot : antiSupport M (.bot : Formula Atom) t := trivial
@[simp] theorem support_ne : support M (.ne : Formula Atom) t ↔ t.Nonempty := Iff.rfl
@[simp] theorem antiSupport_ne : antiSupport M (.ne : Formula Atom) t ↔ t = ∅ := Iff.rfl
@[simp] theorem support_conj : support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl
@[simp] theorem antiSupport_disj :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl
@[simp] theorem support_gdisj : support M (.gdisj φ ψ) t ↔ support M φ t ∨ support M ψ t := Iff.rfl
@[simp] theorem antiSupport_gdisj :
    antiSupport M (.gdisj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl
@[simp] theorem support_empt : support M (.empt φ) t ↔ support M φ t ∨ t = ∅ := Iff.rfl
@[simp] theorem antiSupport_empt : antiSupport M (.empt φ) t ↔ antiSupport M φ t := Iff.rfl

/-- Support and anti-support form a bilateral logic under `Formula.neg`. -/
theorem isBilateral : Bilateral.IsBilateral (support M) (antiSupport M) Formula.neg :=
  Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

/-! ### The §2 equivalences -/

/-- `⊘φ ≡ φ ⨼ ⊥`. -/
theorem support_empt_iff_gdisj_bot : support M (.empt φ) t ↔ support M (.gdisj φ .bot) t :=
  Iff.rfl

/-- `φ ∧ (ψ ⨼ χ) ≡ (φ ∧ ψ) ⨼ (φ ∧ χ)`. -/
theorem support_conj_gdisj :
    support M (.conj φ (.gdisj ψ χ)) t ↔ support M (.gdisj (.conj φ ψ) (.conj φ χ)) t :=
  and_or_left

/-- `φ ∨ (ψ ⨼ χ) ≡ (φ ∨ ψ) ⨼ (φ ∨ χ)`. -/
theorem support_disj_gdisj :
    support M (.disj φ (.gdisj ψ χ)) t ↔ support M (.gdisj (.disj φ ψ) (.disj φ χ)) t := by
  constructor
  · rintro ⟨t₁, t₂, h, h₁, h₂ | h₂⟩
    exacts [Or.inl ⟨t₁, t₂, h, h₁, h₂⟩, Or.inr ⟨t₁, t₂, h, h₁, h₂⟩]
  · rintro (⟨t₁, t₂, h, h₁, h₂⟩ | ⟨t₁, t₂, h, h₁, h₂⟩)
    exacts [⟨t₁, t₂, h, h₁, Or.inl h₂⟩, ⟨t₁, t₂, h, h₁, Or.inr h₂⟩]

/-- `◇(φ ⨼ ψ) ≡ ◇φ ∨ ◇ψ`: the diamond converts the global disjunction into the
    tensor one (the soundness of Conv◇⨼∨ in Theorem 4.3). -/
theorem support_poss_gdisj :
    support M (.poss (.gdisj φ ψ)) t ↔ support M (.disj (.poss φ) (.poss ψ)) t := by
  classical
  constructor
  · intro h
    refine ⟨t.filter λ w ↦ ∃ s ⊆ M.access w, s.Nonempty ∧ support M φ s,
      t.filter λ w ↦ ∃ s ⊆ M.access w, s.Nonempty ∧ support M ψ s, ?_, ?_, ?_⟩
    · show _ ∪ _ = t
      ext w
      simp only [Finset.mem_union, Finset.mem_filter]
      refine ⟨λ h' ↦ h'.elim And.left And.left, λ hw ↦ ?_⟩
      obtain ⟨s, hs, hne, hφ | hψ⟩ := h w hw
      exacts [Or.inl ⟨hw, s, hs, hne, hφ⟩, Or.inr ⟨hw, s, hs, hne, hψ⟩]
    · intro w hw; exact (Finset.mem_filter.mp hw).2
    · intro w hw; exact (Finset.mem_filter.mp hw).2
  · rintro ⟨t₁, t₂, h, h₁, h₂⟩ w hw
    rcases Finset.mem_union.mp (h ▸ hw) with hw | hw
    · obtain ⟨s, hs, hne, hφ⟩ := h₁ w hw; exact ⟨s, hs, hne, Or.inl hφ⟩
    · obtain ⟨s, hs, hne, hψ⟩ := h₂ w hw; exact ⟨s, hs, hne, Or.inr hψ⟩

/-! ### Closure properties (Fact 2.7) -/

private theorem eval_empty_of_neFree (hNE : φ.NEFree) : support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨λ w hw ↦ absurd hw (by simp), λ w hw ↦ absurd hw (by simp)⟩
  | bot => exact ⟨rfl, trivial⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨(ih₁ hNE.1).1, (ih₂ hNE.2).1⟩,
      ⟨∅, ∅, Finset.empty_union ∅, (ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨∅, ∅, Finset.empty_union ∅, (ih₁ hNE.1).1, (ih₂ hNE.2).1⟩,
      ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Or.inl (ih₁ hNE.1).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | empt ψ ih => exact ⟨Or.inr rfl, (ih hNE).2⟩
  | poss ψ _ => exact ⟨λ w hw ↦ absurd hw (by simp), λ w hw ↦ absurd hw (by simp)⟩

/-- NE-free formulas have the empty-state property. -/
theorem support_empty_of_neFree (hNE : φ.NEFree) : support M φ ∅ :=
  (eval_empty_of_neFree M φ hNE).1

private theorem splitsAs_inter {s t t₁ t₂ : Finset W} (h : Team.splitsAs s t₁ t₂) (hsub : t ⊆ s) :
    Team.splitsAs t (t₁ ∩ t) (t₂ ∩ t) := by
  show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
  rw [← Finset.union_inter_distrib_right, show t₁ ∪ t₂ = s from h]
  exact Finset.inter_eq_right.mpr hsub

private theorem eval_lower_of_neFree (hNE : φ.NEFree) :
    (∀ s t : Finset W, t ⊆ s → support M φ s → support M φ t) ∧
    ∀ s t : Finset W, t ⊆ s → antiSupport M φ s → antiSupport M φ t := by
  induction φ with
  | atom p => exact ⟨λ _ _ h hs w hw ↦ hs w (h hw), λ _ _ h hs w hw ↦ hs w (h hw)⟩
  | bot => exact ⟨λ _ _ h hs ↦ Finset.subset_empty.mp (hs ▸ h), λ _ _ _ _ ↦ trivial⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hNE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hNE.2
    refine ⟨λ s t h ⟨h₁, h₂⟩ ↦ ⟨ihs₁ s t h h₁, ihs₂ s t h h₂⟩, ?_⟩
    rintro s t h ⟨t₁, t₂, hsplit, h₁, h₂⟩
    exact ⟨t₁ ∩ t, t₂ ∩ t, splitsAs_inter hsplit h,
      iha₁ t₁ _ Finset.inter_subset_left h₁, iha₂ t₂ _ Finset.inter_subset_left h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hNE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hNE.2
    refine ⟨?_, λ s t h ⟨h₁, h₂⟩ ↦ ⟨iha₁ s t h h₁, iha₂ s t h h₂⟩⟩
    rintro s t h ⟨t₁, t₂, hsplit, h₁, h₂⟩
    exact ⟨t₁ ∩ t, t₂ ∩ t, splitsAs_inter hsplit h,
      ihs₁ t₁ _ Finset.inter_subset_left h₁, ihs₂ t₂ _ Finset.inter_subset_left h₂⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hNE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hNE.2
    exact ⟨λ s t h hs ↦ hs.imp (ihs₁ s t h) (ihs₂ s t h),
      λ s t h ⟨h₁, h₂⟩ ↦ ⟨iha₁ s t h h₁, iha₂ s t h h₂⟩⟩
  | empt ψ ih =>
    obtain ⟨ihs, iha⟩ := ih hNE
    refine ⟨?_, iha⟩
    rintro s t h (hs | rfl)
    · exact Or.inl (ihs s t h hs)
    · exact Or.inr (Finset.subset_empty.mp h)
  | poss ψ _ => exact ⟨λ _ _ h hs w hw ↦ hs w (h hw), λ _ _ h hs w hw ↦ hs w (h hw)⟩

/-- NE-free formulas are downward closed. -/
theorem isLowerSet_support_of_neFree (hNE : φ.NEFree) :
    IsLowerSet { t : Finset W | support M φ t } :=
  λ _ _ h hs ↦ (eval_lower_of_neFree M φ hNE).1 _ _ h hs

private theorem splitsAs_union {s s' s₁ s₂ t₁ t₂ : Finset W} (h : Team.splitsAs s s₁ s₂)
    (h' : Team.splitsAs s' t₁ t₂) : Team.splitsAs (s ∪ s') (s₁ ∪ t₁) (s₂ ∪ t₂) := by
  show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ s'
  rw [← h, ← h']; ac_rfl

private theorem eval_supClosed_of_gdFree (hGD : φ.GDFree) :
    (∀ s t : Finset W, support M φ s → support M φ t → support M φ (s ∪ t)) ∧
    ∀ s t : Finset W, antiSupport M φ s → antiSupport M φ t → antiSupport M φ (s ∪ t) := by
  induction φ with
  | atom p =>
    exact ⟨λ _ _ hs ht w hw ↦ (Finset.mem_union.mp hw).elim (hs w) (ht w),
      λ _ _ hs ht w hw ↦ (Finset.mem_union.mp hw).elim (hs w) (ht w)⟩
  | bot => exact ⟨λ _ _ hs ht ↦ by rw [hs, ht]; rfl, λ _ _ _ _ ↦ trivial⟩
  | ne => exact ⟨λ _ _ hs _ ↦ hs.mono Finset.subset_union_left, λ _ _ hs ht ↦ by rw [hs, ht]; rfl⟩
  | neg ψ ih => exact (ih hGD).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2
    refine ⟨λ s t ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩ ↦ ⟨ihs₁ s t hs₁ ht₁, ihs₂ s t hs₂ ht₂⟩, ?_⟩
    rintro s t ⟨s₁, s₂, hs, hs₁, hs₂⟩ ⟨t₁, t₂, ht, ht₁, ht₂⟩
    exact ⟨s₁ ∪ t₁, s₂ ∪ t₂, splitsAs_union hs ht, iha₁ _ _ hs₁ ht₁, iha₂ _ _ hs₂ ht₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2
    refine ⟨?_, λ s t ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩ ↦ ⟨iha₁ s t hs₁ ht₁, iha₂ s t hs₂ ht₂⟩⟩
    rintro s t ⟨s₁, s₂, hs, hs₁, hs₂⟩ ⟨t₁, t₂, ht, ht₁, ht₂⟩
    exact ⟨s₁ ∪ t₁, s₂ ∪ t₂, splitsAs_union hs ht, ihs₁ _ _ hs₁ ht₁, ihs₂ _ _ hs₂ ht₂⟩
  | gdisj => exact hGD.elim
  | empt ψ ih =>
    obtain ⟨ihs, iha⟩ := ih hGD
    refine ⟨?_, iha⟩
    rintro s t (hs | rfl) (ht | rfl)
    · exact Or.inl (ihs s t hs ht)
    · simpa using Or.inl hs
    · simpa using Or.inl ht
    · simp
  | poss ψ _ =>
    exact ⟨λ _ _ hs ht w hw ↦ (Finset.mem_union.mp hw).elim (hs w) (ht w),
      λ _ _ hs ht w hw ↦ (Finset.mem_union.mp hw).elim (hs w) (ht w)⟩

/-- ⨼-free formulas are union closed; in particular every BSML⊘ formula is. -/
theorem supClosed_support_of_gdFree (hGD : φ.GDFree) :
    SupClosed { t : Finset W | support M φ t } :=
  λ _ hs _ ht ↦ (eval_supClosed_of_gdFree M φ hGD).1 _ _ hs ht

/-- Classical formulas — NE-free and ⨼-free — are flat. -/
theorem isFlat_support_of_neFree_gdFree (hNE : φ.NEFree) (hGD : φ.GDFree) :
    Team.IsFlat { t : Finset W | support M φ t } :=
  Team.isFlat_of_isLowerSet_supClosed_empty (isLowerSet_support_of_neFree M φ hNE)
    (supClosed_support_of_gdFree M φ hGD) (support_empty_of_neFree M φ hNE)

/-! ### BSML is not complete for union-closed properties -/

/-- Lemma 3.18: a BSML formula with the empty-state property is downward closed. -/
theorem isLowerSet_of_support_empty (hGD : φ.GDFree) (hE : φ.EmptFree) :
    (support M φ ∅ → ∀ s t : Finset W, t ⊆ s → support M φ s → support M φ t) ∧
    (antiSupport M φ ∅ → ∀ s t : Finset W, t ⊆ s → antiSupport M φ s → antiSupport M φ t) := by
  induction φ with
  | atom p => exact ⟨λ _ _ _ h hs w hw ↦ hs w (h hw), λ _ _ _ h hs w hw ↦ hs w (h hw)⟩
  | bot => exact ⟨λ _ _ _ h hs ↦ Finset.subset_empty.mp (hs ▸ h), λ _ _ _ _ _ ↦ trivial⟩
  | ne =>
    exact ⟨λ h ↦ absurd h Finset.not_nonempty_empty,
      λ _ _ _ h hs ↦ by rw [hs] at h; exact Finset.subset_empty.mp h⟩
  | neg ψ ih => exact (ih hGD hE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1 hE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2 hE.2
    refine ⟨λ ⟨e₁, e₂⟩ s t h ⟨h₁, h₂⟩ ↦ ⟨ihs₁ e₁ s t h h₁, ihs₂ e₂ s t h h₂⟩, ?_⟩
    rintro ⟨u₁, u₂, hu, e₁, e₂⟩ s t h ⟨t₁, t₂, hsplit, h₁, h₂⟩
    have hu₁ : u₁ = ∅ := Finset.subset_empty.mp (Team.splitsAs_left_subset hu)
    have hu₂ : u₂ = ∅ := Finset.subset_empty.mp (Team.splitsAs_right_subset hu)
    subst hu₁ hu₂
    exact ⟨t₁ ∩ t, t₂ ∩ t, splitsAs_inter hsplit h,
      iha₁ e₁ t₁ _ Finset.inter_subset_left h₁, iha₂ e₂ t₂ _ Finset.inter_subset_left h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1 hE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2 hE.2
    refine ⟨?_, λ ⟨e₁, e₂⟩ s t h ⟨h₁, h₂⟩ ↦ ⟨iha₁ e₁ s t h h₁, iha₂ e₂ s t h h₂⟩⟩
    rintro ⟨u₁, u₂, hu, e₁, e₂⟩ s t h ⟨t₁, t₂, hsplit, h₁, h₂⟩
    have hu₁ : u₁ = ∅ := Finset.subset_empty.mp (Team.splitsAs_left_subset hu)
    have hu₂ : u₂ = ∅ := Finset.subset_empty.mp (Team.splitsAs_right_subset hu)
    subst hu₁ hu₂
    exact ⟨t₁ ∩ t, t₂ ∩ t, splitsAs_inter hsplit h,
      ihs₁ e₁ t₁ _ Finset.inter_subset_left h₁, ihs₂ e₂ t₂ _ Finset.inter_subset_left h₂⟩
  | gdisj => exact hGD.elim
  | empt => exact hE.elim
  | poss ψ _ => exact ⟨λ _ _ _ h hs w hw ↦ hs w (h hw), λ _ _ _ h hs w hw ↦ hs w (h hw)⟩

/-- The two-world model of Fact 3.19: `p` holds at `true` only, nothing is accessible. -/
def twoWorlds : KripkeModel Bool Unit where
  access _ := ∅
  val _ w := w

/-- The property `‖(p ∧ NE) ∨ (¬p ∧ NE)‖ ∪ ‖⊥‖` of Fact 3.19: union closed and
    bisimulation invariant, yet not expressible in BSML. -/
def splitProperty (s : Finset Bool) : Prop :=
  support twoWorlds (.disj (.conj (.atom ()) .ne) (.conj (.neg (.atom ())) .ne)) s ∨ s = ∅

/-- Fact 3.19: no BSML formula expresses `splitProperty` — it holds on `∅` and on
    `{true, false}`, so a BSML formula expressing it would be downward closed
    (Lemma 3.18) and hold on `{true}`, where the property fails. -/
theorem bsml_not_complete_for_unionClosed :
    ¬ ∃ φ : Formula Unit, φ.GDFree ∧ φ.EmptFree ∧
      ∀ s : Finset Bool, support twoWorlds φ s ↔ splitProperty s := by
  rintro ⟨φ, hGD, hE, h⟩
  have hempty : support twoWorlds φ ∅ := (h ∅).mpr (Or.inr rfl)
  have hboth : support twoWorlds φ {true, false} := (h _).mpr <| Or.inl
    ⟨{true}, {false}, rfl, ⟨λ w hw ↦ by simpa [twoWorlds] using hw, by simp⟩,
      ⟨λ w hw ↦ by simpa [twoWorlds] using hw, by simp⟩⟩
  have htrue := (h {true}).mp
    ((isLowerSet_of_support_empty twoWorlds φ hGD hE).1 hempty _ _ (by simp) hboth)
  rcases htrue with ⟨t₁, t₂, hsplit, _, hp, hne⟩ | h1
  · obtain ⟨w, hw⟩ := hne
    have : w ∈ ({true} : Finset Bool) := hsplit ▸ Finset.mem_union_right _ hw
    have hw' := hp w hw
    simp_all [twoWorlds]
  · exact absurd h1 (by simp)

/-! ### The emptiness operator cancels enrichment -/

/-- `⊘(α ∧ NE) ≡ α` for classical `α` (§5): the emptiness operator undoes the
    non-emptiness that pragmatic enrichment adds. -/
theorem support_empt_conj_ne (hα : φ.NEFree) :
    support M (.empt (.conj φ .ne)) t ↔ support M φ t := by
  constructor
  · rintro (⟨h, _⟩ | rfl)
    exacts [h, support_empty_of_neFree M φ hα]
  · intro h
    rcases t.eq_empty_or_nonempty with rfl | hne
    exacts [Or.inr rfl, Or.inl ⟨h, hne⟩]

/-! ### The embedding of BSML -/

/-- BSML formulas as formulas of the joint language. -/
def ofBSML : BSML.Formula Atom → Formula Atom
  | .atom p => .atom p
  | .ne => .ne
  | .neg ψ => .neg (ofBSML ψ)
  | .conj ψ₁ ψ₂ => .conj (ofBSML ψ₁) (ofBSML ψ₂)
  | .disj ψ₁ ψ₂ => .disj (ofBSML ψ₁) (ofBSML ψ₂)
  | .poss ψ => .poss (ofBSML ψ)

theorem gdFree_ofBSML (φ : BSML.Formula Atom) : (ofBSML φ).GDFree := by
  induction φ <;> simp_all [ofBSML, Formula.GDFree]

theorem emptFree_ofBSML (φ : BSML.Formula Atom) : (ofBSML φ).EmptFree := by
  induction φ <;> simp_all [ofBSML, Formula.EmptFree]

/-- The embedding preserves bilateral evaluation: the joint language is a
    conservative extension of BSML. -/
theorem eval_ofBSML (b : Bool) (φ : BSML.Formula Atom) :
    eval M b (ofBSML φ) t ↔ BSML.eval M b φ t := by
  induction φ generalizing b t with
  | atom p => cases b <;> rfl
  | ne => cases b <;> rfl
  | neg ψ ih => cases b <;> simp only [ofBSML, eval, BSML.eval, ih]
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [ofBSML, eval, BSML.eval]
      constructor <;> rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
      exacts [⟨t₁, t₂, hsplit, (ih₁ t₁ false).mp h₁, (ih₂ t₂ false).mp h₂⟩,
        ⟨t₁, t₂, hsplit, (ih₁ t₁ false).mpr h₁, (ih₂ t₂ false).mpr h₂⟩]
    · simp only [ofBSML, eval, BSML.eval, ih₁, ih₂]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [ofBSML, eval, BSML.eval, ih₁, ih₂]
    · simp only [ofBSML, eval, BSML.eval]
      constructor <;> rintro ⟨t₁, t₂, hsplit, h₁, h₂⟩
      exacts [⟨t₁, t₂, hsplit, (ih₁ t₁ true).mp h₁, (ih₂ t₂ true).mp h₂⟩,
        ⟨t₁, t₂, hsplit, (ih₁ t₁ true).mpr h₁, (ih₂ t₂ true).mpr h₂⟩]
  | poss ψ ih =>
    cases b
    · simp only [ofBSML, eval, BSML.eval, ih]
    · simp only [ofBSML, eval, BSML.eval]
      constructor <;> intro h w hw <;> obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
      exacts [⟨s, hsub, hne, (ih s true).mp hsupp⟩, ⟨s, hsub, hne, (ih s true).mpr hsupp⟩]

/-- Narrow-scope free choice, `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β`, transported from
    [aloni-2022] along the embedding. -/
theorem narrowScopeFC {α β : BSML.Formula Atom} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (ofBSML (BSML.enrich (.poss (.disj α β)))) t) :
    support M (ofBSML (.conj (.poss α) (.poss β))) t :=
  (eval_ofBSML M t true _).mpr (Aloni2022.narrowScopeFC hα hβ ((eval_ofBSML M t true _).mp h))

/-! ### Bisimulation invariance (Theorem 3.8) -/

/-- Modal depth: `⊘` and `¬` preserve it, the binary connectives take the maximum,
    `◇` increments. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .bot | .ne => 0
  | .neg ψ | .empt ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ | .disj ψ₁ ψ₂ | .gdisj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-- Theorem 3.8: `k`-bisimilar states agree on every formula of modal depth at most
    `k`, in both polarities. -/
theorem bisim_invariant_eval {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}
    (φ : Formula Atom) {k : ℕ} (hd : φ.modalDepth ≤ k)
    {s : Finset W} {s' : Finset W'} (hbisim : StateBisim k M s M' s')
    (b : Bool) : eval M b φ s ↔ eval M' b φ s' := by
  induction φ generalizing k s s' b with
  | atom p =>
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | bot =>
    cases b
    · exact ⟨λ _ ↦ trivial, λ _ ↦ trivial⟩
    · exact hbisim.eq_empty_iff
  | ne =>
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    cases b
    · exact ih hd hbisim true
    · exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ := hbisim.splitPreserve hsplit
          (Team.splitsAs_left_subset hsplit) (Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁, (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ := StateBisim.splitPreserve hbisim.symm hsplit'
          (Team.splitsAs_left_subset hsplit') (Team.splitsAs_right_subset hsplit')
        exact ⟨t, u, hsplit, (ih₁ hd₁ hbt.symm false).mpr h₁, (ih₂ hd₂ hbu.symm false).mpr h₂⟩
    · exact and_congr (ih₁ hd₁ hbisim true) (ih₂ hd₂ hbisim true)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · exact and_congr (ih₁ hd₁ hbisim false) (ih₂ hd₂ hbisim false)
    · constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ := hbisim.splitPreserve hsplit
          (Team.splitsAs_left_subset hsplit) (Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁, (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ := StateBisim.splitPreserve hbisim.symm hsplit'
          (Team.splitsAs_left_subset hsplit') (Team.splitsAs_right_subset hsplit')
        exact ⟨t, u, hsplit, (ih₁ hd₁ hbt.symm true).mpr h₁, (ih₂ hd₂ hbu.symm true).mpr h₂⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · exact and_congr (ih₁ hd₁ hbisim false) (ih₂ hd₂ hbisim false)
    · exact or_congr (ih₁ hd₁ hbisim true) (ih₂ hd₂ hbisim true)
  | empt ψ ih =>
    cases b
    · exact ih hd hbisim false
    · exact or_congr (ih hd hbisim true) hbisim.eq_empty_iff
  | poss ψ ih =>
    cases k with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ k =>
      have hdψ : ψ.modalDepth ≤ k := Nat.le_of_succ_le_succ hd
      cases b
      · constructor
        · intro h w' hw'
          obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
          exact (ih hdψ hbw.accessStateBisim false).mp (h w hw)
        · intro h w hw
          obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
          exact (ih hdψ hbw.accessStateBisim false).mpr (h w' hw')
      · constructor
        · intro h w' hw'
          obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
          obtain ⟨t, htsub, htne, htsupp⟩ := h w hw
          obtain ⟨t', ht'sub, ht'ne, htbisim⟩ := hbw.accessStateBisim.exists_image_subset htsub
          exact ⟨t', ht'sub, ht'ne htne, (ih hdψ htbisim true).mp htsupp⟩
        · intro h w hw
          obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
          obtain ⟨t', ht'sub, ht'ne, ht'supp⟩ := h w' hw'
          obtain ⟨t, htsub, htne, htbisim⟩ :=
            hbw.accessStateBisim.symm.exists_image_subset ht'sub
          exact ⟨t, htsub, htne ht'ne, (ih hdψ htbisim.symm true).mpr ht'supp⟩

end AloniAnttilaYang2024
