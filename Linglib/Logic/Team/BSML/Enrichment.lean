module

public import Linglib.Logic.Team.BSML.Defs

/-!
# Pragmatic enrichment in BSML

This file defines the pragmatic enrichment `[·]⁺` of a BSML formula and proves how it
interacts with support, negation and the variant BSML*. Enrichment conjoins the
non-emptiness atom `NE` to every subformula, so a team supports an enriched formula only
when each subformula is witnessed by a non-empty team. Aloni introduces it to model the
neglect-zero tendency, the disposition of language users to disregard models that verify a
sentence through an empty witness, and derives the free-choice inferences of
`Studies/Aloni2022.lean` from it. BSML⁺ is BSML with enrichment applied globally, and
BSML* is BSML with the empty team removed from the possible states.

## Main definitions

* `BSML.enrich`: the enrichment function `[·]⁺`.
* `BSML.consequencePlus`: BSML⁺ consequence, consequence between the enriched formulas.
* `BSML.Formula.ClassicalPositive`: the formulas with neither `NE` nor negation.

## Main results

* `BSML.eval_of_eval_enrich`: on `NE`-free formulas enrichment strengthens in both
  polarities (Fact 1); `BSML.support_conj_ne_of_support_enrich` is `[α]⁺ ⊨ α ∧ NE`
  (Fact 2).
* `BSML.antiSupport_enrich_iff`: on positive formulas enrichment is vacuous under a single
  negation (Fact 9).
* `BSML.support_neg_enrich_neg_iff`, `BSML.not_support_neg_neg_enrich_iff`: under a
  double negation it is not (Fact 10).
* `BSML.consequenceStar_iff_consequencePlus`: BSML* and BSML⁺ consequence coincide on
  classical positive formulas (Fact 13).
* `BSML.negativeFC_star_poss`, `BSML.negativeFC_star_nec`: BSML* validates negative free
  choice (Fact 14); its failure in BSML⁺ is proved in the study.

## Implementation notes

Aloni defines `[·]⁺` on the `NE`-free fragment only. `enrich` is total and sends `NE` to
itself, and `□` abbreviates `¬◇¬`, so it has no clause of its own. The paper's `≡` is
mutual support consequence, so Facts 9 and 10 are stated as equivalences of support rather
than through the bilateral `BSML.equivalent`. Fact 1 is one induction over the polarity
parameter of `BSML.eval`, which is the paper's double induction.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

variable {W : Type*} [DecidableEq W] {Atom : Type*} {M : KripkeModel W Atom}
  {φ ψ : Formula Atom} {t : Finset W} {pol : Bool}

/-! ### Enrichment -/

/-- The pragmatic enrichment `[φ]⁺` conjoins `NE` to every subformula of `φ`. -/
def enrich : Formula Atom → Formula Atom
  | .atom p => .conj (.atom p) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg (enrich φ)) .ne
  | .conj φ ψ => .conj (.conj (enrich φ) (enrich ψ)) .ne
  | .disj φ ψ => .conj (.disj (enrich φ) (enrich ψ)) .ne
  | .poss φ => .conj (.poss (enrich φ)) .ne

/-- A team supporting an enriched formula is non-empty. -/
theorem nonempty_of_support_enrich (h : support M (enrich φ) t) : t.Nonempty := by
  cases φ with
  | ne => exact h
  | _ => exact h.2

/-- Only the empty team anti-supports `NE`, so anti-support of `φ ∧ NE` reduces to
anti-support of `φ`. -/
theorem antiSupport_conj_ne (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.conj φ .ne) t ↔ antiSupport M φ t where
  mp := fun ⟨_, _, hu, h, h₂⟩ ↦ by subst h₂; simpa [← hu] using h
  mpr h := ⟨t, ∅, by simp, h, rfl⟩

/-- `[¬¬φ]⁺` and `[φ]⁺` have the same support, since the two `NE` conjuncts added by the
negations are absorbed. -/
theorem support_enrich_neg_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (enrich (.neg (.neg φ))) t ↔ support M (enrich φ) t where
  mp h := (antiSupport_conj_ne M _ t).mp h.1
  mpr h := ⟨(antiSupport_conj_ne M _ t).mpr h, nonempty_of_support_enrich h⟩

/-! ### Enrichment strengthens (Facts 1 and 2) -/

/-- Enrichment strengthens an `NE`-free formula in both polarities (Fact 1). -/
theorem eval_of_eval_enrich (hNE : φ.NEFree) (h : eval M pol (enrich φ) t) :
    eval M pol φ t := by
  induction φ generalizing pol t with
  | ne => exact hNE.elim
  | atom p =>
    cases pol
    · exact (antiSupport_conj_ne M _ t).mp h
    · exact h.1
  | neg ψ ih =>
    cases pol
    · exact ih (pol := true) hNE ((antiSupport_conj_ne M _ t).mp h)
    · exact ih (pol := false) hNE h.1
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases pol
    · obtain ⟨s₁, s₂, hs, h₁, h₂⟩ := (antiSupport_conj_ne M _ t).mp h
      exact ⟨s₁, s₂, hs, ih₁ hNE.1 h₁, ih₂ hNE.2 h₂⟩
    · exact ⟨ih₁ hNE.1 h.1.1, ih₂ hNE.2 h.1.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases pol
    · obtain ⟨h₁, h₂⟩ := (antiSupport_conj_ne M _ t).mp h
      exact ⟨ih₁ hNE.1 h₁, ih₂ hNE.2 h₂⟩
    · obtain ⟨s₁, s₂, hs, h₁, h₂⟩ := h.1
      exact ⟨s₁, s₂, hs, ih₁ hNE.1 h₁, ih₂ hNE.2 h₂⟩
  | poss ψ ih =>
    cases pol
    · exact fun w hw ↦ ih hNE ((antiSupport_conj_ne M _ t).mp h w hw)
    · exact fun w hw ↦ (h.1 w hw).imp fun _ ⟨hs, hne, h'⟩ ↦ ⟨hs, hne, ih hNE h'⟩

/-- `[α]⁺ ⊨ α` for `NE`-free `α`, the support half of Fact 1. -/
theorem support_of_support_enrich (hNE : φ.NEFree) (h : support M (enrich φ) t) :
    support M φ t :=
  eval_of_eval_enrich hNE h

/-- The anti-support half of Fact 1. -/
theorem antiSupport_of_antiSupport_enrich (hNE : φ.NEFree) (h : antiSupport M (enrich φ) t) :
    antiSupport M φ t :=
  eval_of_eval_enrich hNE h

/-- `[α]⁺ ⊨ α ∧ NE` for `NE`-free `α` (Fact 2). -/
theorem support_conj_ne_of_support_enrich (hNE : φ.NEFree) (h : support M (enrich φ) t) :
    support M (.conj φ .ne) t :=
  ⟨support_of_support_enrich hNE h, nonempty_of_support_enrich h⟩

/-! ### Enrichment under negation (Facts 9 and 10) -/

/-- Enrichment is vacuous under a single negation, `¬[α]⁺ ≡ ¬α`, for positive `α`
(Fact 9). -/
theorem antiSupport_enrich_iff (hPos : φ.Positive) :
    antiSupport M (enrich φ) t ↔ antiSupport M φ t := by
  induction φ generalizing t with
  | atom p => exact antiSupport_conj_ne M _ t
  | ne => exact Iff.rfl
  | neg _ => exact hPos.elim
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    rw [enrich, antiSupport_conj_ne]
    exact exists₂_congr fun _ _ ↦ and_congr_right fun _ ↦ and_congr (ih₁ hPos.1) (ih₂ hPos.2)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    rw [enrich, antiSupport_conj_ne]
    exact and_congr (ih₁ hPos.1) (ih₂ hPos.2)
  | poss ψ ih =>
    rw [enrich, antiSupport_conj_ne]
    exact forall₂_congr fun _ _ ↦ ih hPos

/-- `¬[¬φ]⁺ ≡ ¬¬[φ]⁺`, the equivalence half of Fact 10. -/
theorem support_neg_enrich_neg_iff (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg (enrich (.neg φ))) t ↔ support M (.neg (.neg (enrich φ))) t :=
  antiSupport_conj_ne M _ t

/-- Enrichment is not vacuous under a double negation, `¬¬[p]⁺ ≢ ¬¬p` (Fact 10). The empty
team supports `¬¬p` but not `¬¬[p]⁺`. -/
theorem not_support_neg_neg_enrich_iff (p : Atom) :
    ¬ ∀ (M : KripkeModel W Atom) (t : Finset W),
      support M (.neg (.neg (enrich (.atom p)))) t ↔ support M (.neg (.neg (.atom p))) t :=
  fun h ↦ ((h ⟨fun _ ↦ ∅, fun _ _ ↦ false⟩ ∅).mpr (empty_supports_atom _ p)).2.ne_empty rfl

/-! ### BSML⁺ and BSML* (Facts 13 and 14) -/

/-- BSML⁺ consequence is consequence between the enriched formulas,
`α ⊨⁺ β iff [α]⁺ ⊨ [β]⁺`. -/
def consequencePlus (φ ψ : Formula Atom) : Prop :=
  consequence (W := W) (enrich φ) (enrich ψ)

/-- A formula is classical positive when it contains neither `NE` nor negation. -/
def Formula.ClassicalPositive (φ : Formula Atom) : Prop :=
  φ.NEFree ∧ φ.Positive

instance (φ : Formula Atom) : Decidable φ.ClassicalPositive :=
  inferInstanceAs (Decidable (φ.NEFree ∧ φ.Positive))

/-- On classical positive formulas, support of the enrichment is BSML* support on a non-empty
team: the `NE` conjunct at each subformula is the exclusion of `∅` from each split. -/
theorem support_enrich_iff_supportStar (hCP : φ.ClassicalPositive) :
    support M (enrich φ) t ↔ supportStar M φ t ∧ t.Nonempty := by
  induction φ generalizing t with
  | ne => exact hCP.1.elim
  | neg _ => exact hCP.2.elim
  | atom _ => exact Iff.rfl
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ih₁ := ih₁ (t := t) ⟨hCP.1.1, hCP.2.1⟩
    have ih₂ := ih₂ (t := t) ⟨hCP.1.2, hCP.2.2⟩
    exact ⟨fun ⟨⟨h₁, h₂⟩, hne⟩ ↦ ⟨⟨(ih₁.mp h₁).1, (ih₂.mp h₂).1⟩, hne⟩,
      fun ⟨⟨h₁, h₂⟩, hne⟩ ↦ ⟨⟨ih₁.mpr ⟨h₁, hne⟩, ih₂.mpr ⟨h₂, hne⟩⟩, hne⟩⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have ih₁ := fun t ↦ ih₁ (t := t) ⟨hCP.1.1, hCP.2.1⟩
    have ih₂ := fun t ↦ ih₂ (t := t) ⟨hCP.1.2, hCP.2.2⟩
    exact ⟨fun ⟨⟨t₁, t₂, hu, h₁, h₂⟩, hne⟩ ↦
        ⟨⟨t₁, t₂, ⟨hu, ((ih₁ t₁).mp h₁).2, ((ih₂ t₂).mp h₂).2⟩, ((ih₁ t₁).mp h₁).1,
          ((ih₂ t₂).mp h₂).1⟩, hne⟩,
      fun ⟨⟨t₁, t₂, ⟨hu, hne₁, hne₂⟩, h₁, h₂⟩, hne⟩ ↦
        ⟨⟨t₁, t₂, hu, (ih₁ t₁).mpr ⟨h₁, hne₁⟩, (ih₂ t₂).mpr ⟨h₂, hne₂⟩⟩, hne⟩⟩
  | poss ψ ih =>
    have ih := fun s ↦ ih (t := s) hCP
    exact ⟨fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨hs, hs', h'⟩ ↦
          ⟨hs, hs', ((ih _).mp h').1⟩, hne⟩,
      fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨hs, hs', h'⟩ ↦
          ⟨hs, hs', (ih _).mpr ⟨h', hs'⟩⟩, hne⟩⟩

/-- BSML* and BSML⁺ consequence coincide on classical positive formulas (Fact 13). Excluding
the empty team from the states and excluding it syntactically through `[·]⁺` agree. -/
theorem consequenceStar_iff_consequencePlus (hφ : φ.ClassicalPositive)
    (hψ : ψ.ClassicalPositive) :
    consequenceStar (W := W) φ ψ ↔ consequencePlus (W := W) φ ψ where
  mp h M t h' :=
    have ⟨hs, hne⟩ := (support_enrich_iff_supportStar hφ).mp h'
    (support_enrich_iff_supportStar hψ).mpr ⟨h M t hne hs, hne⟩
  mpr h M t hne hs :=
    ((support_enrich_iff_supportStar hψ).mp
      (h M t ((support_enrich_iff_supportStar hφ).mpr ⟨hs, hne⟩))).1

/-- Negative free choice holds in BSML*, `◇¬(α ∧ β) ⊨* ◇¬α` (Fact 14). A BSML* anti-support
split of `α ∧ β` has two non-empty parts, and the part anti-supporting `α` is the witness. -/
theorem negativeFC_star_poss (α β : Formula Atom) :
    consequenceStar (W := W) (.poss (.neg (.conj α β))) (.poss (.neg α)) :=
  fun M _ _ h w hw ↦
    have ⟨s, hs, _, hstar⟩ := h w hw
    have ⟨s₁, s₂, ⟨hsplit, hne₁, _⟩, h₁, _⟩ :
        ∃ s₁ s₂, Team.splitsAsNE s s₁ s₂ ∧ antiSupportStar M α s₁ ∧ antiSupportStar M β s₂ :=
      hstar
    ⟨s₁, fun _ hx ↦ hs (hsplit ▸ Finset.mem_union_left s₂ hx), hne₁, h₁⟩

/-- The `□` form of negative free choice in BSML*, `¬□(α ∧ β) ⊨* ¬□α` (Fact 14), by the
duality `□φ := ¬◇¬φ`. -/
theorem negativeFC_star_nec (α β : Formula Atom) :
    consequenceStar (W := W) (.neg (Formula.nec (.conj α β))) (.neg (Formula.nec α)) :=
  negativeFC_star_poss α β

end BSML
