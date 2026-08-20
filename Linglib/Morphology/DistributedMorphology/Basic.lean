import Linglib.Morphology.DistributedMorphology.Defs
import Linglib.Morphology.Exponence.Select

/-!
# Vocabulary items and allosemes as exponence rules

A `VI.VocabItem` and an `Allosemy.AllosemicEntry` each expose the shared
exponence interface (`Morphology.Exponence.Rule`), so DM's List 2 (form) and
List 3 (meaning) are resolved by one `Exponence.selectBy` competition, whose
winner is the Elsewhere winner. This file holds the two `Rule` instances and
the specificity laws they rest on.
-/

namespace DistributedMorphology

open Morphology.Exponence

namespace Allosemy

@[simp] theorem SyntacticContext.matches_self (c : SyntacticContext) : c.matches c = true := by
  simp [SyntacticContext.matches]

/-- A broader specification (matched by every query the narrower one is)
has no more non-wildcard fields: the score reflects applicability-set
inclusion contravariantly. -/
theorem SyntacticContext.specificity_le_of_matches_subset {r s : SyntacticContext}
    (h : ∀ q, s.matches q = true → r.matches q = true) :
    r.specificity ≤ s.specificity := by
  have hrs : r.matches s = true := h s (SyntacticContext.matches_self s)
  simp only [SyntacticContext.matches, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrs
  obtain ⟨⟨⟨hb, ha⟩, he⟩, hst⟩ := hrs
  simp only [SyntacticContext.specificity]
  have b : (if r.belowCat.isSome then 1 else 0) ≤ (if s.belowCat.isSome then (1 : ℕ) else 0) := by
    rcases hb with hb | hb <;> simp [hb]
  have a : (if r.aboveCat.isSome then 1 else 0) ≤ (if s.aboveCat.isSome then (1 : ℕ) else 0) := by
    rcases ha with ha | ha <;> simp [ha]
  have e : (if r.complementIsEventive then 1 else 0) ≤
      (if s.complementIsEventive then (1 : ℕ) else 0) := by
    cases hr : r.complementIsEventive <;> cases hsc : s.complementIsEventive <;> simp_all
  have t : (if r.complementIsStative then 1 else 0) ≤
      (if s.complementIsStative then (1 : ℕ) else 0) := by
    cases hr : r.complementIsStative <;> cases hsc : s.complementIsStative <;> simp_all
  omega

/-- Equal-score inclusion is equality: if every query matching `s` also
matches `r` and the two carry the same number of non-wildcard fields, the
specifications coincide. -/
theorem SyntacticContext.eq_of_matches_subset_of_specificity_eq {r s : SyntacticContext}
    (h : ∀ q, s.matches q = true → r.matches q = true)
    (hs : r.specificity = s.specificity) : r = s := by
  have hrs : r.matches s = true := h s (SyntacticContext.matches_self s)
  simp only [SyntacticContext.matches, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrs
  obtain ⟨⟨⟨hb, ha⟩, he⟩, hst⟩ := hrs
  simp only [SyntacticContext.specificity] at hs
  have b : (if r.belowCat.isSome then 1 else 0) ≤ (if s.belowCat.isSome then (1 : ℕ) else 0) := by
    rcases hb with h | h <;> simp [h]
  have a : (if r.aboveCat.isSome then 1 else 0) ≤ (if s.aboveCat.isSome then (1 : ℕ) else 0) := by
    rcases ha with h | h <;> simp [h]
  have e : (if r.complementIsEventive then 1 else 0) ≤
      (if s.complementIsEventive then (1 : ℕ) else 0) := by
    cases hr : r.complementIsEventive <;> cases hsc : s.complementIsEventive <;> simp_all
  have t : (if r.complementIsStative then 1 else 0) ≤
      (if s.complementIsStative then (1 : ℕ) else 0) := by
    cases hr : r.complementIsStative <;> cases hsc : s.complementIsStative <;> simp_all
  obtain ⟨rb, ra, rc, rd⟩ := r
  obtain ⟨sb, sa, sc, sd⟩ := s
  have eqb : rb = sb := by cases rb <;> cases sb <;> simp_all; all_goals omega
  have eqa : ra = sa := by cases ra <;> cases sa <;> simp_all; all_goals omega
  have eqc : rc = sc := by cases rc <;> cases sc <;> simp_all; all_goals omega
  have eqd : rd = sd := by cases rd <;> cases sd <;> simp_all
  subst eqb eqa eqc eqd; rfl

section Exponence

variable {Sem : Type}

/-- An `AllosemicEntry` exposes the shared exponence interface: contexts
are `SyntacticContext`s, applicability is `matches`, the exponent is the
denotation. -/
instance : Morphology.Exponence.Rule (AllosemicEntry Sem) SyntacticContext Sem :=
  ⟨AllosemicEntry.denotation, fun e c => e.context.matches c = true⟩

instance : Preorder (AllosemicEntry Sem) := Morphology.Exponence.toPreorder

instance : DecidableRel (Applies : AllosemicEntry Sem → SyntacticContext → Prop) :=
  fun e c => inferInstanceAs (Decidable (e.context.matches c = true))

/-- The specificity score of an alloseme: the non-wildcard-field count of
its conditioning context. -/
def AllosemicEntry.score (e : AllosemicEntry Sem) : Nat := e.context.specificity

/-- The score is strictly antitone in specificity: a strictly broader
alloseme scores strictly lower. -/
theorem score_strictAnti : StrictAnti (AllosemicEntry.score (Sem := Sem)) := by
  intro s r hlt
  have hsub : ∀ q, s.context.matches q = true → r.context.matches q = true := hlt.le
  refine lt_of_le_of_ne (SyntacticContext.specificity_le_of_matches_subset hsub)
    fun heq => not_le_of_gt hlt ?_
  have hctx : r.context = s.context :=
    SyntacticContext.eq_of_matches_subset_of_specificity_eq hsub heq
  show ∀ q, r.context.matches q = true → s.context.matches q = true
  rw [hctx]; exact fun _ h => h

/-- Score selection over an alloseme vocabulary is Elsewhere selection:
the winner is `≤`-minimal among the applicable allosemes. -/
theorem selectBy_score_isElsewhereWinner {v : List (AllosemicEntry Sem)}
    {c : SyntacticContext} {r : AllosemicEntry Sem}
    (h : selectBy AllosemicEntry.score v c = some r) : IsElsewhereWinner v c r :=
  selectBy_isElsewhereWinner (score_strictAnti.strictAntiOn _) h

end Exponence

end Allosemy

namespace VI

variable {Ctx Root : Type*}

/-- A Vocabulary Item exposes the shared exponence core interface
(`Morphology.Exponence.Rule`): contexts are (feature-context, root)
pairs, applicability is `matches`. -/
instance : Morphology.Exponence.Rule (VocabItem Ctx Root) (Ctx × Root) String :=
  ⟨VocabItem.exponent, fun vi cr => vi.matches cr.1 cr.2 = true⟩

instance : DecidableRel (Applies : VocabItem Ctx Root → Ctx × Root → Prop) :=
  fun vi cr => inferInstanceAs (Decidable (vi.matches cr.1 cr.2 = true))

instance : Preorder (VocabItem Ctx Root) := Morphology.Exponence.toPreorder

end VI

end DistributedMorphology
