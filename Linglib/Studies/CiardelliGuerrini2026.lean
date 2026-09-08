import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.English.Auxiliaries
import Linglib.Logic.Modal.Basic
import Linglib.Data.Examples.CiardelliGuerrini2026

/-!
# Ciardelli and Guerrini (2026): Against wide scope free choice

This file formalizes the reductionist thesis of [ciardelli-guerrini-2026]: the free-choice
reading of *you may A or you may B* arises from the narrow-scope LF ◇(A ∨ B), the reading of
the wide-scope ◇A ∨ ◇B being the ignorance one ([fusco-2019]). Possibility distributes over
disjunction, so the two LFs coincide in truth conditions there, and the ambiguity shows where
they differ: *you must A or you must B* has a reading as one disjunctive obligation □(A ∨ B),
strictly weaker than □A ∨ □B, and *you may A and you may B* one as a conjunctive permission
◇(A ∧ B), strictly stronger than ◇A ∧ ◇B. The narrow LF arises by modal concord
([zeijlstra-2007]): a modal auxiliary carries an uninterpretable modal feature, and one silent
interpretable operator above the coordination checks both auxiliaries' features when they fall
in one concord class. Non-auxiliary modals carry interpretable features and cannot be checked,
which is why *it's ok for John to sing or it's ok for John to dance* has no free choice
([meyer-sauerland-2017]), while *may* and *can* share their feature and mix
([alonso-ovalle-2006]). Across negation concord needs dual forces ([grosz-2010],
[anand-brasoveanu-2010]), negation flipping the force of the feature it scopes over, so *I need
not cook and I need not clean* conveys a permission to do neither and not an obligation. The
modal features come from the English auxiliary Fragment, and the paper's coordination and
concord examples are rows.

## Implementation notes

The argument against across-the-board movement from *everyone sang or everyone danced*
([simons-2005]) has no movement substrate here, and the cases the paper leaves open, *it is
possible that A or it is possible that B* and conjoined *be allowed*, are not rows.

## References

* [ciardelli-guerrini-2026]
* [zeijlstra-2007]
* [meyer-sauerland-2017]
* [fusco-2019]
* [simons-2005]
* [grosz-2010]
* [anand-brasoveanu-2010]
* [alonso-ovalle-2006]
-/

namespace CiardelliGuerrini2026

open Modality ModalLogic English.Auxiliaries Data.Examples

/-! ### Scope and truth conditions (§2) -/

section Scope

variable {World : Type*} (A B : Set World)

/-- May-or-may, (2): possibility distributes over disjunction, so this is the one cell of the
paradigm where the scope ambiguity is invisible to truth conditions. -/
theorem poss_union_iff : poss (A ∪ B : Set World) ↔ poss A ∨ poss B := Set.union_nonempty

/-- The wide-scope LF does not entail free choice: one possible disjunct suffices for it. -/
theorem exists_poss_or_not_and : ∃ A B : Set Bool, (poss A ∨ poss B) ∧ ¬ (poss A ∧ poss B) :=
  ⟨Set.univ, ∅, Or.inl ⟨true, trivial⟩, λ ⟨_, w, hw⟩ => Set.notMem_empty w hw⟩

/-- Must-or-must, (5): the narrow-scope disjunctive obligation follows from the wide-scope
disjunction of obligations. -/
theorem nec_union_of_or (h : nec A ∨ nec B) : nec (A ∪ B : Set World) :=
  h.elim (λ h w => Or.inl (h w)) (λ h w => Or.inr (h w))

/-- But not conversely: a disjunctive obligation leaves open which disjunct is met. -/
theorem exists_nec_union_not_or :
    ∃ A B : Set Bool, nec (A ∪ B : Set Bool) ∧ ¬ (nec A ∨ nec B) :=
  ⟨{true}, {false}, λ w => show w ∈ ({true} ∪ {false} : Set Bool) by cases w <;> simp,
    λ h => h.elim (λ h => by simpa using show false ∈ ({true} : Set Bool) from h false)
      (λ h => by simpa using show true ∈ ({false} : Set Bool) from h true)⟩

/-- May-and-may, (7): the narrow-scope conjunctive permission entails the wide-scope
conjunction of permissions. -/
theorem poss_and_of_inter (h : poss (A ∩ B : Set World)) : poss A ∧ poss B :=
  ⟨Set.Nonempty.left h, Set.Nonempty.right h⟩

/-- But not conversely, which is what makes (9b), *you may come with me and you may stay
here*, absurd on its conjunctive reading: two permissions need not be jointly satisfiable. -/
theorem exists_poss_and_not_inter :
    ∃ A B : Set Bool, poss A ∧ poss B ∧ ¬ poss (A ∩ B : Set Bool) :=
  ⟨{true}, {false}, ⟨true, rfl⟩, ⟨false, rfl⟩, λ ⟨w, hA, hB⟩ => by cases w <;> simp_all⟩

end Scope

/-! ### Modal concord (§3) -/

/-- [zeijlstra-2007]'s generalization over the Fragment: every modal auxiliary carries its
feature uninterpretable. -/
theorem modals_uninterpretable :
    ∀ a ∈ modals, ∀ f ∈ a.modalFeature, f.interp = .uninterpretable := by decide

/-- Two modal features stand in concord when both are uninterpretable and fall in one concord
class: one silent interpretable operator above the coordination then checks both, (15), so the
modal outscopes the coordinator. -/
def Concord (f₁ f₂ : ModalFeature) : Prop :=
  f₁.interp = .uninterpretable ∧ f₂.interp = .uninterpretable ∧
    ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force

instance : DecidableRel Concord := λ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The silent operator: an interpretable feature of the shared class checks both features. -/
theorem exists_checks_of_concord {f₁ f₂ : ModalFeature} (h : Concord f₁ f₂) :
    ∃ op : ModalFeature, op.interp = .interpretable ∧ op.Checks f₁ ∧ op.Checks f₂ :=
  ⟨⟨f₁.force, .interpretable⟩, rfl, ⟨rfl, h.1, rfl⟩, ⟨rfl, h.2.1, h.2.2⟩⟩

/-- Conversely, two features one operator checks are in concord. -/
theorem concord_of_checks {op f₁ f₂ : ModalFeature} (h₁ : op.Checks f₁) (h₂ : op.Checks f₂) :
    Concord f₁ f₂ :=
  ⟨h₁.2.1, h₂.2.1, h₁.2.2.symm.trans h₂.2.2⟩

/-- An interpreted feature is never checked, so non-auxiliary modals such as *be allowed* admit
no narrow-scope LF, (19) and (20). -/
theorem not_checks_of_interpretable (op : ModalFeature) {f : ModalFeature}
    (h : f.interp = .interpretable) : ¬ op.Checks f := by
  intro hc
  have := hc.2.1
  simp [h] at this

/-- The Fragment's modals pair as the paper needs: *may* with *may*, *must* with *must*, *may*
with *can*, [alonso-ovalle-2006]'s mixed form of footnote 4, and *may* not with *must*. -/
theorem fragment_concord :
    (∀ f ∈ may.modalFeature, ∀ g ∈ may.modalFeature, Concord f g) ∧
      (∀ f ∈ must.modalFeature, ∀ g ∈ must.modalFeature, Concord f g) ∧
      (∀ f ∈ may.modalFeature, ∀ g ∈ can.modalFeature, Concord f g) ∧
      (∀ f ∈ may.modalFeature, ∀ g ∈ must.modalFeature, ¬ Concord f g) := by
  decide

/-! ### Concord across negation (§4.2) -/

/-- (28), *I need not cook and I need not clean*: the negated feature of *need* is checked by a
silent possibility operator, (29a), and not by a necessity one, (29c), so the sentence conveys
a permission to do neither and not an obligation to do neither. -/
theorem need_not :
    ∀ f ∈ need.modalFeature,
      ModalFeature.Checks ⟨.possibility, .interpretable⟩ f.negated ∧
        ¬ ModalFeature.Checks ⟨.necessity, .interpretable⟩ f.negated := by
  decide

/-! ### The rows -/

/-- The modal feature of a modal named in the rows: the auxiliaries' from the Fragment, and the
interpretable feature of the non-auxiliary modals, (20). -/
private def featureOf : String → Option ModalFeature
  | "may" => may.modalFeature
  | "can" => can.modalFeature
  | "must" => must.modalFeature
  | "need" => need.modalFeature
  | "allow" | "it's ok" | "be allowed" | "be permitted" => some ⟨.possibility, .interpretable⟩
  | "demand" | "be required" => some ⟨.necessity, .interpretable⟩
  | _ => none

/-- A coordination of two modals has a narrow-scope reading exactly when their features are in
concord. -/
theorem coordination_rows :
    ∀ e ∈ Examples.all, ∀ f₁ ∈ (e.feature? "modal1").bind featureOf,
      ∀ f₂ ∈ (e.feature? "modal2").bind featureOf,
        (e.feature? "narrowReading" ≠ none ↔ Concord f₁ f₂) := by
  decide

/-- The narrow-scope reading a row names is among its available readings. -/
theorem narrow_reading_available :
    ∀ e ∈ Examples.all, ∀ n ∈ e.feature? "narrowReading",
      ∃ r ∈ e.readings, r.1 = n ∧ r.2 = .acceptable := by
  decide

/-- Modal concord between a higher and a lower modal is available exactly when the higher
feature checks the lower one, negated when negation intervenes. -/
theorem concord_rows :
    ∀ e ∈ Examples.all, ∀ op ∈ (e.feature? "checker").bind featureOf,
      ∀ f ∈ (e.feature? "checked").bind featureOf,
        ((∃ r ∈ e.readings, r.1 = "modal concord" ∧ r.2 = .acceptable) ↔
          op.Checks (if e.feature? "negated" = some "true" then f.negated else f)) := by
  decide

end CiardelliGuerrini2026
