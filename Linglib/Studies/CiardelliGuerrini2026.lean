import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.English.Auxiliaries
import Linglib.Data.Examples.CiardelliGuerrini2026
import Mathlib.Data.Set.Basic
import Linglib.Logic.Modal.Basic

/-!
# Ciardelli and Guerrini 2026: Against wide scope free choice

The free-choice reading of *you may A or you may B* is not the wide-scope LF `◇A ∨ ◇B` but the
narrow-scope `◇(A ∨ B)`, from which exhaustification derives `◇A ∧ ◇B` as for *you may A or B*,
the wide LF yielding the ignorance reading ([fusco-2019]). For possibility over disjunction the
two LFs have the same truth conditions, so the ambiguity shows where they differ: *you must A
or you must B* has a reading as one disjunctive obligation `□(A ∨ B)`, weaker than `□A ∨ □B`
(5), and *you may A and you may B* one as a conjunctive permission `◇(A ∧ B)`, stronger than
`◇A ∧ ◇B` (7) (§2). The narrow LF arises by modal concord ([zeijlstra-2007]): each auxiliary
carries an uninterpretable modal feature and one silent interpretable operator above the
coordination checks both (§3). Non-auxiliary modals carry interpretable features and cannot be
checked, hence no free choice in [meyer-sauerland-2017]'s (19) (§4.1); concord across negation
needs dual forces, (24)–(27) after [grosz-2010] and [anand-brasoveanu-2010], so *I need not
cook and I need not clean* conveys `◇(¬cook ∧ ¬clean)` but not `□(¬cook ∧ ¬clean)` (§4.2);
*may* and *can* share their feature, answering [alonso-ovalle-2006]'s mixed-form case (fn. 4);
*it is possible that A or it is possible that B* is left open (§4.3).

`scope_equivalence`, `disjunctive_obligation_narrow_weaker` with `_not_wide`, and
`conjunctive_narrow_stronger` are the three cells of §2 on the flat modals `ModalLogic.poss`
and `nec`. A `ConcordDerivation` is two uninterpretable features of one concord class with the
silent checker derived from them, built from the Fragment's auxiliaries as `mayMayConcord`,
`mustMustConcord` and fn. 4's `mayCanConcord`; `interpreted_unchecked` is the §4.1 mechanism
and `negation_concord_pattern` the §4.2 one, with (24)–(29) as instances. `doublyExhaustified`
is [fox-2007]'s exhaustification of the narrow LF, `narrowScope_yields_fc` derives free choice
from it, `wideScope_underdetermines_fc` shows the wide LF does not entail it, and
`reductionist_thesis` packages the two. The stimuli (2), (5) and (7) are in
`Data.Examples.CiardelliGuerrini2026`; the argument against across-the-board movement
([simons-2005]) from *everyone sang or everyone danced* (3) has no movement substrate here.

## References

* [I. Ciardelli and J. Guerrini, *Against Wide Scope Free Choice*
  (2026)][ciardelli-guerrini-2026]
* [H. Zeijlstra, *Modal Concord* (2007)][zeijlstra-2007]
* [M.-C. Meyer and U. Sauerland, *Covert Across-the-Board Movement Revisited: Free Choice and
  the Scope of Modals* (2017)][meyer-sauerland-2017]
* [M. Fusco, *Sluicing on free choice* (2019)][fusco-2019]
* [D. Fox, *Free Choice and the Theory of Scalar Implicatures* (2007)][fox-2007]
* [M. Simons, *Dividing Things Up: The Semantics of Or and the Modal/Or Interaction*
  (2005)][simons-2005]
* [P. Grosz, *Grading Modality: A New Approach to Modal Concord and its Relatives*
  (2010)][grosz-2010]
* [P. Anand and A. Brasoveanu, *Modal Concord as Modal Modification*
  (2010)][anand-brasoveanu-2010]
* [L. Alonso-Ovalle, *Disjunction in Alternative Semantics* (2006)][alonso-ovalle-2006]
-/

namespace CiardelliGuerrini2026

open Modality English.Auxiliaries

/-- Possibility of a proposition, the flat S5 `ModalLogic.poss`. -/
abbrev poss {World : Type*} (p : Set World) : Prop := ModalLogic.poss p

/-- Necessity of a proposition, the flat S5 `ModalLogic.nec`. -/
abbrev nec {World : Type*} (p : Set World) : Prop := ModalLogic.nec p

/-! ### Scope and truth conditions (§2) -/

/-- Possibility distributes over disjunction, so may-or-may is the one cell of the paradigm
where the scope ambiguity is invisible to truth conditions. -/
theorem scope_equivalence {World : Type*} (A B : Set World) :
    poss (A ∪ B) ↔ poss A ∨ poss B :=
  ⟨λ ⟨w, h⟩ => h.elim (λ h => Or.inl ⟨w, h⟩) (λ h => Or.inr ⟨w, h⟩),
    λ h => h.elim (λ ⟨w, h⟩ => ⟨w, Or.inl h⟩) (λ ⟨w, h⟩ => ⟨w, Or.inr h⟩)⟩

/-- Must-or-must (5): the narrow-scope disjunctive obligation `□(A ∪ B)` follows from the wide
`□A ∨ □B`. -/
theorem disjunctive_obligation_narrow_weaker {World : Type*} (A B : Set World) :
    nec A ∨ nec B → nec (A ∪ B) := by
  rintro (h | h)
  · exact ModalLogic.nec_mono (fun _ ha => Or.inl ha) h
  · exact ModalLogic.nec_mono (fun _ hb => Or.inr hb) h

/-- But not conversely: a disjunctive obligation leaves open which disjunct is met. -/
theorem disjunctive_obligation_not_wide :
    ∃ (A B : Set Bool), nec (A ∪ B) ∧ ¬ (nec A ∨ nec B) := by
  refine ⟨{true}, {false}, ?_, ?_⟩
  · intro w; cases w
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (h | h)
    · exact absurd (show false = true from h false) (by decide)
    · exact absurd (show true = false from h true) (by decide)

/-- May-and-may (7): the narrow-scope conjunctive permission `◇(A ∩ B)` entails the wide
`◇A ∧ ◇B`, but not conversely. -/
theorem conjunctive_narrow_stronger {World : Type*}
    (p q : Set World)
    (h : poss (p ∩ q)) : poss p ∧ poss q := by
  obtain ⟨w, hp, hq⟩ := h
  exact ⟨⟨w, hp⟩, ⟨w, hq⟩⟩

/-! ### Modal concord (§3) -/

/-- The modal feature of *may*, from the Fragment. -/
def mayFeature : ModalFeature := may.modalFeature.get!

/-- The modal feature of *must*, from the Fragment. -/
def mustFeature : ModalFeature := must.modalFeature.get!

/-- *May* carries `[u∃-MOD]`. -/
theorem may_feature_eq :
    may.modalFeature = some ⟨.possibility, .uninterpretable⟩ := rfl

/-- *Must* carries `[u∀-MOD]`. -/
theorem must_feature_eq :
    must.modalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The silent operator checking a feature: the same force, interpretable. -/
def silentChecker (f : ModalFeature) : ModalFeature := ⟨f.force, .interpretable⟩

/-- The matching silent operator checks any uninterpretable feature. -/
theorem silent_checker_works (f : ModalFeature) (h : f.interp = .uninterpretable) :
    (silentChecker f).checks f = true := by
  simp only [silentChecker, ModalFeature.checks, h]
  cases f.force <;> decide

private theorem silent_checks_matching (g₁ g₂ : ModalFeature)
    (hI : g₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce g₁.force = ConcordType.fromModalForce g₂.force) :
    (silentChecker g₁).checks g₂ = true := by
  have hforce : (silentChecker g₁).checks g₂ = (silentChecker g₂).checks g₂ := by
    simp only [silentChecker, ModalFeature.checks, hF]
  rw [hforce]
  exact silent_checker_works g₂ hI

/-- A concord derivation: two uninterpretable modal features of one concord class, checked by a
single silent operator. -/
structure ConcordDerivation where
  /-- The feature of the first auxiliary. -/
  f₁ : ModalFeature
  /-- The feature of the second auxiliary. -/
  f₂ : ModalFeature
  uInterp₁ : f₁.interp = .uninterpretable
  uInterp₂ : f₂.interp = .uninterpretable
  sameClass : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force

namespace ConcordDerivation

/-- The silent interpretable operator. -/
def checker (cd : ConcordDerivation) : ModalFeature :=
  silentChecker cd.f₁

theorem checker_interpretable (cd : ConcordDerivation) :
    cd.checker.interp = .interpretable := rfl

theorem checks_first (cd : ConcordDerivation) :
    cd.checker.checks cd.f₁ = true :=
  silent_checker_works cd.f₁ cd.uInterp₁

theorem checks_second (cd : ConcordDerivation) :
    cd.checker.checks cd.f₂ = true :=
  silent_checks_matching cd.f₁ cd.f₂ cd.uInterp₂ cd.sameClass

end ConcordDerivation

/-- A concord derivation from two Fragment auxiliaries. -/
def ConcordDerivation.fromAux (a₁ a₂ : Auxiliary)
    {f₁ f₂ : ModalFeature}
    (_h₁ : a₁.modalFeature = some f₁) (_h₂ : a₂.modalFeature = some f₂)
    (hI₁ : f₁.interp = .uninterpretable) (hI₂ : f₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force) :
    ConcordDerivation :=
  ⟨f₁, f₂, hI₁, hI₂, hF⟩

/-- The Fragment's modals with a modal feature; *dare*'s is unspecified. -/
def concordCapableModals : List Auxiliary :=
  modals.filter (λ a => a.modalFeature.isSome)

/-- [zeijlstra-2007]'s generalization over the Fragment: every modal auxiliary carries its
feature uninterpretable. -/
theorem concordCapable_uninterpretable :
    ∀ a ∈ concordCapableModals,
      a.interpretability = some .uninterpretable := by decide

/-- Non-modal auxiliaries have no modal feature. -/
theorem nonmodal_no_feature :
    ∀ a ∈ [do_, am, have_], a.modalFeature = none := by decide

/-- *May A or may B*. -/
def mayMayConcord : ConcordDerivation :=
  .fromAux may may may_feature_eq may_feature_eq rfl rfl rfl

/-- *Must A or must B*. -/
def mustMustConcord : ConcordDerivation :=
  .fromAux must must must_feature_eq must_feature_eq rfl rfl rfl

/-- A silent `□` cannot check *may*'s `[u∃]`. -/
theorem cross_force_blocked :
    (silentChecker mustFeature).checks mayFeature = false := by decide

/-! ### From the narrow LF to free choice (§3) -/

/-- The narrow-scope `◇(A ∨ B)` doubly exhaustified over its disjunct and conjunctive
alternatives ([fox-2007]). -/
def doublyExhaustified {World : Type*} (A B : Set World) : Prop :=
  poss (A ∪ B) ∧ ¬ poss (A ∩ B) ∧ ¬ (poss A ∧ ¬ poss B) ∧ ¬ (poss B ∧ ¬ poss A)

/-- The exhaustified narrow LF yields free choice. -/
theorem narrowScope_yields_fc {World : Type*} {A B : Set World}
    (hExh : doublyExhaustified A B) : poss A ∧ poss B := by
  obtain ⟨⟨w, hw⟩, -, h₁, h₂⟩ := hExh
  by_cases hA : poss A
  · exact ⟨hA, not_not.1 λ hB => h₁ ⟨hA, hB⟩⟩
  · exact absurd ⟨hw.elim (λ h => absurd ⟨w, h⟩ hA) (λ h => ⟨w, h⟩), hA⟩ h₂

/-- The wide-scope LF does not entail free choice: one possible disjunct suffices for it. -/
theorem wideScope_underdetermines_fc :
    ∃ (A B : Set Unit), (poss A ∨ poss B) ∧ ¬ (poss A ∧ poss B) := by
  refine ⟨Set.univ, ∅, Or.inl ⟨(), trivial⟩, ?_⟩
  rintro ⟨-, w, hw⟩
  exact Set.notMem_empty w hw

/-- The reductionist thesis: the two disjunction LFs are equivalent, and free choice comes from
the exhaustified narrow one. -/
theorem reductionist_thesis {World : Type*} (A B : Set World) :
    (poss (A ∪ B) ↔ poss A ∨ poss B) ∧
    (doublyExhaustified A B → poss A ∧ poss B) :=
  ⟨scope_equivalence A B, narrowScope_yields_fc⟩

/-! ### Auxiliary and non-auxiliary modals (§4.1) -/

/-- The paper's modals are Fragment auxiliaries with uninterpretable features. -/
theorem paper_modals_uninterpretable :
    ∀ a ∈ [may, must, can, need],
      a ∈ modals ∧ a.interpretability = some .uninterpretable := by decide

/-- An interpreted feature is never checked, so non-auxiliary modals such as *be allowed* admit
no narrow-scope LF and no free choice in coordination ((19), [meyer-sauerland-2017]). -/
theorem interpreted_unchecked (checker f : ModalFeature)
    (h : f.interp = .interpretable) : checker.checks f = false := by
  have hb : (f.interp == .uninterpretable) = false := by rw [h]; decide
  simp only [ModalFeature.checks, hb, Bool.and_false, Bool.false_and]

theorem interpreted_not_concord_checked (cd : ConcordDerivation) :
    cd.f₂.interp ≠ .interpretable := by
  rw [cd.uInterp₂]; decide

/-! ### Concord across negation (§4.2) -/

/-- (24): ALLOW`[i∃]` checks ¬NEED`[u∀]`. -/
theorem allow_neg_need_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = true := by decide

/-- (26): DEMAND`[i∀]` does not check ¬NEED`[u∀]`. -/
theorem demand_neg_need_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = false := by decide

/-- (25): DEMAND`[i∀]` checks ¬MAY`[u∃]`. -/
theorem demand_neg_may_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = true := by decide

/-- (27): ALLOW`[i∃]` does not check ¬MAY`[u∃]`. -/
theorem allow_neg_may_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = false := by decide

/-- Concord across negation succeeds iff the checker's force is the dual of the checked one
([grosz-2010], [anand-brasoveanu-2010]). -/
theorem negation_concord_pattern (checkerForce checkedForce : ModalForce)
    (hNec : checkerForce = .necessity ∨ checkerForce = .possibility)
    (hChk : checkedForce = .necessity ∨ checkedForce = .possibility) :
    ModalFeature.checksAcrossNegation
      ⟨checkerForce, .interpretable⟩
      ⟨checkedForce, .uninterpretable⟩ = true
    ↔ checkerForce = checkedForce.dual := by
  rcases hNec with rfl | rfl <;> rcases hChk with rfl | rfl <;> decide

/-- *Need* carries `[u∀-MOD]`. -/
theorem need_feature_eq :
    need.modalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- (28): *I need not cook and I need not clean* has the reading `◇(¬cook ∧ ¬clean)`, the silent
`◇[i∃]` checking ¬NEED`[u∀]`. -/
theorem need_not_existential_ok :
    ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      need.modalFeature.get!
    = true := by decide

/-- (29): it lacks the reading `□(¬cook ∧ ¬clean)`. -/
theorem need_not_universal_blocked :
    ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      need.modalFeature.get!
    = false := by decide

/-! ### Mixed forms (fn. 4) -/

/-- *Can* carries `[u∃-MOD]`, the feature of *may*. -/
theorem can_feature_eq :
    can.modalFeature = some ⟨.possibility, .uninterpretable⟩ := rfl

/-- *You may email us or you can reach the office*, [alonso-ovalle-2006]'s mixed-form case:
one silent `[i∃]` checks both. -/
def mayCanConcord : ConcordDerivation :=
  .fromAux may can may_feature_eq can_feature_eq rfl rfl rfl

/-- No concord between *may* and *must*: a silent `[i∃]` cannot check `[u∀]`. -/
theorem must_may_no_concord :
    (ModalFeature.checks
      ⟨may.modalFeature.get!.force, .interpretable⟩
      must.modalFeature.get!)
    = false := by decide

end CiardelliGuerrini2026
