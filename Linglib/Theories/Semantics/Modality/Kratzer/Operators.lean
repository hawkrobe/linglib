/-
@cite{kratzer-1981} Modal Operators — IL Foundation

Necessity and possibility operators defined as `boxR`/`diamondR` from
`Core.IntensionalLogic.RestrictedModality`, with Kratzer-specific
accessibility relations derived from conversational backgrounds.

The key architectural insight: Kratzer's operators ARE restricted modal
operators. The modal base determines accessibility (`kratzerR`), the
ordering source further restricts to best worlds (`kratzerBestR`), and
the Kratzer operators are literally `boxR`/`diamondR` with these relations.

Frame correspondence theorems (T, D, 4, B, 5) become two-step proofs:
1. Derive the frame condition from the conversational background property
2. Apply the generic axiom from RestrictedModality

Following mathlib conventions: operators are Prop-valued. Propositions
themselves are `W → Prop`; reasoning is classical.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Ordering
import Linglib.Core.IntensionalLogic.RestrictedModality
import Mathlib.Data.Set.Basic

namespace Semantics.Modality.Kratzer

open Core.IntensionalLogic
open Core.IntensionalLogic.RestrictedModality

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- § Modal Frame and Accessibility Relations
-- ════════════════════════════════════════════════════════════════

/-- Accessibility relation derived from a modal base.

    `kratzerR f w w'` iff `w'` satisfies all propositions in `f(w)`,
    i.e., `w' ∈ ⋂f(w)` in Kratzer's notation. -/
def kratzerR (f : ModalBase W) : AccessRel W :=
  fun w w' => ∀ p ∈ f w, p w'

/-- Accessibility restricted to best worlds (modal base + ordering source).

    `kratzerBestR f g w w'` iff `w'` is among the best accessible worlds
    from `w` — accessible via `f` and maximal under the `g(w)`-ordering. -/
def kratzerBestR (f : ModalBase W) (g : OrderingSource W) : AccessRel W :=
  fun w w' => w' ∈ bestWorlds f g w

-- ════════════════════════════════════════════════════════════════
-- § Operators (= boxR / diamondR)
-- ════════════════════════════════════════════════════════════════

/--
**Simple f-necessity** (@cite{kratzer-1981} p. 32): p is true at ALL accessible worlds.

⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')

Defined as `boxR` with modal-base accessibility. -/
def simpleNecessity (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  boxR (kratzerR f) p w

/--
**Simple f-possibility** (@cite{kratzer-1981} p. 32): p is true at SOME accessible world.

⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')

Defined as `diamondR` with modal-base accessibility. -/
def simplePossibility (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  diamondR (kratzerR f) p w

/--
**Necessity with ordering** (@cite{kratzer-1981} p. 40): p is true at ALL best worlds.

⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')

Defined as `boxR` with best-world accessibility. -/
def necessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  boxR (kratzerBestR f g) p w

/--
**Possibility with ordering**: p is true at SOME best world.

⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')

Defined as `diamondR` with best-world accessibility. -/
def possibility (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  diamondR (kratzerBestR f g) p w

-- ════════════════════════════════════════════════════════════════
-- § Connection to Computational Layer
-- ════════════════════════════════════════════════════════════════

/-- `kratzerR f w w'` iff `w' ∈ accessibleWorlds f w`. -/
theorem kratzerR_iff_accessible (f : ModalBase W) (w w' : W) :
    kratzerR f w w' ↔ w' ∈ accessibleWorlds f w :=
  Iff.rfl

/-- `kratzerBestR f g w w'` iff `w' ∈ bestWorlds f g w` (definitional). -/
theorem kratzerBestR_iff_best (f : ModalBase W) (g : OrderingSource W) (w w' : W) :
    kratzerBestR f g w w' ↔ w' ∈ bestWorlds f g w :=
  Iff.rfl

/-- With empty ordering, best-world accessibility reduces to base accessibility. -/
theorem kratzerBestR_empty (f : ModalBase W) (w w' : W) :
    kratzerBestR f (emptyBackground (W := W)) w w' ↔ kratzerR f w w' := by
  rw [kratzerBestR_iff_best, kratzerR_iff_accessible]
  exact empty_ordering_emptyBackground f w ▸ Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § Characterization Lemmas
-- ════════════════════════════════════════════════════════════════

/-- `simpleNecessity f p w` iff p holds at all accessible worlds. -/
theorem simpleNecessity_iff_all (f : ModalBase W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

/-- `simplePossibility f p w` iff p holds at some accessible world. -/
theorem simplePossibility_iff_any (f : ModalBase W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

/-- `necessity f g p w` iff p holds at all best worlds. -/
theorem necessity_iff_all (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- `possibility f g p w` iff p holds at some best world. -/
theorem possibility_iff_any (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Necessity with empty ordering = simple necessity. -/
theorem necessity_empty_eq_simple (f : ModalBase W) (p : W → Prop) (w : W) :
    necessity f (emptyBackground (W := W)) p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff_all, simpleNecessity_iff_all]
  rw [empty_ordering_emptyBackground]

-- ════════════════════════════════════════════════════════════════
-- § Frame Condition Definitions
-- ════════════════════════════════════════════════════════════════

def isTransitiveAccess (f : ModalBase W) : Prop :=
  ∀ w w' w'' : W,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w' →
    w'' ∈ accessibleWorlds f w

def isSymmetricAccess (f : ModalBase W) : Prop :=
  ∀ w w' : W,
    w' ∈ accessibleWorlds f w →
    w ∈ accessibleWorlds f w'

def isEuclideanAccess (f : ModalBase W) : Prop :=
  ∀ w w' w'' : W,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w'

def isS4Base (f : ModalBase W) : Prop :=
  isRealistic f ∧ isTransitiveAccess f

def isS5Base (f : ModalBase W) : Prop :=
  isRealistic f ∧ isEuclideanAccess f

-- ════════════════════════════════════════════════════════════════
-- § Frame Condition Derivation
-- ════════════════════════════════════════════════════════════════

/-! These theorems derive frame conditions on `kratzerR` from properties
of conversational backgrounds. This is the Kratzer-specific contribution:
the frame conditions aren't stipulated, they follow from what kind of
conversational background the modal base is. -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem realistic_refl (f : ModalBase W) (hReal : isRealistic f) :
    Refl (kratzerR f) :=
  fun w p hp => hReal w p hp

/-- An empty modal base gives universal accessibility. -/
theorem empty_base_universalR :
    kratzerR (emptyBackground (W := W)) = universalR := by
  ext w w'
  simp only [kratzerR, emptyBackground, List.not_mem_nil, false_implies,
             forall_const, universalR]

/-- Transitive list-accessibility gives transitive `kratzerR`. -/
theorem transitive_trans (f : ModalBase W) (hTrans : isTransitiveAccess f) :
    Trans (kratzerR f) :=
  fun w w' w'' h1 h2 => hTrans w w' w'' h1 h2

/-- Symmetric list-accessibility gives symmetric `kratzerR`. -/
theorem symmetric_symm (f : ModalBase W) (hSym : isSymmetricAccess f) :
    Symm (kratzerR f) :=
  fun w w' h => hSym w w' h

/-- Euclidean list-accessibility gives euclidean `kratzerR`. -/
theorem euclidean_eucl (f : ModalBase W) (hEuc : isEuclideanAccess f) :
    Eucl (kratzerR f) :=
  fun w w' w'' h1 h2 => hEuc w w' w'' h1 h2

-- ════════════════════════════════════════════════════════════════
-- § Modal Axioms (from RestrictedModality)
-- ════════════════════════════════════════════════════════════════

/-! Each modal axiom is a direct application of the corresponding
`boxR_*` theorem from `RestrictedModality`. The Kratzer-specific work
is deriving the frame condition from the conversational background
property — the modal logic is inherited for free. -/

/--
**Theorem: Modal duality holds.**

□p ↔ ¬◇¬p
-/
theorem duality (f : ModalBase W) (g : OrderingSource W) (p : W → Prop)
    (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' => ¬ p w') w := by
  simp only [necessity, possibility, boxR, diamondR]
  refine ⟨fun h ⟨j, hj, hnp⟩ => hnp (h j hj), fun h j hj => ?_⟩
  by_contra hc
  exact h ⟨j, hj, hc⟩


/--
**K Axiom (Distribution)**: □(p → q) → (□p → □q)

Holds for any accessibility relation. -/
theorem K_axiom (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' => p w' → q w') w)
    (hP : necessity f g p w) :
    necessity f g q w := fun j hj => hImpl j hj (hP j hj)


/--
**T Axiom**: Realistic base → □p → p.

What is necessary is actual. -/
theorem T_axiom (f : ModalBase W) (p : W → Prop) (w : W)
    (hReal : isRealistic f)
    (hNec : simpleNecessity f p w) : p w :=
  boxR_T (kratzerR f) (realistic_refl f hReal) _ w hNec

/--
**D Axiom**: Serial accessibility → □p → ◇p.

What is necessary is possible. -/
theorem D_axiom_simple (f : ModalBase W) (p : W → Prop) (w : W)
    (hReal : isRealistic f)
    (hNec : simpleNecessity f p w) : simplePossibility f p w :=
  boxR_D (kratzerR f) (refl_serial (realistic_refl f hReal)) _ w hNec

/--
**4 Axiom**: Transitive accessibility → □p → □□p.

Positive introspection. -/
theorem four_axiom (f : ModalBase W) (p : W → Prop) (w : W)
    (hTrans : isTransitiveAccess f)
    (hNec : simpleNecessity f p w) :
    simpleNecessity f (fun w' => simpleNecessity f p w') w := by
  intro j hj
  exact boxR_four (kratzerR f) (transitive_trans f hTrans) _ w hNec j hj

/--
**B Axiom**: Symmetric accessibility → p → □◇p.

What is actual is necessarily possible. -/
theorem B_axiom (f : ModalBase W) (p : W → Prop) (w : W)
    (hSym : isSymmetricAccess f)
    (hP : p w) :
    simpleNecessity f (fun w' => simplePossibility f p w') w := by
  intro j hj
  exact boxR_B (kratzerR f) (symmetric_symm f hSym) _ w hP j hj

/--
**5 Axiom**: Euclidean accessibility → ◇p → □◇p.

Positive possibility introspection. -/
theorem five_axiom (f : ModalBase W) (p : W → Prop) (w : W)
    (hEuc : isEuclideanAccess f)
    (hPoss : simplePossibility f p w) :
    simpleNecessity f (fun w' => simplePossibility f p w') w := by
  intro j hj
  exact boxR_five (kratzerR f) (euclidean_eucl f hEuc) _ w hPoss j hj

-- ════════════════════════════════════════════════════════════════
-- § Additional Theorems
-- ════════════════════════════════════════════════════════════════

/-- Totally realistic base implies T axiom for full necessity. -/
theorem totally_realistic_gives_T (f : ModalBase W) (g : OrderingSource W)
    (hTotal : ∀ w, accessibleWorlds f w = {w})
    (p : W → Prop) (w : W)
    (hNec : necessity f g p w) : p w := by
  have : kratzerBestR f g w w := by
    rw [kratzerBestR_iff_best]
    refine ⟨?_, fun w'' hw'' => ?_⟩
    · rw [hTotal w]; exact rfl
    · rw [hTotal w] at hw''
      cases hw''
      exact ordering_reflexive (g w) w
  exact hNec w this

/-- Realistic base gives reflexive accessibility. -/
theorem realistic_gives_reflexive_access (f : ModalBase W)
    (hReal : isRealistic f) (w : W) :
    w ∈ accessibleWorlds f w :=
  realistic_refl f hReal w

/-- Empty modal base gives universal accessibility. -/
theorem empty_base_universal_access (w : W) :
    accessibleWorlds (emptyBackground (W := W)) w = Set.univ := by
  ext w'
  simp only [accessibleWorlds, emptyBackground, propIntersection,
             List.not_mem_nil, false_implies, forall_const, Set.mem_setOf_eq,
             Set.mem_univ]

theorem euclidean_reflexive_implies_symmetric (f : ModalBase W)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isSymmetricAccess f := by
  intro w w' hw'Acc
  have hwAcc := realistic_gives_reflexive_access f hReal w
  exact hEuc w w' w hw'Acc hwAcc

theorem euclidean_reflexive_implies_transitive (f : ModalBase W)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isTransitiveAccess f := by
  intro w w' w'' hw'Acc hw''AccW'
  have hSym := euclidean_reflexive_implies_symmetric f hReal hEuc
  have hwAccW' : w ∈ accessibleWorlds f w' := hSym w w' hw'Acc
  exact hEuc w' w w'' hwAccW' hw''AccW'

theorem S5_satisfies_all (f : ModalBase W) (hS5 : isS5Base f) :
    isRealistic f ∧ isSymmetricAccess f ∧ isTransitiveAccess f ∧ isEuclideanAccess f := by
  obtain ⟨hReal, hEuc⟩ := hS5
  exact ⟨hReal,
         euclidean_reflexive_implies_symmetric f hReal hEuc,
         euclidean_reflexive_implies_transitive f hReal hEuc,
         hEuc⟩

theorem realistic_is_serial (f : ModalBase W) (hReal : isRealistic f) (w : W) :
    (accessibleWorlds f w).Nonempty :=
  ⟨w, realistic_gives_reflexive_access f hReal w⟩


-- ════════════════════════════════════════════════════════════════
-- § Comparative Possibility
-- ════════════════════════════════════════════════════════════════

/--
p is **at least as good a possibility as** q in w with respect to f and g.

For every accessible world satisfying q-but-not-p, there exists an
accessible world satisfying p-but-not-q that is at least as good.
-/
def atLeastAsGoodPossibility (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ accessibleWorlds f w, q w' → ¬ p w' →
    ∃ w'' ∈ accessibleWorlds f w, p w'' ∧ ¬ q w'' ∧
      atLeastAsGoodAs (g w) w'' w'

def betterPossibility (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) : Prop :=
  atLeastAsGoodPossibility f g p q w ∧ ¬ atLeastAsGoodPossibility f g q p w

theorem comparative_poss_reflexive (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    atLeastAsGoodPossibility f g p p w := by
  intro w' _ hp hnp
  exact absurd hp hnp

-- ════════════════════════════════════════════════════════════════
-- § Conditionals as Restriction
-- ════════════════════════════════════════════════════════════════

/--
Conditionals as modal base restrictors.

"If α, (must) β" = must_f+α β
-/
def restrictedBase (f : ModalBase W) (antecedent : W → Prop) : ModalBase W :=
  fun w => antecedent :: f w

/-- Material implication. -/
def implies (p q : W → Prop) : W → Prop := fun w => p w → q w

def materialImplication (p q : W → Prop) (w : W) : Prop :=
  implies p q w

def strictImplication (p q : W → Prop) : Prop :=
  ∀ w : W, p w → q w

end Semantics.Modality.Kratzer
