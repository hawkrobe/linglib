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

Following mathlib conventions: operators are Prop-valued, with `Decidable`
instances for computation over finite domains.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Ordering
import Linglib.Core.IntensionalLogic.RestrictedModality

namespace Semantics.Modality.Kratzer

open Semantics.Attitudes.Intensional
open Core.IntensionalLogic
open Core.IntensionalLogic.RestrictedModality

-- ════════════════════════════════════════════════════════════════
-- § Modal Frame and Accessibility Relations
-- ════════════════════════════════════════════════════════════════

/-- The IL frame for Kratzer modal semantics.
    Entity is irrelevant for modality; Index = World. -/
@[reducible] def modalFrame : Frame := { Entity := Unit, Index := World }

/-- Accessibility relation derived from a modal base.

    `kratzerR f w w'` iff `w'` satisfies all propositions in `f(w)`,
    i.e., `w' ∈ ⋂f(w)` in Kratzer's notation. -/
def kratzerR (f : ModalBase) : AccessRel modalFrame :=
  fun w w' => ∀ p ∈ f w, p w' = true

/-- Accessibility restricted to best worlds (modal base + ordering source).

    `kratzerBestR f g w w'` iff `w'` is among the best accessible worlds
    from `w` — accessible via `f` and maximal under the `g(w)`-ordering. -/
def kratzerBestR (f : ModalBase) (g : OrderingSource) : AccessRel modalFrame :=
  fun w w' => w' ∈ bestWorlds f g w

-- ════════════════════════════════════════════════════════════════
-- § Decidability
-- ════════════════════════════════════════════════════════════════

instance kratzerR_decidable (f : ModalBase) (w w' : World) :
    Decidable (kratzerR f w w') :=
  inferInstanceAs (Decidable (∀ p ∈ f w, p w' = true))

instance kratzerBestR_decidable (f : ModalBase) (g : OrderingSource) (w w' : World) :
    Decidable (kratzerBestR f g w w') :=
  inferInstanceAs (Decidable (w' ∈ bestWorlds f g w))

/-- Decidable universal quantification over `World` (= `World4`, 4 values). -/
instance World_forall_decidable (P : World → Prop) [inst : ∀ w, Decidable (P w)] :
    Decidable (∀ w, P w) :=
  match inst .w0, inst .w1, inst .w2, inst .w3 with
  | .isTrue h0, .isTrue h1, .isTrue h2, .isTrue h3 =>
    .isTrue (fun w => match w with | .w0 => h0 | .w1 => h1 | .w2 => h2 | .w3 => h3)
  | .isFalse h, _, _, _ => .isFalse (fun hf => h (hf .w0))
  | _, .isFalse h, _, _ => .isFalse (fun hf => h (hf .w1))
  | _, _, .isFalse h, _ => .isFalse (fun hf => h (hf .w2))
  | _, _, _, .isFalse h => .isFalse (fun hf => h (hf .w3))

/-- Decidable existential quantification over `World`. -/
instance World_exists_decidable (P : World → Prop) [inst : ∀ w, Decidable (P w)] :
    Decidable (∃ w, P w) :=
  match inst .w0, inst .w1, inst .w2, inst .w3 with
  | .isTrue h, _, _, _ => .isTrue ⟨.w0, h⟩
  | _, .isTrue h, _, _ => .isTrue ⟨.w1, h⟩
  | _, _, .isTrue h, _ => .isTrue ⟨.w2, h⟩
  | _, _, _, .isTrue h => .isTrue ⟨.w3, h⟩
  | .isFalse h0, .isFalse h1, .isFalse h2, .isFalse h3 =>
    .isFalse (fun ⟨w, hw⟩ => match w with
      | .w0 => h0 hw | .w1 => h1 hw | .w2 => h2 hw | .w3 => h3 hw)

-- ════════════════════════════════════════════════════════════════
-- § Operators (= boxR / diamondR)
-- ════════════════════════════════════════════════════════════════

/--
**Simple f-necessity** (@cite{kratzer-1981} p. 32): p is true at ALL accessible worlds.

⟦must⟧_f(p)(w) = ∀w' ∈ ∩f(w). p(w')

Defined as `boxR` with modal-base accessibility. -/
def simpleNecessity (f : ModalBase) (p : BProp World) (w : World) : Prop :=
  boxR (kratzerR f) (fun w' => p w' = true) w

/--
**Simple f-possibility** (@cite{kratzer-1981} p. 32): p is true at SOME accessible world.

⟦can⟧_f(p)(w) = ∃w' ∈ ∩f(w). p(w')

Defined as `diamondR` with modal-base accessibility. -/
def simplePossibility (f : ModalBase) (p : BProp World) (w : World) : Prop :=
  diamondR (kratzerR f) (fun w' => p w' = true) w

/--
**Necessity with ordering** (@cite{kratzer-1981} p. 40): p is true at ALL best worlds.

⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')

Defined as `boxR` with best-world accessibility. -/
def necessity (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) : Prop :=
  boxR (kratzerBestR f g) (fun w' => p w' = true) w

/--
**Possibility with ordering**: p is true at SOME best world.

⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')

Defined as `diamondR` with best-world accessibility. -/
def possibility (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) : Prop :=
  diamondR (kratzerBestR f g) (fun w' => p w' = true) w

instance (f : ModalBase) (p : BProp World) (w : World) :
    Decidable (simpleNecessity f p w) :=
  inferInstanceAs (Decidable (∀ j, kratzerR f w j → p j = true))

instance (f : ModalBase) (p : BProp World) (w : World) :
    Decidable (simplePossibility f p w) :=
  inferInstanceAs (Decidable (∃ j, kratzerR f w j ∧ p j = true))

instance (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    Decidable (necessity f g p w) :=
  inferInstanceAs (Decidable (∀ j, kratzerBestR f g w j → p j = true))

instance (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    Decidable (possibility f g p w) :=
  inferInstanceAs (Decidable (∃ j, kratzerBestR f g w j ∧ p j = true))

-- ════════════════════════════════════════════════════════════════
-- § Connection to Computational Layer
-- ════════════════════════════════════════════════════════════════

/-- `kratzerR f w w'` iff `w' ∈ accessibleWorlds f w`. -/
theorem kratzerR_iff_accessible (f : ModalBase) (w w' : World) :
    kratzerR f w w' ↔ w' ∈ accessibleWorlds f w := by
  simp only [kratzerR, accessibleWorlds, propIntersection]
  constructor
  · intro h
    simp only [List.mem_filter, List.all_eq_true]
    exact ⟨Core.Proposition.FiniteWorlds.complete w', fun p hp => h p hp⟩
  · intro h
    simp only [List.mem_filter, List.all_eq_true] at h
    exact h.2

/-- `kratzerBestR f g w w'` iff `w' ∈ bestWorlds f g w` (definitional). -/
theorem kratzerBestR_iff_best (f : ModalBase) (g : OrderingSource) (w w' : World) :
    kratzerBestR f g w w' ↔ w' ∈ bestWorlds f g w :=
  Iff.rfl

/-- With empty ordering, best-world accessibility reduces to base accessibility. -/
theorem kratzerBestR_empty (f : ModalBase) (w w' : World) :
    kratzerBestR f emptyBackground w w' ↔ kratzerR f w w' := by
  rw [kratzerBestR_iff_best, kratzerR_iff_accessible]
  unfold emptyBackground
  rw [empty_ordering_simple]

-- ════════════════════════════════════════════════════════════════
-- § Characterization Lemmas (Prop ↔ Bool computation)
-- ════════════════════════════════════════════════════════════════

/-- `simpleNecessity f p w` iff the Bool check over accessible worlds passes. -/
theorem simpleNecessity_iff_all (f : ModalBase) (p : BProp World) (w : World) :
    simpleNecessity f p w ↔ (accessibleWorlds f w).all p = true := by
  simp only [simpleNecessity, boxR, List.all_eq_true]
  exact ⟨fun h j hj => h j ((kratzerR_iff_accessible f w j).mpr hj),
         fun h j hj => h j ((kratzerR_iff_accessible f w j).mp hj)⟩

/-- `simplePossibility f p w` iff the Bool check over accessible worlds passes. -/
theorem simplePossibility_iff_any (f : ModalBase) (p : BProp World) (w : World) :
    simplePossibility f p w ↔ (accessibleWorlds f w).any p = true := by
  simp only [simplePossibility, diamondR, List.any_eq_true]
  exact ⟨fun ⟨j, hj, hp⟩ => ⟨j, (kratzerR_iff_accessible f w j).mp hj, hp⟩,
         fun ⟨j, hj, hp⟩ => ⟨j, (kratzerR_iff_accessible f w j).mpr hj, hp⟩⟩

/-- `necessity f g p w` iff the Bool check over best worlds passes. -/
theorem necessity_iff_all (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    necessity f g p w ↔ (bestWorlds f g w).all p = true := by
  simp only [necessity, boxR, kratzerBestR, List.all_eq_true]

/-- `possibility f g p w` iff the Bool check over best worlds passes. -/
theorem possibility_iff_any (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    possibility f g p w ↔ (bestWorlds f g w).any p = true := by
  simp only [possibility, diamondR, kratzerBestR, List.any_eq_true]

/-- Necessity with empty ordering = simple necessity. -/
theorem necessity_empty_eq_simple (f : ModalBase) (p : BProp World) (w : World) :
    necessity f emptyBackground p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff_all, simpleNecessity_iff_all]
  unfold emptyBackground
  rw [empty_ordering_simple]

-- ════════════════════════════════════════════════════════════════
-- § Frame Condition Definitions (for downstream compatibility)
-- ════════════════════════════════════════════════════════════════

def isTransitiveAccess (f : ModalBase) : Prop :=
  ∀ w w' w'' : World,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w' →
    w'' ∈ accessibleWorlds f w

def isSymmetricAccess (f : ModalBase) : Prop :=
  ∀ w w' : World,
    w' ∈ accessibleWorlds f w →
    w ∈ accessibleWorlds f w'

def isEuclideanAccess (f : ModalBase) : Prop :=
  ∀ w w' w'' : World,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w'

def isS4Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isTransitiveAccess f

def isS5Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isEuclideanAccess f

-- ════════════════════════════════════════════════════════════════
-- § Frame Condition Derivation
-- ════════════════════════════════════════════════════════════════

/-! These theorems derive frame conditions on `kratzerR` from properties
of conversational backgrounds. This is the Kratzer-specific contribution:
the frame conditions aren't stipulated, they follow from what kind of
conversational background the modal base is. -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem realistic_refl (f : ModalBase) (hReal : isRealistic f) :
    Refl (kratzerR f) := by
  intro w p hp
  exact List.all_eq_true.mp (hReal w) p hp

/-- An empty modal base gives universal accessibility. -/
theorem empty_base_universalR :
    kratzerR emptyBackground = universalR (F := modalFrame) := by
  ext w w'
  simp only [kratzerR, emptyBackground, universalR, List.not_mem_nil, false_implies,
             forall_const]

/-- Transitive list-accessibility gives transitive `kratzerR`. -/
theorem transitive_trans (f : ModalBase) (hTrans : isTransitiveAccess f) :
    Trans (kratzerR f) := by
  intro w w' w'' h1 h2
  rw [kratzerR_iff_accessible] at *
  exact hTrans w w' w'' h1 h2

/-- Symmetric list-accessibility gives symmetric `kratzerR`. -/
theorem symmetric_symm (f : ModalBase) (hSym : isSymmetricAccess f) :
    Symm (kratzerR f) := by
  intro w w' h
  rw [kratzerR_iff_accessible] at *
  exact hSym w w' h

/-- Euclidean list-accessibility gives euclidean `kratzerR`. -/
theorem euclidean_eucl (f : ModalBase) (hEuc : isEuclideanAccess f) :
    Eucl (kratzerR f) := by
  intro w w' w'' h1 h2
  rw [kratzerR_iff_accessible] at *
  exact hEuc w w' w'' h1 h2

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
theorem duality (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    necessity f g p w ↔ ¬ possibility f g (fun w' => !p w') w := by
  simp only [necessity, possibility, boxR, diamondR]
  constructor
  · intro h ⟨j, hj, hpj⟩
    simp only [Bool.not_eq_true'] at hpj
    exact absurd (h j hj) (by simp [hpj])
  · intro h j hj
    by_contra hc
    exact h ⟨j, hj, by cases hp : p j <;> simp_all⟩


/--
**K Axiom (Distribution)**: □(p → q) → (□p → □q)

Holds for any accessibility relation. -/
theorem K_axiom (f : ModalBase) (g : OrderingSource) (p q : BProp World) (w : World)
    (hImpl : necessity f g (fun w' => !p w' || q w') w)
    (hP : necessity f g p w) :
    necessity f g q w := by
  intro j hj
  have hI := hImpl j hj
  have hPj := hP j hj
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hI
  rcases hI with hpf | hq
  · exact absurd hpf (by simp [hPj])
  · exact hq


/--
**T Axiom**: Realistic base → □p → p.

What is necessary is actual. -/
theorem T_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hReal : isRealistic f)
    (hNec : simpleNecessity f p w) : p w = true :=
  boxR_T (kratzerR f) (realistic_refl f hReal) _ w hNec

/--
**D Axiom**: Serial accessibility → □p → ◇p.

What is necessary is possible. -/
theorem D_axiom_simple (f : ModalBase) (p : BProp World) (w : World)
    (hReal : isRealistic f)
    (hNec : simpleNecessity f p w) : simplePossibility f p w :=
  boxR_D (kratzerR f) (refl_serial (realistic_refl f hReal)) _ w hNec

/--
**4 Axiom**: Transitive accessibility → □p → □□p.

Positive introspection. -/
theorem four_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hTrans : isTransitiveAccess f)
    (hNec : simpleNecessity f p w) :
    simpleNecessity f (fun w' => decide (simpleNecessity f p w')) w := by
  intro j hj
  simp only [decide_eq_true_eq]
  exact boxR_four (kratzerR f) (transitive_trans f hTrans) _ w hNec j hj

/--
**B Axiom**: Symmetric accessibility → p → □◇p.

What is actual is necessarily possible. -/
theorem B_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hSym : isSymmetricAccess f)
    (hP : p w = true) :
    simpleNecessity f (fun w' => decide (simplePossibility f p w')) w := by
  intro j hj
  simp only [decide_eq_true_eq]
  exact boxR_B (kratzerR f) (symmetric_symm f hSym) _ w hP j hj

/--
**5 Axiom**: Euclidean accessibility → ◇p → □◇p.

Positive possibility introspection. -/
theorem five_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hEuc : isEuclideanAccess f)
    (hPoss : simplePossibility f p w) :
    simpleNecessity f (fun w' => decide (simplePossibility f p w')) w := by
  intro j hj
  simp only [decide_eq_true_eq]
  exact boxR_five (kratzerR f) (euclidean_eucl f hEuc) _ w hPoss j hj

-- ════════════════════════════════════════════════════════════════
-- § Additional Theorems
-- ════════════════════════════════════════════════════════════════

/-- Totally realistic base implies T axiom for full necessity. -/
theorem totally_realistic_gives_T (f : ModalBase) (g : OrderingSource)
    (hTotal : ∀ w, accessibleWorlds f w = [w])
    (p : BProp World) (w : World)
    (hNec : necessity f g p w) : p w = true := by
  have : kratzerBestR f g w w := by
    rw [kratzerBestR_iff_best]
    unfold bestWorlds
    simp only [hTotal w, List.filter_cons, List.filter_nil]
    have : atLeastAsGoodAs (g w) w w = true := ordering_reflexive (g w) w
    simp [this]
  exact hNec w this

/-- Realistic base gives reflexive accessibility. -/
theorem realistic_gives_reflexive_access (f : ModalBase)
    (hReal : isRealistic f) (w : World) :
    w ∈ accessibleWorlds f w :=
  (kratzerR_iff_accessible f w w).mp (realistic_refl f hReal w)

/-- Empty modal base gives universal accessibility. -/
theorem empty_base_universal_access (w : World) :
    accessibleWorlds emptyBackground w = allWorlds := by
  unfold accessibleWorlds emptyBackground propIntersection
  simp only [List.filter_eq_self, List.all_eq_true]
  intro _ _ p hp
  simp only [List.not_mem_nil] at hp

theorem euclidean_reflexive_implies_symmetric (f : ModalBase)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isSymmetricAccess f := by
  intro w w' hw'Acc
  have hwAcc := realistic_gives_reflexive_access f hReal w
  exact hEuc w w' w hw'Acc hwAcc

theorem euclidean_reflexive_implies_transitive (f : ModalBase)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isTransitiveAccess f := by
  intro w w' w'' hw'Acc hw''AccW'
  have hSym := euclidean_reflexive_implies_symmetric f hReal hEuc
  have hwAccW' : w ∈ accessibleWorlds f w' := hSym w w' hw'Acc
  exact hEuc w' w w'' hwAccW' hw''AccW'

theorem S5_satisfies_all (f : ModalBase) (hS5 : isS5Base f) :
    isRealistic f ∧ isSymmetricAccess f ∧ isTransitiveAccess f ∧ isEuclideanAccess f := by
  obtain ⟨hReal, hEuc⟩ := hS5
  exact ⟨hReal,
         euclidean_reflexive_implies_symmetric f hReal hEuc,
         euclidean_reflexive_implies_transitive f hReal hEuc,
         hEuc⟩

theorem realistic_is_serial (f : ModalBase) (hReal : isRealistic f) (w : World) :
    (accessibleWorlds f w).length > 0 :=
  List.length_pos_of_mem (realistic_gives_reflexive_access f hReal w)


-- ════════════════════════════════════════════════════════════════
-- § Comparative Possibility
-- ════════════════════════════════════════════════════════════════

/--
p is **at least as good a possibility as** q in w with respect to f and g.
-/
def atLeastAsGoodPossibility (f : ModalBase) (g : OrderingSource)
    (p q : BProp World) (w : World) : Bool :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  let qMinusP := accessible.filter (λ w' => q w' && !p w')
  let pMinusQ := accessible.filter (λ w' => p w' && !q w')
  qMinusP.all λ w' => pMinusQ.any λ w'' => atLeastAsGoodAs ordering w'' w'

def betterPossibility (f : ModalBase) (g : OrderingSource)
    (p q : BProp World) (w : World) : Bool :=
  atLeastAsGoodPossibility f g p q w && !atLeastAsGoodPossibility f g q p w

theorem comparative_poss_reflexive (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    atLeastAsGoodPossibility f g p p w = true := by
  unfold atLeastAsGoodPossibility
  simp only [Bool.and_not_self, List.filter_false, List.all_nil]

-- ════════════════════════════════════════════════════════════════
-- § Conditionals as Restriction
-- ════════════════════════════════════════════════════════════════

/--
Conditionals as modal base restrictors.

"If α, (must) β" = must_f+α β
-/
def restrictedBase (f : ModalBase) (antecedent : BProp World) : ModalBase :=
  λ w => antecedent :: f w

/-- Material implication. -/
def implies (p q : BProp World) : BProp World := λ w => !p w || q w

def materialImplication (p q : BProp World) (w : World) : Bool :=
  implies p q w

def strictImplication (p q : BProp World) : Bool :=
  allWorlds.all λ w => !p w || q w

end Semantics.Modality.Kratzer
