/-
@cite{kratzer-1981} Modal Operators

Necessity and possibility operators, modal axioms (T, D, 4, B, 5),
frame correspondence theorems, and comparative possibility.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Ordering

namespace Semantics.Modality.Kratzer

open Semantics.Attitudes.Intensional

/--
**Simple f-necessity** (Kratzer p. 32): p is true at ALL accessible worlds.

⟦must⟧_f(p)(w) = ∀w' ∈ ∩f(w). p(w')
-/
def simpleNecessity (f : ModalBase) (p : BProp World) (w : World) : Bool :=
  (accessibleWorlds f w).all p

/--
**Simple f-possibility** (Kratzer p. 32): p is true at SOME accessible world.

⟦can⟧_f(p)(w) = ∃w' ∈ ∩f(w). p(w')
-/
def simplePossibility (f : ModalBase) (p : BProp World) (w : World) : Bool :=
  (accessibleWorlds f w).any p

/--
**Necessity with ordering** (Kratzer p. 40): p is true at ALL best worlds.

⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')
-/
def necessity (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) : Bool :=
  (bestWorlds f g w).all p

/--
**Possibility with ordering**: p is true at SOME best world.

⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')
-/
def possibility (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) : Bool :=
  (bestWorlds f g w).any p


private theorem list_all_not_any_not (L : List World) (p : BProp World) :
    (L.all p == !L.any λ w => !p w) = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/--
**Theorem: Modal duality holds.**

□p ↔ ¬◇¬p
-/
theorem duality (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World) :
    (necessity f g p w == !possibility f g (λ w' => !p w') w) = true := by
  unfold necessity possibility
  exact list_all_not_any_not (bestWorlds f g w) p


/--
**Theorem 4: Totally realistic base gives T axiom.**

If f is totally realistic (∩f(w) = {w}), then □p → p.
-/
theorem totally_realistic_gives_T (f : ModalBase) (g : OrderingSource)
    (hTotal : ∀ w, (accessibleWorlds f w) = [w])
    (p : BProp World) (w : World)
    (hNec : necessity f g p w = true) : p w = true := by
  unfold necessity at hNec
  have hAcc : accessibleWorlds f w = [w] := hTotal w
  unfold bestWorlds at hNec
  simp only [hAcc] at hNec
  simp only [List.all_cons, List.all_nil, Bool.and_true] at hNec
  have hRefl : atLeastAsGoodAs (g w) w w = true := ordering_reflexive (g w) w
  simp only [List.filter_cons, hRefl, ↓reduceIte, List.filter_nil,
             List.all_cons, List.all_nil, Bool.and_true] at hNec
  exact hNec

/--
**Theorem 5: Realistic base gives reflexive accessibility.**

If f is realistic (w ∈ ∩f(w) for all w), then the evaluation world
is always accessible from itself.
-/
theorem realistic_gives_reflexive_access (f : ModalBase)
    (hReal : isRealistic f) (w : World) :
    w ∈ accessibleWorlds f w := by
  unfold accessibleWorlds propIntersection
  simp only [List.mem_filter]
  exact ⟨Core.Proposition.FiniteWorlds.complete w, hReal w⟩

/--
**Theorem 6: Empty modal base gives universal accessibility.**

If f(w) = ∅ for all w, then ∩f(w) = W (all worlds accessible).
-/
theorem empty_base_universal_access (w : World) :
    accessibleWorlds emptyBackground w = allWorlds := by
  unfold accessibleWorlds emptyBackground propIntersection
  simp only [List.filter_eq_self, List.all_eq_true]
  intro _ _ p hp
  simp only [List.not_mem_nil] at hp

-- Frame Correspondence Theorems

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

/--
**D Axiom (Seriality)**: □p → ◇p
-/
theorem D_axiom (f : ModalBase) (g : OrderingSource) (p : BProp World) (w : World)
    (hSerial : (bestWorlds f g w).length > 0)
    (hNec : necessity f g p w = true) :
    possibility f g p w = true := by
  unfold necessity possibility at *
  have hAll : (bestWorlds f g w).all p = true := hNec
  match hBest : bestWorlds f g w with
  | [] =>
    simp only [hBest, List.length_nil, gt_iff_lt, Nat.lt_irrefl] at hSerial
  | w' :: ws =>
    simp only [List.any_cons]
    have hPw' : p w' = true := by
      simp only [hBest, List.all_cons, Bool.and_eq_true] at hAll
      exact hAll.1
    simp only [hPw', Bool.true_or]

theorem realistic_is_serial (f : ModalBase) (hReal : isRealistic f) (w : World) :
    (accessibleWorlds f w).length > 0 := by
  have hw_acc := realistic_gives_reflexive_access f hReal w
  exact List.length_pos_of_mem hw_acc

theorem D_axiom_realistic (f : ModalBase) (hReal : isRealistic f)
    (p : BProp World) (w : World)
    (hNec : necessity f emptyBackground p w = true) :
    possibility f emptyBackground p w = true := by
  have hSimple := empty_ordering_simple f w
  have hSerial := realistic_is_serial f hReal w
  have hBestSerial : (bestWorlds f emptyBackground w).length > 0 := by
    unfold emptyBackground at hSimple ⊢
    rw [hSimple]
    exact hSerial
  exact D_axiom f emptyBackground p w hBestSerial hNec

/--
**4 Axiom (Transitivity)**: □p → □□p
-/
theorem four_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hTrans : isTransitiveAccess f)
    (hNec : necessity f emptyBackground p w = true) :
    necessity f emptyBackground (necessity f emptyBackground p) w = true := by
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    λ v => empty_ordering_simple f v
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  show (bestWorlds f emptyBackground w').all p = true
  rw [hSimple w']
  apply List.all_eq_true.mpr
  intro w'' hw''Acc
  have hw''AccW : w'' ∈ accessibleWorlds f w := hTrans w w' w'' hw'Acc hw''Acc
  unfold necessity at hNec
  rw [hSimple w] at hNec
  exact List.all_eq_true.mp hNec w'' hw''AccW

/--
**B Axiom (Symmetry)**: p → □◇p
-/
theorem B_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hSym : isSymmetricAccess f)
    (hP : p w = true) :
    necessity f emptyBackground (possibility f emptyBackground p) w = true := by
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    λ v => empty_ordering_simple f v
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  unfold possibility
  rw [hSimple w']
  apply List.any_eq_true.mpr
  have hwAccW' : w ∈ accessibleWorlds f w' := hSym w w' hw'Acc
  exact ⟨w, hwAccW', hP⟩

/--
**5 Axiom (Euclidean)**: ◇p → □◇p
-/
theorem five_axiom (f : ModalBase) (p : BProp World) (w : World)
    (hEuc : isEuclideanAccess f)
    (hPoss : possibility f emptyBackground p w = true) :
    necessity f emptyBackground (possibility f emptyBackground p) w = true := by
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    λ v => empty_ordering_simple f v
  unfold possibility at hPoss
  rw [hSimple w] at hPoss
  obtain ⟨w'', hw''Acc, hPw''⟩ := List.any_eq_true.mp hPoss
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  unfold possibility
  rw [hSimple w']
  apply List.any_eq_true.mpr
  have hw''AccW' : w'' ∈ accessibleWorlds f w' := hEuc w w' w'' hw'Acc hw''Acc
  exact ⟨w'', hw''AccW', hPw''⟩

def isS4Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isTransitiveAccess f

def isS5Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isEuclideanAccess f

theorem euclidean_reflexive_implies_symmetric (f : ModalBase)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isSymmetricAccess f := by
  intro w w' hw'Acc
  have hwAcc : w ∈ accessibleWorlds f w := realistic_gives_reflexive_access f hReal w
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

/-- Material conditional as material implication. -/
def implies (p q : BProp World) : BProp World := λ w => !p w || q w

/--
**Theorem: K Axiom (Distribution) holds.**

□(p → q) → (□p → □q)
-/
theorem K_axiom (f : ModalBase) (g : OrderingSource) (p q : BProp World) (w : World)
    (hImpl : necessity f g (implies p q) w = true)
    (hP : necessity f g p w = true) :
    necessity f g q w = true := by
  unfold necessity at hImpl hP ⊢
  apply List.all_eq_true.mpr
  intro w' hW'Best
  have hImplW' : implies p q w' = true := List.all_eq_true.mp hImpl w' hW'Best
  have hPW' : p w' = true := List.all_eq_true.mp hP w' hW'Best
  unfold implies at hImplW'
  cases hp : p w' with
  | false => simp [hp] at hPW'
  | true => simp [hp] at hImplW'; exact hImplW'


/--
Conditionals as modal base restrictors.

"If α, (must) β" = must_f+α β
-/
def restrictedBase (f : ModalBase) (antecedent : BProp World) : ModalBase :=
  λ w => antecedent :: f w

def materialImplication (p q : BProp World) (w : World) : Bool :=
  !p w || q w

def strictImplication (p q : BProp World) : Bool :=
  allWorlds.all λ w => !p w || q w

end Semantics.Modality.Kratzer
