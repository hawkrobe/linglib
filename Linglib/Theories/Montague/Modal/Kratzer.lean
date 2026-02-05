/-
Kratzer (1981) Modal Semantics.

Accessibility is derived from two conversational backgrounds: modal base f
(relevant facts) and ordering source g (criteria for ranking worlds).
w ≤_A z iff {p in A : z in p} ⊆ {p in A : w in p}.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
- Kratzer, A. (2012). Modals and Conditionals. Oxford University Press.
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples
import Linglib.Theories.Montague.Modal.Basic
import Linglib.Core.Proposition
import Linglib.Theories.Montague.Modal.SatisfactionOrdering
import Mathlib.Order.Basic

namespace Montague.Modal.Kratzer

open Montague.Verb.Attitude.Examples
open Montague.Modal (ModalTheory ModalForce Proposition allWorlds')


/-- A proposition is a characteristic function on worlds (Kratzer-local). -/
abbrev Prop' := World → Bool

/-- Convert to list of worlds where proposition holds. -/
def Prop'.extension (p : Prop') : List World :=
  allWorlds.filter p

/-- The intersection of a set of propositions: worlds satisfying ALL. -/
def propIntersection (props : List Prop') : List World :=
  allWorlds.filter λ w => props.all λ p => p w

/-- A proposition p **follows from** a set A iff ∩A ⊆ p (Kratzer p. 31)

In other words: every world satisfying all of A also satisfies p. -/
def followsFrom (p : Prop') (A : List Prop') : Bool :=
  (propIntersection A).all p

/-- A set of propositions is **consistent** iff ∩A ≠ ∅ (Kratzer p. 31) -/
def isConsistent (A : List Prop') : Bool :=
  !(propIntersection A).isEmpty

/-- A proposition p is **compatible with** A iff A ∪ {p} is consistent (Kratzer p. 31) -/
def isCompatibleWith (p : Prop') (A : List Prop') : Bool :=
  isConsistent (p :: A)


/--
A conversational background maps worlds to sets of propositions.

This is Kratzer's key innovation: the modal base and ordering source are both
conversational backgrounds, but play different roles.
-/
abbrev ConvBackground := World → List Prop'

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase := ConvBackground

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource := ConvBackground

/--
A conversational background is **realistic** iff for all w: w ∈ ∩f(w).

This means the actual world satisfies all propositions in the modal base.
Kratzer (p. 32): "For each world, there is a particular body of facts in w
that has a counterpart in each world in ∩f(w)."
-/
def isRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, (f w).all (λ p => p w) = true

/--
A conversational background is **totally realistic** iff for all w: ∩f(w) = {w}.

This is the strongest form: only the actual world is accessible.
Kratzer (p. 33): "A totally realistic conversational background is a function f
such that for any world w, ∩f(w) = {w}."
-/
def isTotallyRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, propIntersection (f w) = [w]

/--
The **empty** conversational background: f(w) = ∅ for all w.

Kratzer (p. 33): "The empty conversational background is the function f such
that for any w ∈ W, f(w) = ∅. Since ∩f(w) = W if f(w) = ∅, empty
conversational backgrounds are also realistic."
-/
def emptyBackground : ConvBackground := λ _ => []


/--
The set of propositions from A that world w satisfies.

This is {p ∈ A : w ∈ p} in Kratzer's notation.
-/
def satisfiedPropositions (A : List Prop') (w : World) : List Prop' :=
  A.filter (λ p => p w)

/--
Kratzer's ordering relation: w ≤_A z

Definition (p. 39): "For all worlds w and z ∈ W:
  w ≤_A z iff {p: p ∈ A and z ∈ p} ⊆ {p: p ∈ A and w ∈ p}"

Intuitively: w is at least as good as z (w.r.t. ideal A) iff every
ideal proposition that z satisfies, w also satisfies.

Note: This is the CORRECT definition using subset inclusion,
NOT counting (which would be incorrect).
-/
def atLeastAsGoodAs (A : List Prop') (w z : World) : Bool :=
  -- Every proposition in A satisfied by z is also satisfied by w
  (satisfiedPropositions A z).all λ p => p w

notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

/--
Strict ordering: w <_A z iff w ≤_A z but not z ≤_A w.

This means w satisfies strictly more ideal propositions than z.
-/
def strictlyBetter (A : List Prop') (w z : World) : Bool :=
  atLeastAsGoodAs A w z && !atLeastAsGoodAs A z w

notation:50 w " <[" A "] " z => strictlyBetter A w z


open Core.OrderTheory

/--
Kratzer's world ordering as a `SatisfactionOrdering`.

A world w satisfies proposition p iff p(w) = true.
This connects Kratzer semantics to the generic ordering framework.
-/
def worldOrdering (A : List Prop') : SatisfactionOrdering World Prop' where
  satisfies := λ w p => p w
  criteria := A

/--
**Kratzer's ordering matches the generic framework.**

This theorem establishes that `atLeastAsGoodAs` is exactly the
generic `SatisfactionOrdering.atLeastAsGood` for worlds.
-/
theorem atLeastAsGoodAs_eq_generic (A : List Prop') (w z : World) :
    atLeastAsGoodAs A w z = (worldOrdering A).atLeastAsGood w z := by
  unfold atLeastAsGoodAs worldOrdering SatisfactionOrdering.atLeastAsGood
         SatisfactionOrdering.satisfiedBy satisfiedPropositions
  rfl

/-- Reflexivity via generic framework. -/
theorem ordering_reflexive (A : List Prop') (w : World) :
    atLeastAsGoodAs A w w = true := by
  rw [atLeastAsGoodAs_eq_generic]
  exact SatisfactionOrdering.atLeastAsGood_refl (worldOrdering A) w

/-- Transitivity via generic framework. -/
theorem ordering_transitive (A : List Prop') (u v w : World)
    (huv : atLeastAsGoodAs A u v = true)
    (hvw : atLeastAsGoodAs A v w = true) :
    atLeastAsGoodAs A u w = true := by
  rw [atLeastAsGoodAs_eq_generic] at *
  exact SatisfactionOrdering.atLeastAsGood_trans (worldOrdering A) u v w huv hvw

-- PART 4b: Mathlib Preorder Instance (via generic framework)

/--
**Kratzer's ordering as a mathlib Preorder.**

Derived from the generic `SatisfactionOrdering.toPreorder`.
-/
def kratzerPreorder (A : List Prop') : Preorder World :=
  (worldOrdering A).toPreorder

/-- Equivalence under the ordering (via generic framework). -/
def orderingEquiv (A : List Prop') (w z : World) : Prop :=
  (worldOrdering A).equiv w z

theorem orderingEquiv_refl (A : List Prop') (w : World) : orderingEquiv A w w :=
  SatisfactionOrdering.equiv_refl (worldOrdering A) w

theorem orderingEquiv_symm (A : List Prop') (w z : World)
    (h : orderingEquiv A w z) : orderingEquiv A z w :=
  SatisfactionOrdering.equiv_symm (worldOrdering A) w z h

theorem orderingEquiv_trans (A : List Prop') (u v w : World)
    (huv : orderingEquiv A u v) (hvw : orderingEquiv A v w) :
    orderingEquiv A u w :=
  SatisfactionOrdering.equiv_trans (worldOrdering A) u v w huv hvw

/--
**Theorem 2: Empty ordering makes all worlds equivalent.**

If A = ∅, then for all w, z: w ≤_A z and z ≤_A w.

Proof: The set of propositions in ∅ satisfied by any world is ∅.
Vacuously, ∅ ⊆ ∅. ∎
-/
theorem empty_ordering_all_equivalent (w z : World) :
    atLeastAsGoodAs [] w z = true ∧ atLeastAsGoodAs [] z w = true := by
  constructor <;> (unfold atLeastAsGoodAs satisfiedPropositions; simp)

theorem empty_ordering_trivial (w z : World) :
    (kratzerPreorder []).le w z :=
  (empty_ordering_all_equivalent w z).1

theorem empty_ordering_universal_equiv (w z : World) :
    orderingEquiv [] w z :=
  ⟨(empty_ordering_all_equivalent w z).1, (empty_ordering_all_equivalent w z).2⟩

-- PART 4d: Galois Connection (Proposition-World Duality)

open Core.Proposition.GaloisConnection

/--
**Kratzer's extension**: List-based version for the finite World type.

This is `propIntersection` renamed for clarity.
-/
def extension (props : List Prop') : List World :=
  propIntersection props

/--
**Kratzer's intension**: Filter propositions true at all given worlds.
-/
def intension (worlds : List World) (props : List Prop') : List Prop' :=
  intensionL worlds props

theorem extension_eq_core (props : List Prop') :
    extension props = extensionL allWorlds props := by
  unfold extension propIntersection extensionL
  rfl

theorem extension_antitone (A B : List Prop') (w : World)
    (hSub : ∀ p, p ∈ A → p ∈ B)
    (hw : w ∈ extension B) :
    w ∈ extension A := by
  rw [extension_eq_core] at hw ⊢
  exact extensionL_antitone allWorlds A B w hSub hw

theorem intension_antitone (W V : List World) (A : List Prop') (p : Prop')
    (hSub : ∀ w, w ∈ W → w ∈ V)
    (hp : p ∈ intension V A) :
    p ∈ intension W A :=
  intensionL_antitone A W V p hSub hp


/--
The set of worlds **accessible** from w given modal base f.

These are exactly the worlds in ∩f(w) - worlds compatible with all facts in f(w).
-/
def accessibleWorlds (f : ModalBase) (w : World) : List World :=
  propIntersection (f w)

theorem accessible_is_extension (f : ModalBase) (w : World) :
    accessibleWorlds f w = extension (f w) := rfl

/--
**Accessibility predicate**: w' is accessible from w iff w' ∈ ∩f(w).
-/
def accessibleFrom (f : ModalBase) (w w' : World) : Bool :=
  (f w).all (λ p => p w')

/--
The **best** worlds among accessible worlds, according to ordering source g.

These are the accessible worlds that are maximal under ≤_{g(w)}:
worlds w' such that for all accessible w'', w' ≤_{g(w)} w''.

When g(w) = ∅, all accessible worlds are best (by Theorem 2).
-/
def bestWorlds (f : ModalBase) (g : OrderingSource) (w : World) : List World :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  accessible.filter λ w' =>
    accessible.all λ w'' => atLeastAsGoodAs ordering w' w''

/--
**Theorem 3: Empty ordering source reduces to simple accessibility.**

When g(w) = ∅, bestWorlds = accessibleWorlds.
-/
theorem empty_ordering_simple (f : ModalBase) (w : World) :
    bestWorlds f (λ _ => []) w = accessibleWorlds f w := by
  unfold bestWorlds accessibleWorlds
  simp only [List.filter_eq_self]
  intro w' _
  simp only [List.all_eq_true]
  intro w'' _
  exact (empty_ordering_all_equivalent w' w'').1


/--
**Simple f-necessity** (Kratzer p. 32): p is true at ALL accessible worlds.

⟦must⟧_f(p)(w) = ∀w' ∈ ∩f(w). p(w')
-/
def simpleNecessity (f : ModalBase) (p : Prop') (w : World) : Bool :=
  (accessibleWorlds f w).all p

/--
**Simple f-possibility** (Kratzer p. 32): p is true at SOME accessible world.

⟦can⟧_f(p)(w) = ∃w' ∈ ∩f(w). p(w')
-/
def simplePossibility (f : ModalBase) (p : Prop') (w : World) : Bool :=
  (accessibleWorlds f w).any p

/--
**Necessity with ordering** (Kratzer p. 40): p is true at ALL best worlds.

⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')
-/
def necessity (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) : Bool :=
  (bestWorlds f g w).all p

/--
**Possibility with ordering**: p is true at SOME best world.

⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')
-/
def possibility (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) : Bool :=
  (bestWorlds f g w).any p


private theorem list_all_not_any_not (L : List World) (p : Prop') :
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
theorem duality (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) :
    (necessity f g p w == !possibility f g (λ w' => !p w') w) = true := by
  unfold necessity possibility
  exact list_all_not_any_not (bestWorlds f g w) p


/--
**Theorem 4: Totally realistic base gives T axiom.**

If f is totally realistic (∩f(w) = {w}), then □p → p.
-/
theorem totally_realistic_gives_T (f : ModalBase) (g : OrderingSource)
    (hTotal : ∀ w, (accessibleWorlds f w) = [w])
    (p : Prop') (w : World)
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
  constructor
  · cases w <;> simp [allWorlds]
  · exact hReal w

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

-- PART 8b: Frame Correspondence Theorems

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
theorem D_axiom (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World)
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
    (p : Prop') (w : World)
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
theorem four_axiom (f : ModalBase) (p : Prop') (w : World)
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
theorem B_axiom (f : ModalBase) (p : Prop') (w : World)
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
theorem five_axiom (f : ModalBase) (p : Prop') (w : World)
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
    (p q : Prop') (w : World) : Bool :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  let qMinusP := accessible.filter (λ w' => q w' && !p w')
  let pMinusQ := accessible.filter (λ w' => p w' && !q w')
  qMinusP.all λ w' => pMinusQ.any λ w'' => atLeastAsGoodAs ordering w'' w'

def betterPossibility (f : ModalBase) (g : OrderingSource)
    (p q : Prop') (w : World) : Bool :=
  atLeastAsGoodPossibility f g p q w && !atLeastAsGoodPossibility f g q p w

theorem comparative_poss_reflexive (f : ModalBase) (g : OrderingSource)
    (p : Prop') (w : World) :
    atLeastAsGoodPossibility f g p p w = true := by
  unfold atLeastAsGoodPossibility
  simp only [Bool.and_not_self, List.filter_false, List.all_nil]


/--
**Epistemic modality**: what is known/believed.

- Modal base: evidence/knowledge
- Ordering source: empty (or stereotypical for "probably")
-/
structure EpistemicFlavor where
  evidence : ModalBase
  ordering : OrderingSource := emptyBackground

/--
**Deontic modality**: what is required/permitted by norms.

- Modal base: circumstances
- Ordering source: laws/norms
-/
structure DeonticFlavor where
  circumstances : ModalBase
  norms : OrderingSource

/--
**Bouletic modality**: what is wanted/desired.

- Modal base: circumstances
- Ordering source: desires
-/
structure BouleticFlavor where
  circumstances : ModalBase
  desires : OrderingSource

/--
**Teleological modality**: what leads to goals.

- Modal base: circumstances
- Ordering source: goals
-/
structure TeleologicalFlavor where
  circumstances : ModalBase
  goals : OrderingSource


def implies (p q : Prop') : Prop' := λ w => !p w || q w

/--
**Theorem: K Axiom (Distribution) holds.**

□(p → q) → (□p → □q)
-/
theorem K_axiom (f : ModalBase) (g : OrderingSource) (p q : Prop') (w : World)
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
def restrictedBase (f : ModalBase) (antecedent : Prop') : ModalBase :=
  λ w => antecedent :: f w

def materialImplication (p q : Prop') (w : World) : Bool :=
  !p w || q w

def strictImplication (p q : Prop') : Bool :=
  allWorlds.all λ w => !p w || q w


structure KratzerParams where
  base : ModalBase
  ordering : OrderingSource

def KratzerTheory (params : KratzerParams) : ModalTheory where
  name := "Kratzer"
  citation := "Kratzer 1981"
  eval := λ force p w =>
    let best := bestWorlds params.base params.ordering w
    match force with
    | .necessity => best.all p
    | .possibility => best.any p

-- Standard parameter configurations

def emptyModalBase : ModalBase := emptyBackground
def emptyOrderingSource : OrderingSource := emptyBackground

def minimalParams : KratzerParams where
  base := emptyModalBase
  ordering := emptyOrderingSource

def epistemicParams (evidence : ModalBase) : KratzerParams where
  base := evidence
  ordering := emptyBackground

def deonticParams (circumstances : ModalBase) (norms : OrderingSource) : KratzerParams where
  base := circumstances
  ordering := norms

def KratzerMinimal : ModalTheory := KratzerTheory minimalParams

def concreteEpistemicBase : ModalBase := λ _ => [groundWet]

def concreteEpistemicParams : KratzerParams where
  base := concreteEpistemicBase
  ordering := emptyBackground

def KratzerEpistemic : ModalTheory := KratzerTheory concreteEpistemicParams

def concreteCircumstantialBase : ModalBase := λ _ => []
def concreteDeonticOrdering : OrderingSource := λ _ => [johnHome]

def concreteDeonticParams : KratzerParams where
  base := concreteCircumstantialBase
  ordering := concreteDeonticOrdering

def KratzerDeontic : ModalTheory := KratzerTheory concreteDeonticParams

-- Duality for ModalTheory Interface

private theorem list_duality_helper (L : List World) (p : Proposition) :
    (L.all p == !L.any λ w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

theorem kratzer_duality (params : KratzerParams) (p : Proposition) (w : World) :
    (KratzerTheory params).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds KratzerTheory ModalTheory.necessity ModalTheory.possibility
  exact list_duality_helper (bestWorlds params.base params.ordering w) p

theorem kratzer_isNormal (params : KratzerParams) : (KratzerTheory params).isNormal :=
  λ p w => kratzer_duality params p w

theorem kratzerMinimal_isNormal : KratzerMinimal.isNormal :=
  kratzer_isNormal minimalParams

end Montague.Modal.Kratzer
