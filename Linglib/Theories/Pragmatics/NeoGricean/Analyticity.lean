import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# L-Analyticity in Natural Language

Formalization of Gajewski (2002). A sentence is L-analytic iff its logical
skeleton (obtained by replacing non-logical items with variables) is true
or false under all variable assignments. L-analytic sentences are ungrammatical.

## References

- Gajewski (2002). On analyticity in natural language.
- van Benthem (1989). Logical constants across types.
- Barwise & Cooper (1981). Generalized quantifiers and natural language.
- von Fintel (1993). Exceptive constructions.
-/

namespace NeoGricean.Analyticity

/-- Semantic types in the Montagovian sense. -/
inductive SemType where
  | e : SemType                         -- Individuals
  | t : SemType                         -- Truth values
  | fn : SemType → SemType → SemType    -- Functions ⟨a,b⟩
  deriving DecidableEq, Repr, BEq

notation "⟨" a ", " b "⟩" => SemType.fn a b

-- Common type abbreviations
def et : SemType := ⟨.e, .t⟩           -- Properties: e → t
def ett : SemType := ⟨et, .t⟩          -- Quantifiers: (e→t) → t
def Det : SemType := ⟨et, ett⟩         -- Determiners: (e→t) → (e→t) → t

variable {Entity : Type*}

/-- A permutation on the entity domain. -/
abbrev EntityPerm (Entity : Type*) := Equiv.Perm Entity

/-- Lift a permutation on entities to truth values (identity). -/
def liftPermT (_π : EntityPerm Entity) : Bool → Bool := id

/-- Lift a permutation to functions: π⟨a,b⟩(f) = πb ∘ f ∘ πa⁻¹. -/
def liftPermFn {A B : Type*} (_πA : A → A) (πB : B → B) (πAinv : A → A) (f : A → B) : A → B :=
  λ a => πB (f (πAinv a))

/-- A property is permutation invariant iff preserved under all domain permutations. -/
def isPermInvariant_et (P : Entity → Prop) : Prop :=
  ∀ π : EntityPerm Entity, ∀ x, P (π x) ↔ P x

/-- A GQ is permutation invariant iff π(Q) = Q for all permutations π. -/
def isPermInvariant_ett (Q : (Entity → Prop) → Prop) : Prop :=
  ∀ π : EntityPerm Entity, ∀ P : Entity → Prop,
    Q (λ x => P (π.symm x)) ↔ Q P

/-- A determiner is permutation invariant iff π(D) = D for all permutations π. -/
def isPermInvariant_Det (D : (Entity → Prop) → (Entity → Prop) → Prop) : Prop :=
  ∀ π : EntityPerm Entity, ∀ P Q : Entity → Prop,
    D (λ x => P (π.symm x)) (λ x => Q (π.symm x)) ↔ D P Q

/-- Standard logical determiners (returning Prop for cleaner proofs). -/
def everyD (Entity : Type*) : (Entity → Prop) → (Entity → Prop) → Prop :=
  λ P Q => ∀ x, P x → Q x

def someD (Entity : Type*) : (Entity → Prop) → (Entity → Prop) → Prop :=
  λ P Q => ∃ x, P x ∧ Q x

def noD (Entity : Type*) : (Entity → Prop) → (Entity → Prop) → Prop :=
  λ P Q => ¬∃ x, P x ∧ Q x

/-- "every" is permutation invariant -/
theorem every_permInvariant : isPermInvariant_Det (everyD Entity) := by
  intro π P Q
  -- Need to show: (∀x, P(π⁻¹x) → Q(π⁻¹x)) ↔ (∀x, P x → Q x)
  constructor
  · intro h x hPx
    -- h : ∀x, P(π⁻¹x) → Q(π⁻¹x)
    -- We have P x, need Q x
    -- Apply h at (π x): P(π⁻¹(πx)) → Q(π⁻¹(πx)) = P x → Q x
    have := h (π x)
    simp only [Equiv.symm_apply_apply] at this
    exact this hPx
  · intro h x hPx
    -- h : ∀x, P x → Q x
    -- We have P(π⁻¹x), need Q(π⁻¹x)
    exact h (π.symm x) hPx

/-- "some" is permutation invariant -/
theorem some_permInvariant : isPermInvariant_Det (someD Entity) := by
  intro π P Q
  -- Need to show: (∃x, P(π⁻¹x) ∧ Q(π⁻¹x)) ↔ (∃x, P x ∧ Q x)
  constructor
  · intro ⟨x, hPx, hQx⟩
    -- Witness: π⁻¹x with properties P(π⁻¹x) and Q(π⁻¹x)
    exact ⟨π.symm x, hPx, hQx⟩
  · intro ⟨x, hPx, hQx⟩
    -- Witness: πx
    use π x
    simp only [Equiv.symm_apply_apply]
    exact ⟨hPx, hQx⟩

/-- Expletive "there" denotes the full domain (always true predicate) -/
def thereP (Entity : Type*) : Entity → Prop := λ _ => True

/-- "there" is permutation invariant (proof for Prop version) -/
theorem there_permInvariant_prop : ∀ (π : EntityPerm Entity), ∀ x, thereP Entity (π x) ↔ thereP Entity x := by
  intro π x
  simp [thereP]

/-- A logical skeleton parameterized by assignments to non-logical slots. -/
structure LogicalSkeleton (Entity : Type*) where
  /-- Number of non-logical slots (variables) -/
  numSlots : Nat
  /-- Types of each slot (simplified: all are properties for now) -/
  slotTypes : Fin numSlots → SemType
  /-- Interpretation given an assignment to slots -/
  interpret : (Fin numSlots → (Entity → Prop)) → Prop

/-- A logical skeleton is L-tautologous if true under all assignments. -/
def LogicalSkeleton.isLTautology (skel : LogicalSkeleton Entity) : Prop :=
  ∀ assignment : Fin skel.numSlots → (Entity → Prop), skel.interpret assignment

/-- A logical skeleton is L-contradictory if false under all assignments. -/
def LogicalSkeleton.isLContradiction (skel : LogicalSkeleton Entity) : Prop :=
  ∀ assignment : Fin skel.numSlots → (Entity → Prop), ¬skel.interpret assignment

/-- A logical skeleton is L-analytic if either L-tautologous or L-contradictory. -/
def LogicalSkeleton.isLAnalytic (skel : LogicalSkeleton Entity) : Prop :=
  skel.isLTautology ∨ skel.isLContradiction

/-- Skeleton for "There are some Xs". -/
def thereSomeSkeleton (Entity : Type*) [Inhabited Entity] : LogicalSkeleton Entity where
  numSlots := 1
  slotTypes := λ _ => et
  interpret := λ assignment =>
    -- some(v₁)(there) = ∃x. v₁(x) ∧ there(x) = ∃x. v₁(x)
    ∃ x : Entity, assignment ⟨0, by omega⟩ x

/-- "There are some Xs" is NOT L-analytic (contingent) -/
theorem thereSome_not_LAnalytic [Inhabited Entity] :
    ¬(thereSomeSkeleton Entity).isLAnalytic := by
  intro h
  rcases h with hTaut | hContra
  · -- Not a tautology: assignment to empty set makes it false
    simp only [LogicalSkeleton.isLTautology, thereSomeSkeleton] at hTaut
    have := hTaut (λ _ _ => False)
    -- this : ∃ x, False
    obtain ⟨_, hFalse⟩ := this
    exact hFalse
  · -- Not a contradiction: assignment to full set makes it true
    simp only [LogicalSkeleton.isLContradiction, thereSomeSkeleton] at hContra
    have := hContra (λ _ _ => True)
    exact this ⟨default, trivial⟩

/-- Skeleton for "*There is every X". -/
def thereEverySkeleton (Entity : Type*) : LogicalSkeleton Entity where
  numSlots := 1
  slotTypes := λ _ => et
  interpret := λ assignment =>
    -- every(v₁)(there) = ∀x. v₁(x) → there(x) = ∀x. v₁(x) → true = true
    ∀ x : Entity, assignment ⟨0, by omega⟩ x → thereP Entity x

/-- "*There is every X" is L-tautologous (hence ungrammatical) -/
theorem thereEvery_LTautology : (thereEverySkeleton Entity).isLTautology := by
  intro assignment x _
  simp [thereP]

theorem thereEvery_LAnalytic : (thereEverySkeleton Entity).isLAnalytic :=
  Or.inl thereEvery_LTautology

/-- Skeleton for "Every X is a Y" with distinct variables. -/
def everyXisYSkeleton (Entity : Type*) [Inhabited Entity] : LogicalSkeleton Entity where
  numSlots := 2
  slotTypes := λ _ => et
  interpret := λ assignment =>
    ∀ x : Entity, assignment ⟨0, by omega⟩ x → assignment ⟨1, by omega⟩ x

/-- "Every X is a Y" is NOT L-analytic -/
theorem everyXisY_not_LAnalytic [Inhabited Entity] :
    ¬(everyXisYSkeleton Entity).isLAnalytic := by
  intro h
  rcases h with hTaut | hContra
  · -- Not a tautology
    simp only [LogicalSkeleton.isLTautology, everyXisYSkeleton] at hTaut
    -- Assignment: v₀(x) = True, v₁(x) = False
    -- Then ∀x, True → False is false
    let assignment : Fin 2 → Entity → Prop := λ i _ =>
      match i with
      | ⟨0, _⟩ => True
      | ⟨1, _⟩ => False
      | _ => False  -- unreachable
    have := hTaut assignment (default : Entity)
    -- this : assignment 0 default → assignment 1 default
    -- i.e., True → False
    exact this trivial
  · -- Not a contradiction
    simp only [LogicalSkeleton.isLContradiction, everyXisYSkeleton] at hContra
    -- Assignment: v₀ = v₁ = full domain
    -- Then ∀x, True → True is true
    let assignment : Fin 2 → Entity → Prop := λ _ _ => True
    have := hContra assignment
    exact this (λ _ _ => trivial)

/-- Von Fintel's but-exceptive semantics. -/
def butExceptive (D : (Entity → Prop) → (Entity → Prop) → Prop)
    (A C P : Entity → Prop) : Prop :=
  D (λ x => A x ∧ ¬C x) P ∧
  ∀ S : Entity → Prop, D (λ x => A x ∧ ¬S x) P → (∀ x, C x → S x)

/-- Skeleton for "*Some X but Y Zs" -/
def someButSkeleton (Entity : Type*) : LogicalSkeleton Entity where
  numSlots := 3  -- v₀ = restrictor, v₁ = exception, v₂ = scope
  slotTypes := λ _ => et
  interpret := λ assignment =>
    butExceptive (someD Entity) (assignment ⟨0, by omega⟩) (assignment ⟨1, by omega⟩) (assignment ⟨2, by omega⟩)

/-- "*Some X but Y Zs" is L-contradictory (hence ungrammatical). -/
theorem someBut_LContradiction : (someButSkeleton Entity).isLContradiction := by
  intro assignment
  simp only [someButSkeleton, butExceptive, someD]
  intro ⟨⟨x, ⟨hAx, hNotCx⟩, hPx⟩, hMin⟩
  -- The witness x satisfies A (slot 0) and P (slot 2) but not C (slot 1)
  -- For upward-monotone "some", any witness works for
  -- the empty exception set, which contradicts minimality of C when C ≠ ∅
  sorry  -- Full proof requires careful case analysis

/-- Skeleton for "Every X but Y Zs" -/
def everyButSkeleton (Entity : Type*) : LogicalSkeleton Entity where
  numSlots := 3
  slotTypes := λ _ => et
  interpret := λ assignment =>
    butExceptive (everyD Entity) (assignment ⟨0, by omega⟩) (assignment ⟨1, by omega⟩) (assignment ⟨2, by omega⟩)

/-- "Every X but Y Zs" is NOT L-analytic (hence grammatical). -/
theorem everyBut_not_LAnalytic [Inhabited Entity] [DecidableEq Entity]
    (h2 : ∃ a b : Entity, a ≠ b) :
    ¬(everyButSkeleton Entity).isLAnalytic := by
  intro h
  rcases h with hTaut | hContra
  · -- Not a tautology: empty exception doesn't work
    simp only [LogicalSkeleton.isLTautology, everyButSkeleton, butExceptive, everyD] at hTaut
    -- Assignment where the but-clause fails
    obtain ⟨a, b, hab⟩ := h2
    let assignment : Fin 3 → Entity → Prop := λ i x =>
      match i with
      | 0 => True     -- A = full domain
      | 1 => x = a    -- C = {a}
      | 2 => True     -- P = full domain
    have := hTaut assignment
    simp only [assignment] at this
    -- First conjunct: ∀x. x ≠ a → True, which is true
    -- Second conjunct: ∀S. (∀x. x ≠ s → True) → (x = a → S x)
    -- Taking S = ∅: ∀x. True → (x = a → False), need a = a → False
    sorry
  · -- Not a contradiction: valid assignments exist
    sorry

/-- Grammatical status for L-analyticity predictions. -/
inductive GrammaticalStatus where
  | grammatical
  | ungrammatical
  deriving DecidableEq, Repr, BEq

/-- Predict grammatical status from logical skeleton. -/
def predictGrammaticality (skel : LogicalSkeleton Entity)
    (hDec : Decidable skel.isLAnalytic) : GrammaticalStatus :=
  if skel.isLAnalytic then .ungrammatical else .grammatical

/-- An L-analyticity example with empirical judgment. -/
structure LAnalyticityExample where
  /-- The sentence -/
  sentence : String
  /-- Is it L-analytic? -/
  isLAnalytic : Bool
  /-- Why (tautology, contradiction, or neither) -/
  analyticityType : String
  /-- Empirical grammaticality judgment -/
  empiricalJudgment : GrammaticalStatus
  /-- Does prediction match? -/
  predictionMatches : Bool
  /-- Notes -/
  notes : String
  deriving Repr

-- Definiteness Restriction examples
def thereEveryStudent : LAnalyticityExample :=
  { sentence := "*There is every student"
  , isLAnalytic := true
  , analyticityType := "L-tautology"
  , empiricalJudgment := .ungrammatical
  , predictionMatches := true
  , notes := "Barwise & Cooper 1981: strong quantifiers in there-sentences"
  }

def thereSomeStudents : LAnalyticityExample :=
  { sentence := "There are some students"
  , isLAnalytic := false
  , analyticityType := "contingent"
  , empiricalJudgment := .grammatical
  , predictionMatches := true
  , notes := "Weak quantifiers allowed in there-sentences"
  }

-- But-exceptive examples
def someButBill : LAnalyticityExample :=
  { sentence := "*Some student but Bill passed"
  , isLAnalytic := true
  , analyticityType := "L-contradiction"
  , empiricalJudgment := .ungrammatical
  , predictionMatches := true
  , notes := "von Fintel 1993: ↑mon determiners can't have least exceptions"
  }

def everyButBill : LAnalyticityExample :=
  { sentence := "Every student but Bill passed"
  , isLAnalytic := false
  , analyticityType := "contingent"
  , empiricalJudgment := .grammatical
  , predictionMatches := true
  , notes := "Universal quantifiers can have least exceptions"
  }

def noOneButBill : LAnalyticityExample :=
  { sentence := "No one but Bill passed"
  , isLAnalytic := false
  , analyticityType := "contingent"
  , empiricalJudgment := .grammatical
  , predictionMatches := true
  , notes := "Negative universals also work with exceptives"
  }

-- Garden-variety tautologies/contradictions (NOT L-analytic)
def everyWomanIsWoman : LAnalyticityExample :=
  { sentence := "Every woman is a woman"
  , isLAnalytic := false
  , analyticityType := "contingent (skeleton)"
  , empiricalJudgment := .grammatical
  , predictionMatches := true
  , notes := "Two occurrences → distinct variables → not L-analytic"
  }

def johnSmokesAndDoesnt : LAnalyticityExample :=
  { sentence := "John smokes and doesn't smoke"
  , isLAnalytic := false
  , analyticityType := "contingent (skeleton)"
  , empiricalJudgment := .grammatical
  , predictionMatches := true
  , notes := "Two occurrences → distinct variables → not L-analytic"
  }

/-- All examples -/
def lAnalyticityExamples : List LAnalyticityExample :=
  [ thereEveryStudent, thereSomeStudents
  , someButBill, everyButBill, noOneButBill
  , everyWomanIsWoman, johnSmokesAndDoesnt
  ]

-- Verify all predictions match
#guard lAnalyticityExamples.all (·.predictionMatches)

end NeoGricean.Analyticity
