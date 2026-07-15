import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

/-!
# The relational update algebra
[heim-1982] [groenendijk-stokhof-1991] [kamp-reyle-1993]

`Update S = S → S → Prop` and its operations: the semantic algebra that
DRT, DPL, File Change Semantics, PLA, CDRT, and BUS instantiate.
[heim-1982]'s file change potentials, [kamp-reyle-1993]'s verification
clauses (Def. 1.4.4), and [groenendijk-stokhof-1991]'s DPL relations all
arrive at this structure; [muskens-1996] parametrizes it over the state
type. The set-transformer face, and the bridge identifying this algebra
with its distributive fragment, live in `ContextChange.lean`; the
canonical account of the pair — Kleisli arrows of the powerset monad
inside their suplattice completion — is certified in `Kleisli.lean`.

## Main definitions

- `Update S`, `Condition S`: relations on states, properties of states.
- `dseq` (`⨟`), `test`, `dneg`, `dimpl`, `ddisj`, `closure`: the
  connectives; a `Monoid` under `⨟` (scoped instance).
- `Update.IsTest`: DPL's tests — updates that never change the state.
- `valid`, `entails` (`⊨`), `sEntails` (`⊨ₛ`): truth and
  [groenendijk-stokhof-1991] §3.5's two entailment notions.

## Main results

- `Update.IsTest.eq_test_closure`: a test is the test of its own truth
  conditions — the semantic content of [groenendijk-stokhof-1991]'s
  Fact 6.
- `entails_iff_valid_test_dimpl` (the deduction theorem, Fact 11),
  `sEntails_iff_test_closure_entails` (Fact 12), `sEntails_of_subset`
  (Fact 10).

## Implementation notes

`dneg` fails double-negation elimination: negation collapses positive
update information to a state predicate. The repairs are
framework-specific and mutually incompatible — bilateral swap
(`UpdateSemantics/Bilateral.lean`), propositional drefs (ICDRT,
`Studies/Hofmann2025.lean`), classical metalanguage (TTR,
`Studies/Cooper2023.lean`) — and the comparisons live in those studies.
-/

namespace DynamicSemantics

/-! ### Core types -/

/-- Update meaning: type `s(st)` — binary relation on states.

A proposition in dynamic semantics is a relation between an input
state and an output state. This is the type that [heim-1982]'s
file change potentials, [kamp-reyle-1993]'s Update verification,
and [groenendijk-stokhof-1991]'s DPL meanings all instantiate. -/
abbrev Update (S : Type*) := S → S → Prop

/-- Condition: type `st` — property of a single state.

Static conditions that do not change the state. Conditions are
lifted to Update meanings via `test`. -/
abbrev Condition (S : Type*) := S → Prop

/-! ### Operations -/

section Operations

variable {S : Type*}

/-- Dynamic negation: `¬D` holds at `i` iff no output `k` satisfies `D`.

Corresponds to [kamp-reyle-1993] Def 1.4.4 (negation verification)
and [groenendijk-stokhof-1991] DPL negation. -/
def dneg (D : Update S) : Condition S :=
  λ i => ¬∃ k, D i k

scoped notation "∼" D => dneg D

/-- Test: lift a condition to an Update that checks `C` without changing state.

Corresponds to [heim-1982]'s intersection with the satisfaction
set: `SAT(F') = SAT(F) ∩ {a : C(a)}`. -/
def test (C : Condition S) : Update S :=
  λ i j => i = j ∧ C j

scoped notation "[" C "]" => test C

/-- A test relates a state only to itself. Operators that return a
`Condition` (`dneg`, `dimpl`, `ddisj`) re-enter the update algebra via
`test`, so updates factoring through `test` cannot modify the state —
the algebraic core of anaphoric-island facts. -/
theorem eq_of_test {C : Condition S} {i j : S} (h : test C i j) : i = j :=
  h.1

/-- An update is a *test* when it never changes the state
([groenendijk-stokhof-1991], Definition 11) — DPL's tests. The CCP-level
`IsTest` of `ContextChange.lean` (pass-or-`∅`, Veltman's tests) is a
different notion: `lift` of a relational test is a filter, not a
pass-or-`∅` test. -/
def Update.IsTest (D : Update S) : Prop := ∀ ⦃i j⦄, D i j → i = j

theorem Update.isTest_test (C : Condition S) : Update.IsTest (test C) :=
  fun _ _ h => h.1

/-- Dynamic conjunction (sequencing): `D₁ ; D₂`.

Mathlib's relational composition `Relation.Comp` at endorelations: there
exists an intermediate state witnessing both transitions. This is
[heim-1982]'s successive file change, [kamp-reyle-1993]'s Update
sequencing, and [groenendijk-stokhof-1991]'s DPL conjunction. -/
def dseq (D₁ D₂ : Update S) : Update S :=
  Relation.Comp D₁ D₂

infixl:65 " ⨟ " => dseq

/-- Dynamic implication: `D₁ → D₂`.

Every way of satisfying the antecedent can be extended to satisfy
the consequent. Corresponds to [kamp-reyle-1993] Def 1.4.4
(implication verification): for all `h`, if `D₁ i h` then
`∃ k, D₂ h k`. -/
def dimpl (D₁ D₂ : Update S) : Condition S :=
  λ i => ∀ h, D₁ i h → ∃ k, D₂ h k

/-- Dynamic disjunction: `D₁ ∨ D₂`.

Corresponds to [kamp-reyle-1993] Def 1.4.4 (disjunction
verification): there exists an output via either disjunct. -/
def ddisj (D₁ D₂ : Update S) : Condition S :=
  λ i => ∃ k, D₁ i k ∨ D₂ i k

/-- Anaphoric closure: `∃ output state`.

[heim-1982]'s truth definition: a file is true iff its
satisfaction set is non-empty, i.e., some assignment satisfies it. -/
def closure (D : Update S) : Condition S :=
  λ i => ∃ k, D i k

scoped notation "!" D => closure D

end Operations

/-! ### Truth and entailment -/

section Truth

variable {S : Type*}

/-- An `Update` is valid iff satisfiable (`closure`) at every input. -/
def valid (D : Update S) : Prop := ∀ i, closure D i

/-- Dynamic entailment: `D₁ ⊨ D₂` iff every output of `D₁` can be
extended by `D₂`. -/
def entails (D₁ D₂ : Update S) : Prop :=
  ∀ i j, D₁ i j → closure D₂ j

scoped notation D₁ " ⊨ " D₂ => entails D₁ D₂

/-- A test is the test of its own closure — the semantic content of
[groenendijk-stokhof-1991]'s Fact 6: up to contradictions, tests are
exactly the conditions. -/
theorem Update.IsTest.eq_test_closure {D : Update S} (h : Update.IsTest D) :
    D = test (closure D) := by
  funext i j
  simp only [test, closure, eq_iff_iff]
  constructor
  · intro hij
    obtain rfl := h hij
    exact ⟨rfl, i, hij⟩
  · rintro ⟨rfl, k, hk⟩
    obtain rfl := h hk
    exact hk

/-- s-entailment ([groenendijk-stokhof-1991], Definition 18): truth is
preserved from premiss to conclusion. Unlike `⊨`, it sees no binding
between them. -/
def sEntails (D₁ D₂ : Update S) : Prop :=
  ∀ i, closure D₁ i → closure D₂ i

scoped notation D₁ " ⊨ₛ " D₂ => sEntails D₁ D₂

/-- Meaning inclusion implies s-entailment ([groenendijk-stokhof-1991],
Fact 10); the converse fails. -/
theorem sEntails_of_subset {D₁ D₂ : Update S}
    (h : ∀ ⦃i j⦄, D₁ i j → D₂ i j) : D₁ ⊨ₛ D₂ :=
  fun _ ⟨j, hj⟩ => ⟨j, h hj⟩

/-- The deduction theorem ([groenendijk-stokhof-1991], Fact 11):
entailment is validity of the implication test. -/
theorem entails_iff_valid_test_dimpl (D₁ D₂ : Update S) :
    (D₁ ⊨ D₂) ↔ valid (test (dimpl D₁ D₂)) := by
  constructor
  · intro h i
    exact ⟨i, rfl, h i⟩
  · rintro h i j hij
    obtain ⟨k, rfl, hd⟩ := h i
    exact hd j hij

/-- [groenendijk-stokhof-1991]'s Fact 12, in closure form: s-entailment
is entailment from the closed premiss. -/
theorem sEntails_iff_test_closure_entails (D₁ D₂ : Update S) :
    (D₁ ⊨ₛ D₂) ↔ (test (closure D₁) ⊨ D₂) :=
  ⟨fun h _ j ⟨_, hc⟩ => h j hc, fun h i hc => h i i ⟨rfl, hc⟩⟩

end Truth

/-! ### Algebraic properties -/

section Theorems

variable {S : Type*}

/-- Sequencing is associative: mathlib's `Relation.comp_assoc`. -/
theorem dseq_assoc (D₁ D₂ D₃ : Update S) :
    (D₁ ⨟ D₂) ⨟ D₃ = D₁ ⨟ (D₂ ⨟ D₃) :=
  Relation.comp_assoc

/-- Test is left identity for sequencing (when condition holds everywhere). -/
theorem test_dseq (C : Condition S) (D : Update S) (hC : ∀ i, C i) :
    test C ⨟ D = D := by
  funext i j
  simp only [dseq, Relation.Comp, test, eq_iff_iff]
  constructor
  · intro ⟨h, ⟨hih, _⟩, hD⟩
    subst hih
    exact hD
  · intro hD
    exact ⟨i, ⟨rfl, hC i⟩, hD⟩

/-- Test is right identity for sequencing (when condition holds everywhere).
Together with `test_dseq` and `dseq_assoc`, this makes `(Update S, ⨟, test ⊤)`
a monoid. -/
theorem dseq_test (D : Update S) (C : Condition S) (hC : ∀ i, C i) :
    D ⨟ test C = D := by
  funext i j
  simp only [dseq, Relation.Comp, test, eq_iff_iff]
  constructor
  · intro ⟨h, hD, hhj, _⟩
    subst hhj
    exact hD
  · intro hD
    exact ⟨j, hD, rfl, hC j⟩

/-- `Update S` is a monoid under dynamic conjunction `⨟` with the trivial
test as unit (`dseq_assoc`, `test_dseq`, `dseq_test`). Scoped because
`Update S` is an abbreviation for `S → S → Prop`: a global instance would
attach `*`/`1` to the bare function type. Activate with
`open scoped DynamicSemantics`; mathlib's
`WriterT (Update S) Id` then gets `Monad`/`LawfulMonad` for free. -/
scoped instance : Monoid (Update S) where
  mul := dseq
  one := test (λ _ => True)
  mul_assoc := dseq_assoc
  one_mul D := test_dseq _ D (λ _ => trivial)
  mul_one D := dseq_test D _ (λ _ => trivial)

/-- Double negation for tests. -/
theorem dneg_dneg_test (C : Condition S) :
    dneg (test (dneg (test C))) = C := by
  funext i
  simp only [dneg, test, eq_iff_iff]
  constructor
  · intro h
    by_contra hC
    apply h
    use i
    constructor
    · rfl
    · intro ⟨k, hik, hCk⟩
      subst hik
      exact hC hCk
  · intro hC ⟨j, hji, hNeg⟩
    apply hNeg
    use i
    exact ⟨hji.symm, hC⟩

/-- Closure is idempotent. -/
theorem closure_closure (D : Update S) :
    closure (test (closure D)) = closure D := by
  funext i
  simp only [closure, test, eq_iff_iff]
  constructor
  · intro ⟨j, hij, k, hD⟩
    subst hij
    exact ⟨k, hD⟩
  · intro ⟨k, hD⟩
    exact ⟨i, rfl, k, hD⟩

/-- Sequencing distributes over closure. -/
theorem dseq_closure (D₁ D₂ : Update S) :
    closure (D₁ ⨟ D₂) = λ i => ∃ h, D₁ i h ∧ closure D₂ h := by
  funext i
  simp only [closure, dseq, Relation.Comp, eq_iff_iff]
  constructor
  · intro ⟨j, h, hD₁, hD₂⟩
    exact ⟨h, hD₁, j, hD₂⟩
  · intro ⟨h, hD₁, j, hD₂⟩
    exact ⟨j, h, hD₁, hD₂⟩

end Theorems

end DynamicSemantics
