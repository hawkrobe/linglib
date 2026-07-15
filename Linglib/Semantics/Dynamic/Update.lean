import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

/-!
# Dynamic Propositions: The Semantic Algebra
[heim-1982] [groenendijk-stokhof-1991] [kamp-reyle-1993]

The relational type `Update S = S → S → Prop` and its core operations
form the semantic algebra shared by all dynamic semantic systems:
DRT, DPL, File Change Semantics, PLA, CDRT, BUS, and others.

## Intellectual Origins

Three independent but converging lines of work arrive at essentially
the same algebraic structure:

- **[heim-1982]**: Sentence meanings are *file change potentials* —
  functions from files to files. Her principle (A),
  `SAT(F + φ) = SAT(F) ∩ {a : a SAT φ}`, decomposes update into
  the operations formalized here as `test` (intersection) and `dseq`
  (successive file change).

- **[kamp-reyle-1993]**: Update verification clauses (Def 1.4.4)
  define when an embedding can be extended to satisfy each connective.
  These clauses correspond exactly to `test`, `dseq`, `dneg`, `dimpl`,
  and `ddisj`.

- **[groenendijk-stokhof-1991]**: Dynamic Predicate Logic makes
  the relational type explicit: meanings ARE binary relations on
  assignments. Their DPL conjunction = relational composition (`dseq`),
  DPL negation = universal non-existence (`dneg`), etc.

[muskens-1996] unified these by parametrizing over the state
type `S`, showing all systems embed into this algebra.

## Operations

| Operation | Type | Origin |
|-----------|------|--------|
| `Update S` | `S → S → Prop` | G&S 1991, implicit in Heim 1982 |
| `dseq` | `Update S → Update S → Update S` | relational composition |
| `test` | `Condition S → Update S` | identity + check |
| `dneg` | `Update S → Condition S` | universal non-existence |
| `dimpl` | `Update S → Update S → Condition S` | K&R verification for ⇒ |
| `ddisj` | `Update S → Update S → Condition S` | K&R verification for ∨ |
| `closure` | `Update S → Condition S` | existential closure (Heim's truth) |

## Cross-cutting smell: three incompatible DNE solutions

`dneg` (above) gives the standard relational negation `¬D i ⟺ ¬∃k, D i k`,
which fails double-negation elimination — `dneg (dneg D) ≢ D` because
positive update information is destroyed when negation collapses to a
state predicate. Three downstream frameworks repair DNE in mutually
incompatible ways:

| Framework | DNE mechanism | File |
|-----------|---------------|------|
| Bilateral (BUS, [krahmer-muskens-1995], [elliott-sudo-2025]) | Two update channels (positive/negative); negation = swap | `Dynamic/UpdateSemantics/Bilateral.lean`, `Studies/ElliottSudo2025.lean` |
| ICDRT ([hofmann-2025]) | Propositional drefs + complementation under flat update | `Studies/Hofmann2025.lean` |
| TTR ([cooper-2023]) | Classical metalanguage reduction; negation is static | `Semantics/TypeTheoretic/` |

These are not mere notational variants. Bilateral DNE is structural
(swap is involutive by definition); ICDRT DNE is derived (complementation
of a propositional dref); TTR DNE is inherited (the metalanguage is
classical so `¬¬p ↔ p` holds at the static layer). Each repair pays
for itself with different downstream costs — bilateral cannot
distinguish speaker-vs-hearer commitments; ICDRT requires intensional
contexts; TTR loses dynamic state-threading at the negation site.

The cross-framework comparisons are formalized at the phenomenon level:
`Studies/Hofmann2025.lean §7` (bilateral vs ICDRT on
the bathroom sentence), `Studies/Cooper2023.lean §§ 4-5`
(CDRT ↔ TTR truth-conditional equivalence + dynamic divergence under
negation), and `Studies/Dekker2012.lean` (PLA vs BUS
on the bathroom sentence: eliminative test vs structural swap). New
dynamic frameworks should declare which DNE strategy they adopt and
link to one of these comparisons.
-/

namespace Semantics.Dynamic.Core.DynProp

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
`open scoped Semantics.Dynamic.Core.DynProp`; mathlib's
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

end Semantics.Dynamic.Core.DynProp
