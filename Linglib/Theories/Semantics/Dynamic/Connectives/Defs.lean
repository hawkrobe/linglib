import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

/-!
# Dynamic Propositions: The Semantic Algebra
@cite{heim-1982} @cite{groenendijk-stokhof-1991} @cite{kamp-reyle-1993}

The relational type `DRS S = S → S → Prop` and its core operations
form the semantic algebra shared by all dynamic semantic systems:
DRT, DPL, File Change Semantics, PLA, CDRT, BUS, and others.

## Intellectual Origins

Three independent but converging lines of work arrive at essentially
the same algebraic structure:

- **@cite{heim-1982}**: Sentence meanings are *file change potentials* —
  functions from files to files. Her principle (A),
  `SAT(F + φ) = SAT(F) ∩ {a : a SAT φ}`, decomposes update into
  the operations formalized here as `test` (intersection) and `dseq`
  (successive file change).

- **@cite{kamp-reyle-1993}**: DRS verification clauses (Def 1.4.4)
  define when an embedding can be extended to satisfy each connective.
  These clauses correspond exactly to `test`, `dseq`, `dneg`, `dimpl`,
  and `ddisj`.

- **@cite{groenendijk-stokhof-1991}**: Dynamic Predicate Logic makes
  the relational type explicit: meanings ARE binary relations on
  assignments. Their DPL conjunction = relational composition (`dseq`),
  DPL negation = universal non-existence (`dneg`), etc.

@cite{muskens-1996} unified these by parametrizing over the state
type `S`, showing all systems embed into this algebra.

## Operations

| Operation | Type | Origin |
|-----------|------|--------|
| `DRS S` | `S → S → Prop` | G&S 1991, implicit in Heim 1982 |
| `dseq` | `DRS S → DRS S → DRS S` | relational composition |
| `test` | `Condition S → DRS S` | identity + check |
| `dneg` | `DRS S → Condition S` | universal non-existence |
| `dimpl` | `DRS S → DRS S → Condition S` | K&R verification for ⇒ |
| `ddisj` | `DRS S → DRS S → Condition S` | K&R verification for ∨ |
| `closure` | `DRS S → Condition S` | existential closure (Heim's truth) |

## Cross-cutting smell: three incompatible DNE solutions

`dneg` (above) gives the standard relational negation `¬D i ⟺ ¬∃k, D i k`,
which fails double-negation elimination — `dneg (dneg D) ≢ D` because
positive update information is destroyed when negation collapses to a
state predicate. Three downstream frameworks repair DNE in mutually
incompatible ways:

| Framework | DNE mechanism | File |
|-----------|---------------|------|
| Bilateral (BUS, @cite{krahmer-muskens-1995}, @cite{elliott-sudo-2025}) | Two update channels (positive/negative); negation = swap | `Dynamic/Bilateral/Basic.lean`, `Dynamic/Bilateral/ICDRT.lean` |
| ICDRT (@cite{hofmann-2025}) | Propositional drefs + complementation under flat update | `Phenomena/Anaphora/Studies/Hofmann2025.lean` |
| TTR (@cite{cooper-2023}) | Classical metalanguage reduction; negation is static | `Theories/Semantics/TypeTheoretic/` |

These are not mere notational variants. Bilateral DNE is structural
(swap is involutive by definition); ICDRT DNE is derived (complementation
of a propositional dref); TTR DNE is inherited (the metalanguage is
classical so `¬¬p ↔ p` holds at the static layer). Each repair pays
for itself with different downstream costs — bilateral cannot
distinguish speaker-vs-hearer commitments; ICDRT requires intensional
contexts; TTR loses dynamic state-threading at the negation site.

The cross-framework comparisons are formalized at the phenomenon level:
`Phenomena/Anaphora/Studies/Hofmann2025.lean §7` (bilateral vs ICDRT on
the bathroom sentence), `Phenomena/Anaphora/Studies/Cooper2023.lean §§ 4-5`
(CDRT ↔ TTR truth-conditional equivalence + dynamic divergence under
negation), and `Phenomena/Anaphora/Studies/Dekker2012.lean` (PLA vs BUS
on the bathroom sentence: eliminative test vs structural swap). New
dynamic frameworks should declare which DNE strategy they adopt and
link to one of these comparisons.
-/

namespace Semantics.Dynamic.Core.DynProp

-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

/-- DRS meaning: type `s(st)` — binary relation on states.

A proposition in dynamic semantics is a relation between an input
state and an output state. This is the type that @cite{heim-1982}'s
file change potentials, @cite{kamp-reyle-1993}'s DRS verification,
and @cite{groenendijk-stokhof-1991}'s DPL meanings all instantiate. -/
abbrev DRS (S : Type*) := S → S → Prop

/-- Condition: type `st` — property of a single state.

Static conditions that do not change the state. Conditions are
lifted to DRS meanings via `test`. -/
abbrev Condition (S : Type*) := S → Prop

-- ════════════════════════════════════════════════════════════════
-- § 2. Operations
-- ════════════════════════════════════════════════════════════════

section Operations

variable {S : Type*}

/-- Dynamic negation: `¬D` holds at `i` iff no output `k` satisfies `D`.

Corresponds to @cite{kamp-reyle-1993} Def 1.4.4 (negation verification)
and @cite{groenendijk-stokhof-1991} DPL negation. -/
def dneg (D : DRS S) : Condition S :=
  λ i => ¬∃ k, D i k

notation "∼" D => dneg D

/-- Test: lift a condition to a DRS that checks `C` without changing state.

Corresponds to @cite{heim-1982}'s intersection with the satisfaction
set: `SAT(F') = SAT(F) ∩ {a : C(a)}`. -/
def test (C : Condition S) : DRS S :=
  λ i j => i = j ∧ C j

notation "[" C "]" => test C

/-- Dynamic conjunction (sequencing): `D₁ ; D₂`.

Relational composition: there exists an intermediate state `h`
witnessing both transitions. This is @cite{heim-1982}'s successive
file change, @cite{kamp-reyle-1993}'s DRS sequencing, and
@cite{groenendijk-stokhof-1991}'s DPL conjunction. -/
def dseq (D₁ D₂ : DRS S) : DRS S :=
  λ i j => ∃ h, D₁ i h ∧ D₂ h j

infixl:65 " ⨟ " => dseq

/-- Dynamic implication: `D₁ → D₂`.

Every way of satisfying the antecedent can be extended to satisfy
the consequent. Corresponds to @cite{kamp-reyle-1993} Def 1.4.4
(implication verification): for all `h`, if `D₁ i h` then
`∃ k, D₂ h k`. -/
def dimpl (D₁ D₂ : DRS S) : Condition S :=
  λ i => ∀ h, D₁ i h → ∃ k, D₂ h k

/-- Dynamic disjunction: `D₁ ∨ D₂`.

Corresponds to @cite{kamp-reyle-1993} Def 1.4.4 (disjunction
verification): there exists an output via either disjunct. -/
def ddisj (D₁ D₂ : DRS S) : Condition S :=
  λ i => ∃ k, D₁ i k ∨ D₂ i k

/-- Anaphoric closure: `∃ output state`.

@cite{heim-1982}'s truth definition: a file is true iff its
satisfaction set is non-empty, i.e., some assignment satisfies it. -/
def closure (D : DRS S) : Condition S :=
  λ i => ∃ k, D i k

scoped notation "!" D => closure D

end Operations

-- ════════════════════════════════════════════════════════════════
-- § 3. Truth and Entailment
-- ════════════════════════════════════════════════════════════════

section Truth

variable {S : Type*}

/-- A DRS `D` is true relative to input `i` iff some output `j` satisfies `D`. -/
def trueAt (D : DRS S) (i : S) : Prop := ∃ j, D i j

/-- A DRS `D` is valid iff true at all inputs. -/
def valid (D : DRS S) : Prop := ∀ i, trueAt D i

/-- Dynamic entailment: `D₁ ⊨ D₂` iff every output of `D₁` can be
extended by `D₂`. -/
def entails (D₁ D₂ : DRS S) : Prop :=
  ∀ i, (∃ j, D₁ i j) → ∀ j, D₁ i j → ∃ k, D₂ j k

notation D₁ " ⊨ " D₂ => entails D₁ D₂

end Truth

-- ════════════════════════════════════════════════════════════════
-- § 4. Algebraic Properties
-- ════════════════════════════════════════════════════════════════

section Theorems

variable {S : Type*}

/-- Sequencing is associative. -/
theorem dseq_assoc (D₁ D₂ D₃ : DRS S) :
    (D₁ ⨟ D₂) ⨟ D₃ = D₁ ⨟ (D₂ ⨟ D₃) := by
  funext i j
  simp only [dseq, eq_iff_iff]
  constructor
  · intro ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩
    exact ⟨h', hD₁, h, hD₂, hD₃⟩
  · intro ⟨h', hD₁, h, hD₂, hD₃⟩
    exact ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩

/-- Test is left identity for sequencing (when condition holds everywhere). -/
theorem test_dseq (C : Condition S) (D : DRS S) (hC : ∀ i, C i) :
    test C ⨟ D = D := by
  funext i j
  simp only [dseq, test, eq_iff_iff]
  constructor
  · intro ⟨h, ⟨hih, _⟩, hD⟩
    subst hih
    exact hD
  · intro hD
    exact ⟨i, ⟨rfl, hC i⟩, hD⟩

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
theorem closure_closure (D : DRS S) :
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
theorem dseq_closure (D₁ D₂ : DRS S) :
    closure (D₁ ⨟ D₂) = λ i => ∃ h, D₁ i h ∧ closure D₂ h := by
  funext i
  simp only [closure, dseq, eq_iff_iff]
  constructor
  · intro ⟨j, h, hD₁, hD₂⟩
    exact ⟨h, hD₁, j, hD₂⟩
  · intro ⟨h, hD₁, j, hD₂⟩
    exact ⟨j, h, hD₁, hD₂⟩

end Theorems

end Semantics.Dynamic.Core.DynProp
