import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

/-!
# The update algebra
[heim-1982] [groenendijk-stokhof-1991] [kamp-reyle-1993] [veltman-1996]

Dynamic meanings in their two canonical faces. The *relational* face
(`Update S = S → S → Prop`, [groenendijk-stokhof-1991]'s DPL relations,
[heim-1982]'s file change potentials, [kamp-reyle-1993]'s verification
clauses, parametrized over the state type by [muskens-1996]): meanings
relate input states to output states pointwise. The *set-transformer*
face (`CCP S = Set S → Set S`, [heim-1983], [veltman-1996]): meanings
act on information states — plain sets — as wholes. The literature says
"state" at both levels: DPL's states are the points `S`, Veltman's are
the sets `Set S`, and `lift` identifies the relational face's states
with the transformer face's points — one carrier, two vocabularies. `lift` (the relational image,
[muskens-van-benthem-visser-2011]'s strongest postcondition) and `lower`
identify the relational algebra with the *distributive* transformers —
those that process elements independently — and what the transformer
face genuinely adds is the non-distributive tests (`CCP.guard`, `might`,
`must`, `negTest`) that inspect the whole state. `Kleisli.lean`
certifies the pair as canonical: updates are the Kleisli arrows of the
powerset monad, transformers their suplattice completion.

## Main definitions

- `Update S`, `Condition S`: relations on states, properties of states;
  `dseq` (`⨟`), `test`, `dneg`, `dimpl`, `ddisj`, `closure`; a `Monoid`
  under `⨟` (scoped instance).
- `Update.IsTest`: DPL's tests — updates that never change the state.
- `valid`, `entails` (`⊨`), `sEntails` (`⊨ₛ`): truth and
  [groenendijk-stokhof-1991] §3.5's two entailment notions.
- `CCP S`: meanings as transformers of information states (plain
  `Set S`), a monoid under `CCP.seq`; `CCP.neg`, `disj`,
  `CCP.guard` and the whole-state tests `might`, `must`, `negTest`.
- `IsEliminative`, `IsExpansive`, `IsTest`, `IsDistributive`: the
  classification of CCPs. N.B. the CCP-level `IsTest` (pass-or-`∅`,
  Veltman's test) is *not* the counterpart of the relational
  `Update.IsTest` (stay-put, DPL's test): `lift` of a relational test
  is an eliminative filter, not a pass-or-`∅` test.
- `supportOf`, `contentOf`, `updateFromSat`: satisfaction-based updates
  and the support relation.
- `lift`, `lower`: the bridge between the faces.

## Main results

- `Update.IsTest.eq_test_closure`: a test is the test of its own truth
  conditions ([groenendijk-stokhof-1991]'s Fact 6).
- `entails_iff_valid_test_dimpl` (the deduction theorem, Fact 11),
  `sEntails_iff_test_closure_entails` (Fact 12), `sEntails_of_subset`
  (Fact 10).
- `lower_lift`, `lift_lower`, `lift_isDistributive`: distributive CCPs
  are exactly the relational images.
- `lift_le_lift_iff`: `lift` reflects the pointwise order — the
  SP-characterization of update-update consequence.
- `might_not_isDistributive`: whole-state tests are genuinely beyond
  the relational fragment.

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
CCP-level `IsTest` below (pass-or-`∅`, Veltman's tests) is a
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

/-! ## The set-transformer face -/


/--
A Context Change Potential (CCP) is a function from states to states.

This is the semantic type for dynamic meanings.
-/
abbrev CCP (S : Type*) := Set S → Set S

namespace CCP

variable {S : Type*}

/-- Identity CCP: leaves state unchanged -/
def id : CCP S := λ s => s

/-- Absurd CCP: yields empty state -/
def absurd : CCP S := λ _ => ∅

/-- Sequential composition of CCPs -/
def seq (u v : CCP S) : CCP S := λ s => v (u s)

scoped infixl:70 " ;; " => seq

theorem seq_assoc (u v w : CCP S) : (u ;; v) ;; w = u ;; (v ;; w) := rfl
theorem id_seq (u : CCP S) : id ;; u = u := rfl
theorem seq_id (u : CCP S) : u ;; id = u := rfl

/-- CCPs form a monoid under sequential composition. Scoped because
`CCP S` is an abbreviation for `Set S → Set S`: a global instance would
attach `*`/`1` to a bare function type for every importer. Activate with
`open scoped DynamicSemantics.CCP`. -/
scoped instance : Monoid (CCP S) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- seq_absurd: anything followed by absurd is absurd -/
theorem seq_absurd (u : CCP S) : u ;; absurd = absurd := rfl

/--
Dynamic negation: complement within the input state.

This is the standard dynamic negation of [heim-1982], [veltman-1996]:
¬φ(s) = s \ φ(s). Worlds survive iff they do not survive φ.
Does not validate DNE on non-eliminative updates. For the whole-state
consistency test (must-not), see `negTest`.
-/
def neg (φ : CCP S) : CCP S :=
  λ s => s \ φ s

open Classical in
/-- Whole-state test: pass the state through iff it satisfies `C` — the
shared shape of `negTest`, `might`, `must`, and `impl`, the
non-distributive tests that inspect the entire input state. -/
noncomputable def guard (C : Set S → Prop) : CCP S :=
  λ s => if C s then s else ∅

/-- A guard whose condition holds passes the state through. -/
@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  if_pos h

/-- A guard whose condition fails crashes to `∅`. -/
@[simp] theorem guard_neg {C : Set S → Prop} {s} (h : ¬C s) : guard C s = ∅ :=
  if_neg h

/--
Test-based negation: passes (returns input) iff φ yields ∅.

A whole-state consistency test ("must-not"), NOT [heim-1982]'s or
[veltman-1996]'s negation (that is `neg`, set difference). The two
coincide only when `φ s = ∅` or `φ s = s` — see
`Studies/Beaver2001/ABLE.lean` for the proven divergence.
-/
noncomputable def negTest (φ : CCP S) : CCP S :=
  guard (λ s => ¬ (φ s).Nonempty)

/--
Compatibility test ("might"): passes iff φ yields a nonempty result.

might(φ)(s) = s if φ(s) ≠ ∅, else ∅
-/
noncomputable def might (φ : CCP S) : CCP S :=
  guard (λ s => (φ s).Nonempty)

open Classical in
/--
Full support test ("must"): passes iff φ returns input unchanged.

must(φ)(s) = s if φ(s) = s, else ∅
-/
noncomputable def must (φ : CCP S) : CCP S :=
  guard (λ s => φ s = s)

open Classical in
/--
Dynamic implication test: passes iff output of φ is preserved by ψ.

impl(φ,ψ)(s) = s if φ(s) ⊆ ψ(φ(s)), else ∅
-/
noncomputable def impl (φ ψ : CCP S) : CCP S :=
  guard (λ s => φ s ⊆ ψ (φ s))

/--
Dynamic disjunction via De Morgan: φ ∨ ψ = ¬(¬φ ; ¬ψ).

For eliminative updates this unfolds to φ(s) ∪ ψ(s \ φ(s)): the second
disjunct is evaluated in the input updated with the negation of the
first — the local-context clause of the satisfaction literature
([beaver-2001]; [heim-1983] itself gives CCPs only for *not/and/if*).
-/
def disj (φ ψ : CCP S) : CCP S := neg (seq (neg φ) (neg ψ))

/-- Dynamic entailment: φ entails ψ iff ψ adds no information after φ. -/
def entails (φ ψ : CCP S) : Prop :=
  ∀ s : Set S, (φ s).Nonempty → ψ (φ s) = φ s

/-- Entailment is reflexive -/
theorem entails_id (φ : CCP S) : entails φ id := by
  intro s _; rfl

end CCP

variable {S : Type*}

/--
An update is eliminative if it never adds possibilities.

This is the fundamental property of dynamic semantics:
information only grows (possibilities only decrease).
-/
def IsEliminative (u : CCP S) : Prop :=
  ∀ s, u s ⊆ s

/-- Identity is eliminative -/
theorem eliminative_id : IsEliminative (CCP.id : CCP S) :=
  λ _ => Set.Subset.rfl

/-- Sequential composition preserves eliminativity -/
theorem eliminative_seq (u v : CCP S)
    (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) := λ s _ hp =>
  hu s (hv (u s) hp)


/--
An update is expansive if it never removes possibilities.

Expansive operations include discourse referent introduction (DRT/DPL),
modal horizon expansion ([kirkpatrick-2024]), and accommodation.
These are the dual of eliminative operations: where eliminative updates
can only shrink the state, expansive updates can only grow it.
-/
def IsExpansive (u : CCP S) : Prop :=
  ∀ s, s ⊆ u s

/-- Identity is expansive -/
theorem expansive_id : IsExpansive (CCP.id : CCP S) :=
  λ _ => Set.Subset.rfl

/-- Sequential composition preserves expansiveness -/
theorem expansive_seq (u v : CCP S)
    (hu : IsExpansive u) (hv : IsExpansive v) :
    IsExpansive (u.seq v) := λ s _ hp =>
  hv (u s) (hu s hp)

/-- A CCP that is both eliminative and expansive is the identity on every input. -/
theorem eliminative_expansive_id (u : CCP S)
    (he : IsEliminative u) (hx : IsExpansive u) :
    ∀ s, u s = s :=
  λ s => Set.Subset.antisymm (he s) (hx s)

/-- A test either passes (returns its input) or fails (returns `∅`) —
[veltman-1996]'s tests: `might`, `must`, presupposition checks. Not the
counterpart of the relational `Update.IsTest`: lifting a relational
test gives an eliminative filter, not a pass-or-`∅` test. -/
def IsTest (u : CCP S) : Prop :=
  ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative -/
theorem test_eliminative (u : CCP S) (h : IsTest u) :
    IsEliminative u := λ s p hp => by
  cases h s with
  | inl heq => rw [heq] at hp; exact hp
  | inr hemp => rw [hemp] at hp; exact False.elim hp

open Classical in
theorem CCP.guard_isTest (C : Set S → Prop) : IsTest (CCP.guard C) := by
  intro s; simp only [CCP.guard]; split <;> simp

theorem CCP.negTest_isTest (φ : CCP S) : IsTest (CCP.negTest φ) :=
  CCP.guard_isTest _

theorem CCP.might_isTest (φ : CCP S) : IsTest (CCP.might φ) :=
  CCP.guard_isTest _

theorem CCP.must_isTest (φ : CCP S) : IsTest (CCP.must φ) :=
  CCP.guard_isTest _

theorem CCP.impl_isTest (φ ψ : CCP S) : IsTest (CCP.impl φ ψ) :=
  CCP.guard_isTest _

open Classical in
/-- Duality for the test pair: might φ = must-not (must-not φ). The
analogous identity fails for set-difference `neg` (DNE holds instead
on eliminative updates). -/
theorem CCP.might_eq_negTest_negTest (φ : CCP S) :
    CCP.might φ = CCP.negTest (CCP.negTest φ) := by
  funext s
  by_cases h : (φ s).Nonempty
  · simp [CCP.might, CCP.negTest, CCP.guard, h]
  · by_cases hs : s.Nonempty
    · simp [CCP.might, CCP.negTest, CCP.guard, h, hs]
    · simp [CCP.might, CCP.negTest, CCP.guard,
        Set.not_nonempty_iff_eq_empty.mp hs]


section GaloisContent

variable {S φ : Type*}

/--
Support relation: s supports ψ if all possibilities in s satisfy ψ.

This is the fundamental entailment relation of dynamic semantics.
-/
def supportOf (sat : S → φ → Prop) (s : Set S) (ψ : φ) : Prop :=
  ∀ p ∈ s, sat p ψ

/--
Content of a formula: all possibilities satisfying it.
-/
def contentOf (sat : S → φ → Prop) (ψ : φ) : Set S :=
  { p | sat p ψ }

/--
Galois connection: s ⊆ content ψ ↔ s supports ψ

This is the fundamental duality of dynamic semantics.
-/
theorem support_iff_subset_content (sat : S → φ → Prop) (s : Set S) (ψ : φ) :
    supportOf sat s ψ ↔ s ⊆ contentOf sat ψ := by
  constructor
  · intro h p hp
    exact h p hp
  · intro h p hp
    exact h hp

/--
Support is downward closed: smaller states support more.
-/
theorem support_mono (sat : S → φ → Prop) (s t : Set S) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  λ p hp => hs p (h hp)

/--
Empty state supports everything (vacuously).
-/
theorem empty_supports (sat : S → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ := λ _ hp => False.elim hp

/--
Content is antitone in entailment.
-/
theorem content_mono (sat : S → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  λ _ hp => h _ hp

end GaloisContent


/-! ### Separation (filtering) infrastructure -/

/-- Filtering a set by a predicate is monotone. This is the shared foundation
    for monotonicity of `updateFromSat`, `atom`, `pred1`, `pred2`, etc. -/
theorem sep_monotone (pred : S → Prop) :
    Monotone (λ s : Set S => { p ∈ s | pred p }) :=
  λ _ _ h _ hp => ⟨h hp.1, hp.2⟩

/-- Filtering a set by a predicate is eliminative. -/
theorem sep_eliminative (pred : S → Prop) :
    IsEliminative (λ s : Set S => { p ∈ s | pred p }) :=
  λ _ _ hp => hp.1


/--
The standard update construction: filter by satisfaction.

This is how PLA, DRT, DPL all define updates.
-/
def updateFromSat {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) : CCP S :=
  λ s => { p ∈ s | sat p ψ }

/-- Standard updates are eliminative -/
theorem updateFromSat_eliminative {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    IsEliminative (updateFromSat sat ψ) :=
  sep_eliminative _

/-- Standard update membership -/
theorem mem_updateFromSat {S φ : Type*} (sat : S → φ → Prop) (ψ : φ)
    (s : Set S) (p : S) :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Update equals intersection with content -/
theorem updateFromSat_eq_inter_content {S φ : Type*} (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ := by
  ext p
  simp only [mem_updateFromSat, contentOf, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Support-Update equivalence -/
theorem support_iff_update_eq {S φ : Type*} (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    supportOf sat s ψ ↔ updateFromSat sat ψ s = s := by
  constructor
  · intro h
    ext p
    simp only [mem_updateFromSat]
    constructor
    · intro ⟨hp, _⟩; exact hp
    · intro hp; exact ⟨hp, h p hp⟩
  · intro h p hp
    have : p ∈ updateFromSat sat ψ s := by rw [h]; exact hp
    exact this.2


/--
Dynamic entailment: φ dynamically entails ψ if updating with φ
always yields a state that supports ψ.
-/
def dynamicEntailsOf {S φ : Type*} (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : Set S, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is reflexive -/
theorem dynamicEntails_refl {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  λ _ _ hp => hp.2

/-- Dynamic entailment is transitive -/
theorem dynamicEntails_trans {S φ : Type*} (sat : S → φ → Prop)
    (ψ₁ ψ₂ ψ₃ : φ) (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ :=
  fun s p hp => h2 s p ⟨hp.1, h1 s p hp⟩


/--
`updateFromSat` is monotone in the state argument: larger input states yield
larger output states. Uses mathlib's `Monotone` (i.e., `s ≤ t → f s ≤ f t`
where `≤` on `Set` is `⊆`).
-/
theorem updateFromSat_monotone {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    Monotone (updateFromSat sat ψ) :=
  sep_monotone _


/-! ### Distributivity -/

/-- A CCP is distributive when it processes each element of the input independently:
    φ(s) = ⋃_{i∈s} φ({i}). -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- `updateFromSat` is always distributive: it filters per-element. -/
theorem updateFromSat_isDistributive {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    IsDistributive (updateFromSat sat ψ) := by
  intro s; ext p; simp only [updateFromSat, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hsat⟩; exact ⟨p, hp, ⟨rfl, hsat⟩⟩
  · rintro ⟨i, hi, hpi, hsat⟩; cases hpi; exact ⟨hi, hsat⟩

/-- `CCP.might` is not distributive: the whole-context test can pass while
    individual-element tests fail.

    Witness: S = Bool, φ keeps only `true`.
    `might φ {true, false} = {true, false}` (whole-context test passes),
    but per-singleton: `might φ {false} = ∅` (test fails on false-only context).
    So `false` is in the whole-context result but not the distributive union. -/
theorem might_not_isDistributive :
    ∃ (S : Type) (φ : CCP S), ¬IsDistributive (CCP.might φ) := by
  use Bool
  let φ : CCP Bool := λ s => {p ∈ s | p = true}
  use φ
  intro hD
  let s : Set Bool := {true, false}
  have hφ_nonempty : (φ s).Nonempty := by
    refine ⟨true, ?_, rfl⟩
    show true ∈ s
    exact Or.inl rfl
  have hmem : false ∈ CCP.might φ s := by
    simp only [CCP.might, CCP.guard, hφ_nonempty, ↓reduceIte]
    show false ∈ s
    exact Or.inr rfl
  rw [hD s] at hmem
  obtain ⟨i, hi, hmem_i⟩ := hmem
  simp only [CCP.might, CCP.guard] at hmem_i
  split at hmem_i
  · next hne =>
    cases hi with
    | inl h =>
      subst h
      have : false ∈ ({true} : Set Bool) := hmem_i
      change false = true at this
      exact absurd this (by decide)
    | inr h =>
      subst h
      obtain ⟨x, hx_mem, hx_val⟩ := hne
      change x = false at hx_mem
      subst hx_mem
      exact absurd hx_val (by decide)
  · exact hmem_i

/-! ### The relational bridge -/

/-! The relational type `Update S = S → S → Prop` from `DynProp` is the
primary dynamic semantic type. Every `Update` gives rise to a distributive
`CCP` via the relational image (`lift`), and every distributive CCP
arises this way (`lower`). The round-trip is the identity in both
directions (for distributive CCPs).

Non-distributive CCP operations (`negTest`, `might`, `must`) test the
*whole* input state and have no direct `Update` counterpart — they are
genuine additions of the set-transformer perspective. -/

section RelationalBridge


variable {S : Type*}

/-- Lift a relational Update meaning to a CCP (set transformer).

This is the relational image: given input state `σ`, collect all
outputs reachable from any element of `σ`. The resulting CCP is
always distributive (`lift_isDistributive`). -/
def lift (R : Update S) : CCP S :=
  λ σ => { j | ∃ i ∈ σ, R i j }

/-- Lower a CCP to a relational Update meaning.

`lower φ i j` holds iff `j` is in the output of the singleton `{i}`.
This is the inverse of `lift` for distributive CCPs. -/
def lower (φ : CCP S) : Update S :=
  λ i j => j ∈ φ {i}

/-- Lifting preserves sequential composition:
`lift (R₁ ⨟ R₂) = lift R₁ ;; lift R₂`. -/
theorem lift_dseq (R₁ R₂ : Update S) :
    lift (dseq R₁ R₂) = CCP.seq (lift R₁) (lift R₂) := by
  funext σ; ext k; simp only [lift, CCP.seq, dseq, Relation.Comp, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, j, hR₁, hR₂⟩
    exact ⟨j, ⟨i, hi, hR₁⟩, hR₂⟩
  · rintro ⟨j, ⟨i, hi, hR₁⟩, hR₂⟩
    exact ⟨i, hi, j, hR₁, hR₂⟩

/-- Lifting a test produces a per-element filter:
`lift (test C) σ = { i ∈ σ | C i }`. -/
theorem lift_test (C : Condition S) :
    lift (test C) = λ σ => { i ∈ σ | C i } := by
  funext σ; ext j; simp only [lift, test, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, rfl, hC⟩; exact ⟨hi, hC⟩
  · rintro ⟨hj, hC⟩; exact ⟨j, hj, rfl, hC⟩

/-- Lifted CCPs are always distributive. -/
theorem lift_isDistributive (R : Update S) : IsDistributive (lift R) := by
  intro σ; ext j; simp only [lift, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hR⟩
    refine ⟨i, hi, i, ?_, hR⟩; exact rfl
  · rintro ⟨i, hi, i', hi', hR⟩
    refine ⟨i, hi, ?_⟩; rwa [hi'] at hR

/-- Round-trip: `lower (lift R) = R`. The relational type loses no
information when lifted and lowered. -/
theorem lower_lift (R : Update S) : lower (lift R) = R := by
  funext i j; simp only [lower, lift, Set.mem_setOf_eq, eq_iff_iff]
  constructor
  · rintro ⟨i', hi', hR⟩; rwa [hi'] at hR
  · intro hR; exact ⟨i, rfl, hR⟩

/-- Round-trip: `lift (lower φ) = φ` for distributive CCPs.
Distributive CCPs are exactly the relational images. -/
theorem lift_lower (φ : CCP S) (hd : IsDistributive φ) :
    lift (lower φ) = φ := by
  funext σ; ext j; simp only [lift, lower, Set.mem_setOf_eq]
  rw [hd σ]
  simp only [Set.mem_setOf_eq]

/-- `lift` is the strongest-postcondition operator `SP(A, R) = R[A]` of
[muskens-van-benthem-visser-2011], and it reflects the pointwise order:
update inclusion at every input state is relational inclusion — the
SP-characterization of update-update consequence. -/
theorem lift_le_lift_iff {R R' : Update S} : lift R ≤ lift R' ↔ R ≤ R' := by
  constructor
  · intro h i j hR
    obtain ⟨i', hi', hR'⟩ := h {i} ⟨i, rfl, hR⟩
    cases hi'
    exact hR'
  · rintro h σ j ⟨i, hi, hR⟩
    exact ⟨i, hi, h i j hR⟩

/-- `lift (test C)` is eliminative: it only removes elements. -/
theorem lift_test_isEliminative (C : Condition S) :
    IsEliminative (lift (test C)) := by
  rw [lift_test]; intro σ j ⟨hj, _⟩; exact hj

@[simp] theorem mem_lift_test {C : Condition S} {σ : Set S} {i : S} :
    i ∈ lift (test C) σ ↔ i ∈ σ ∧ C i := by
  rw [lift_test]; exact Iff.rfl

/-- Composing test filters conjoins the conditions. -/
theorem lift_test_lift_test (C₁ C₂ : Condition S) (σ : Set S) :
    lift (test C₂) (lift (test C₁) σ) = lift (test fun i => C₁ i ∧ C₂ i) σ :=
  Set.ext fun i => by
    simp only [mem_lift_test]
    exact and_assoc

/-- Test filters are idempotent. -/
theorem lift_test_idem (C : Condition S) (σ : Set S) :
    lift (test C) (lift (test C) σ) = lift (test C) σ := by
  rw [lift_test_lift_test]
  exact Set.ext fun i => by simp only [mem_lift_test, and_self]

/-- Contradictory test filters compose to the empty state. -/
theorem lift_test_disjoint (C₁ C₂ : Condition S)
    (h : ∀ i, C₁ i → C₂ i → False) (σ : Set S) :
    lift (test C₂) (lift (test C₁) σ) = ∅ := by
  rw [lift_test_lift_test]
  exact Set.eq_empty_of_forall_notMem fun i hi =>
    h i (mem_lift_test.mp hi).2.1 (mem_lift_test.mp hi).2.2

/-- Covering test filters partition the state: if the conditions cover,
the union of the filters is the identity. -/
theorem lift_test_cover₃ (C₁ C₂ C₃ : Condition S)
    (h : ∀ i, C₁ i ∨ C₂ i ∨ C₃ i) (σ : Set S) :
    lift (test C₁) σ ∪ lift (test C₂) σ ∪ lift (test C₃) σ = σ :=
  Set.ext fun i => by
    simp only [Set.mem_union, mem_lift_test]
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · rcases hi with (⟨h', -⟩ | ⟨h', -⟩) | ⟨h', -⟩ <;> exact h'
    · rcases h i with h' | h' | h'
      · exact Or.inl (Or.inl ⟨hi, h'⟩)
      · exact Or.inl (Or.inr ⟨hi, h'⟩)
      · exact Or.inr ⟨hi, h'⟩

/-- `updateFromSat` is the lifting of `test` applied to a satisfaction
relation. This connects the CCP-native `updateFromSat` to the
primary relational algebra. -/
theorem updateFromSat_eq_lift_test {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    updateFromSat sat ψ = lift (test (λ p => sat p ψ)) := by
  funext σ; ext p
  simp only [updateFromSat, lift, test, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp, hsat⟩; exact ⟨p, hp, rfl, hsat⟩
  · rintro ⟨i, hi, rfl, hsat⟩; exact ⟨hi, hsat⟩

end RelationalBridge

end DynamicSemantics
