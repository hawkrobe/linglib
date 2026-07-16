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
[kamp-reyle-1993]'s verification clauses, parametrized over the state
type by [muskens-1996]): meanings relate input states to output states
pointwise. The *set-transformer* face (`CCP S = Set S → Set S`,
[heim-1982]'s file change potentials, [heim-1983]'s and
[veltman-1996]'s context change): meanings act on information states —
plain sets — as wholes. The literature says "state" at both levels:
DPL's states are the points `S`, Veltman's are the sets `Set S`, and
`lift` identifies the relational face's states with the transformer
face's points — one carrier, two vocabularies. `lift` (the relational
image, [muskens-van-benthem-visser-2011]'s strongest postcondition) and
`lower` identify the relational algebra with the *distributive*
transformers — those that process elements independently — and what the
transformer face genuinely adds is the non-distributive tests
(`CCP.guard`, `might`, `must`) that inspect the whole state.
`Kleisli.lean` certifies the pair as canonical: updates are the Kleisli
arrows of the powerset monad, transformers endomaps of its free
algebra, and `lift` the comparison between the two — so the two faces
are the Kleisli and Eilenberg–Moore presentations of one monad.

The algebra is the same at both levels. Meanings compose as a monoid
(`⨟` relational, `;;` transformer); *tests* are the subidentities —
`Update.IsTest` is `D ≤ 1` (`isTest_iff_le_one`) — and each level
normalizes its tests against its own carrier: a relational test is the
`test` of its truth condition (`Update.IsTest.eq_test_closure`), a
transformer test is the `guard` of its acceptance condition
(`CCP.IsTest.eq_guard`). The two notions are one concept at adjacent
carriers, which is why `lift` does *not* intertwine them: `lift [C]` is
the kernel operator `σ ↦ σ ∩ C` (eliminative, per-point), not a
pass-or-`∅` guard.

## Main definitions

- `Update S`, `Condition S`: relations on states, properties of states;
  `dseq` (`⨟`), `test`, `dneg`, `dimpl`, `ddisj`, `closure`; a `Monoid`
  under `⨟` (scoped instance).
- `Update.IsTest`: DPL's tests — the subidentities of the update
  monoid.
- `CCP S`: meanings as transformers of information states (plain
  `Set S`), a monoid under `CCP.seq`; `CCP.neg`, `CCP.guard` and the
  whole-state tests `might`, `must`, `negTest`; `CCP.entails`
  (acceptance-based consequence).
- `CCP.IsEliminative`, `CCP.IsTest`, `CCP.IsDistributive`: the
  classification of CCPs.
- `supportOf`, `contentOf`, `updateFromSat`, `dynamicEntailsOf`: the
  satisfaction-parameterized layer instantiated by PLA, DRT, DPL.
- `lift`, `lower`: the bridge between the faces.

## Main results

- `Update.IsTest.eq_test_closure` ([groenendijk-stokhof-1991]'s
  Fact 6) and `CCP.IsTest.eq_guard`: the mirror normal forms for tests
  at the two levels.
- `lower_lift`, `lift_lower`, `lift_isDistributive`: distributive CCPs
  are exactly the relational images.
- `lift_le_lift_iff`: `lift` reflects the pointwise order — the
  SP-characterization of update-update consequence.
- `exists_eq_lift_test_iff`: the static fragment is exactly
  eliminative ∧ distributive — van Benthem's additivity
  ([van-benthem-1986]; [rothschild-yalcin-2016]; [gillies-2022]) — and
  `CCP.might_not_isDistributive` witnesses that whole-state tests are
  genuinely beyond it.
- `support_iff_update_eq`: support is being a fixed point of the
  update — the hinge between the satisfaction layer and `CCP.entails`.

## Implementation notes

[groenendijk-stokhof-1991] §3.5's entailment notions (`⊨`, `⊨ₛ`, the
deduction theorem, Facts 10–12) live with their paper in
`Studies/GroenendijkStokhof1991.lean`.

`dneg` fails double-negation elimination: negation collapses positive
update information to a state predicate. The repairs are
framework-specific and mutually incompatible — bilateral swap
(`UpdateSemantics/Bilateral.lean`), propositional drefs (ICDRT,
`Studies/Hofmann2025.lean`), classical metalanguage (TTR,
`Studies/Cooper2023/`) — and the comparisons live in those studies.
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

[kamp-reyle-1993]'s verifying-embedding clause for negation and
[groenendijk-stokhof-1991]'s DPL negation. -/
def dneg (D : Update S) : Condition S :=
  λ i => ¬∃ k, D i k

scoped notation "∼" D => dneg D

/-- Test: lift a condition to an Update that checks `C` without changing state.

Under `lift` this is [heim-1982]'s intersection with the satisfaction
set, `SAT(F') = SAT(F) ∩ {a : C(a)}` (`lift_test`). -/
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
([groenendijk-stokhof-1991], Definition 11) — DPL's tests, the
subidentities of the update monoid (`isTest_iff_le_one`). `CCP.IsTest`
(pass-or-`∅`, Veltman's tests) is the same concept one carrier up:
`lift` of a relational test is a filter, not a pass-or-`∅` guard. -/
def Update.IsTest (D : Update S) : Prop := ∀ ⦃i j⦄, D i j → i = j

theorem Update.isTest_test (C : Condition S) : Update.IsTest (test C) :=
  fun _ _ h => h.1

/-- Dynamic conjunction (sequencing): `D₁ ; D₂`.

Mathlib's relational composition `Relation.Comp` at endorelations: there
exists an intermediate state witnessing both transitions. This is
[heim-1982]'s successive file change, [kamp-reyle-1993]'s DRS merge,
and [groenendijk-stokhof-1991]'s DPL conjunction. -/
def dseq (D₁ D₂ : Update S) : Update S :=
  Relation.Comp D₁ D₂

infixl:65 " ⨟ " => dseq

/-- Dynamic implication: `D₁ → D₂`.

Every way of satisfying the antecedent can be extended to satisfy the
consequent — [kamp-reyle-1993]'s verifying-embedding clause for the
conditional. -/
def dimpl (D₁ D₂ : Update S) : Condition S :=
  λ i => ∀ h, D₁ i h → ∃ k, D₂ h k

/-- Dynamic disjunction: `D₁ ∨ D₂`.

There exists an output via either disjunct — [kamp-reyle-1993]'s
verifying-embedding clause for disjunction. -/
def ddisj (D₁ D₂ : Update S) : Condition S :=
  λ i => ∃ k, D₁ i k ∨ D₂ i k

/-- Anaphoric closure: `∃ output state`.

[heim-1982]'s truth definition: a file is true iff its
satisfaction set is non-empty, i.e., some assignment satisfies it. -/
def closure (D : Update S) : Condition S :=
  λ i => ∃ k, D i k

scoped notation "!" D => closure D

end Operations

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
  simp [dseq, Relation.Comp, test, hC]

/-- Test is right identity for sequencing (when condition holds everywhere).
Together with `test_dseq` and `dseq_assoc`, this makes `(Update S, ⨟, test ⊤)`
a monoid. -/
theorem dseq_test (D : Update S) (C : Condition S) (hC : ∀ i, C i) :
    D ⨟ test C = D := by
  funext i j
  simp [dseq, Relation.Comp, test, hC]

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

/-! ### Tests are the subidentities -/

/-- Tests are the subidentities of the update monoid: `D` is a test iff
`D ≤ 1` in the pointwise order — the coreflexive relations. -/
theorem Update.isTest_iff_le_one {D : Update S} :
    D.IsTest ↔ D ≤ 1 :=
  ⟨fun h _ _ hij => ⟨h hij, trivial⟩, fun h _ _ hij => (h _ _ hij).1⟩

/-- A test is the test of its own closure — the semantic content of
[groenendijk-stokhof-1991]'s Fact 6: up to contradictions, tests are
exactly the conditions. The transformer-face mirror is
`CCP.IsTest.eq_guard`. -/
theorem Update.IsTest.eq_test_closure {D : Update S} (h : Update.IsTest D) :
    D = test (closure D) := by
  funext i j
  exact propext (by grind [test, closure, Update.IsTest])

end Theorems

/-! ## The set-transformer face -/


/-- A Context Change Potential: meanings as transformers of whole
information states, [heim-1983]'s and [veltman-1996]'s semantic type.
The distributive CCPs are exactly the `lift`s of relational `Update`s;
the rest — the whole-state tests below — are what this face adds. -/
abbrev CCP (S : Type*) := Set S → Set S

namespace CCP

variable {S : Type*}

/-- The identity CCP. -/
def id : CCP S := λ s => s

/-- The absurd CCP: crash to the empty state. -/
def absurd : CCP S := λ _ => ∅

/-- Sequential composition of CCPs, in diagrammatic order. -/
def seq (u v : CCP S) : CCP S := λ s => v (u s)

scoped infixl:70 " ;; " => seq

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

/-- The absurd CCP absorbs on the right. -/
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
shared shape of `negTest`, `might`, and `must`, the non-distributive
tests that inspect the entire input state. Every pass-or-`∅` CCP is a
guard (`IsTest.eq_guard`). -/
noncomputable def guard (C : Set S → Prop) : CCP S :=
  λ s => if C s then s else ∅

/-- A guard whose condition holds passes the state through. -/
@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  if_pos h

/-- A guard whose condition fails crashes to `∅`. -/
@[simp] theorem guard_neg {C : Set S → Prop} {s} (h : ¬C s) : guard C s = ∅ :=
  if_neg h

/--
Test-indexed negation: passes (returns input) iff φ yields ∅.

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

/--
Full support test ("must"): passes iff φ returns input unchanged.

must(φ)(s) = s if φ(s) = s, else ∅
-/
noncomputable def must (φ : CCP S) : CCP S :=
  guard (λ s => φ s = s)

/-- Acceptance-based consequence: every output of `φ` is a fixed point
of `ψ` — updating with the conclusion after the premiss changes nothing
([veltman-1996]'s acceptance validity; [beaver-2001]'s D45 entailment,
`Studies/Beaver2001/ABLE.lean`). `support_iff_update_eq` connects the
fixed-point reading to the satisfaction layer's `supportOf`. -/
def entails (φ ψ : CCP S) : Prop :=
  ∀ s : Set S, ψ (φ s) = φ s

end CCP

/-! ### The classification of CCPs -/

namespace CCP

variable {S : Type*}

/-- An update is *eliminative* when it never adds possibilities —
information only grows. Equivalently, `u ≤ id` in the pointwise order:
the deflationary transformers. -/
def IsEliminative (u : CCP S) : Prop :=
  ∀ s, u s ⊆ s

/-- The identity is eliminative. -/
theorem isEliminative_id : IsEliminative (id : CCP S) :=
  λ _ => Set.Subset.rfl

/-- Sequencing preserves eliminativity. -/
theorem IsEliminative.seq {u v : CCP S}
    (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) := λ s _ hp =>
  hu s (hv (u s) hp)

/-- A test either passes (returns its input) or fails (returns `∅`) —
[veltman-1996]'s tests: `might`, `must`, presupposition checks. The
same subidentity concept as the relational `Update.IsTest`, one carrier
up — which is why `lift` does not intertwine the two: lifting a
relational test gives an eliminative filter, not a pass-or-`∅` guard. -/
def IsTest (u : CCP S) : Prop :=
  ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative. -/
theorem IsTest.isEliminative {u : CCP S} (h : IsTest u) :
    IsEliminative u := λ s p hp => by
  cases h s with
  | inl heq => rw [heq] at hp; exact hp
  | inr hemp => rw [hemp] at hp; exact False.elim hp

theorem guard_isTest (C : Set S → Prop) : IsTest (guard C) := by
  intro s; simp only [guard]; split <;> simp

/-- A test is the guard of its own acceptance condition — the
transformer-face mirror of `Update.IsTest.eq_test_closure`. -/
theorem IsTest.eq_guard {u : CCP S} (h : IsTest u) :
    u = guard fun s => u s = s := by
  funext s
  by_cases hs : u s = s
  · rw [guard_pos (C := fun t => u t = t) hs, hs]
  · rw [guard_neg (C := fun t => u t = t) hs]
    exact (h s).resolve_left hs

/-- The tests are exactly the guards. -/
theorem isTest_iff_exists_guard {u : CCP S} :
    IsTest u ↔ ∃ C, u = guard C :=
  ⟨fun h => ⟨_, h.eq_guard⟩, fun ⟨C, hC⟩ => hC ▸ guard_isTest C⟩

end CCP


/-! ### The satisfaction layer

A satisfaction relation `sat : S → φ → Prop` induces the standard
eliminative fragment: per-formula contents, filter updates, the support
relation, and acceptance-based entailment. PLA, DRT, and DPL define
their updates by instantiating `sat`. -/

section Satisfaction

variable {S φ : Type*}

/-- `s` supports `ψ` when every possibility in `s` satisfies `ψ`. -/
def supportOf (sat : S → φ → Prop) (s : Set S) (ψ : φ) : Prop :=
  ∀ p ∈ s, sat p ψ

/-- The content of a formula: all possibilities satisfying it. -/
def contentOf (sat : S → φ → Prop) (ψ : φ) : Set S :=
  { p | sat p ψ }

/-- Support is inclusion in content. -/
theorem support_iff_subset_content (sat : S → φ → Prop) (s : Set S) (ψ : φ) :
    supportOf sat s ψ ↔ s ⊆ contentOf sat ψ :=
  Iff.rfl

/-- Support is downward closed: smaller states support more. -/
theorem support_mono (sat : S → φ → Prop) (s t : Set S) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  λ p hp => hs p (h hp)

/-- The empty state supports everything (vacuously). -/
theorem empty_supports (sat : S → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ := λ _ hp => False.elim hp

/-- Content is monotone in pointwise entailment. -/
theorem content_mono (sat : S → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  λ _ hp => h _ hp

/-- Filtering a set by a predicate is monotone — the shared foundation
for `updateFromSat_monotone` and its per-predicate instances. -/
theorem sep_monotone (pred : S → Prop) :
    Monotone (λ s : Set S => { p ∈ s | pred p }) :=
  λ _ _ h _ hp => ⟨h hp.1, hp.2⟩

/-- Filtering a set by a predicate is eliminative. -/
theorem sep_eliminative (pred : S → Prop) :
    CCP.IsEliminative (λ s : Set S => { p ∈ s | pred p }) :=
  λ s => Set.sep_subset s pred

/-- The standard update construction: filter by satisfaction — how PLA,
DRT, and DPL all define updates. Kept as the literal filter (rather
than `lift (test _)`, see `updateFromSat_eq_lift_test`) so instantiating
frameworks connect by `rfl`. -/
def updateFromSat (sat : S → φ → Prop) (ψ : φ) : CCP S :=
  λ s => { p ∈ s | sat p ψ }

/-- Standard updates are eliminative. -/
theorem updateFromSat_eliminative (sat : S → φ → Prop) (ψ : φ) :
    CCP.IsEliminative (updateFromSat sat ψ) :=
  sep_eliminative _

@[simp] theorem mem_updateFromSat {sat : S → φ → Prop} {ψ : φ}
    {s : Set S} {p : S} :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Updating is intersecting with the content. -/
theorem updateFromSat_eq_inter_content (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ :=
  rfl

/-- Support is being a fixed point of the update ([dekker-2012]'s
Proper Support) — the hinge between the satisfaction layer and the
acceptance-based `CCP.entails`. -/
theorem support_iff_update_eq (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    supportOf sat s ψ ↔ updateFromSat sat ψ s = s := by
  constructor
  · intro h
    ext p
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, h p hp⟩⟩
  · intro h p hp
    have : p ∈ updateFromSat sat ψ s := by rw [h]; exact hp
    exact this.2

/-- Dynamic entailment: updating with `ψ₁` always yields a state
supporting `ψ₂`. -/
def dynamicEntailsOf (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : Set S, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is `CCP.entails` of the induced updates: the
satisfaction layer's consequence is the acceptance-based one. -/
theorem dynamicEntailsOf_iff_entails (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) :
    dynamicEntailsOf sat ψ₁ ψ₂ ↔
      CCP.entails (updateFromSat sat ψ₁) (updateFromSat sat ψ₂) :=
  forall_congr' fun s => support_iff_update_eq sat ψ₂ (updateFromSat sat ψ₁ s)

/-- Dynamic entailment is reflexive. -/
theorem dynamicEntails_refl (sat : S → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  λ _ _ hp => hp.2

/-- Dynamic entailment is transitive. -/
theorem dynamicEntails_trans (sat : S → φ → Prop) (ψ₁ ψ₂ ψ₃ : φ)
    (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ :=
  fun s p hp => h2 s p ⟨hp.1, h1 s p hp⟩

/-- `updateFromSat` is monotone in the state argument. -/
theorem updateFromSat_monotone (sat : S → φ → Prop) (ψ : φ) :
    Monotone (updateFromSat sat ψ) :=
  sep_monotone _

end Satisfaction


/-! ### Distributivity -/

namespace CCP

variable {S : Type*}

/-- A CCP is distributive when it processes each element of the input
independently: `φ(s) = ⋃_{i ∈ s} φ({i})` — equivalently, it preserves
arbitrary joins of states (`Kleisli.lean`'s
`isDistributive_iff_map_sSup`). -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- `might` is not distributive: the whole-context test can pass while
every individual-element test fails. Witness: `S = Bool`, `φ` keeps only
`true`; then `false` survives `might φ` on `{true, false}` but lies in
no per-singleton output. -/
theorem might_not_isDistributive :
    ∃ (S : Type) (φ : CCP S), ¬IsDistributive (might φ) := by
  refine ⟨Bool, (fun s => {p ∈ s | p = true}), fun hD => ?_⟩
  have hfalse :
      false ∈ might (fun s : Set Bool => {p ∈ s | p = true}) {true, false} := by
    rw [might, guard_pos ⟨true, Or.inl rfl, rfl⟩]
    exact Or.inr rfl
  rw [hD] at hfalse
  obtain ⟨i, hi, hmem⟩ := hfalse
  rcases hi with rfl | rfl
  · rw [might, guard_pos ⟨true, rfl, rfl⟩] at hmem
    exact Bool.false_ne_true hmem
  · rw [might, guard_neg (fun ⟨x, hx, hx'⟩ => Bool.false_ne_true (hx ▸ hx'))]
      at hmem
    exact hmem

end CCP

/-- `updateFromSat` is always distributive: it filters per-element. -/
theorem updateFromSat_isDistributive {S φ : Type*} (sat : S → φ → Prop) (ψ : φ) :
    CCP.IsDistributive (updateFromSat sat ψ) := by
  intro s; ext p; simp only [updateFromSat, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hsat⟩; exact ⟨p, hp, ⟨rfl, hsat⟩⟩
  · rintro ⟨i, hi, hpi, hsat⟩; cases hpi; exact ⟨hi, hsat⟩

/-! ### The relational bridge

The relational type `Update S = S → S → Prop` is the primary dynamic
semantic type. Every `Update` gives rise to a distributive `CCP` via
the relational image (`lift`), and every distributive CCP arises this
way (`lower`); the round-trip is the identity in both directions.

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

theorem mem_lift {R : Update S} {σ : Set S} {j : S} :
    j ∈ lift R σ ↔ ∃ i ∈ σ, R i j := Iff.rfl

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
theorem lift_isDistributive (R : Update S) : CCP.IsDistributive (lift R) := by
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
theorem lift_lower (φ : CCP S) (hd : CCP.IsDistributive φ) :
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
    CCP.IsEliminative (lift (test C)) := by
  rw [lift_test]; intro σ j ⟨hj, _⟩; exact hj

/-- The static fragment characterized: a CCP is a lifted test filter iff
it is both eliminative and distributive — van Benthem's *additivity*
([van-benthem-1986]; [rothschild-yalcin-2016]; [gillies-2022]). The two
canonical dynamic systems drop exactly one conjunct each, in
complementary directions: update semantics keeps eliminativity but its
whole-state tests break distributivity
(`CCP.might_not_isDistributive`), while DPL's random reassignment keeps
distributivity but breaks eliminativity. -/
theorem exists_eq_lift_test_iff {φ : CCP S} :
    (∃ C : Condition S, φ = lift (test C)) ↔
      CCP.IsEliminative φ ∧ CCP.IsDistributive φ := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨lift_test_isEliminative C, lift_isDistributive _⟩
  · rintro ⟨he, hd⟩
    refine ⟨fun i => i ∈ φ {i}, ?_⟩
    funext s
    rw [hd s, lift_test]
    ext p
    exact ⟨fun ⟨i, hi, hpi⟩ => by obtain rfl : p = i := he {i} hpi; exact ⟨hi, hpi⟩,
      fun ⟨hp, hC⟩ => ⟨p, hp, hC⟩⟩

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
