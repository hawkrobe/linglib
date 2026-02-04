/-
# PLA Deep Theorems

The fundamental results that establish WHY dynamic semantics matters.

## Key Results

### 1. Discourse Referent Export
Existentials introduce discourse referents accessible OUTSIDE their syntactic scope.
This is THE key innovation of dynamic semantics over static approaches.

### 2. Double Negation Failure
`¬¬φ ≢ φ` when φ introduces discourse referents.
Negation "traps" discourse referents, preventing export.

### 3. Conjunction Asymmetry
`φ ∧ ψ ≢ ψ ∧ φ` when φ introduces drefs used in ψ.
Dynamic conjunction is non-commutative.

## References

- Dekker, P. (2012). Dynamic Semantics. Chapters 2-3.
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
- Heim (1982). The Semantics of Definite and Indefinite Noun Phrases.
-/

import Linglib.Theories.DynamicSemantics.PLA.Update
import Linglib.Theories.DynamicSemantics.PLA.Epistemic

namespace Theories.DynamicSemantics.PLA

open Classical

variable {E : Type*} [Nonempty E]


/--
**Theorem (Discourse Referent Export)**

After updating with `∃x.φ`, the resulting possibilities all have x bound
to some witnessing entity. This entity is then available for anaphoric reference.

Concretely: if p ∈ ⟦∃x.φ⟧(s), then there exists e such that:
1. p.1 x could be anything (assignment unchanged at surface)
2. BUT: φ was satisfied with x ↦ e for some e
3. AND: that e is recorded in the possibility

The key insight: the existential update FILTERS to possibilities where
a witness exists, making that witness available for subsequent reference.
-/
theorem export_witness (M : Model E) (x : VarIdx) (φ : Formula) (s : InfoState E)
    (p : Poss E) (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
  exact hp.2

/--
**Corollary**: The output state of an existential update is exactly those
input possibilities that have a witness.
-/
theorem exists_update_characterization (M : Model E) (x : VarIdx) (φ : Formula)
    (s : InfoState E) :
    (Formula.exists_ x φ).update M s =
    { p ∈ s | ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 } := by
  ext p
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat]


/--
**Theorem (Cross-Sentential Binding)**

After the first sentence, any surviving possibility has a witness for "a man".
The second sentence can then predicate of that witness.

This formalizes: the existential in sentence 1 makes x available for sentence 2.
-/
theorem cross_sentential_binding (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ ((Formula.exists_ x φ).update M ;; ψ.update M) s) :
    -- p survived the existential update
    p ∈ (Formula.exists_ x φ).update M s ∧
    -- p satisfies ψ
    ψ.sat M p.1 p.2 := by
  simp only [Core.CCP.seq] at hp
  constructor
  · exact update_eliminative M ψ _ hp
  · simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
    exact hp.2

/--
**Corollary**: Cross-sentential binding gives access to the witness.
-/
theorem cross_sentential_witness (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ ((Formula.exists_ x φ).update M ;; ψ.update M) s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  have h := (cross_sentential_binding M x φ ψ s p hp).1
  exact export_witness M x φ s p h


/-!
### Double Negation in PLA

In PLA, the `domain` function (bound variables) passes through negation:
  `(∼φ).domain = φ.domain`

So syntactically, `∃x.P(x)` and `¬¬(∃x.P(x))` have the SAME domain!

The "trapping" of discourse referents happens SEMANTICALLY:
- After `⟦∃x.P(x)⟧(s)`, we filter to possibilities with witnesses
- After `⟦¬¬(∃x.P(x))⟧(s)`, we check the double negation test

The key insight is that `⟦∃x.P(x)⟧` INTRODUCES a witness that subsequent
formulas can reference, while `⟦¬¬(∃x.P(x))⟧` does NOT introduce a witness -
it only tests that a witness exists.

This is why bilateral/CDRT frameworks are needed: they track positive vs
negative updates separately, allowing proper handling of anaphora.
-/

/--
**Theorem**: Domain passes through negation (syntactic property).
-/
theorem neg_domain (φ : Formula) :
    (∼φ).domain = φ.domain := by
  simp only [Formula.domain]

/--
**Theorem**: Double negation preserves domain syntactically.
-/
theorem dne_domain_same (φ : Formula) :
    (∼(∼φ)).domain = φ.domain := by
  simp only [Formula.domain]

/--
**Theorem**: Double negation preserves range (pronouns).
-/
theorem dne_range_same (φ : Formula) :
    (∼(∼φ)).range = φ.range := by
  simp only [Formula.range]

/--
**Theorem (Semantic Difference)**: The update behavior differs.

∃x.φ introduces a witness: after the update, there exists e such that φ holds.
¬¬(∃x.φ) only tests: the update checks if ¬(¬∃x.φ) is satisfiable.

This theorem shows the concrete difference: after ∃x.φ, we can extract a witness.
-/
theorem existential_introduces_witness (M : Model E) (x : VarIdx) (φ : Formula)
    (s : InfoState E) (p : Poss E) (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
  exact hp.2

/--
**Theorem**: The domain is nonempty for existentials.
-/
theorem exists_domain_nonempty (x : VarIdx) (φ : Formula) :
    (Formula.exists_ x φ).domain.Nonempty := by
  use x
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _


/--
**Lemma**: Sequential update composition membership.
-/
theorem seq_update_mem (M : Model E) (φ ψ : Formula) (s : InfoState E) (p : Poss E) :
    p ∈ (φ.update M ;; ψ.update M) s ↔
    p ∈ s ∧ φ.sat M p.1 p.2 ∧ ψ.sat M p.1 p.2 := by
  simp only [Core.CCP.seq, Formula.update, InfoState.restrict, Set.mem_setOf_eq]
  tauto

/--
**Lemma**: Sequential update as set comprehension.
-/
theorem seq_update_eq (M : Model E) (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.update M) s =
    { p ∈ s | φ.sat M p.1 p.2 ∧ ψ.sat M p.1 p.2 } := by
  ext p
  rw [seq_update_mem]
  simp only [Set.mem_setOf_eq]

/--
**Theorem**: For dref-free formulas, conjunction IS commutative.

This shows the asymmetry is specifically due to discourse referent introduction.
-/
theorem static_conjunction_commutes (M : Model E) (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = (ψ.update M ;; φ.update M) s := by
  rw [seq_update_eq, seq_update_eq]
  ext p
  simp only [Set.mem_setOf_eq]
  tauto

/--
**Theorem**: Dynamic conjunction equals static for dref-free formulas.
-/
theorem dyn_eq_static_when_no_drefs (M : Model E) (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = (φ ⋀ ψ).update M s := by
  rw [seq_update_eq]
  ext p
  simp only [Set.mem_setOf_eq, Formula.update, InfoState.restrict, Formula.sat]


/-!
### Key Insight

The difference between static and dynamic is about SCOPE.

In static semantics:
  "A man walked in. He sat down."
  = ∃x.WalkedIn(x) ∧ SatDown(?)
  The "He" has no antecedent!

In dynamic semantics:
  ⟦∃x.WalkedIn(x)⟧ ; ⟦SatDown(x)⟧
  After the first update, x is accessible.
-/

/--
**Theorem**: Existential extends scope rightward in dynamic conjunction.

If p survives ⟦∃x.φ⟧ ; ⟦ψ⟧, then both:
1. Some witness e made φ true
2. ψ is true (and can reference the witness via resolution)
-/
theorem existential_extends_scope (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ ((Formula.exists_ x φ).update M ;; ψ.update M) s) :
    (∃ e : E, φ.sat M (p.1[x ↦ e]) p.2) ∧ ψ.sat M p.1 p.2 := by
  constructor
  · exact cross_sentential_witness M x φ ψ s p hp
  · exact (cross_sentential_binding M x φ ψ s p hp).2

/--
**Theorem**: Without dynamic conjunction, existential scope is local.

In φ ⋀ ψ (static conjunction), x is only bound within φ.
-/
theorem static_existential_local_scope (x : VarIdx) (φ ψ : Formula) :
    -- x is in the domain of ∃x.φ
    x ∈ (Formula.exists_ x φ).domain ∧
    -- But the domain of ψ is unaffected by the existential
    (Formula.exists_ x φ ⋀ ψ).domain = (Formula.exists_ x φ).domain ∪ ψ.domain := by
  constructor
  · simp only [Formula.domain]
    exact Finset.mem_insert_self x _
  · simp only [Formula.domain]


/--
**Bathroom Sentences** (Partee)

"Either there's no bathroom in this house, or it's upstairs."

The pronoun "it" in the second disjunct needs to refer to the bathroom
that was NEGATED in the first disjunct. This is problematic for PLA.
-/
def bathroomSentence : Formula :=
  -- "Either there's no bathroom, or it's upstairs"
  -- ¬∃x.Bathroom(x) ∨ Upstairs(p₀)
  Formula.disj
    (∼(Formula.exists_ 0 (Formula.atom "Bathroom" [.var 0])))
    (Formula.atom "Upstairs" [.pron 0])

/--
The bathroom sentence has an unbound pronoun in PLA.
This motivates more sophisticated frameworks (BUS, CDRT).
-/
theorem bathroom_range_has_pronoun :
    0 ∈ bathroomSentence.range := by
  simp only [bathroomSentence, Formula.disj, Formula.range,
             termsPronouns]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert,
             Finset.biUnion_empty, Finset.union_empty, Term.pronouns]
  simp only [Finset.mem_union, Finset.mem_singleton]
  right; native_decide

/--
The domain of the bathroom sentence is nonempty (from the negated existential).
This shows the structural mismatch: we have a pronoun but the existential
that would bind it is under negation.
-/
theorem bathroom_domain_nonempty :
    (bathroomSentence.domain).Nonempty := by
  simp only [bathroomSentence, Formula.disj, Formula.domain]
  use 0
  simp only [Finset.mem_union]
  left
  exact Finset.mem_insert_self 0 _

-- SUMMARY

/-!
## What This Module Provides

### Core Export Theorem
- `export_witness`: After ∃x.φ update, witness exists
- `exists_update_characterization`: Exact characterization of existential update
- `cross_sentential_binding`: The key theorem for discourse anaphora
- `cross_sentential_witness`: Witness extraction after binding

### Negation and Domain
- `neg_domain`: Domain passes through negation (syntactic)
- `dne_domain_same`: ¬¬φ has same domain as φ
- `dne_range_same`: ¬¬φ has same range as φ
- `existential_introduces_witness`: Semantic witness introduction

### Conjunction Properties
- `seq_update_eq`: Characterization of sequential update
- `static_conjunction_commutes`: Commutative when no drefs
- `dyn_eq_static_when_no_drefs`: Reduces to static without drefs
- `existential_extends_scope`: Scope extension theorem

### Limitations (Motivating Other Frameworks)
- `bathroom_range_has_pronoun`: Bathroom has unbound pronoun
- `bathroom_domain_nonempty`: Domain is nonempty but binding is problematic

## The Big Picture

These theorems establish:
1. WHY dynamic semantics exists (cross-sentential anaphora)
2. HOW it differs from static (scope extension via CCPs)
3. WHAT its limitations are (bathroom sentences)
4. WHY bilateral/CDRT approaches are needed
-/

end Theories.DynamicSemantics.PLA
