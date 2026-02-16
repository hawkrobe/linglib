/-
# PLA Deep Theorems

Fundamental results distinguishing dynamic from static semantics.

## Main definitions

- `export_witness`, `cross_sentential_binding`
- `existential_introduces_witness`
- `static_conjunction_commutes`

## References

- Dekker, P. (2012). Dynamic Semantics.
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
- Heim (1982). The Semantics of Definite and Indefinite Noun Phrases.
-/

import Linglib.Theories.Semantics.Dynamic.Systems.PLA.Update
import Linglib.Theories.Semantics.Dynamic.Systems.PLA.Epistemic

namespace Semantics.Dynamic.PLA

open Classical

variable {E : Type*} [Nonempty E]


/-- Discourse referent export: existential update makes witnesses available for anaphora. -/
theorem export_witness (M : Model E) (x : VarIdx) (φ : Formula) (s : InfoState E)
    (p : Poss E) (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
  exact hp.2

/-- Existential update output characterization. -/
theorem exists_update_characterization (M : Model E) (x : VarIdx) (φ : Formula)
    (s : InfoState E) :
    (Formula.exists_ x φ).update M s =
    { p ∈ s | ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 } := by
  ext p
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat]


/-- Cross-sentential binding: existentials in first sentence bind variables in second. -/
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

/-- Cross-sentential binding gives access to the witness. -/
theorem cross_sentential_witness (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ ((Formula.exists_ x φ).update M ;; ψ.update M) s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  have h := (cross_sentential_binding M x φ ψ s p hp).1
  exact export_witness M x φ s p h



/-- Domain passes through negation. -/
theorem neg_domain (φ : Formula) :
    (∼φ).domain = φ.domain := by
  simp only [Formula.domain]

/-- Double negation preserves domain. -/
theorem dne_domain_same (φ : Formula) :
    (∼(∼φ)).domain = φ.domain := by
  simp only [Formula.domain]

/-- Double negation preserves range. -/
theorem dne_range_same (φ : Formula) :
    (∼(∼φ)).range = φ.range := by
  simp only [Formula.range]

/-- Existential introduces witness unlike double-negated existential. -/
theorem existential_introduces_witness (M : Model E) (x : VarIdx) (φ : Formula)
    (s : InfoState E) (p : Poss E) (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
  exact hp.2

/-- Existential domain is nonempty. -/
theorem exists_domain_nonempty (x : VarIdx) (φ : Formula) :
    (Formula.exists_ x φ).domain.Nonempty := by
  use x
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _


/-- Sequential update composition membership. -/
theorem seq_update_mem (M : Model E) (φ ψ : Formula) (s : InfoState E) (p : Poss E) :
    p ∈ (φ.update M ;; ψ.update M) s ↔
    p ∈ s ∧ φ.sat M p.1 p.2 ∧ ψ.sat M p.1 p.2 := by
  simp only [Core.CCP.seq, Formula.update, InfoState.restrict, Set.mem_setOf_eq]
  tauto

/-- Sequential update as set comprehension. -/
theorem seq_update_eq (M : Model E) (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.update M) s =
    { p ∈ s | φ.sat M p.1 p.2 ∧ ψ.sat M p.1 p.2 } := by
  ext p
  rw [seq_update_mem]
  simp only [Set.mem_setOf_eq]

/-- Dref-free formulas have commutative conjunction. -/
theorem static_conjunction_commutes (M : Model E) (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = (ψ.update M ;; φ.update M) s := by
  rw [seq_update_eq, seq_update_eq]
  ext p
  simp only [Set.mem_setOf_eq]
  tauto

/-- Dynamic conjunction equals static for dref-free formulas. -/
theorem dyn_eq_static_when_no_drefs (M : Model E) (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = (φ ⋀ ψ).update M s := by
  rw [seq_update_eq]
  ext p
  simp only [Set.mem_setOf_eq, Formula.update, InfoState.restrict, Formula.sat]



/-- Existential extends scope rightward in dynamic conjunction. -/
theorem existential_extends_scope (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ ((Formula.exists_ x φ).update M ;; ψ.update M) s) :
    (∃ e : E, φ.sat M (p.1[x ↦ e]) p.2) ∧ ψ.sat M p.1 p.2 := by
  constructor
  · exact cross_sentential_witness M x φ ψ s p hp
  · exact (cross_sentential_binding M x φ ψ s p hp).2

/-- Static existential has local scope. -/
theorem static_existential_local_scope (x : VarIdx) (φ ψ : Formula) :
    -- x is in the domain of ∃x.φ
    x ∈ (Formula.exists_ x φ).domain ∧
    -- But the domain of ψ is unaffected by the existential
    (Formula.exists_ x φ ⋀ ψ).domain = (Formula.exists_ x φ).domain ∪ ψ.domain := by
  constructor
  · simp only [Formula.domain]
    exact Finset.mem_insert_self x _
  · simp only [Formula.domain]


/-- Bathroom sentence: pronoun binding from negated existential (Partee). -/
def bathroomSentence : Formula :=
  -- "Either there's no bathroom, or it's upstairs"
  -- ¬∃x.Bathroom(x) ∨ Upstairs(p₀)
  Formula.disj
    (∼(Formula.exists_ 0 (Formula.atom "Bathroom" [.var 0])))
    (Formula.atom "Upstairs" [.pron 0])

/-- Bathroom sentence has unbound pronoun in PLA. -/
theorem bathroom_range_has_pronoun :
    0 ∈ bathroomSentence.range := by
  simp only [bathroomSentence, Formula.disj, Formula.range,
             termsPronouns]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert,
             Finset.biUnion_empty, Finset.union_empty, Term.pronouns]
  simp only [Finset.mem_union, Finset.mem_singleton]
  right; native_decide

/-- Bathroom sentence domain is nonempty despite negated existential. -/
theorem bathroom_domain_nonempty :
    (bathroomSentence.domain).Nonempty := by
  simp only [bathroomSentence, Formula.disj, Formula.domain]
  use 0
  simp only [Finset.mem_union]
  left
  exact Finset.mem_insert_self 0 _

end Semantics.Dynamic.PLA
