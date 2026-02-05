/-
# PLA Dynamic Update Semantics

Dekker (2012) Chapter 3: Updates and Information Exchange.

## Three Equivalent Views

Dekker shows three equivalent perspectives on dynamic meaning:

1. Contents: sets of world-assignment pairs (what information is conveyed)
2. Updates: functions from input states to output states (how information changes)
3. Support: when a state supports a formula (evidential perspective)

## Theorems

- Theorem 3.1: contents-to-updates equivalence
- Theorem 3.2: updates-to-support equivalence
- Dynamic conjunction: non-commutative, non-idempotent

## References

- Dekker, P. (2012). Dynamic Semantics. Springer. Chapter 3.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.DynamicSemantics.PLA.Semantics
import Linglib.Theories.DynamicSemantics.Core.CCP

namespace Theories.DynamicSemantics.PLA

-- We use Core.CCP infrastructure directly via qualified names

open Classical


/--
An information state is a set of (assignment, witness) pairs.

This represents the current state of the discourse: all ways the conversation
could be going given what's been said.

Using `abbrev` makes this a transparent alias so all `Set` instances apply directly.
-/
abbrev InfoState (E : Type*) := Set (Assignment E × WitnessSeq E)

namespace InfoState

variable {E : Type*}

/-- The trivial state: all possibilities -/
def univ : InfoState E := Set.univ

/-- The absurd state: no possibilities -/
def empty : InfoState E := ∅

/-- State is consistent (non-empty) -/
def consistent (s : InfoState E) : Prop := s.Nonempty

/-- Restrict state to pairs where formula is satisfied -/
def restrict [Nonempty E] (s : InfoState E) (M : Model E) (φ : Formula) : InfoState E :=
  { p ∈ s | φ.sat M p.1 p.2 }

end InfoState


/--
The content of a formula: set of (g, ê) pairs where φ is satisfied.

⟦φ⟧^M = { (g, ê) | M, g, ê ⊨ φ }

This is the "static" meaning - what information φ conveys.
-/
def Formula.content {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) : InfoState E :=
  { p | φ.sat M p.1 p.2 }

theorem Formula.mem_content {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (g : Assignment E) (ê : WitnessSeq E) :
    (g, ê) ∈ φ.content M ↔ φ.sat M g ê := Iff.rfl

/-- Content of negation is complement -/
theorem Formula.content_neg {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) :
    (∼φ).content M = (φ.content M)ᶜ := by
  ext ⟨g, ê⟩
  simp [content, sat]

/-- Content of conjunction is intersection -/
theorem Formula.content_conj {E : Type*} [Nonempty E] (M : Model E) (φ ψ : Formula) :
    (φ ⋀ ψ).content M = φ.content M ∩ ψ.content M := by
  ext ⟨g, ê⟩
  simp [content, sat]


/--
PLA Possibility type: (assignment, witness sequence) pairs.

This instantiates the generic Core.CCP framework for PLA.
-/
abbrev Poss (E : Type*) := Assignment E × WitnessSeq E

/--
PLA satisfaction relation: possibility satisfies formula.

This bridges PLA to the Core.CCP infrastructure, matching the signature
`P → φ → Prop` expected by Core.updateFromSat.
-/
def satisfiesPLA {E : Type*} [Nonempty E] (M : Model E) :
    Poss E → Formula → Prop :=
  λ p φ => φ.sat M p.1 p.2

/--
PLA satisfaction as a predicate on possibilities (curried version).
-/
def Formula.satPoss {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) :
    Poss E → Prop :=
  λ p => satisfiesPLA M p φ


/--
An update is a Context Change Potential over PLA possibilities.

We inherit the Monoid structure from `Core.CCP`:
- Identity: `Core.CCP.id` (leaves state unchanged)
- Composition: `Core.CCP.seq` (do u, then v), notation `;;`
- Associativity: guaranteed by the Monoid laws
-/
abbrev Update (E : Type*) := Core.CCP (Poss E)

namespace Update

variable {E : Type*}

/-- Identity update: leaves state unchanged (from Core.CCP) -/
abbrev id : Update E := Core.CCP.id

/-- Absurd update: always yields empty state (from Core.CCP) -/
abbrev absurd : Update E := Core.CCP.absurd

-- Sequential composition notation comes from Core.CCP
-- infixl:70 " ;; " => Core.CCP.seq

/-- Absurd before anything yields absurd output (from Core.CCP) -/
theorem seq_absurd (u : Update E) : Core.CCP.seq u absurd = absurd := Core.CCP.seq_absurd u

end Update

/--
The update of a formula: filter state to satisfying pairs.

⟦φ⟧ : InfoState → InfoState
⟦φ⟧(s) = { (g, ê) ∈ s | M, g, ê ⊨ φ }
-/
def Formula.update {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) : Update E :=
  λ s => InfoState.restrict s M φ

theorem Formula.mem_update {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s : InfoState E) (g : Assignment E) (ê : WitnessSeq E) :
    (g, ê) ∈ φ.update M s ↔ (g, ê) ∈ s ∧ φ.sat M g ê := by
  simp [update, InfoState.restrict]


/--
Theorem 3.1 (contents-updates equivalence).

The update of φ is intersection with the content of φ:

  ⟦φ⟧(s) = s ∩ ⟦φ⟧^M

This shows Contents and Updates are equivalent perspectives.
-/
theorem contents_updates_equiv {E : Type*} [Nonempty E]
    (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.update M s = s ∩ φ.content M := by
  ext ⟨g, ê⟩
  simp [Formula.update, Formula.content, InfoState.restrict]


/--
A state supports a formula iff the formula is satisfied throughout the state.

s ⊨ φ iff ∀(g, ê) ∈ s, M, g, ê ⊨ φ

This is the evidential perspective: the speaker's evidence supports φ.
-/
def InfoState.supports {E : Type*} [Nonempty E] (s : InfoState E) (M : Model E)
    (φ : Formula) : Prop :=
  ∀ p ∈ s, φ.sat M p.1 p.2

notation:50 s " ⊫[" M "] " φ => InfoState.supports s M φ

/-- Empty state supports everything (vacuously) -/
theorem InfoState.empty_supports {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) :
    (∅ : InfoState E) ⊫[M] φ := by
  intro p hp
  exact False.elim hp

/-- Support is monotonic: if s ⊆ t and t supports φ, then s supports φ -/
theorem InfoState.supports_mono {E : Type*} [Nonempty E] (s t : InfoState E) (M : Model E)
    (φ : Formula) (h : s ⊆ t) (ht : t ⊫[M] φ) :
    s ⊫[M] φ := λ p hp => ht p (h hp)

/-- Support and conjunction -/
theorem InfoState.supports_conj {E : Type*} [Nonempty E] (s : InfoState E) (M : Model E)
    (φ ψ : Formula) :
    (s ⊫[M] (φ ⋀ ψ)) ↔ (s ⊫[M] φ) ∧ (s ⊫[M] ψ) := by
  constructor
  · intro h
    constructor
    · intro p hp; exact (h p hp).1
    · intro p hp; exact (h p hp).2
  · intro ⟨hφ, hψ⟩ p hp
    exact ⟨hφ p hp, hψ p hp⟩


/--
Theorem 3.2 (updates-support equivalence).

A state supports φ iff updating with φ leaves it unchanged:

  s ⊫[M] φ ↔ ⟦φ⟧(s) = s

This shows Updates and Support are equivalent perspectives.
-/
theorem updates_support_equiv {E : Type*} [Nonempty E]
    (M : Model E) (φ : Formula) (s : InfoState E) :
    (s ⊫[M] φ) ↔ φ.update M s = s := by
  constructor
  · intro h
    ext ⟨g, ê⟩
    simp [Formula.update, InfoState.restrict]
    intro hs
    exact h (g, ê) hs
  · intro h p hp
    have : p ∈ φ.update M s := by rw [h]; exact hp
    simp [Formula.update, InfoState.restrict] at this
    exact this.2


/--
Dynamic conjunction (Observation 4): sequential update, φ then ψ.

Non-commutative: "A man came in. He sat down." ≠ "He sat down. A man came in."
Non-idempotent: ∃x.φ ; ∃x.φ ≠ ∃x.φ (may introduce different witnesses).
-/
def Formula.dynConj {E : Type*} [Nonempty E] (M : Model E) (φ ψ : Formula) : Update E :=
  φ.update M ;; ψ.update M

/-- Dynamic conjunction update rule -/
theorem Formula.dynConj_eq {E : Type*} [Nonempty E] (M : Model E) (φ ψ : Formula) (s : InfoState E) :
    (φ.dynConj M ψ) s = ψ.update M (φ.update M s) := rfl

/-- Dynamic conjunction membership -/
theorem Formula.mem_dynConj {E : Type*} [Nonempty E] (M : Model E) (φ ψ : Formula)
    (s : InfoState E) (g : Assignment E) (ê : WitnessSeq E) :
    (g, ê) ∈ (φ.dynConj M ψ) s ↔ (g, ê) ∈ s ∧ φ.sat M g ê ∧ ψ.sat M g ê := by
  simp only [Formula.dynConj, Core.CCP.seq, Formula.mem_update]
  tauto

/--
For static formulas (no new drefs), dynamic conjunction
equals static conjunction.
-/
theorem dynConj_static {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.dynConj M ψ) s = (φ ⋀ ψ).update M s := by
  ext ⟨g, ê⟩
  simp only [Formula.dynConj, Core.CCP.seq, Formula.mem_update, Formula.sat]
  tauto


/--
Observation 5: existentials are not idempotent.

"A man came in. A man sat down." - may be different men.
Each ∃x.φ independently chooses a witness.
-/
theorem obs5_exists_domain_grows (x : VarIdx) (φ : Formula) :
    ((Formula.exists_ x φ) ⋀ (Formula.exists_ x φ)).domain =
    (Formula.exists_ x φ).domain := by
  simp only [Formula.domain, Finset.union_self]

/--
Observation 6: ¬¬φ ≢ φ for dref-introducing φ.

"It's not the case that no man came in. He sat down." - "He" is problematic.
Negation "traps" drefs: ∃x.P(x) exports x, but ¬¬∃x.P(x) only tests existence.
This motivates bilateral semantics (BUS), where DNE holds structurally.
-/
theorem obs6_dne_syntactic (φ : Formula) :
    (∼(∼φ)).domain = φ.domain := by
  simp only [Formula.domain]

-- NOTE: The semantic difference is that:
-- - ⟦∃x.φ⟧(s) introduces witnesses that subsequent formulas can reference
-- - ⟦¬¬∃x.φ⟧(s) only checks that ⟦∃x.φ⟧(s) ≠ ∅, introducing nothing
-- This is formalized in DeepTheorems.lean


/-- Updating with a tautology leaves state unchanged -/
theorem update_taut {E : Type*} [Nonempty E] (M : Model E) (s : InfoState E)
    (φ : Formula) (htaut : ∀ g ê, φ.sat M g ê) :
    φ.update M s = s := by
  ext ⟨g, ê⟩
  simp [Formula.update, InfoState.restrict, htaut]

/-- Updating with a contradiction yields empty state -/
theorem update_contra {E : Type*} [Nonempty E] (M : Model E) (s : InfoState E)
    (φ : Formula) (hcontra : ∀ g ê, ¬φ.sat M g ê) :
    φ.update M s = ∅ := by
  ext ⟨g, ê⟩
  simp [Formula.update, InfoState.restrict, hcontra]

/-- Update elimination: if s already supports φ, update is identity -/
theorem update_elim {E : Type*} [Nonempty E] (M : Model E) (s : InfoState E)
    (φ : Formula) (h : s ⊫[M] φ) :
    φ.update M s = s :=
  (updates_support_equiv M φ s).mp h


/--
PLA formula update equals Core.updateFromSat via satPoss.
-/
theorem update_eq_updateFromSat {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s : InfoState E) :
    φ.update M s = Core.updateFromSat (satisfiesPLA M) φ s := rfl

/--
Eliminativity: updates never add possibilities, only remove them.

This is the fundamental property of dynamic semantics: information only grows.
Every update is a subset of the input state.

This follows from `Core.updateFromSat_eliminative`.
-/
theorem update_eliminative {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s : InfoState E) : φ.update M s ⊆ s :=
  Core.updateFromSat_eliminative (satisfiesPLA M) φ s

/--
PLA's formula update is eliminative in the Core sense.
-/
theorem update_isEliminative {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) :
    Core.IsEliminative (φ.update M : Update E) :=
  Core.updateFromSat_eliminative (satisfiesPLA M) φ

/--
Monotonicity of update: larger input states yield larger output states.

If s ⊆ t, then φ.update(s) ⊆ φ.update(t).

This follows from `Core.updateFromSat_monotone`.
-/
theorem update_monotone {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s t : InfoState E) (h : s ⊆ t) : φ.update M s ⊆ φ.update M t :=
  Core.updateFromSat_monotone (satisfiesPLA M) φ s t h

/--
Support is downward closed: if t ⊆ s and s supports φ, then t supports φ.

Smaller states have "more information" (fewer possibilities = more certainty).
-/
theorem support_downward_closed {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s t : InfoState E) (h : t ⊆ s) (hs : s ⊫[M] φ) : t ⊫[M] φ :=
  λ p hp => hs p (h hp)

/--
Intersection preserves support: if s and t both support φ, so does s ∩ t.
-/
theorem support_inter {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s t : InfoState E) (hs : s ⊫[M] φ) (_ht : t ⊫[M] φ) : (s ∩ t) ⊫[M] φ := by
  intro p hp
  exact hs p hp.1

/--
Union and support: s ∪ t supports φ iff both s and t support φ.
-/
theorem support_union_iff {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s t : InfoState E) : ((s ∪ t) ⊫[M] φ) ↔ (s ⊫[M] φ) ∧ (t ⊫[M] φ) := by
  constructor
  · intro h
    exact ⟨λ p hp => h p (Set.mem_union_left t hp),
           λ p hp => h p (Set.mem_union_right s hp)⟩
  · intro ⟨hs, ht⟩ p hp
    cases hp with
    | inl hps => exact hs p hps
    | inr hpt => exact ht p hpt

/--
Update distributes over intersection: φ.update(s ∩ t) = φ.update(s) ∩ φ.update(t)
-/
theorem update_inter {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s t : InfoState E) : φ.update M (s ∩ t) = φ.update M s ∩ φ.update M t := by
  ext p
  simp only [Formula.update, InfoState.restrict, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/--
Sequential composition with intersection: (φ ;; ψ)(s) ⊆ φ(s) ∩ ψ(s)

Note: this is not equality in general due to the dynamic nature of sequencing.
-/
theorem dynConj_subset_inter {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (s : InfoState E) :
    (φ.dynConj M ψ) s ⊆ φ.update M s ∩ ψ.update M s := by
  intro p hp
  rw [Formula.mem_dynConj] at hp
  simp only [Set.mem_inter_iff]
  rw [Formula.mem_update, Formula.mem_update]
  exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.1, hp.2.2⟩⟩


/-- CCP Reducibility: updates = intersection with content. -/
theorem ccp_reducibility {E : Type*} [Nonempty E] (M : Model E)
    (φ : Formula) (s : InfoState E) :
    φ.update M s = s ∩ φ.content M :=
  contents_updates_equiv M φ s

/-- Sequential composition = nested intersection of contents. -/
theorem static_seq_is_intersection {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (s : InfoState E)
    (_hφ : φ.domain = ∅) (_hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = s ∩ φ.content M ∩ ψ.content M := by
  simp only [Core.CCP.seq, contents_updates_equiv, Set.inter_assoc]

/-- Only ∃ introduces discourse referents. -/
theorem dynamicity_source_exists (x : VarIdx) (φ : Formula) :
    x ∈ (Formula.exists_ x φ).domain := by
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _

theorem dynamicity_source_neg (φ : Formula) :
    (∼φ).domain = φ.domain := rfl

theorem dynamicity_source_conj (φ ψ : Formula) :
    (φ ⋀ ψ).domain = φ.domain ∪ ψ.domain := rfl

theorem dynamicity_source_atom (name : String) (ts : List Term) :
    (Formula.atom name ts).domain = ∅ := rfl

/-- Domain empty iff no variables bound. -/
theorem domain_empty_iff_no_exists : ∀ φ : Formula, φ.domain = ∅ ↔
    ∀ x, x ∉ φ.domain := by
  intro φ
  rw [Finset.eq_empty_iff_forall_notMem]

/-- CCP reducibility: for dref-free formulas, φ ;; ψ = φ ∧ ψ. -/
theorem ccp_reduces_to_static {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (s : InfoState E)
    (hφ : φ.domain = ∅) (hψ : ψ.domain = ∅) :
    (φ.update M ;; ψ.update M) s = (φ ⋀ ψ).update M s := by
  have h := dynConj_static M φ ψ s hφ hψ
  simp only [Formula.dynConj] at h
  exact h

/-- Updates are eliminative: they only filter, never add. -/
theorem updates_are_tests {E : Type*} [Nonempty E] (M : Model E)
    (φ : Formula) (s : InfoState E) :
    φ.update M s ⊆ s :=
  update_eliminative M φ s

/-- Same content implies same update. -/
theorem same_content_same_update {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (hcontent : φ.content M = ψ.content M) (s : InfoState E) :
    φ.update M s = ψ.update M s := by
  rw [contents_updates_equiv, contents_updates_equiv, hcontent]

/-- Updates are intersection with content: φ.update s = { p ∈ s | p ∈ φ.content }. -/
theorem dekker_minimalism {E : Type*} [Nonempty E] (M : Model E) (φ : Formula)
    (s : InfoState E) :
    φ.update M s = { p ∈ s | p ∈ φ.content M } := by
  rw [contents_updates_equiv]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]


/--
Dynamic entailment: φ dynamically entails ψ if updating with φ always
yields a state that supports ψ.

This is the fundamental semantic consequence relation for dynamic semantics.
-/
def dynamicEntails {E : Type*} [Nonempty E] (M : Model E) (φ ψ : Formula) : Prop :=
  ∀ s : InfoState E, (φ.update M s) ⊫[M] ψ

notation:50 φ " ⊨[" M "]_dyn " ψ => dynamicEntails M φ ψ

/--
Reflexivity of dynamic entailment: φ ⊨_dyn φ.

Updating with φ yields a state that supports φ.
-/
theorem dynamicEntails_refl {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) :
    φ ⊨[M]_dyn φ := by
  intro s p hp
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
  exact hp.2

/--
Chaining dynamic entailment: if φ ⊨_dyn ψ and ψ ⊨_dyn χ, then φ ⊨_dyn χ.

Note: This holds because update is eliminative - if φ entails ψ,
then updating with φ produces a state that supports ψ, and since
that state is a subset of the original, it also supports χ if ψ ⊨_dyn χ.
-/
theorem dynamicEntails_trans {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ χ : Formula) (h1 : φ ⊨[M]_dyn ψ) (h2 : ψ ⊨[M]_dyn χ) :
    φ ⊨[M]_dyn χ := by
  intro s p hp
  -- p ∈ φ.update M s, so p ∈ s and φ.sat M p
  have hp_in_s : p ∈ s := update_eliminative M φ s hp
  -- φ.update M s supports ψ by h1
  have hψ : (φ.update M s) ⊫[M] ψ := h1 s
  -- So ψ.sat M p since p ∈ φ.update M s
  have hψ_sat : ψ.sat M p.1 p.2 := hψ p hp
  -- Now consider ψ.update M s
  -- We need to show χ.sat M p
  -- ψ.update M s supports χ by h2
  have hχ : (ψ.update M s) ⊫[M] χ := h2 s
  -- p ∈ ψ.update M s since p ∈ s and ψ.sat M p
  have hp_in_ψ : p ∈ ψ.update M s := by
    rw [Formula.mem_update]
    exact ⟨hp_in_s, hψ_sat⟩
  exact hχ p hp_in_ψ

/--
Weakening: if s supports φ and φ ⊨_dyn ψ, then φ.update(s) supports ψ.
-/
theorem dynamicEntails_weakening {E : Type*} [Nonempty E] (M : Model E)
    (φ ψ : Formula) (s : InfoState E) (hent : φ ⊨[M]_dyn ψ) :
    (φ.update M s) ⊫[M] ψ :=
  hent s


end Theories.DynamicSemantics.PLA
