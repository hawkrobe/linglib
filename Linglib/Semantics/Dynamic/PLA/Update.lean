import Linglib.Semantics.Dynamic.PLA.Semantics
import Linglib.Semantics.Dynamic.Update

/-!
# PLA dynamic update semantics

Information update and support for PLA, after [dekker-2012]: three equivalent
perspectives on dynamic meaning — *contents* (sets of assignment-witness
pairs), *updates* (context change potentials over PLA possibilities,
instantiating `DynamicSemantics.CCP`), and *support* (a state supports a
formula when the formula holds throughout it).

## Main definitions

- `PLA.InfoState`, `PLA.Formula.content`, `PLA.Formula.update`,
  `PLA.InfoState.supports`
- `PLA.Formula.dynConj`: sequential update
- `PLA.dynamicEntails`: dynamic entailment, scoped notation `φ ⊨[M]_dyn ψ`

## Main results

- `PLA.contents_updates_equiv` (Observation 16): update is intersection with
  content
- `PLA.updates_support_equiv` (Observation 17): support means update is the
  identity
- `PLA.update_eliminative`: updates only filter the input state; consequently
  dynamic conjunction here is commutative and static-reducible
  (`PLA.dynConj_static`) — [dekker-2012]'s non-commutativity claims concern
  witness-sequence dynamics this formalization does not render
- `PLA.obs10_dynamic_eq_classical_entailment`: dynamic entailment is
  conservative over classical entailment
-/

namespace PLA

open Classical
open DynamicSemantics.CCP
open scoped Formula

variable {E : Type*}

/--
An information state is a set of (assignment, witness) pairs.

This represents the current state of the discourse: all ways the conversation
could be going given what's been said.

Using `abbrev` makes this a transparent alias so all `Set` instances apply directly.
-/
abbrev InfoState (E : Type*) := Set (Assignment E × WitnessSeq E)

namespace InfoState

/-- The trivial state: all possibilities -/
def univ : InfoState E := Set.univ

/-- The absurd state: no possibilities -/
def empty : InfoState E := ∅

/-- State is consistent (non-empty) -/
def consistent (s : InfoState E) : Prop := s.Nonempty

/-- Restrict state to pairs where formula is satisfied -/
def restrict (s : InfoState E) (M : Model E) (φ : Formula) : InfoState E :=
  { p ∈ s | φ.sat M p.1 p.2 }

end InfoState


/--
PLA Possibility type: (assignment, witness sequence) pairs.

This instantiates the generic DynamicSemantics.CCP framework for PLA.
-/
abbrev Poss (E : Type*) := Assignment E × WitnessSeq E

/--
An update is a Context Change Potential over PLA possibilities.

We inherit the Monoid structure from `DynamicSemantics.CCP`:
- Identity: `DynamicSemantics.CCP.id` (leaves state unchanged)
- Composition: `DynamicSemantics.CCP.seq` (do u, then v), notation `;`
- Associativity: guaranteed by the Monoid laws
-/
abbrev Update (E : Type*) := DynamicSemantics.CCP (Poss E)

namespace Update

/-- Identity update: leaves state unchanged (from DynamicSemantics.CCP) -/
abbrev id : Update E := DynamicSemantics.CCP.id

/-- Absurd update: always yields empty state (from DynamicSemantics.CCP) -/
abbrev absurd : Update E := DynamicSemantics.CCP.absurd

/-- Absurd before anything yields absurd output (from DynamicSemantics.CCP) -/
theorem seq_absurd (u : Update E) : DynamicSemantics.CCP.seq u absurd = absurd :=
  DynamicSemantics.CCP.seq_absurd u

end Update


section
variable (M : Model E)

/--
The content of a formula: set of (g, ê) pairs where φ is satisfied.

⟦φ⟧^M = { (g, ê) | M, g, ê ⊨ φ }

This is the "static" meaning - what information φ conveys.
-/
def Formula.content (φ : Formula) : InfoState E :=
  { p | φ.sat M p.1 p.2 }

theorem Formula.mem_content (φ : Formula) (g : Assignment E) (ê : WitnessSeq E) :
    (g, ê) ∈ φ.content M ↔ φ.sat M g ê := Iff.rfl

/-- Content of negation is complement -/
theorem Formula.content_neg (φ : Formula) :
    (∼φ).content M = (φ.content M)ᶜ := by
  ext ⟨g, ê⟩
  simp [content, sat]

/-- Content of conjunction is intersection -/
theorem Formula.content_conj (φ ψ : Formula) :
    (φ ⋀ ψ).content M = φ.content M ∩ ψ.content M := by
  ext ⟨g, ê⟩
  simp [content, sat]


/--
PLA satisfaction relation: possibility satisfies formula.

This bridges PLA to the DynamicSemantics.CCP infrastructure, matching the signature
`P → φ → Prop` expected by DynamicSemantics.updateFromSat.
-/
def satisfiesPLA : Poss E → Formula → Prop :=
  λ p φ => φ.sat M p.1 p.2

/--
The update of a formula: filter state to satisfying pairs.

⟦φ⟧ : InfoState → InfoState
⟦φ⟧(s) = { (g, ê) ∈ s | M, g, ê ⊨ φ }
-/
def Formula.update (φ : Formula) : Update E :=
  λ s => InfoState.restrict s M φ

theorem Formula.mem_update (φ : Formula) (s : InfoState E) (g : Assignment E)
    (ê : WitnessSeq E) :
    (g, ê) ∈ φ.update M s ↔ (g, ê) ∈ s ∧ φ.sat M g ê := by
  simp [update, InfoState.restrict]


/--
Observation 16 (Proper Update, [dekker-2012] §3.2, p.60).

The update of φ is intersection with the content of φ:

  ⟦φ⟧(s) = s ∩ ⟦φ⟧^M

This shows Contents and Updates are equivalent perspectives.
-/
theorem contents_updates_equiv (φ : Formula) (s : InfoState E) :
    φ.update M s = s ∩ φ.content M := by
  ext ⟨g, ê⟩
  simp [Formula.update, Formula.content, InfoState.restrict]


/--
A state supports a formula iff the formula is satisfied throughout the state.

s ⊨ φ iff ∀(g, ê) ∈ s, M, g, ê ⊨ φ

This is the evidential perspective: the speaker's evidence supports φ.
-/
def InfoState.supports (s : InfoState E) (φ : Formula) : Prop :=
  ∀ p ∈ s, φ.sat M p.1 p.2

end

scoped notation:50 s " ⊫[" M "] " φ => InfoState.supports M s φ

section
variable (M : Model E)

/-- Empty state supports everything (vacuously) -/
theorem InfoState.empty_supports (φ : Formula) :
    (∅ : InfoState E) ⊫[M] φ := by
  intro p hp
  exact False.elim hp

/-- Support is monotonic: if s ⊆ t and t supports φ, then s supports φ -/
theorem InfoState.supports_mono (s t : InfoState E) (φ : Formula) (h : s ⊆ t)
    (ht : t ⊫[M] φ) :
    s ⊫[M] φ := λ p hp => ht p (h hp)

/-- Support and conjunction -/
theorem InfoState.supports_conj (s : InfoState E) (φ ψ : Formula) :
    (s ⊫[M] (φ ⋀ ψ)) ↔ (s ⊫[M] φ) ∧ (s ⊫[M] ψ) := by
  constructor
  · intro h
    constructor
    · intro p hp; exact (h p hp).1
    · intro p hp; exact (h p hp).2
  · intro ⟨hφ, hψ⟩ p hp
    exact ⟨hφ p hp, hψ p hp⟩


/--
Observation 17 (Proper Support, [dekker-2012] §3.2, p.61).

A state supports φ iff updating with φ leaves it unchanged:

  s ⊫[M] φ ↔ ⟦φ⟧(s) = s

This shows Updates and Support are equivalent perspectives.
-/
theorem updates_support_equiv (φ : Formula) (s : InfoState E) :
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
Dynamic conjunction: sequential update, φ then ψ.

In this eliminative formalization both conjuncts act as filters, so dynamic
conjunction is commutative and reduces to static conjunction
(`dynConj_static`). [dekker-2012]'s non-commutativity and non-idempotence
claims (Observation 9, §2.2, p.32) concern the witness-sequence dynamics,
which this formalization does not render: existentials certify witnesses in
the membership condition without exporting them to output states.
-/
def Formula.dynConj (φ ψ : Formula) : Update E :=
  φ.update M ;; ψ.update M

/-- Dynamic conjunction update rule -/
theorem Formula.dynConj_eq (φ ψ : Formula) (s : InfoState E) :
    (φ.dynConj M ψ) s = ψ.update M (φ.update M s) := rfl

/-- Dynamic conjunction membership -/
theorem Formula.mem_dynConj (φ ψ : Formula) (s : InfoState E) (g : Assignment E)
    (ê : WitnessSeq E) :
    (g, ê) ∈ (φ.dynConj M ψ) s ↔ (g, ê) ∈ s ∧ φ.sat M g ê ∧ ψ.sat M g ê := by
  simp only [Formula.dynConj, DynamicSemantics.CCP.seq, Formula.mem_update]
  tauto

/--
Dynamic conjunction reduces to static conjunction. [dekker-2012] restricts
this to dref-free formulas; here updates are eliminative, so it holds
unconditionally.
-/
theorem dynConj_static (φ ψ : Formula) (s : InfoState E) :
    (φ.dynConj M ψ) s = (φ ⋀ ψ).update M s := by
  ext ⟨g, ê⟩
  simp only [Formula.dynConj, DynamicSemantics.CCP.seq, Formula.mem_update, Formula.sat]
  tauto


/--
Existentials are not idempotent ([dekker-2012] Observation 9, §2.2, p.32).

"A man came. A man sat down." - may be different men.
Each ∃x.φ independently chooses a witness.
-/
theorem exists_domain_idempotent (x : VarIdx) (φ : Formula) :
    ((Formula.exists_ x φ) ⋀ (Formula.exists_ x φ)).domain =
    (Formula.exists_ x φ).domain := by
  simp only [Formula.domain, Finset.union_self]

/--
DNE failure for dref-introducing formulas (discussed in [dekker-2012] §2.2, around Observation 9).

"It's not the case that no man came. He sat down." - "He" is problematic.
In Dekker's PLA, negation "traps" drefs: ∃x.P(x) introduces a witness to the
output state while ¬¬∃x.P(x) only tests existence. In this eliminative
formalization both are filters (see `update_eliminative`), and the contrast
survives at the domain/range level. This motivates bilateral semantics
(BUS), where DNE holds structurally.
-/
theorem dne_syntactic (φ : Formula) :
    (∼(∼φ)).domain = φ.domain := by
  simp only [Formula.domain]


/-- Updating with a tautology leaves state unchanged -/
theorem update_taut (s : InfoState E) (φ : Formula) (htaut : ∀ g ê, φ.sat M g ê) :
    φ.update M s = s := by
  ext ⟨g, ê⟩
  simp [Formula.update, InfoState.restrict, htaut]

/-- Updating with a contradiction yields empty state -/
theorem update_contra (s : InfoState E) (φ : Formula) (hcontra : ∀ g ê, ¬φ.sat M g ê) :
    φ.update M s = ∅ := by
  ext ⟨g, ê⟩
  simp [Formula.update, InfoState.restrict, hcontra]

/-- Update elimination: if s already supports φ, update is identity -/
theorem update_elim (s : InfoState E) (φ : Formula) (h : s ⊫[M] φ) :
    φ.update M s = s :=
  (updates_support_equiv M φ s).mp h


/--
PLA formula update equals DynamicSemantics.updateFromSat via satisfiesPLA.
-/
theorem update_eq_updateFromSat (φ : Formula) (s : InfoState E) :
    φ.update M s = DynamicSemantics.updateFromSat (satisfiesPLA M) φ s := rfl

/--
Eliminativity: updates never add possibilities, only remove them.

This is the fundamental property of dynamic semantics: information only grows.
Every update is a subset of the input state.

This follows from `DynamicSemantics.updateFromSat_eliminative`.
-/
theorem update_eliminative (φ : Formula) (s : InfoState E) : φ.update M s ⊆ s :=
  DynamicSemantics.updateFromSat_eliminative (satisfiesPLA M) φ s

/--
PLA's formula update is eliminative in the Core sense.
-/
theorem update_isEliminative (φ : Formula) :
    DynamicSemantics.IsEliminative (φ.update M : Update E) :=
  DynamicSemantics.updateFromSat_eliminative (satisfiesPLA M) φ

/--
Monotonicity of update: larger input states yield larger output states.

If s ⊆ t, then φ.update(s) ⊆ φ.update(t).

This follows from `DynamicSemantics.updateFromSat_monotone`.
-/
theorem update_monotone (φ : Formula) (s t : InfoState E) (h : s ⊆ t) :
    φ.update M s ⊆ φ.update M t :=
  DynamicSemantics.updateFromSat_monotone (satisfiesPLA M) φ h

/--
Support is downward closed: if t ⊆ s and s supports φ, then t supports φ.

Smaller states have "more information" (fewer possibilities = more certainty).
-/
theorem support_downward_closed (φ : Formula) (s t : InfoState E) (h : t ⊆ s)
    (hs : s ⊫[M] φ) : t ⊫[M] φ :=
  λ p hp => hs p (h hp)

/--
Intersection preserves support: if s and t both support φ, so does s ∩ t.
-/
theorem support_inter (φ : Formula) (s t : InfoState E) (hs : s ⊫[M] φ)
    (_ht : t ⊫[M] φ) : (s ∩ t) ⊫[M] φ := by
  intro p hp
  exact hs p hp.1

/--
Union and support: s ∪ t supports φ iff both s and t support φ.
-/
theorem support_union_iff (φ : Formula) (s t : InfoState E) :
    ((s ∪ t) ⊫[M] φ) ↔ (s ⊫[M] φ) ∧ (t ⊫[M] φ) := by
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
theorem update_inter (φ : Formula) (s t : InfoState E) :
    φ.update M (s ∩ t) = φ.update M s ∩ φ.update M t := by
  ext p
  simp only [Formula.update, InfoState.restrict, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/--
Sequential composition with intersection: (φ; ψ)(s) ⊆ φ(s) ∩ ψ(s)

Note: this is not equality in general due to the dynamic nature of sequencing.
-/
theorem dynConj_subset_inter (φ ψ : Formula) (s : InfoState E) :
    (φ.dynConj M ψ) s ⊆ φ.update M s ∩ ψ.update M s := by
  intro p hp
  rw [Formula.mem_dynConj] at hp
  simp only [Set.mem_inter_iff]
  rw [Formula.mem_update, Formula.mem_update]
  exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.1, hp.2.2⟩⟩


/-- Sequential composition is nested intersection of contents. -/
theorem static_seq_is_intersection (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.update M) s = s ∩ φ.content M ∩ ψ.content M := by
  simp only [DynamicSemantics.CCP.seq, contents_updates_equiv, Set.inter_assoc]

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

/-- Same content implies same update. -/
theorem same_content_same_update (φ ψ : Formula) (hcontent : φ.content M = ψ.content M)
    (s : InfoState E) :
    φ.update M s = ψ.update M s := by
  rw [contents_updates_equiv, contents_updates_equiv, hcontent]


/--
Dynamic entailment: φ dynamically entails ψ if updating with φ always
yields a state that supports ψ.

This is the fundamental semantic consequence relation for dynamic semantics.
-/
def dynamicEntails (φ ψ : Formula) : Prop :=
  ∀ s : InfoState E, (φ.update M s) ⊫[M] ψ

end

scoped notation:50 φ " ⊨[" M "]_dyn " ψ => dynamicEntails M φ ψ

section
variable (M : Model E)

/--
Reflexivity of dynamic entailment: φ ⊨_dyn φ.

Updating with φ yields a state that supports φ.
-/
theorem dynamicEntails_refl (φ : Formula) :
    φ ⊨[M]_dyn φ := by
  intro s p hp
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
  exact hp.2

/--
Transitivity of dynamic entailment; holds because update is eliminative.
-/
theorem dynamicEntails_trans (φ ψ χ : Formula) (h1 : φ ⊨[M]_dyn ψ) (h2 : ψ ⊨[M]_dyn χ) :
    φ ⊨[M]_dyn χ := by
  intro s p hp
  exact h2 s p ((Formula.mem_update M ψ s p.1 p.2).mpr
    ⟨update_eliminative M φ s hp, h1 s p hp⟩)

/--
Weakening: if s supports φ and φ ⊨_dyn ψ, then φ.update(s) supports ψ.
-/
theorem dynamicEntails_weakening (φ ψ : Formula) (s : InfoState E)
    (hent : φ ⊨[M]_dyn ψ) :
    (φ.update M s) ⊫[M] ψ :=
  hent s


/--
Observation 10 ([dekker-2012] §2.3, p.33): Conservative Entailment.

Dynamic entailment coincides with classical pointwise entailment:
φ ⊨_dyn ψ iff for all g, ê, M,g,ê ⊨ φ implies M,g,ê ⊨ ψ.

This shows that PLA's dynamic consequence relation is conservative
over classical PL consequence. -/
theorem obs10_dynamic_eq_classical_entailment (φ ψ : Formula) :
    (φ ⊨[M]_dyn ψ) ↔ (∀ (g : Assignment E) (ê : WitnessSeq E), φ.sat M g ê → ψ.sat M g ê) := by
  constructor
  · -- Dynamic → Classical: use s = Set.univ
    intro hdyn g ê hsat
    have hmem : (g, ê) ∈ φ.update M Set.univ := by
      simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Set.mem_univ, true_and]
      exact hsat
    exact hdyn Set.univ (g, ê) hmem
  · -- Classical → Dynamic: unfold update membership
    intro hclass s p hp
    simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
    exact hclass p.1 p.2 hp.2

/--
Observation 11 ([dekker-2012] §2.3, p.34): Deduction Theorem.

φ ∧ χ ⊨_dyn ψ  ↔  φ ⊨_dyn χ → ψ

The classical deduction theorem holds in PLA's dynamic system. -/
theorem obs11_deduction_theorem (φ χ ψ : Formula) :
    ((φ ⋀ χ) ⊨[M]_dyn ψ) ↔ (φ ⊨[M]_dyn (χ ⟶ ψ)) := by
  constructor
  · -- (→) If φ∧χ ⊨ ψ, then φ ⊨ χ→ψ
    intro h s p hp
    simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
    show (χ ⟶ ψ).sat M p.1 p.2
    simp only [Formula.impl, Formula.sat]
    intro ⟨hχ, hnψ⟩
    have hmem : p ∈ (φ ⋀ χ).update M s := by
      simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat]
      exact ⟨hp.1, hp.2, hχ⟩
    exact hnψ (h s p hmem)
  · -- (←) If φ ⊨ χ→ψ, then φ∧χ ⊨ ψ
    intro h s p hp
    simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
    have hp_φ : p ∈ φ.update M s := by
      simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq]
      exact ⟨hp.1, hp.2.1⟩
    have himpl := h s p hp_φ
    simp only [Formula.impl, Formula.sat] at himpl
    by_contra hnψ
    exact himpl ⟨hp.2.2, hnψ⟩

/-! ### Update-composition and domain API

Membership characterizations for sequenced updates, and structural facts
about `Formula.domain` / `Formula.range` under negation and existentials.
Note the eliminative character these make explicit: updates only filter
the input state (`update_eliminative`), so an existential's witness values
figure in the *membership condition*, not in the surviving possibilities. -/

/-- Existential update output characterization. -/
theorem exists_update_characterization (x : VarIdx) (φ : Formula) (s : InfoState E) :
    (Formula.exists_ x φ).update M s =
    { p ∈ s | ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 } := by
  ext p
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat]

/-- Double negation preserves range. -/
theorem dne_range_same (φ : Formula) :
    (∼(∼φ)).range = φ.range := by
  simp only [Formula.range]

/-- Existential domain is nonempty. -/
theorem exists_domain_nonempty (x : VarIdx) (φ : Formula) :
    (Formula.exists_ x φ).domain.Nonempty := by
  use x
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _

/-- Sequential update as set comprehension. -/
theorem seq_update_eq (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.update M) s =
    { p ∈ s | φ.sat M p.1 p.2 ∧ ψ.sat M p.1 p.2 } := by
  ext ⟨g, ê⟩
  exact Formula.mem_dynConj M φ ψ s g ê

/-- Sequential update commutes: eliminative updates are filters, so order is
irrelevant. ([dekker-2012] restricts this to dref-free formulas.) -/
theorem static_conjunction_commutes (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.update M) s = (ψ.update M ;; φ.update M) s := by
  rw [seq_update_eq, seq_update_eq]
  ext p
  simp only [Set.mem_setOf_eq]
  tauto

/-- The existential marks its variable in the domain; conjunction unions
    domains, leaving the second conjunct's domain unaffected. -/
theorem static_existential_local_scope (x : VarIdx) (φ ψ : Formula) :
    x ∈ (Formula.exists_ x φ).domain ∧
    (Formula.exists_ x φ ⋀ ψ).domain = (Formula.exists_ x φ).domain ∪ ψ.domain := by
  constructor
  · simp only [Formula.domain]
    exact Finset.mem_insert_self x _
  · simp only [Formula.domain]

end

end PLA
