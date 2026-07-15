import Linglib.Semantics.Dynamic.Update
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Context change potentials

The set-transformer view of dynamic meaning ([heim-1983],
[veltman-1996]): a `CCP P` acts on information states `InfoStateOf P`
(sets of possibilities) as a whole. It is the global counterpart of the
relational `Update S` of `Update.lean`: `lift` (the relational image,
[muskens-van-benthem-visser-2011]'s strongest postcondition) and `lower`
form a round trip — `lower_lift` everywhere, `lift_lower` exactly on the
`IsDistributive` CCPs, which process elements independently. What the
set-transformer view genuinely adds is the non-distributive tests
(`CCP.guard`, `might`, `must`, `negTest`) that inspect the whole state.

## Main definitions

- `InfoStateOf P`, `CCP P`: states as sets, meanings as set
  transformers, a monoid under `CCP.seq`.
- `CCP.neg`, `disj`: Heim/Veltman negation and its derived disjunction;
  `CCP.guard` and the whole-state tests `might`, `must`, `negTest`.
- `IsEliminative`, `IsExpansive`, `IsTest`, `IsDistributive`: the basic
  classification of CCPs. N.B. `IsTest` (pass-or-`∅`, Veltman's test) is
  *not* the counterpart of the relational `Update.IsTest` (stay-put,
  DPL's test): `lift` of a relational test is an eliminative filter, not
  a pass-or-`∅` test.
- `supportOf`, `contentOf`, `updateFromSat`: satisfaction-based updates
  and the support relation.
- `lift`, `lower`: the bridge to the relational algebra.

## Main results

- `lower_lift`, `lift_lower`, `lift_isDistributive`: distributive CCPs
  are exactly the relational images.
- `lift_le_lift_iff`: `lift` reflects the pointwise order — the
  SP-characterization of update-update consequence.
- `might_not_isDistributive`: whole-state tests are genuinely beyond the
  relational fragment.
-/

namespace DynamicSemantics

/--
An InfoState is a set of possibilities.

Different theories instantiate `P` differently:
- PLA: Assignment × WitnessSeq
- DRT: Assignment
- Intensional: World × Assignment
-/
abbrev InfoStateOf (P : Type*) := Set P

/--
A Context Change Potential (CCP) is a function from states to states.

This is the semantic type for dynamic meanings.
-/
abbrev CCP (P : Type*) := InfoStateOf P → InfoStateOf P

namespace CCP

variable {P : Type*}

/-- Identity CCP: leaves state unchanged -/
def id : CCP P := λ s => s

/-- Absurd CCP: yields empty state -/
def absurd : CCP P := λ _ => ∅

/-- Sequential composition of CCPs -/
def seq (u v : CCP P) : CCP P := λ s => v (u s)

scoped infixl:70 " ;; " => seq

theorem seq_assoc (u v w : CCP P) : (u ;; v) ;; w = u ;; (v ;; w) := rfl
theorem id_seq (u : CCP P) : id ;; u = u := rfl
theorem seq_id (u : CCP P) : u ;; id = u := rfl

/-- CCPs form a monoid under sequential composition. Scoped because
`CCP P` is an abbreviation for `Set P → Set P`: a global instance would
attach `*`/`1` to a bare function type for every importer. Activate with
`open scoped DynamicSemantics.CCP`. -/
scoped instance : Monoid (CCP P) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- seq_absurd: anything followed by absurd is absurd -/
theorem seq_absurd (u : CCP P) : u ;; absurd = absurd := rfl

/--
Dynamic negation: complement within the input state.

This is the standard dynamic negation of [heim-1982], [veltman-1996]:
¬φ(s) = s \ φ(s). Worlds survive iff they do not survive φ.
Does not validate DNE on non-eliminative updates. For the whole-state
consistency test (must-not), see `negTest`.
-/
def neg (φ : CCP P) : CCP P :=
  λ s => s \ φ s

open Classical in
/-- Whole-state test: pass the state through iff it satisfies `C` — the
shared shape of `negTest`, `might`, `must`, and `impl`, the
non-distributive tests that inspect the entire input state. -/
noncomputable def guard (C : InfoStateOf P → Prop) : CCP P :=
  λ s => if C s then s else ∅

/--
Test-based negation: passes (returns input) iff φ yields ∅.

A whole-state consistency test ("must-not"), NOT [heim-1982]'s or
[veltman-1996]'s negation (that is `neg`, set difference). The two
coincide only when `φ s = ∅` or `φ s = s` — see
`Studies/Beaver2001/ABLE.lean` for the proven divergence.
-/
noncomputable def negTest (φ : CCP P) : CCP P :=
  guard (λ s => ¬ (φ s).Nonempty)

/--
Compatibility test ("might"): passes iff φ yields a nonempty result.

might(φ)(s) = s if φ(s) ≠ ∅, else ∅
-/
noncomputable def might (φ : CCP P) : CCP P :=
  guard (λ s => (φ s).Nonempty)

open Classical in
/--
Full support test ("must"): passes iff φ returns input unchanged.

must(φ)(s) = s if φ(s) = s, else ∅
-/
noncomputable def must (φ : CCP P) : CCP P :=
  guard (λ s => φ s = s)

open Classical in
/--
Dynamic implication test: passes iff output of φ is preserved by ψ.

impl(φ,ψ)(s) = s if φ(s) ⊆ ψ(φ(s)), else ∅
-/
noncomputable def impl (φ ψ : CCP P) : CCP P :=
  guard (λ s => φ s ⊆ ψ (φ s))

/--
Dynamic disjunction via De Morgan: φ ∨ ψ = ¬(¬φ ; ¬ψ).

For eliminative updates this unfolds to φ(s) ∪ ψ(s \ φ(s)): the second
disjunct is evaluated in the input updated with the negation of the
first — the local-context clause of the satisfaction literature
([beaver-2001]; [heim-1983] itself gives CCPs only for *not/and/if*).
-/
def disj (φ ψ : CCP P) : CCP P := neg (seq (neg φ) (neg ψ))

/-- Dynamic entailment: φ entails ψ iff ψ adds no information after φ. -/
def entails (φ ψ : CCP P) : Prop :=
  ∀ s : InfoStateOf P, (φ s).Nonempty → ψ (φ s) = φ s

/-- Entailment is reflexive -/
theorem entails_id (φ : CCP P) : entails φ id := by
  intro s _; rfl

end CCP

variable {P : Type*}

/--
An update is eliminative if it never adds possibilities.

This is the fundamental property of dynamic semantics:
information only grows (possibilities only decrease).
-/
def IsEliminative (u : CCP P) : Prop :=
  ∀ s, u s ⊆ s

/-- Identity is eliminative -/
theorem eliminative_id : IsEliminative (CCP.id : CCP P) :=
  λ _ => Set.Subset.rfl

/-- Sequential composition preserves eliminativity -/
theorem eliminative_seq (u v : CCP P)
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
def IsExpansive (u : CCP P) : Prop :=
  ∀ s, s ⊆ u s

/-- Identity is expansive -/
theorem expansive_id : IsExpansive (CCP.id : CCP P) :=
  λ _ => Set.Subset.rfl

/-- Sequential composition preserves expansiveness -/
theorem expansive_seq (u v : CCP P)
    (hu : IsExpansive u) (hv : IsExpansive v) :
    IsExpansive (u.seq v) := λ s _ hp =>
  hv (u s) (hu s hp)

/-- A CCP that is both eliminative and expansive is the identity on every input. -/
theorem eliminative_expansive_id (u : CCP P)
    (he : IsEliminative u) (hx : IsExpansive u) :
    ∀ s, u s = s :=
  λ s => Set.Subset.antisymm (he s) (hx s)

/-- A test either passes (returns its input) or fails (returns `∅`) —
[veltman-1996]'s tests: `might`, `must`, presupposition checks. Not the
counterpart of the relational `Update.IsTest`: lifting a relational
test gives an eliminative filter, not a pass-or-`∅` test. -/
def IsTest (u : CCP P) : Prop :=
  ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative -/
theorem test_eliminative (u : CCP P) (h : IsTest u) :
    IsEliminative u := λ s p hp => by
  cases h s with
  | inl heq => rw [heq] at hp; exact hp
  | inr hemp => rw [hemp] at hp; exact False.elim hp

open Classical in
theorem CCP.guard_isTest (C : Set P → Prop) : IsTest (CCP.guard C) := by
  intro s; simp only [CCP.guard]; split <;> simp

theorem CCP.negTest_isTest (φ : CCP P) : IsTest (CCP.negTest φ) :=
  CCP.guard_isTest _

theorem CCP.might_isTest (φ : CCP P) : IsTest (CCP.might φ) :=
  CCP.guard_isTest _

theorem CCP.must_isTest (φ : CCP P) : IsTest (CCP.must φ) :=
  CCP.guard_isTest _

theorem CCP.impl_isTest (φ ψ : CCP P) : IsTest (CCP.impl φ ψ) :=
  CCP.guard_isTest _

open Classical in
/-- Duality for the test pair: might φ = must-not (must-not φ). The
analogous identity fails for set-difference `neg` (DNE holds instead
on eliminative updates). -/
theorem CCP.might_eq_negTest_negTest (φ : CCP P) :
    CCP.might φ = CCP.negTest (CCP.negTest φ) := by
  funext s
  by_cases h : (φ s).Nonempty
  · simp [CCP.might, CCP.negTest, CCP.guard, h]
  · by_cases hs : s.Nonempty
    · simp [CCP.might, CCP.negTest, CCP.guard, h, hs]
    · simp [CCP.might, CCP.negTest, CCP.guard,
        Set.not_nonempty_iff_eq_empty.mp hs]


section GaloisContent

variable {P φ : Type*}

/--
Support relation: s supports ψ if all possibilities in s satisfy ψ.

This is the fundamental entailment relation of dynamic semantics.
-/
def supportOf (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) : Prop :=
  ∀ p ∈ s, sat p ψ

/--
Content of a formula: all possibilities satisfying it.
-/
def contentOf (sat : P → φ → Prop) (ψ : φ) : InfoStateOf P :=
  { p | sat p ψ }

/--
Galois connection: s ⊆ content ψ ↔ s supports ψ

This is the fundamental duality of dynamic semantics.
-/
theorem support_iff_subset_content (sat : P → φ → Prop) (s : InfoStateOf P) (ψ : φ) :
    supportOf sat s ψ ↔ s ⊆ contentOf sat ψ := by
  constructor
  · intro h p hp
    exact h p hp
  · intro h p hp
    exact h hp

/--
Support is downward closed: smaller states support more.
-/
theorem support_mono (sat : P → φ → Prop) (s t : InfoStateOf P) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  λ p hp => hs p (h hp)

/--
Empty state supports everything (vacuously).
-/
theorem empty_supports (sat : P → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ := λ _ hp => False.elim hp

/--
Content is antitone in entailment.
-/
theorem content_mono (sat : P → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  λ _ hp => h _ hp

end GaloisContent


/-! ### Separation (filtering) infrastructure -/

/-- Filtering a set by a predicate is monotone. This is the shared foundation
    for monotonicity of `updateFromSat`, `atom`, `pred1`, `pred2`, etc. -/
theorem sep_monotone (pred : P → Prop) :
    Monotone (λ s : Set P => { p ∈ s | pred p }) :=
  λ _ _ h _ hp => ⟨h hp.1, hp.2⟩

/-- Filtering a set by a predicate is eliminative. -/
theorem sep_eliminative (pred : P → Prop) :
    IsEliminative (λ s : Set P => { p ∈ s | pred p }) :=
  λ _ _ hp => hp.1


/--
The standard update construction: filter by satisfaction.

This is how PLA, DRT, DPL all define updates.
-/
def updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) : CCP P :=
  λ s => { p ∈ s | sat p ψ }

/-- Standard updates are eliminative -/
theorem updateFromSat_eliminative {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    IsEliminative (updateFromSat sat ψ) :=
  sep_eliminative _

/-- Standard update membership -/
theorem mem_updateFromSat {P φ : Type*} (sat : P → φ → Prop) (ψ : φ)
    (s : InfoStateOf P) (p : P) :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Update equals intersection with content -/
theorem updateFromSat_eq_inter_content {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ := by
  ext p
  simp only [mem_updateFromSat, contentOf, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Support-Update equivalence -/
theorem support_iff_update_eq {P φ : Type*} (sat : P → φ → Prop)
    (ψ : φ) (s : InfoStateOf P) :
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
def dynamicEntailsOf {P φ : Type*} (sat : P → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : InfoStateOf P, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is reflexive -/
theorem dynamicEntails_refl {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  λ _ _ hp => hp.2

/-- Dynamic entailment is transitive -/
theorem dynamicEntails_trans {P φ : Type*} (sat : P → φ → Prop)
    (ψ₁ ψ₂ ψ₃ : φ) (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ :=
  fun s p hp => h2 s p ⟨hp.1, h1 s p hp⟩


/--
`updateFromSat` is monotone in the state argument: larger input states yield
larger output states. Uses mathlib's `Monotone` (i.e., `s ≤ t → f s ≤ f t`
where `≤` on `Set` is `⊆`).
-/
theorem updateFromSat_monotone {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    Monotone (updateFromSat sat ψ) :=
  sep_monotone _


/-! ### Distributivity -/

/-- A CCP is distributive when it processes each element of the input independently:
    φ(s) = ⋃_{i∈s} φ({i}). -/
def IsDistributive (φ : CCP P) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- `updateFromSat` is always distributive: it filters per-element. -/
theorem updateFromSat_isDistributive {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    IsDistributive (updateFromSat sat ψ) := by
  intro s; ext p; simp only [updateFromSat, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hsat⟩; exact ⟨p, hp, ⟨rfl, hsat⟩⟩
  · rintro ⟨i, hi, hpi, hsat⟩; cases hpi; exact ⟨hi, hsat⟩

/-- `CCP.might` is not distributive: the whole-context test can pass while
    individual-element tests fail.

    Witness: P = Bool, φ keeps only `true`.
    `might φ {true, false} = {true, false}` (whole-context test passes),
    but per-singleton: `might φ {false} = ∅` (test fails on false-only context).
    So `false` is in the whole-context result but not the distributive union. -/
theorem might_not_isDistributive :
    ∃ (P : Type) (φ : CCP P), ¬IsDistributive (CCP.might φ) := by
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

/-- `updateFromSat` is the lifting of `test` applied to a satisfaction
relation. This connects the CCP-native `updateFromSat` to the
primary relational algebra. -/
theorem updateFromSat_eq_lift_test {P φ : Type*} (sat : P → φ → Prop) (ψ : φ) :
    updateFromSat sat ψ = lift (test (λ p => sat p ψ)) := by
  funext σ; ext p
  simp only [updateFromSat, lift, test, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp, hsat⟩; exact ⟨p, hp, rfl, hsat⟩
  · rintro ⟨i, hi, rfl, hsat⟩; exact ⟨hi, hsat⟩

end RelationalBridge

end DynamicSemantics
