module

public import Linglib.Core.ModelTheory.Atom
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Factors of relational structures

A `k`-factor is a connected structure on at most `k` elements, presented by a set of atoms on
`Fin n`. It occurs in a structure when some assignment realizes its atoms there, that is, when
its canonical structure maps homomorphically into the structure. Homomorphisms are the weak ones
of mathlib, so a factor may leave a relation or a label unsaid, and a factor occurring in a
structure occurs in every structure it maps into. Among the members of a family of structures, a
set is strictly `k`-local when a set of permitted `k`-factors cuts it out. Over words ordered by
successor these are the strictly local stringsets, and over words ordered by precedence the
strictly piecewise ones.

## Main definitions

* `FirstOrder.Language.Atom.gaifman`: the Gaifman graph of a set of atoms.
* `FirstOrder.Language.Factor`: connected sets of atoms on at most `k` variables.
* `FirstOrder.Language.Factor.Occurs`, `FirstOrder.Language.factors`: occurrence, and the
  `k`-factors of a structure.
* `FirstOrder.Language.IsStrictlyLocal`, `FirstOrder.Language.IsLocallyTestable`: the strictly
  local and the locally testable sets of members of a family of structures.

## Main statements

* `FirstOrder.Language.factors_mono`: a homomorphism carries the factors of its domain to
  factors of its codomain.
* `FirstOrder.Language.isStrictlyLocal_iff`: a set is strictly local exactly when it contains
  every member whose factors all occur in its members.
* `FirstOrder.Language.IsStrictlyLocal.mem_of_factors_subset_union`: strictly local sets are
  closed under any operation that adds no factor.

## References

* [rogers-lambert-2019]
-/

@[expose] public section

universe u v w x

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- The Gaifman graph of a set of atoms joins two distinct variables that an atom mentions
together. -/
def Atom.gaifman {α : Type w} (T : Set (L.Atom α)) : SimpleGraph α :=
  .fromRel fun x y ↦ ∃ a ∈ T, x ∈ Set.range a.args ∧ y ∈ Set.range a.args

variable (L) in
/-- A `k`-factor is a connected set of atoms on at most `k` variables, presenting a connected
structure on at most `k` elements. -/
structure Factor (k : ℕ) where
  /-- The number of variables. -/
  {n : ℕ}
  le : n ≤ k
  /-- The atoms. -/
  atoms : Set (L.Atom (Fin n))
  preconnected : (Atom.gaifman atoms).Preconnected

namespace Factor

variable {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N] {f : L.Factor k}

variable (M) in
/-- A factor occurs in a structure when some assignment realizes its atoms there. -/
def Occurs (f : L.Factor k) : Prop :=
  (Atom.realizers M f.atoms).Nonempty

/-- A factor occurs exactly when its canonical structure maps homomorphically into the
structure. -/
theorem occurs_iff_nonempty_hom [L.IsRelational] :
    f.Occurs M ↔ Nonempty (Atom.Canonical f.atoms →[L] M) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨(Atom.Canonical.homEquiv _).symm ⟨v, hv⟩⟩,
    fun ⟨φ⟩ ↦ ⟨_, (Atom.Canonical.homEquiv _ φ).2⟩⟩

/-- A homomorphism carries an occurrence of a factor to an occurrence. -/
theorem Occurs.hom (φ : M →[L] N) : f.Occurs M → f.Occurs N :=
  fun ⟨v, hv⟩ ↦ ⟨φ ∘ v, Atom.comp_mem_realizers φ hv⟩

end Factor

variable (L) in
/-- The `k`-factors of a structure are the factors occurring in it. -/
def factors (k : ℕ) (M : Type w) [L.Structure M] : Set (L.Factor k) :=
  {f | f.Occurs M}

@[simp] theorem mem_factors {k : ℕ} {M : Type w} [L.Structure M] {f : L.Factor k} :
    f ∈ L.factors k M ↔ f.Occurs M :=
  .rfl

/-- A homomorphism carries the factors of its domain to factors of its codomain. -/
theorem factors_mono {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N]
    (φ : M →[L] N) : L.factors k M ⊆ L.factors k N :=
  fun _ ↦ Factor.Occurs.hom φ

/-! ### Strictly local sets -/

section Family

variable {ι : Type x} (M : ι → Type w) [∀ i, L.Structure (M i)] (k : ℕ)

variable (L) in
/-- A set of members of a family of structures is strictly `k`-local when it consists of the
members all of whose `k`-factors a fixed set of factors permits. -/
def IsStrictlyLocal (S : Set ι) : Prop :=
  ∃ G : Set (L.Factor k), S = {i | L.factors k (M i) ⊆ G}

variable (L) in
/-- A set of members of a family of structures is locally `k`-testable when membership depends
only on the set of `k`-factors. -/
def IsLocallyTestable (S : Set ι) : Prop :=
  Function.FactorsThrough (· ∈ S) fun i ↦ L.factors k (M i)

variable {M k} {S T : Set ι}

/-- A set is strictly local exactly when it contains every member whose factors all occur in its
members. -/
theorem isStrictlyLocal_iff :
    L.IsStrictlyLocal M k S ↔ ∀ i, L.factors k (M i) ⊆ ⋃ j ∈ S, L.factors k (M j) → i ∈ S := by
  refine ⟨?_, fun h ↦ ⟨⋃ j ∈ S, L.factors k (M j), Set.ext fun i ↦
    ⟨fun hi ↦ Set.subset_biUnion_of_mem (u := fun j ↦ L.factors k (M j)) hi, h i⟩⟩⟩
  rintro ⟨G, rfl⟩ i hi
  exact hi.trans (Set.iUnion₂_subset fun _ hj ↦ hj)

/-- Strictly local sets are closed under any operation that adds no factor. -/
theorem IsStrictlyLocal.mem_of_factors_subset_union (hS : L.IsStrictlyLocal M k S) {a b c : ι}
    (ha : a ∈ S) (hb : b ∈ S) (h : L.factors k (M c) ⊆ L.factors k (M a) ∪ L.factors k (M b)) :
    c ∈ S := by
  obtain ⟨G, rfl⟩ := hS
  exact h.trans (Set.union_subset ha hb)

/-- Strictly local sets are downward closed under inclusion of factor sets. -/
theorem IsStrictlyLocal.mem_of_factors_subset (hS : L.IsStrictlyLocal M k S) {i j : ι}
    (hi : i ∈ S) (h : L.factors k (M j) ⊆ L.factors k (M i)) : j ∈ S :=
  hS.mem_of_factors_subset_union hi hi (h.trans Set.subset_union_left)

/-- Strictly local sets pull back along any reindexing of the family. -/
theorem IsStrictlyLocal.comap {κ : Type*} (hS : L.IsStrictlyLocal M k S) (π : κ → ι) :
    L.IsStrictlyLocal (fun j ↦ M (π j)) k (π ⁻¹' S) := by
  obtain ⟨G, rfl⟩ := hS
  exact ⟨G, rfl⟩

theorem IsStrictlyLocal.inter (hS : L.IsStrictlyLocal M k S) (hT : L.IsStrictlyLocal M k T) :
    L.IsStrictlyLocal M k (S ∩ T) := by
  obtain ⟨G, rfl⟩ := hS
  obtain ⟨H, rfl⟩ := hT
  exact ⟨G ∩ H, Set.ext fun _ ↦ Set.subset_inter_iff.symm⟩

/-! ### Locally testable sets -/

theorem IsStrictlyLocal.isLocallyTestable (hS : L.IsStrictlyLocal M k S) :
    L.IsLocallyTestable M k S := by
  obtain ⟨G, rfl⟩ := hS
  exact fun _ _ h ↦ congrArg (· ⊆ G) h

theorem IsLocallyTestable.compl (hS : L.IsLocallyTestable M k S) :
    L.IsLocallyTestable M k Sᶜ :=
  fun _ _ h ↦ congrArg Not (hS h)

theorem IsLocallyTestable.inter (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∩ T) :=
  fun _ _ h ↦ congrArg₂ And (hS h) (hT h)

theorem IsLocallyTestable.union (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∪ T) :=
  fun _ _ h ↦ congrArg₂ Or (hS h) (hT h)

end Family

end FirstOrder.Language
