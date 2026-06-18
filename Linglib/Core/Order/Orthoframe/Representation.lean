import Linglib.Core.Order.Orthoframe
import Mathlib.Order.Irreducible

/-!
# Representation of ortholattices by orthoframes

[holliday-mandelkern-2024] Theorem 4.13: every complete ortholattice is isomorphic
to `Orthoframe.Reg` of its canonical orthoframe; every finite ortholattice via its
join-irreducibles (Corollary 4.14). This is the converse of the `Orthoframe` layer
(which gives `frame → ortholattice`).

Translation: our `Orthoframe` carries the **orthogonality** relation, so the paper's
compatibility `a ◇ b ↔ a ≰ ¬b` becomes orthogonality `a ⊥ b ↔ a ≤ bᶜ`. Points are
the nonzero elements of a join-dense `V`, and the representation map is
`a ↦ {b ∈ V\{0} | b ≤ a}`.

## Status

**Theorem 4.13 is complete and sorry-free.** The construction (`ofOrtholattice`), the
extent characterization, the full ortholattice **embedding** (`⊓ ⊔ ¬ ⊤ ⊥` preserved,
order-reflecting), and — for a `CompleteOrthocomplementedLattice` — the
**isomorphism** `representation : L ≃o (ofOrtholattice V).Reg` over any join-dense
`V`. The orthocomplement preservation (`represent_compl`, the heart) falls out of the
`upperPolar` computation `upperPolar_Iic`; no De Morgan over the join is needed.
Corollary 4.14 (`representationFinite`) specialises the isomorphism to a
well-founded (e.g. finite) ortholattice, taking `V` to be the join-irreducibles.
-/

open Order Set

/-- `V` is join-dense in `L`: every element is the least upper bound of the elements
    of `V` below it. -/
def JoinDense {L : Type*} [Preorder L] (V : Set L) : Prop :=
  ∀ a : L, IsLUB {b | b ∈ V ∧ b ≤ a} a

/-- A **complete orthocomplemented lattice**: a complete lattice with an
    orthocomplement satisfying the ortholattice axioms. Bundling avoids the
    `Lattice` diamond that `[CompleteLattice] [OrthocomplementedLattice]` would
    create — the single `Lattice` comes from `CompleteLattice`. -/
class CompleteOrthocomplementedLattice (α : Type*) extends CompleteLattice α, Compl α where
  /-- Complement is involutive. -/
  compl_compl (a : α) : aᶜᶜ = a
  /-- Complement is order-reversing. -/
  compl_antitone {a b : α} : a ≤ b → bᶜ ≤ aᶜ
  /-- Non-contradiction. -/
  inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥
  /-- Excluded middle. -/
  top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ

instance (priority := 100) {α : Type*} [CompleteOrthocomplementedLattice α] :
    OrthocomplementedLattice α where
  compl_compl := CompleteOrthocomplementedLattice.compl_compl
  compl_antitone := CompleteOrthocomplementedLattice.compl_antitone
  inf_compl_le_bot := CompleteOrthocomplementedLattice.inf_compl_le_bot
  top_le_sup_compl := CompleteOrthocomplementedLattice.top_le_sup_compl

namespace Orthoframe

variable {L : Type*} [OrthocomplementedLattice L]

/-- Points of the canonical orthoframe of `(L, V)`: the nonzero elements of `V`. -/
abbrev Point (V : Set L) : Type _ := {a : L // a ∈ V ∧ a ≠ ⊥}

/-- The canonical orthoframe ([holliday-mandelkern-2024] Theorem 4.13): the nonzero
    elements of `V`, orthogonal when `a ≤ bᶜ` (incompatible). -/
def ofOrtholattice (V : Set L) : Orthoframe (Point V) where
  ortho a b := a.1 ≤ b.1ᶜ
  ortho_symm := ⟨fun a b h => by
    have := OrthocomplementedLattice.compl_antitone h
    rwa [OrthocomplementedLattice.compl_compl] at this⟩
  ortho_irrefl := ⟨fun a h => a.2.2 <| le_bot_iff.mp <|
    (le_inf le_rfl h).trans (OrthocomplementedLattice.inf_compl_le_bot a.1)⟩

@[simp] theorem ofOrtholattice_ortho {V : Set L} (a b : Point V) :
    (ofOrtholattice V).ortho a b ↔ a.1 ≤ b.1ᶜ := Iff.rfl

/-- The representation map `a ↦ {b ∈ V\{0} | b ≤ a}`, as a concept. -/
def represent (V : Set L) (a : L) : (ofOrtholattice V).Reg :=
  Concept.ofObjects (ofOrtholattice V).ortho {b | b.1 ≤ a}

variable {V : Set L}

/-- In an ortholattice, `a ≤ bᶜ ↔ b ≤ aᶜ` (orthogonality is symmetric). -/
theorem _root_.OrthocomplementedLattice.le_compl_comm {a b : L} : a ≤ bᶜ ↔ b ≤ aᶜ :=
  ⟨fun h => OrthocomplementedLattice.compl_compl b ▸ OrthocomplementedLattice.compl_antitone h,
   fun h => OrthocomplementedLattice.compl_compl a ▸ OrthocomplementedLattice.compl_antitone h⟩

/-- The upper polar of `{c | c ≤ x}` is `{d | x ≤ dᶜ}` (uses join-density at `x`). -/
theorem upperPolar_Iic (hV : JoinDense V) (x : L) :
    upperPolar (ofOrtholattice V).ortho {c : Point V | c.1 ≤ x} = {d | x ≤ d.1ᶜ} := by
  ext d
  simp only [mem_upperPolar_iff, Set.mem_setOf_eq, ofOrtholattice_ortho]
  constructor
  · intro h
    refine (isLUB_le_iff (hV x)).mpr ?_
    rintro b ⟨hbV, hbx⟩
    rcases eq_or_ne b ⊥ with rfl | hb0
    · exact bot_le
    · exact @h ⟨b, hbV, hb0⟩ hbx
  · intro h c hc
    exact hc.trans h

/-- `{b ∈ V\{0} | b ≤ a}` is a concept extent (uses join-density). -/
theorem isExtent_Iic (hV : JoinDense V) (a : L) :
    IsExtent (ofOrtholattice V).ortho {b : Point V | b.1 ≤ a} := by
  have key : {d : Point V | a ≤ d.1ᶜ} = {d : Point V | d.1 ≤ aᶜ} := by
    ext d; exact OrthocomplementedLattice.le_compl_comm
  rw [isExtent_iff, upperPolar_Iic hV a, key,
      ← upperPolar_eq_lowerPolar (ofOrtholattice V).ortho, upperPolar_Iic hV aᶜ]
  ext e
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, OrthocomplementedLattice.le_compl_comm,
      OrthocomplementedLattice.compl_compl]

/-- The representation map's extent is exactly `{b ∈ V\{0} | b ≤ a}` (Thm 4.13). -/
theorem represent_extent (hV : JoinDense V) (a : L) :
    (represent V a).extent = {b : Point V | b.1 ≤ a} :=
  Concept.extent_ofObjects_of_isExtent (isExtent_Iic hV a)

/-! ### The representation is an order-embedding preserving the lattice operations -/

/-- `represent` is an order-embedding: `represent V a ≤ represent V a' ↔ a ≤ a'`. -/
theorem represent_le_iff (hV : JoinDense V) {a a' : L} :
    represent V a ≤ represent V a' ↔ a ≤ a' := by
  rw [← Concept.extent_subset_extent_iff]
  simp only [represent_extent hV]
  constructor
  · intro h
    refine (isLUB_le_iff (hV a)).mpr ?_
    rintro b ⟨hbV, hba⟩
    rcases eq_or_ne b ⊥ with rfl | hb0
    · exact bot_le
    · exact @h ⟨b, hbV, hb0⟩ hba
  · intro h b hb
    exact hb.trans h

/-- `represent` preserves meets (`Concept` inf is extent intersection). -/
theorem represent_inf (hV : JoinDense V) (a a' : L) :
    represent V (a ⊓ a') = represent V a ⊓ represent V a' := by
  apply Concept.ext
  simp only [Concept.extent_inf, represent_extent hV]
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, le_inf_iff]

/-- `represent` preserves the top. -/
theorem represent_top (hV : JoinDense V) : represent V (⊤ : L) = ⊤ :=
  top_le_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, represent_extent hV]; exact fun b _ => le_top

/-- `represent` preserves the bottom (the zero is excluded from the carrier). -/
theorem represent_bot (hV : JoinDense V) : represent V (⊥ : L) = ⊥ :=
  le_bot_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, represent_extent hV]
    exact fun b hb => absurd (le_bot_iff.mp hb) b.2.2

/-- **Orthocomplement preservation** ([holliday-mandelkern-2024] Theorem 4.13).
    The orthocomplement of `represent V a` has extent `upperPolar ortho {b ≤ a}`,
    which `upperPolar_Iic` computes as `{d | a ≤ dᶜ} = {d | d ≤ aᶜ}` — exactly the
    extent of `represent V aᶜ`. No De Morgan over the join is needed: the
    `upperPolar` computation already carries the argument. -/
theorem represent_compl (hV : JoinDense V) (a : L) :
    represent V aᶜ = (represent V a)ᶜ := by
  apply Concept.ext
  rw [Concept.extent_compl, ← Concept.upperPolar_extent]
  simp only [represent_extent hV]
  rw [upperPolar_Iic hV]
  ext b
  exact OrthocomplementedLattice.le_compl_comm

/-- `represent` preserves joins (from `⊓`- and `ᶜ`-preservation via De Morgan). -/
theorem represent_sup (hV : JoinDense V) (a a' : L) :
    represent V (a ⊔ a') = represent V a ⊔ represent V a' := by
  rw [show a ⊔ a' = (aᶜ ⊓ a'ᶜ)ᶜ by
        rw [OrthocomplementedLattice.compl_inf, OrthocomplementedLattice.compl_compl,
            OrthocomplementedLattice.compl_compl],
      represent_compl hV, represent_inf hV, represent_compl hV, represent_compl hV,
      OrthocomplementedLattice.compl_inf, OrthocomplementedLattice.compl_compl,
      OrthocomplementedLattice.compl_compl]

/-! ### The representation isomorphism (complete case, Theorem 4.13) -/

section Iso

variable {L : Type*} [CompleteOrthocomplementedLattice L] {V : Set L}

/-- Surjectivity (the `←` of Theorem 4.13): every concept is `represent V a`, taking
    `a` to be the join of the underlying elements of its extent. -/
theorem represent_surjective (hV : JoinDense V) (c : (ofOrtholattice V).Reg) :
    represent V (sSup (Subtype.val '' c.extent)) = c := by
  apply Concept.ext
  rw [represent_extent hV]
  ext b
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hb
    rw [← (Concept.isExtent_extent c).eq]
    intro d hd
    show b.1 ≤ d.1ᶜ
    refine hb.trans (sSup_le ?_)
    rintro x ⟨e, he, rfl⟩
    exact hd he
  · intro hb
    exact le_sSup ⟨b, hb, rfl⟩

/-- The join of `represent V a`'s extent recovers `a` (the `→` of Theorem 4.13). -/
theorem sSup_represent_extent (hV : JoinDense V) (a : L) :
    sSup (Subtype.val '' (represent V a).extent) = a := by
  rw [represent_extent hV]
  refine (isLUB_sSup _).unique ⟨?_, ?_⟩
  · rintro x ⟨b, hb, rfl⟩; exact hb
  · intro u hu
    refine (isLUB_le_iff (hV a)).mpr ?_
    rintro c ⟨hcV, hca⟩
    rcases eq_or_ne c ⊥ with rfl | hc0
    · exact bot_le
    · exact hu ⟨⟨c, hcV, hc0⟩, hca, rfl⟩

/-- **The representation isomorphism** ([holliday-mandelkern-2024] Theorem 4.13): a
    complete ortholattice is order-isomorphic to `Orthoframe.Reg` of its canonical
    orthoframe over any join-dense `V`. -/
def representation (hV : JoinDense V) : L ≃o (ofOrtholattice V).Reg where
  toFun := represent V
  invFun c := sSup (Subtype.val '' c.extent)
  left_inv := sSup_represent_extent hV
  right_inv := represent_surjective hV
  map_rel_iff' := represent_le_iff hV

/-! ### Corollary 4.14 — the finite case via join-irreducibles -/

/-- The join-irreducibles are join-dense in a well-founded ortholattice (every
    finite ortholattice is well-founded): each element is the least upper bound of
    the join-irreducibles below it, by `exists_supIrred_decomposition`. -/
theorem joinDense_supIrred [WellFoundedLT L] : JoinDense {a : L | SupIrred a} := by
  intro a
  refine ⟨fun b hb => hb.2, fun u hu => ?_⟩
  obtain ⟨s, hs, hsIrred⟩ := exists_supIrred_decomposition a
  rw [← hs]
  exact Finset.sup_le fun b hb => hu ⟨hsIrred hb, hs ▸ Finset.le_sup hb⟩

/-- **Corollary 4.14** ([holliday-mandelkern-2024]): a finite (more generally,
    well-founded) ortholattice is order-isomorphic to `Orthoframe.Reg` of the
    orthoframe on its join-irreducibles. -/
def representationFinite [WellFoundedLT L] :
    L ≃o (ofOrtholattice {a : L | SupIrred a}).Reg :=
  representation joinDense_supIrred

end Iso

end Orthoframe
