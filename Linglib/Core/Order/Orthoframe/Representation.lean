import Linglib.Core.Order.Orthoframe

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

The construction (`ofOrtholattice`), the extent characterization, and the full
ortholattice **embedding** (`⊓ ⊔ ¬ ⊤ ⊥` preserved, order-reflecting) are complete
and sorry-free. The orthocomplement preservation — the heart of Theorem 4.13 — is
`represent_compl`, which falls out of the `upperPolar` computation `upperPolar_Iic`
(no De Morgan over the join is needed). Remaining (PR 3): surjectivity for complete
`L` to assemble the isomorphism `L ≃o (ofOrtholattice V).Reg`, and Corollary 4.14.
-/

open Order Set

/-- `V` is join-dense in `L`: every element is the least upper bound of the elements
    of `V` below it. -/
def JoinDense {L : Type*} [Preorder L] (V : Set L) : Prop :=
  ∀ a : L, IsLUB {b | b ∈ V ∧ b ≤ a} a

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

/- TODO (Phase B, PR 3): the representation is now a full ortholattice embedding
   (`⊓ ⊔ ¬ ⊤ ⊥` preserved, order-reflecting). Remaining: surjectivity for complete
   `L` (`a := sSup` of a concept's extent) to assemble the isomorphism
   `L ≃o (ofOrtholattice V).Reg` (Theorem 4.13), and Corollary 4.14 via
   join-irreducibles for finite `L`. Needs a `CompleteLattice + OrthocomplementedLattice`
   carrier (resolve the `Lattice` diamond). -/

end Orthoframe
