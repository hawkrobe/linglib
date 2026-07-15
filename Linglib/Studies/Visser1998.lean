import Linglib.Semantics.Dynamic.DPL
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Tauto

/-!
# Visser (1998): Contexts in Dynamic Predicate Logic
[visser-1998]

Contexts in Dynamic Predicate Logic. *Journal of Logic, Language, and
Information* 7: 21–52. A context in the type-theoretic sense — a
declaration of variables — for DPL: a triple `⟨I, B, O⟩` of input set,
block set, and output set typing which variables a relation reads, cuts,
and writes. The paper's metatheory of these types, over the semantic
`DPLRel` substrate.

## Main results

- `Context` with `1`, `*`, and `≤`: the contexts form a monoid and the
  information order is a partial order (Theorem 3.3).
- `IsCRel c R`: `R` is a `c`-relation (Definition 3.4), with
  `isCRel_iff_eq` recovering the paper's equational form
  `R = (≡ᵢ ; R ; ≡ₒ) ∩ [B]`.
- `IsCRel.mono`: the order is sound for the typing — `c ≤ d` types more
  relations (Theorem 3.5(1)).
- `IsCRel.patch`: the unique-output lemma (Lemma 3.7).
- `IsCRel.conj`, `IsCRel.impl`: composition and implication typing
  (Theorems 3.8–3.9), and the typing of DPL's generators —
  `isCRel_atom` (conditions at `⟨V, ∅, V⟩`) and `isCRel_reset`
  (random reset at `⟨∅, {x}, {x}⟩`).

The converse of Theorem 3.5 (for `|D| ≥ 2`) and §§4–5's Switching
Property characterization of the DPL-expressible relations await a
follow-up; the latter's completeness direction needs the syntax stratum.
-/

namespace Visser1998

open DPL

variable {M : Type*}

/-! ### Contexts (Definition 3.1) -/

/-- A DPL-context (Definition 3.1): input set `I` (variables the incoming
assignment is read at), block set `B` (variables whose input-output link
is cut), output set `O` (variables the outgoing assignment is constrained
at), coherent in the sense `I ∪ B = O ∪ B`. -/
@[ext] structure Context where
  /-- The input set. -/
  I : Finset ℕ
  /-- The block set: the barrier between past and future. -/
  B : Finset ℕ
  /-- The output set. -/
  O : Finset ℕ
  /-- Coherence: off the blocks, inputs and outputs coincide. -/
  coh : I ∪ B = O ∪ B

namespace Context

/-- Membership form of coherence. -/
theorem coh_mem (c : Context) {v : ℕ} : v ∈ c.I ∪ c.B ↔ v ∈ c.O ∪ c.B :=
  Finset.ext_iff.mp c.coh v

instance : One Context := ⟨⟨∅, ∅, ∅, rfl⟩⟩

/-- Context composition (Definition 3.1):
`⟨I,B,O⟩ * ⟨I',B',O'⟩ = ⟨I ∪ (I'∖B), B ∪ B', (O∖B') ∪ O'⟩`. -/
instance : Mul Context :=
  ⟨fun c d =>
    ⟨c.I ∪ (d.I \ c.B), c.B ∪ d.B, (c.O \ d.B) ∪ d.O, by
      ext v
      have h1 := c.coh_mem (v := v)
      have h2 := d.coh_mem (v := v)
      simp only [Finset.mem_union, Finset.mem_sdiff] at *
      tauto⟩⟩

@[simp] theorem I_mul (c d : Context) : (c * d).I = c.I ∪ (d.I \ c.B) := rfl
@[simp] theorem B_mul (c d : Context) : (c * d).B = c.B ∪ d.B := rfl
@[simp] theorem O_mul (c d : Context) : (c * d).O = (c.O \ d.B) ∪ d.O := rfl
@[simp] theorem I_one : (1 : Context).I = ∅ := rfl
@[simp] theorem B_one : (1 : Context).B = ∅ := rfl
@[simp] theorem O_one : (1 : Context).O = ∅ := rfl

/-- The contexts form a monoid (Theorem 3.3). -/
instance : Monoid Context where
  mul_assoc c d e := by
    ext v <;> simp only [I_mul, B_mul, O_mul, Finset.mem_union,
      Finset.mem_sdiff] <;> tauto
  one_mul c := by ext v <;> simp
  mul_one c := by ext v <;> simp

/-- The information order on contexts (Definition 3.1): more informative
contexts read, write, and block more — with new blocks confined to
variables the larger context both reads and writes. A partial order
(Theorem 3.3). -/
instance : PartialOrder Context where
  le c d := c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O)
  le_refl c := ⟨subset_rfl, subset_rfl, subset_rfl, Finset.subset_union_left⟩
  le_trans c d e h h' :=
    ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, by
      intro v hv
      rcases Finset.mem_union.mp (h'.2.2.2 hv) with hd | hio
      · rcases Finset.mem_union.mp (h.2.2.2 hd) with hc | hio'
        · exact Finset.mem_union_left _ hc
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
            ⟨h'.1 (Finset.mem_inter.mp hio').1,
             h'.2.1 (Finset.mem_inter.mp hio').2⟩)
      · exact Finset.mem_union_right _ hio⟩
  le_antisymm c d h h' :=
    Context.ext (Finset.Subset.antisymm h.1 h'.1)
      (Finset.Subset.antisymm h.2.2.1 h'.2.2.1)
      (Finset.Subset.antisymm h.2.1 h'.2.1)

theorem le_def {c d : Context} :
    c ≤ d ↔ c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O) :=
  Iff.rfl

end Context

/-! ### c-relations (Definition 3.4) -/

/-- `R` is a `c`-relation (Definition 3.4): it reads inputs only at `c.I`,
constrains outputs only at `c.O`, and changes values only at `c.B`.
`blocks` is `R ⊆ [B]`; `stable` is the nontrivial inclusion of the
paper's equation `R = (≡ᵢ ; R ; ≡ₒ) ∩ [B]`. -/
structure IsCRel (c : Context) (R : DPLRel M) : Prop where
  /-- Only blocked variables change. -/
  blocks : ∀ ⦃f g⦄, R f g → ∀ v ∉ c.B, f v = g v
  /-- Membership is invariant under input agreement on `I`, output
  agreement on `O`, and preservation off `B`. -/
  stable : ∀ ⦃f f' g g'⦄, R f g → (∀ v ∈ c.I, f' v = f v) →
    (∀ v ∈ c.O, g v = g' v) → (∀ v ∉ c.B, f' v = g' v) → R f' g'

/-- The paper's equational form of Definition 3.4. -/
theorem isCRel_iff_eq (c : Context) (R : DPLRel M) :
    IsCRel c R ↔
      R = fun f' g' => (∃ f g, (∀ v ∈ c.I, f' v = f v) ∧ R f g ∧
        (∀ v ∈ c.O, g v = g' v)) ∧ ∀ v ∉ c.B, f' v = g' v := by
  constructor
  · intro h
    funext f' g'
    simp only [eq_iff_iff]
    exact ⟨fun hR => ⟨⟨f', g', fun _ _ => rfl, hR, fun _ _ => rfl⟩, h.blocks hR⟩,
      fun ⟨⟨f, g, hI, hR, hO⟩, hB⟩ => h.stable hR hI hO hB⟩
  · intro h
    constructor
    · intro f g hR
      rw [h] at hR
      exact hR.2
    · intro f f' g g' hR hI hO hB
      rw [h]
      exact ⟨⟨f, g, hI, hR, hO⟩, hB⟩

/-! ### The order is sound for the typing (Theorem 3.5) -/

/-- Theorem 3.5(1): larger contexts type more relations —
`c ≤ d` and `R` a `c`-relation make `R` a `d`-relation. -/
theorem IsCRel.mono {c d : Context} {R : DPLRel M} (hcd : c ≤ d)
    (h : IsCRel c R) : IsCRel d R := by
  obtain ⟨hI, hO, hB, hBio⟩ := hcd
  constructor
  · exact fun f g hR v hv => h.blocks hR v fun hvB => hv (hB hvB)
  · intro f f' g g' hR hI' hO' hB'
    refine h.stable hR (fun v hv => hI' v (hI hv)) (fun v hv => hO' v (hO hv))
      (fun v hv => ?_)
    by_cases hvd : v ∈ d.B
    · rcases Finset.mem_union.mp (hBio hvd) with hc | hio
      · exact absurd hc hv
      · obtain ⟨hvi, hvo⟩ := Finset.mem_inter.mp hio
        rw [hI' v hvi, ← hO' v hvo]
        exact h.blocks hR v hv
    · exact hB' v hvd

/-! ### The unique-output lemma (Lemma 3.7) -/

/-- Lemma 3.7: if `R` is a `c`-relation, `f' ≡ᵢ f`, and `f R g`, then `f'`
reaches the patch of `f'` by `g` at the blocks — the unique output
agreeing with `g` on the blocks. -/
theorem IsCRel.patch {c : Context} {R : DPLRel M}
    (h : IsCRel c R) {f f' g : ℕ → M}
    (hI : ∀ v ∈ c.I, f' v = f v) (hR : R f g) :
    R f' (fun v => if v ∈ c.B then g v else f' v) := by
  refine h.stable hR hI (fun v hv => ?_) (fun v hv => by simp [hv])
  by_cases hvB : v ∈ c.B
  · simp [hvB]
  · rw [if_neg hvB, ← h.blocks hR v hvB]
    rcases Finset.mem_union.mp (c.coh_mem.mpr (Finset.mem_union_left _ hv)) with
      hvi | hvB'
    · exact (hI v hvi).symm
    · exact absurd hvB' hvB

/-! ### Composition and implication typing (Theorems 3.8–3.9) -/

/-- Theorem 3.8: composition of a `c`-relation and a `d`-relation is a
`c * d`-relation. The stability witness is the paper's three-zone patch on
the intermediate assignment: keep it at `c.O ∪ d.I`, take the new output
at the old blocks, the new input elsewhere. -/
theorem IsCRel.conj {c d : Context} {R S : DPLRel M}
    (hR : IsCRel c R) (hS : IsCRel d S) :
    IsCRel (c * d) (DPLRel.conj R S) := by
  classical
  constructor
  · rintro f g ⟨k, hfk, hkg⟩ v hv
    simp only [Context.B_mul, Finset.mem_union, not_or] at hv
    exact (hR.blocks hfk v hv.1).trans (hS.blocks hkg v hv.2)
  · rintro f f' g g' ⟨k, hfk, hkg⟩ hI hO hB
    classical
    refine ⟨fun v => if v ∈ c.O ∪ d.I then k v
        else if v ∈ c.B then g' v else f' v,
      hR.stable hfk (fun v hv => hI v (Finset.mem_union_left _ hv)) ?_ ?_,
      hS.stable hkg ?_ (fun v hv => hO v (Finset.mem_union_right _ hv)) ?_⟩
    · -- k agrees with the patch on c.O
      intro v hv
      rw [if_pos (Finset.mem_union_left _ hv)]
    · -- f' agrees with the patch off c.B
      intro v hv
      by_cases hoi : v ∈ c.O ∪ d.I
      · rw [if_pos hoi, ← hR.blocks hfk v hv]
        rcases Finset.mem_union.mp hoi with ho | hi
        · rcases Finset.mem_union.mp
            (c.coh_mem.mpr (Finset.mem_union_left _ ho)) with hvi | hvB
          · exact hI v (Finset.mem_union_left _ hvi)
          · exact absurd hvB hv
        · exact hI v (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hv⟩))
      · rw [if_neg hoi, if_neg hv]
    · -- the patch agrees with k on d.I
      intro v hv
      rw [if_pos (Finset.mem_union_right _ hv)]
    · -- the patch agrees with g' off d.B
      intro v hv
      by_cases hoi : v ∈ c.O ∪ d.I
      · rw [if_pos hoi, hS.blocks hkg v hv]
        rcases Finset.mem_union.mp hoi with ho | hi
        · exact hO v (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ho, hv⟩))
        · rcases Finset.mem_union.mp
            (d.coh_mem.mp (Finset.mem_union_left _ hi)) with hvo | hvB
          · exact hO v (Finset.mem_union_right _ hvo)
          · exact absurd hvB hv
      · rw [if_neg hoi]
        split_ifs with hvB
        · rfl
        · exact hB v (by
            simp only [Context.B_mul, Finset.mem_union, not_or]
            exact ⟨hvB, hv⟩)

/-- The implication context: `c → d = ⟨I ∪ (I'∖B), ∅, I ∪ (I'∖B)⟩` —
implications are tests reading the combined inputs. -/
def Context.dimpl (c d : Context) : Context :=
  ⟨c.I ∪ (d.I \ c.B), ∅, c.I ∪ (d.I \ c.B), rfl⟩

/-- Theorem 3.9: DPL implication of a `c`-relation and a `d`-relation is a
`(c → d)`-relation, via two applications of the patch lemma. -/
theorem IsCRel.impl {c d : Context} {R S : DPLRel M}
    (hR : IsCRel c R) (hS : IsCRel d S) :
    IsCRel (c.dimpl d) (DPLRel.impl R S) := by
  constructor
  · rintro f g ⟨rfl, -⟩ v _
    rfl
  · rintro f f' g g' ⟨rfl, hall⟩ hI - hB
    obtain rfl : f' = g' := funext fun v => hB v (Finset.notMem_empty v)
    refine ⟨rfl, fun k hRk => ?_⟩
    -- Transport the antecedent back to `f` by the patch lemma.
    have hIff' : ∀ v ∈ c.I, f v = f' v := fun v hv =>
      (hI v (Finset.mem_union_left _ hv)).symm
    have hfk₀ := hR.patch hIff' hRk
    set k₀ : ℕ → M := fun v => if v ∈ c.B then k v else f v with hk₀
    obtain ⟨j, hSj⟩ := hall k₀ hfk₀
    -- Transport the consequent forward to `k` by the patch lemma.
    have hIk : ∀ v ∈ d.I, k v = k₀ v := by
      intro v hv
      by_cases hvB : v ∈ c.B
      · simp [hk₀, hvB]
      · rw [hk₀]
        simp only [if_neg hvB]
        rw [← hR.blocks hRk v hvB]
        exact (hI v (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvB⟩)))
    exact ⟨_, hS.patch hIk hSj⟩

/-! ### The DPL generators, typed -/

/-- A condition depending only on `V` is a `⟨V, ∅, V⟩`-relation as a test
(the atomic case of the paper's semantic Theorem 3.13). -/
theorem isCRel_atom (V : Finset ℕ) (p : (ℕ → M) → Prop)
    (hp : ∀ ⦃f f'⦄, (∀ v ∈ V, f v = f' v) → p f → p f') :
    IsCRel ⟨V, ∅, V, rfl⟩ (DPLRel.atom p) := by
  constructor
  · rintro f g ⟨rfl, -⟩ v -
    rfl
  · rintro f f' g g' ⟨rfl, hpf⟩ hI - hB
    obtain rfl : f' = g' := funext fun v => hB v (Finset.notMem_empty v)
    exact ⟨rfl, hp (fun v hv => (hI v hv).symm) hpf⟩

/-- The random reset at `x` — differ at most at `x`, [visser-1998]'s
`[x]` — read as a `DPLRel`. -/
def reset (x : ℕ) : DPLRel M := fun f g => ∀ v, v ≠ x → f v = g v

/-- The reset is a `⟨∅, {x}, {x}⟩`-relation: it reads nothing, blocks
`x`, and writes `x`. -/
theorem isCRel_reset (x : ℕ) :
    IsCRel ⟨∅, {x}, {x}, by simp⟩ (reset (M := M) x) := by
  constructor
  · intro f g hR v hv
    exact hR v (by simpa using hv)
  · intro f f' g g' _ _ _ hB v hv
    exact hB v (by simpa using hv)

end Visser1998
