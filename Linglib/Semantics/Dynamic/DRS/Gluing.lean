import Linglib.Semantics.Dynamic.DRS.Presheaf
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Gluing basic DRSs

This file defines covers of a context — jointly surjective families of context morphisms — and
gluing of a family of local sections of a presheaf along a cover: a global section restricting to
each local one, the indexed form of `Presieve.FamilyOfElements.IsAmalgamation` for
`Presieve.ofArrows`. For the presheaf of basic DRSs the candidate gluing is the pushforward of the
local literals along the cover maps: every gluing contains it, it is the unique gluing when every
literal of the glued context factors through a cover map, and it glues outright when the local
vocabularies are pairwise disjoint and the cover maps injective. Read on DRSs, the pushforward is
the merge of the local DRSs after renaming — discourse representation theory's merge followed by
unification of referents.

## Main definitions

* `DRT.Cover`, `DRT.Cover.presieve`: covers and their presieves.
* `DRT.Cover.IsGluing`: gluing of local sections of a presheaf along a cover.
* `DRT.Cover.pushforward`, `DRT.Cover.Factors`, `DRT.Cover.glue`: the candidate gluing, the
  factorization condition, and the gluing under disjoint vocabularies.

## Main statements

* `DRT.Cover.IsGluing.pushforward_subset`, `DRT.Cover.IsGluing.unique`,
  `DRT.Cover.isSeparatedFor_of_factors`: the pushforward is the least gluing and the unique one
  under factorization.
* `DRT.Cover.isGluing_glue`, `DRT.Cover.coe_conditions_toDRS_glue`: under disjoint vocabularies
  and injective maps the pushforward glues, and its DRS is the merge of the renamed local DRSs.

## References

* [abramsky-sadrzadeh-2014]
* [mac-lane-moerdijk-1992]
-/

open CategoryTheory FirstOrder

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- A cover of a context: a jointly surjective family of context morphisms into it
(`⋃ Im fᵢ = X` and `L = ⋃ Lᵢ`). -/
structure Cover (c : Context L V) (ι : Type*) where
  /-- The covering contexts. -/
  part : ι → Context L V
  /-- The covering morphisms. -/
  map : ∀ i, part i ⟶ c
  exists_map_eq : ∀ x : c.vars, ∃ i y, (map i).map y = x
  exists_mem_vocab : ∀ r ∈ c.vocab, ∃ i, r ∈ (part i).vocab

namespace Cover

variable {c : Context L V} {ι : Type*} (C : Cover c ι)

/-- The presieve of the covering morphisms. -/
abbrev presieve : Presieve c := Presieve.ofArrows C.part C.map

/-- `s` glues the family `x` over the cover: `P(fᵢ)(s) = xᵢ` for every `i`. -/
def IsGluing (P : (Context L V)ᵒᵖ ⥤ Type*) (x : ∀ i, P.obj (Opposite.op (C.part i)))
    (s : P.obj (Opposite.op c)) : Prop :=
  ∀ i, P.map (C.map i).op s = x i

variable {C}

theorem eq_of_map_eq (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    {i j : ι} {m : Literal (C.part i)} {m' : Literal (C.part j)}
    (h : m.map (C.map i) = m'.map (C.map j)) : i = j :=
  by_contra fun hij => Finset.disjoint_left.1 (hdisj hij) m.rel.2
    (by rw [show m.rel.1 = m'.rel.1 from congrArg (fun l : Literal c => l.rel.1) h]; exact m'.rel.2)

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)] {x : ∀ i, Theory (C.part i)}
  {s s' : Theory c}

instance [Fintype ι] : Decidable (C.IsGluing (presheaf L V) x s) :=
  inferInstanceAs (Decidable (∀ i, s.restrict (C.map i) = x i))

/-- The candidate gluing `{±A(fᵢ(x̄)) | ±A(x̄) ∈ sᵢ}`. -/
def pushforward [Fintype ι] (C : Cover c ι) (x : ∀ i, Theory (C.part i)) : Finset (Literal c) :=
  Finset.univ.biUnion fun i => (x i).lits.image (Literal.map (C.map i))

@[simp] theorem mem_pushforward [Fintype ι] {l : Literal c} :
    l ∈ C.pushforward x ↔ ∃ i, ∃ m ∈ (x i).lits, m.map (C.map i) = l := by
  simp [pushforward]

theorem IsGluing.pushforward_subset [Fintype ι] (hs : C.IsGluing (presheaf L V) x s) :
    C.pushforward x ⊆ s.lits := by
  intro l hl
  obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
  rw [← hs i] at hm
  exact Theory.mem_restrict.1 hm

/-- Every literal over the glued context is the image of a literal over some part. -/
def Factors (C : Cover c ι) : Prop :=
  ∀ l : Literal c, ∃ i, ∃ m : Literal (C.part i), m.map (C.map i) = l

instance [Fintype ι] : Decidable C.Factors :=
  inferInstanceAs (Decidable (∀ l : Literal c, ∃ i, ∃ m : Literal (C.part i), m.map (C.map i) = l))

theorem IsGluing.lits_eq_pushforward [Fintype ι] (hC : C.Factors)
    (hs : C.IsGluing (presheaf L V) x s) : s.lits = C.pushforward x :=
  subset_antisymm (fun l hl => by
      obtain ⟨i, m, rfl⟩ := hC l
      exact mem_pushforward.2 ⟨i, m, by rw [← hs i]; exact Theory.mem_restrict.2 hl, rfl⟩)
    hs.pushforward_subset

/-- Gluings are unique for covers through which every literal factors. -/
theorem IsGluing.unique [Fintype ι] (hC : C.Factors) (hs : C.IsGluing (presheaf L V) x s)
    (hs' : C.IsGluing (presheaf L V) x s') : s = s' :=
  Theory.ext ((hs.lits_eq_pushforward hC).trans (hs'.lits_eq_pushforward hC).symm)

/-- The presheaf of basic DRSs is separated for a factoring cover. -/
theorem isSeparatedFor_of_factors [Fintype ι] (hC : C.Factors) :
    C.presieve.IsSeparatedFor (presheaf L V) := fun x _ _ h h' =>
  IsGluing.unique hC (x := fun i => x _ (.mk i))
    ((Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows _ _ x _).1 h)
    ((Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows _ _ x _).1 h')

/-- With pairwise disjoint vocabularies and injective cover maps the pushforward is consistent. -/
def glue [Fintype ι] (C : Cover c ι)
    (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, Theory (C.part i)) : Theory c where
  lits := C.pushforward x
  consistent _ hl hn := by
    obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
    obtain ⟨j, m', hm', h⟩ := mem_pushforward.1 hn
    rw [Literal.neg_map] at h
    obtain rfl : i = j := (eq_of_map_eq hdisj h).symm
    exact (x i).consistent m hm (Literal.map_injective (hinj i) h ▸ hm')

section Glue

variable [Fintype ι] (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
  (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, Theory (C.part i))

/-- Under disjoint vocabularies and injective cover maps the pushforward glues: the only
obstruction to gluing is consistency, and it does not arise. -/
theorem isGluing_glue : C.IsGluing (presheaf L V) x (C.glue hdisj hinj x) := fun i =>
  Theory.ext (Finset.ext fun l => by
    simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict, glue, mem_pushforward]
    constructor
    · rintro ⟨j, m, hm, h⟩
      obtain rfl : i = j := (eq_of_map_eq hdisj h).symm
      exact Literal.map_injective (hinj i) h ▸ hm
    · exact fun hl => ⟨i, l, hl, rfl⟩)

/-- The referents of the glued DRS are those of the renamed local DRSs. -/
theorem referents_toDRS_glue (g : ι → V → V)
    (hg : ∀ i (t : (C.part i).vars), g i t = ((C.map i).map t : V)) :
    (C.glue hdisj hinj x).toDRS.referents =
      Finset.univ.biUnion fun i => ((x i).toDRS.map (g i)).referents := by
  ext t
  simp only [Theory.referents_toDRS, DRS.referents_map, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_image, true_and]
  constructor
  · intro ht
    obtain ⟨i, y, hy⟩ := C.exists_map_eq ⟨t, ht⟩
    exact ⟨i, y, y.2, by rw [hg, hy]⟩
  · rintro ⟨i, y, hy, rfl⟩
    rw [hg i ⟨y, hy⟩]
    exact ((C.map i).map ⟨y, hy⟩).2

/-- The conditions of the glued DRS are those of the renamed local DRSs, as a multiset: the
pushforward is the merge of the local DRSs after unification of referents. -/
theorem coe_conditions_toDRS_glue (g : ι → V → V)
    (hg : ∀ i (t : (C.part i).vars), g i t = ((C.map i).map t : V)) :
    ((C.glue hdisj hinj x).toDRS.conditions : Multiset (Condition L V)) =
      ∑ i, (((x i).toDRS.map (g i)).conditions : Multiset (Condition L V)) := by
  have hpd : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      fun i => (x i).lits.image (Literal.map (C.map i)) := fun _ _ _ _ hij =>
    Finset.disjoint_left.2 fun l hi hj => by
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨m', -, h⟩ := Finset.mem_image.1 hj
      exact hij (eq_of_map_eq hdisj h.symm)
  rw [Theory.coe_conditions_toDRS, Finset.sum_eq_multiset_sum]
  change (Finset.univ.biUnion _).val.map _ = _
  rw [← Finset.disjiUnion_eq_biUnion _ _ hpd, Finset.disjiUnion_val, Multiset.map_bind]
  change (Finset.univ.val.map _).sum = _
  refine congrArg _ (Multiset.map_congr rfl fun i _ => ?_)
  rw [Finset.image_val,
    Multiset.dedup_eq_self.2 ((x i).lits.nodup.map (Literal.map_injective (hinj i))),
    Multiset.map_map, DRS.conditions_map, ← Multiset.map_coe, Theory.coe_conditions_toDRS,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun l _ => Literal.toCondition_map _ _ (hg i) l

end Glue

end Cover

end DRT
