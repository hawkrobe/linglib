import Linglib.Semantics.Mereology
import Mathlib.Logic.Equiv.Finset

/-!
# Group formation and dissolution

[landman-1989] [landman-2000]

Landman's group operators over a part-of domain: `up` packs a plural sum
into a group atom — *the committee* as a singular entity over its
members — and `down` dissolves the group back into the underlying sum.
The carrier is any `SemilatticeSup`, so the operators serve the domain of
individuals and the domain of events alike ([landman-2000]); in the event
domain, a symmetric verb's atomic event dissolves into the sum of its
directional sub-events ([siloni-2012] §4.1).

## Main declarations

* `GroupStructure` — `up`/`down` with the atomicity and dissolution laws.
* `GroupStructure.up_injective` — distinct sums form distinct groups.
-/

namespace Semantics.Plurality

/-- Landman's group structure: `up` packs a sum into a group atom, `down`
    recovers the underlying sum. The two laws are the operative core of
    [landman-1989]'s postulates. -/
structure GroupStructure (E : Type*) [SemilatticeSup E] where
  /-- Group formation (Landman's `↑`). -/
  up : E → E
  /-- Group dissolution (Landman's `↓`). -/
  down : E → E
  /-- A group is an atom: it has no proper parts. -/
  atom_up (x : E) : Mereology.Atom (up x)
  /-- Dissolution inverts formation. -/
  down_up (x : E) : down (up x) = x

namespace GroupStructure

variable {E : Type*} [SemilatticeSup E] (G : GroupStructure E)

/-- Distinct sums form distinct group atoms. -/
theorem up_injective : Function.Injective G.up :=
  Function.LeftInverse.injective G.down_up

/-! ### A model

Nonempty finite subsets of `β ⊕ ℕ`, with sum as union: the `β`-singletons
are the ordinary atoms, and packing recruits a fresh `ℕ`-marked singleton
for each plurality, so groups are atoms of the same domain. -/

instance {α : Type*} [DecidableEq α] :
    SemilatticeSup {F : Finset α // F.Nonempty} :=
  Subtype.semilatticeSup fun _ _ hx _ => hx.mono Finset.subset_union_left

@[simp] theorem coe_sup {α : Type*} [DecidableEq α]
    (x y : {F : Finset α // F.Nonempty}) :
    (↑(x ⊔ y) : Finset α) = ↑x ∪ ↑y :=
  Finset.sup_eq_union ..

variable {β : Type*} [Encodable β]

instance {α : Type*} : DecidablePred (fun F : Finset α => F.Nonempty) :=
  fun _ => Finset.decidableNonempty

/-- Group formation in the model: the fresh marker singleton indexed by
    the plurality's code. -/
def modelUp (x : {F : Finset (β ⊕ ℕ) // F.Nonempty}) :
    {F : Finset (β ⊕ ℕ) // F.Nonempty} :=
  ⟨{Sum.inr (Encodable.encode x)}, Finset.singleton_nonempty _⟩

theorem modelUp_injective :
    Function.Injective (modelUp (β := β)) := fun x y h => by
  have h' : ({Sum.inr (Encodable.encode x)} : Finset (β ⊕ ℕ)) =
      {Sum.inr (Encodable.encode y)} := congrArg Subtype.val h
  exact Encodable.encode_injective (Sum.inr.inj
    (Finset.singleton_injective h'))

open Classical in
/-- Landman's group operators are consistent: the nonempty finite subsets
    of `β ⊕ ℕ` carry a `GroupStructure`, with dissolution recovering the
    packed plurality from the marker's code. -/
noncomputable def finsetModel (β : Type*) [DecidableEq β] [Encodable β] :
    GroupStructure {F : Finset (β ⊕ ℕ) // F.Nonempty} where
  up := modelUp
  down y := if h : ∃ x, modelUp x = y then h.choose else y
  atom_up x := by
    intro z hz
    have hsub : z.val ⊆ {Sum.inr (Encodable.encode x)} := hz
    rcases Finset.subset_singleton_iff.mp hsub with hempty | hsingle
    · exact absurd hempty (Finset.nonempty_iff_ne_empty.mp z.2)
    · exact le_of_eq (Subtype.ext hsingle.symm)
  down_up x := by
    have h : ∃ x', modelUp x' = modelUp (β := β) x := ⟨x, rfl⟩
    rw [dif_pos h]
    exact modelUp_injective h.choose_spec

@[simp] theorem finsetModel_up [DecidableEq β]
    (x : {F : Finset (β ⊕ ℕ) // F.Nonempty}) :
    (finsetModel β).up x = modelUp x := rfl

end GroupStructure

end Semantics.Plurality
