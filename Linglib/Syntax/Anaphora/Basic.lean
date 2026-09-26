module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Deep and surface anaphora

[hankamer-sag-1976] divide anaphoric processes into two kinds. A surface anaphor is derived by
deletion under identity with a linguistic antecedent, so its site keeps the syntactic structure of
the elided phrase: VP-ellipsis, sluicing, NP-ellipsis and argument ellipsis are surface anaphora. A
deep anaphor is a pro-form with no internal structure, interpreted as a pronoun is: null complement
anaphora, *pro*, empty nouns and *do it* are deep. This file defines the classification, its
defining property, and the conditions a model of null anaphora must meet to realize it: a
surface site leaves some syntactic position unpronounced, and a deep site leaves none. The
classification is of anaphoric processes, not nominals, and is independent of the binding classes
of `Binding.BindingClass`.

## Main definitions

* `Anaphor.Depth`: the depth of an anaphoric process, deep or surface.
* `Anaphor.Depth.HasInternalStructure`: the site of the anaphor contains syntactic structure,
  which holds of surface anaphora and of no others.
* `Anaphor.DepthModel`: a model of null sites that realizes the classification, assigning each
  site a depth and the positions it leaves unpronounced.

## Main results

* `Anaphor.DepthModel.depth_eq_surface_iff`: in any model, a site is surface exactly when it
  leaves some position unpronounced.
* `Anaphor.DepthModel.depth_eq_surface_of_silences`: a dependency that ends inside a site finds
  a surface anaphor there.

## Implementation notes

The classification is defined by internal structure alone, and a framework realizes it by giving
a `DepthModel`: [E]-deletion in `Syntax/Minimalist/Ellipsis.lean` is one model, and a framework
with another source of unpronounced structure, or with none, supplies its own. The other
properties Hankamer and Sag
associated with depth, such as pragmatic control and the missing-antecedent phenomenon, are tests
for that structure, and a test is stated with the data of the study that applies it.
[merchant-2013-diagnosing] keeps extraction, agreement and inverse scope as diagnostics of
ellipsis and sets pragmatic control aside, since an ellipsis can be pragmatically controlled under
limited conditions; [landau-2026] adds a test that decides depth where extraction and agreement
cannot, and `Studies/Landau2026.lean` shows when a test decides depth.

## References

* [hankamer-sag-1976]
* [merchant-2013-diagnosing]
* [landau-2026]
-/

@[expose] public section

namespace Anaphor

/-- The depth of an anaphoric process [hankamer-sag-1976]. A `surface` anaphor is derived by
deletion under identity and keeps the structure of the elided phrase; a `deep` anaphor is a
pro-form without internal structure. -/
inductive Depth where
  | deep
  | surface
  deriving DecidableEq, Repr, Fintype

namespace Depth

/-- The site of an anaphor has internal structure when the anaphor is surface: deletion leaves
the structure of the elided phrase in place, and a deep anaphor has none. -/
def HasInternalStructure (d : Depth) : Prop := d = .surface

instance : DecidablePred HasInternalStructure := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end Depth

/-- A model of anaphoric depth: null sites `S`, each assigned a depth, and the syntactic positions
`P` a site leaves unpronounced. The two conditions are Hankamer and Sag's: a surface anaphor
contains unpronounced structure, and a deep anaphor contains none. -/
class DepthModel (S : Type*) (P : outParam Type*) where
  /-- The depth the model assigns to a null site. -/
  depth : S → Depth
  /-- `Silences s p`: the position `p` lies inside the site `s` and is not pronounced. -/
  Silences : S → P → Prop
  /-- A surface anaphor leaves some position unpronounced. -/
  exists_silences_of_surface (s : S) : depth s = .surface → ∃ p, Silences s p
  /-- A deep anaphor leaves no position unpronounced. -/
  not_silences_of_deep (s : S) (p : P) : depth s = .deep → ¬ Silences s p

namespace DepthModel

variable {S P : Type*} [DepthModel S P] {s : S} {p : P}

theorem depth_eq_surface_of_silences (h : Silences s p) : depth s = .surface := by
  cases hd : depth s
  · exact absurd h (not_silences_of_deep s p hd)
  · rfl

theorem depth_eq_surface_iff : depth s = .surface ↔ ∃ p, Silences s p :=
  ⟨exists_silences_of_surface s, fun ⟨_, h⟩ ↦ depth_eq_surface_of_silences h⟩

theorem depth_eq_deep_iff : depth s = .deep ↔ ∀ p, ¬ Silences s p := by
  cases hd : depth s
  · exact iff_of_true rfl fun p ↦ not_silences_of_deep s p hd
  · exact iff_of_false (by decide) fun h ↦
      (exists_silences_of_surface s hd).elim fun p hp ↦ h p hp

theorem hasInternalStructure_depth_iff : (depth s).HasInternalStructure ↔ ∃ p, Silences s p :=
  depth_eq_surface_iff

end DepthModel

end Anaphor
