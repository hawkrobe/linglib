import Mathlib.Data.Set.Subsingleton
import Mathlib.Tactic.DeriveFintype

/-!
# The person space and function-valued person features

This file defines the person space of Ackema and Neeleman: a nested chain of sets of atoms
`Sᵢ ⊆ Sᵢ₊ᵤ ⊆ Sᵢ₊ᵤ₊ₒ` in which the speaker is an obligatory member of the innermost set and an
addressee of the middle one, together with two privative person features interpreted as partial
functions on it — `PROX` discards the outermost layer of a layered set and `DIST` selects it — and
the feature structures built by applying them in sequence to the whole space. Third person selects
the others layer, second person the addressee layer, first person the innermost set, and the
inclusive the middle set; neither feature applies to a layer or to the innermost set, which bounds
the inventory. Plural is defined only on an output of the person system with more than one member.

## Main definitions

* `Minimalist.Phi.PersonSpace`: the nested person space over a type of atoms.
* `PersonSpace.Region`, `PersonSpace.denote`: the sets a feature structure can select and their
  denotations.
* `PersonSpace.Feature`, `Feature.apply`, `PersonSpace.Spec`, `Spec.eval`: the features as partial
  functions on regions, and feature structures evaluated on the whole space.
* `PersonSpace.PluralDefined`: the definedness condition of plural.

## Main statements

* `PersonSpace.Spec.eval_mem`: every feature structure evaluates to one of the five regions or is
  incoherent.
* `PersonSpace.denote_nonempty`, `PersonSpace.exists_denote_others_eq_empty`: only the others
  layer can be empty.
* `PersonSpace.nontrivial_denote_siu`, `PersonSpace.nontrivial_denote_siuo`: the middle set and
  the whole space have two obligatory members.

## References

* [ackema-neeleman-2018]
-/

namespace Minimalist.Phi

/-- The person space: nested sets of atoms with the speaker an obligatory member of `Sᵢ` and an
addressee of `Sᵢ₊ᵤ`; the remaining members are associates and others. -/
structure PersonSpace (α : Type*) where
  /-- The speaker `i`. -/
  speaker : α
  /-- The addressee `u`. -/
  addressee : α
  /-- `Sᵢ`: the speaker and any associates or co-speakers. -/
  Si : Set α
  /-- `Sᵢ₊ᵤ`: additionally an addressee and any associates or co-addressees. -/
  Siu : Set α
  /-- `Sᵢ₊ᵤ₊ₒ`: additionally the others. -/
  Siuo : Set α
  speaker_mem : speaker ∈ Si
  addressee_mem : addressee ∈ Siu
  addressee_notMem : addressee ∉ Si
  Si_subset : Si ⊆ Siu
  Siu_subset : Siu ⊆ Siuo

namespace PersonSpace

variable {α : Type*} (S : PersonSpace α)

/-- The regions a feature structure can select: the three nested sets and the two layers between
them. -/
inductive Region
  | si
  | siu
  | siuo
  | addressees
  | others
  deriving DecidableEq, Repr, Fintype

/-- The predecessor of a layered set: `Pred Sᵢ₊ᵤ = Sᵢ`, `Pred Sᵢ₊ᵤ₊ₒ = Sᵢ₊ᵤ`. -/
def Region.pred : Region → Option Region
  | .siuo => some .siu
  | .siu => some .si
  | _ => none

/-- The two privative person features. -/
inductive Feature
  | prox
  | dist
  deriving DecidableEq, Repr, Fintype

/-- `PROX S = Pred S` discards, and `DIST S = S − Pred S` selects, the outermost layer of a
layered set; neither applies to an unlayered one. -/
def Feature.apply : Feature → Region → Option Region
  | .prox, r => r.pred
  | .dist, .siuo => some .others
  | .dist, .siu => some .addressees
  | .dist, _ => none

/-- A person feature structure: the features in order of application. -/
abbrev Spec := List Feature

/-- Apply the features in order to `Sᵢ₊ᵤ₊ₒ`; `none` when a feature meets an unlayered set. -/
def Spec.eval (fs : Spec) : Option Region :=
  fs.foldl (fun acc f => acc.bind f.apply) (some .siuo)

/-- Every feature structure is incoherent or selects one of the five regions. -/
theorem Spec.eval_mem (fs : Spec) :
    fs.eval = none ∨ fs.eval = some .siuo ∨ fs.eval = some .si ∨ fs.eval = some .siu ∨
      fs.eval = some .addressees ∨ fs.eval = some .others := by
  rcases h : fs.eval with _ | r
  · exact .inl rfl
  · cases r <;> simp

/-- The set of atoms a region denotes. -/
def denote : Region → Set α
  | .si => S.Si
  | .siu => S.Siu
  | .siuo => S.Siuo
  | .addressees => S.Siu \ S.Si
  | .others => S.Siuo \ S.Siu

theorem speaker_ne_addressee : S.speaker ≠ S.addressee := fun h =>
  S.addressee_notMem (h ▸ S.speaker_mem)

theorem speaker_mem_denote_si : S.speaker ∈ S.denote .si := S.speaker_mem

theorem speaker_mem_denote_siu : S.speaker ∈ S.denote .siu := S.Si_subset S.speaker_mem

theorem speaker_mem_denote_siuo : S.speaker ∈ S.denote .siuo :=
  S.Siu_subset S.speaker_mem_denote_siu

theorem addressee_mem_denote_addressees : S.addressee ∈ S.denote .addressees :=
  ⟨S.addressee_mem, S.addressee_notMem⟩

theorem speaker_notMem_denote_addressees : S.speaker ∉ S.denote .addressees := fun h =>
  h.2 S.speaker_mem

theorem speaker_notMem_denote_others : S.speaker ∉ S.denote .others := fun h =>
  h.2 S.speaker_mem_denote_siu

theorem addressee_notMem_denote_others : S.addressee ∉ S.denote .others := fun h =>
  h.2 S.addressee_mem

/-- Every region but the others layer contains the speaker or the addressee. -/
theorem denote_nonempty {r : Region} (h : r ≠ .others) : (S.denote r).Nonempty := by
  cases r with
  | addressees => exact ⟨_, S.addressee_mem_denote_addressees⟩
  | others => exact absurd rfl h
  | si => exact ⟨_, S.speaker_mem_denote_si⟩
  | siu => exact ⟨_, S.speaker_mem_denote_siu⟩
  | siuo => exact ⟨_, S.speaker_mem_denote_siuo⟩

/-- The others layer can be empty. -/
theorem exists_denote_others_eq_empty {a b : α} (hab : a ≠ b) :
    ∃ S : PersonSpace α, S.denote .others = ∅ :=
  ⟨⟨a, b, {a}, {a, b}, {a, b}, rfl, by simp, by simpa using hab.symm, by simp, subset_rfl⟩,
    by simp [denote]⟩

/-- `Sᵢ₊ᵤ` has two obligatory members, the speaker and an addressee. -/
theorem nontrivial_denote_siu : (S.denote .siu).Nontrivial :=
  ⟨_, S.speaker_mem_denote_siu, _, S.addressee_mem, S.speaker_ne_addressee⟩

/-- The whole space has two obligatory members. -/
theorem nontrivial_denote_siuo : (S.denote .siuo).Nontrivial :=
  ⟨_, S.speaker_mem_denote_siuo, _, S.Siu_subset S.addressee_mem, S.speaker_ne_addressee⟩

/-- Plural is defined on an output of the person system with more than one member, and not on
the whole space. -/
def PluralDefined (r : Region) : Prop := r ≠ .siuo ∧ (S.denote r).Nontrivial

theorem not_pluralDefined_siuo : ¬ S.PluralDefined .siuo := fun h => h.1 rfl

theorem not_pluralDefined_of_eq_empty {r : Region} (h : S.denote r = ∅) : ¬ S.PluralDefined r :=
  fun ⟨_, ⟨_, ha, _⟩⟩ => by simp [h] at ha

end PersonSpace

end Minimalist.Phi
