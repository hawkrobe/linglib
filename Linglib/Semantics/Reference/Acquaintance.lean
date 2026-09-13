/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Rigidity
import Mathlib.Data.Set.Function

/-!
# Conceptual covers

A *conceptual cover* is a set of concepts, intensions from an index type to a domain of
values, representing an agent's ways of identifying the values: the covers of [aloni-2001],
the acquaintance relations of [lewis-1979-attitudes] and [cresswell-vonstechow-1982] read
through the concept that identifies the res, the cover-relative belief of [dekker-2012], and
the time-concepts of [heim-1994-comments] and [abusch-1997] with contexts as indices and times
as values. A value is *acquainted* at an index when some concept in the cover picks it out
there (`Cover.Acquainted`, membership in an image), and a cover is *exhaustive* on a domain
when every value in it is picked out at every index (`Cover.IsExhaustiveOn`, `Set.SurjOn` at
each index). The name cover identifies each value of a domain by its constant concept
(`Cover.names`): its concepts are rigid (`Cover.isRigid_of_mem_names`), it is exhaustive on its
domain (`Cover.names_isExhaustiveOn`), and it acquaints with every value of the domain at every
index (`Cover.names_acquainted`).

## References

* [aloni-2001]
* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [heim-1994-comments]
* [abusch-1997]
* [dekker-2012]
-/

namespace Reference

/-- A conceptual cover: a set of concepts from indices to values. -/
abbrev Cover (Idx Res : Type*) : Type _ := Set (Idx → Res)

namespace Cover

variable {Idx Res : Type*} {C : Cover Idx Res} {dom : Set Res} {r : Res} {p : Idx}

/-- A cover is exhaustive on `dom` when at every index every value of `dom` is picked out by
some concept in it. -/
def IsExhaustiveOn (C : Cover Idx Res) (dom : Set Res) : Prop := ∀ p : Idx, Set.SurjOn (· p) C dom

/-- `r` is acquainted at `p` through `C` when some concept in `C` picks it out at `p`. -/
def Acquainted (C : Cover Idx Res) (r : Res) (p : Idx) : Prop := r ∈ (· p) '' C

/-- The name cover of a domain: each value identified by its constant concept. -/
def names (dom : Set Res) : Cover Idx Res := (λ r _ => r) '' dom

theorem isRigid_of_mem_names {c : Idx → Res} (h : c ∈ names dom) : IsRigid c := by
  obtain ⟨r, -, rfl⟩ := h
  exact isRigid_const r

theorem names_isExhaustiveOn : (names dom : Cover Idx Res).IsExhaustiveOn dom :=
  λ _ r hr => ⟨λ _ => r, ⟨r, hr, rfl⟩, rfl⟩

theorem names_acquainted (hr : r ∈ dom) : (names dom : Cover Idx Res).Acquainted r p :=
  ⟨λ _ => r, ⟨r, hr, rfl⟩, rfl⟩

end Cover

end Reference
