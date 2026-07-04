/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Floating

/-!
# Lexical melodies: per-morpheme autosegmental contributions

A **melody** is one morpheme's underlying autosegmental contribution
([rolle-2018] §2.1 Def 1): tier elements and backbone slots, every one
sponsored by the same morpheme ([rolle-2018] §2.1.4; [wolf-2007]), plus
the lexical pre-linking ([pulleyblank-1986]) in melody-local coordinates.
Which elements are pre-linked is per-analysis data — a melody with no
links is [mccarthy-mullin-smith-2012]'s universally-unlinked underlying
form, while a partially linked one is [mcpherson-lamont-2026]'s stratal
`/M^H/`. In [rolle-2018] Table 1's vocabulary, a backbone slot `j` is
*valued* iff `Graph.IsLinkedLower j`, *unvalued* iff
`Graph.IsFloatingLower j`, and a tier element is *floating* iff
`Graph.IsFloatingUpper i` — the per-index predicates the `Graph`
substrate already provides.

A word's underlying form is the left-to-right `Graph.concat` fold of its
melodies ([jardine-heinz-2015] §5), and `FloatingForm.ofGraph` packages
it as a derivation input. This melody-concatenation view of
non-concatenative exponence is the Generalized Nonlinear Affixation
program — [bermudez-otero-2012]'s term; [bye-svenonius-2012] give the
programmatic statement (non-concatenative morphology as epiphenomenon
of deficient lexical entries); [zimmermann-2024] surveys. GEN's
compliance with Consistency of Exponence is
`FloatingForm.gen_preserves_morphemes`.

## Main definitions

* `Graph.melody` — one morpheme's tones, slots, and pre-links.
* `Graph.concatList` — the word: melodies folded by `Graph.concat`.
* `FloatingForm.ofGraph` — an underlying graph as a derivation input
  (surface mirrors underlying).
-/

namespace Autosegmental

variable {S T : Type*}

namespace Graph

/-- One morpheme's underlying autosegmental contribution ([rolle-2018]
    §2.1 Def 1): `tones` over `tbus`, every element sponsored by `m`,
    pre-linked by `links` in melody-local coordinates. -/
def melody (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) : Graph (TierSpec T) (SegSpec S) where
  upper := .ofList (tones.map fun t => { value := t, morpheme := m })
  lower := .ofList (tbus.map fun s => { seg := s, morpheme := m })
  links := links

@[simp] theorem melody_upper (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) :
    (melody m tones tbus links).upper
      = .ofList (tones.map fun t => { value := t, morpheme := m }) := rfl

@[simp] theorem melody_lower (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) :
    (melody m tones tbus links).lower
      = .ofList (tbus.map fun s => { seg := s, morpheme := m }) := rfl

@[simp] theorem melody_links (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) : (melody m tones tbus links).links = links := rfl

/-- Every tier element of a melody is sponsored by its morpheme. -/
theorem melody_upper_morpheme (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) {k : ℕ} (hk : k < tones.length) :
    ((melody m tones tbus links).upper.get? k).map TierSpec.morpheme = some m := by
  rw [melody_upper, LabeledTuple.ofList_get?]
  simp [hk]

/-- Every backbone slot of a melody is sponsored by its morpheme. -/
theorem melody_lower_morpheme (m : Morpheme) (tones : List T) (tbus : List S)
    (links : Finset Link) {j : ℕ} (hj : j < tbus.length) :
    ((melody m tones tbus links).lower.get? j).map SegSpec.morpheme = some m := by
  rw [melody_lower, LabeledTuple.ofList_get?]
  simp [hj]

/-- Left-to-right concatenation of a word's melodies ([jardine-heinz-2015]
    §5): tier juxtaposition with index-shifted links. -/
def concatList {α β : Type*} (gs : List (Graph α β)) : Graph α β :=
  gs.foldr concat empty

@[simp] theorem concatList_nil {α β : Type*} :
    concatList ([] : List (Graph α β)) = empty := rfl

@[simp] theorem concatList_cons {α β : Type*} (g : Graph α β) (gs : List (Graph α β)) :
    concatList (g :: gs) = g.concat (concatList gs) := rfl

end Graph

/-- Package an underlying graph as a derivation input: nothing deleted,
    surface links mirror the underlying links. -/
def FloatingForm.ofGraph (g : Graph (TierSpec T) (SegSpec S)) : FloatingForm S T :=
  { g with deletedTier := ∅, surfaceLinks := g.links }

/-- `mkInput` is `ofGraph` of the corresponding raw graph. -/
theorem FloatingForm.mkInput_eq_ofGraph (lower : List (SegSpec S))
    (upper : List (TierSpec T)) (links : Finset Link) :
    mkInput lower upper links = ofGraph ⟨.ofList upper, .ofList lower, links⟩ := rfl

/-- **Consistency of Exponence** ([zimmermann-2024] §4): GEN never alters
    morphemic affiliation — every one-step candidate carries its input's
    sponsors on both tiers. -/
theorem FloatingForm.gen_preserves_morphemes [DecidableEq S] [DecidableEq T]
    (f : FloatingForm S T) : ∀ g ∈ f.gen,
    g.upperMorpheme? = f.upperMorpheme? ∧ g.lowerMorpheme? = f.lowerMorpheme? := by
  intro g hg
  simp only [FloatingForm.gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product] at hg
  rcases hg with rfl | ⟨k, _, rfl⟩ | ⟨⟨k, i⟩, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

end Autosegmental
