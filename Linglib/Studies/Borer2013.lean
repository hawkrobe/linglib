import Linglib.Morphology.Realization
import Mathlib.Tactic.DeriveFintype

/-!
# Borer 2013: categorizing roots and the adjective asymmetry

This file formalizes the categorial paradigm of [borer-2013]'s chapter on categorizing roots. A
root is a phonological index that a categorial frame realizes; the frame does the categorizing, so
nothing is added to the form when a root occurs as a noun rather than a verb. On
`Morphology.Realization` that fixes `Ctx` as the frame itself, with no head in it, where a
Distributed Morphology instance would put a categorizer there.

The paradigm is Borer's (120)–(121): √DANCE and √CHAIR are licensed in the verbal and nominal
frames but not the adjectival one, √GREEN and √BIG only in the adjectival frame. Her point is that
the asymmetry survives the question of zero categorizers — a theory that mediates categorization
through possibly-null category heads still has to rule these cells in and out one by one. Footnote
39 adds the residue: *thin* and *yellow*, but not *red* and *fat*, occur as verbs too, and since
nothing about their adjectival behaviour predicts which, the verbal uses must be listed.

## Main definitions

* `Root`, `Frame`, `licensed` — the roots and frames of (120)–(121) and footnote 39
* `english` — the frames as a `Realization`, each licensed root realized by its own index

## Main results

* `english_invariant` — no root has more than one exponent: the frame categorizes and adds nothing
* `adjectival_roots_are_rigid` — no root of the adjectival frame is licensed in the nominal one
* `nv_flexibility_systematic` — outside the adjectival roots, the nominal and verbal frames license
  exactly the same roots
* `verbal_use_unpredictable` — two adjectival roots agree everywhere but the verbal frame, so that
  cell is not a function of the rest of the paradigm and must be listed

## References

* [borer-2013]
-/

namespace Borer2013

open Morphology

/-- The categorial frames a root may be realized in. -/
inductive Frame | nFrame | vFrame | aFrame
  deriving DecidableEq, Fintype, Repr

/-- The roots of (120)–(121) and footnote 39. -/
inductive Root | dance | chair | green | big | thin | yellow | red | fat
  deriving DecidableEq, Fintype, Repr

/-- Which frames license which root: (120) for √DANCE and √CHAIR, (121) for √GREEN and √BIG, and
footnote 39 for the four property roots, of which only *thin* and *yellow* also occur as verbs. -/
def licensed : Root → Frame → Bool
  | .dance, .nFrame  | .dance, .vFrame  => true
  | .chair, .nFrame  | .chair, .vFrame  => true
  | .green, .aFrame  | .big, .aFrame    => true
  | .red, .aFrame    | .fat, .aFrame    => true
  | .thin, .aFrame   | .thin, .vFrame   => true
  | .yellow, .aFrame | .yellow, .vFrame => true
  | _, _ => false

/-- The exoskeletal system: where a frame licenses a root, the root is realized by its own
phonological index. Categorization is the frame's doing, so the form is the same in every frame
that licenses it. -/
def english : Realization Root Frame Root where
  realize r c := if licensed r c then {r} else ∅

@[simp] theorem isLicensed_iff (r : Root) (c : Frame) :
    english.IsLicensed r c ↔ licensed r c = true := by
  cases h : licensed r c <;> simp [Realization.IsLicensed, english, h]

instance (r : Root) (c : Frame) : Decidable (english.IsLicensed r c) :=
  decidable_of_iff _ (isLicensed_iff r c).symm

/-- No root has more than one exponent: a root occurring in two frames is spelled the same in both,
since the frame categorizes and no morphology is added. This is what distinguishes the exoskeletal
instance from one whose `Ctx` carries a categorizer. -/
theorem english_invariant (r : Root) : english.IsInvariant r := by
  intro c c' x hx x' hx'
  simp only [english] at hx hx'
  split at hx
  · split at hx' <;> simp_all
  · simp at hx

/-- (121b–c): a root licensed in the adjectival frame is licensed in neither of the others, save
for the listed verbal uses of footnote 39 — no adjectival root at all is licensed in the nominal
frame. -/
theorem adjectival_roots_are_rigid (r : Root) (h : english.IsLicensed r .aFrame) :
    ¬ english.IsLicensed r .nFrame := by
  revert h; cases r <;> decide

/-- (120b–c): outside the adjectival roots, noun-verb flexibility is systematic — the nominal and
verbal frames license exactly the same roots. -/
theorem nv_flexibility_systematic (r : Root) (h : ¬ english.IsLicensed r .aFrame) :
    english.IsLicensed r .nFrame ↔ english.IsLicensed r .vFrame := by
  revert h; cases r <;> decide

/-- (120a) and (121b): no root is licensed in all three frames — the categorial systems do not
fully overlap. -/
theorem no_root_in_all_frames (r : Root) :
    ¬ (english.IsLicensed r .nFrame ∧ english.IsLicensed r .vFrame ∧
        english.IsLicensed r .aFrame) := by
  cases r <;> decide

/-- Footnote 39: *thin* and *red* are alike in every frame but the verbal one, so a root's verbal
cell is not a function of the rest of its paradigm. The verbal uses of *to thin* and *to yellow*
cannot be predicted and must be listed. -/
theorem verbal_use_unpredictable :
    english.IsLicensed .thin .aFrame ∧ english.IsLicensed .red .aFrame ∧
      (english.IsLicensed .thin .nFrame ↔ english.IsLicensed .red .nFrame) ∧
      english.IsLicensed .thin .vFrame ∧ ¬ english.IsLicensed .red .vFrame := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The same holds of *yellow* against *fat*: the pair of listed verbs is not a class the paradigm
picks out. -/
theorem yellow_fat_unpredictable :
    english.IsLicensed .yellow .vFrame ∧ ¬ english.IsLicensed .fat .vFrame := by
  refine ⟨by decide, by decide⟩

end Borer2013
