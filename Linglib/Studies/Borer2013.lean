import Linglib.Morphology.Root.System
import Mathlib.Tactic.DeriveFintype

/-!
# Borer 2013: categorial flexibility and the adjective asymmetry
[borer-2013]

Roots as phonological indices realized in categorial frames, with no zero
categorizer heads: a bare root inserted in a nominal frame is N-equivalent,
in a verbal frame V-equivalent — categorization by environment, against
DM's merger with a (possibly null) categorizing head. On
`Morphology.Root.System` the exoskeletal claim fixes `Ctx` as the frame
itself, with no head in it; the DM rival puts a categorizer in `Ctx` — a
contrast in what instantiates `Ctx`, not in the shared core.

The book's categorial puzzle: noun-verb flexibility is systematic (*chair*,
*walk* occur in both frames with no added morphology), but adjectives do not
participate — property roots do not extend to nominal or verbal frames
(*to red*, *to fat* are out), and the verbal uses that do exist (*to thin*,
*to yellow*) are unpredictable and listed. Adjectives are complex and
derived, not bare roots in frames.

## Main results

* `english` — a mini root system over N/V/A frames.
* `nv_flexibility` — *chair* and *walk* are licensed in both the nominal and
  verbal frames.
* `adjective_rigidity` — *red* and *fat* are licensed in no frame beyond the
  adjectival one.
* `listedness` — *thin* and *red* are both property roots, yet only *thin*
  has a verbal cell: no frame-level generalization predicts the difference,
  so the verbal uses are listed.
-/

namespace Borer2013

open Morphology.Root

/-- The three categorial frames. -/
inductive Frame | nFrame | vFrame | aFrame
  deriving DecidableEq, Fintype, Repr

/-- The sample roots. -/
inductive Lex | chair | walk | red | fat | thin | yellow
  deriving DecidableEq, Fintype, Repr

/-- The mini English system: flexible *chair*/*walk*, frame-bound *red*/*fat*,
and the listed verbal uses of *thin*/*yellow*. -/
def english : System Lex Frame String where
  spellout := fun r c =>
    match r, c with
    | .chair, .nFrame => {"chair"}
    | .chair, .vFrame => {"chair"}
    | .walk, .nFrame => {"walk"}
    | .walk, .vFrame => {"walk"}
    | .red, .aFrame => {"red"}
    | .fat, .aFrame => {"fat"}
    | .thin, .aFrame => {"thin"}
    | .thin, .vFrame => {"thin"}
    | .yellow, .aFrame => {"yellow"}
    | .yellow, .vFrame => {"yellow"}
    | _, _ => ∅

/-- Noun-verb flexibility is systematic: the bare roots *chair* and *walk*
are licensed in both frames, with identical spellout — no zero head, no
added morphology. -/
theorem nv_flexibility :
    english.IsLicensed .chair .nFrame ∧ english.IsLicensed .chair .vFrame ∧
      english.IsLicensed .walk .nFrame ∧ english.IsLicensed .walk .vFrame := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The adjective asymmetry: *red* and *fat* occur in the adjectival frame
only — property roots do not extend to nominal or verbal frames. -/
theorem adjective_rigidity :
    ¬ english.IsLicensed .red .nFrame ∧ ¬ english.IsLicensed .red .vFrame ∧
      ¬ english.IsLicensed .fat .nFrame ∧ ¬ english.IsLicensed .fat .vFrame := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Listedness: *thin* and *red* are both adjectival-frame roots, yet only
*thin* has a verbal cell — the difference tracks no frame-level property, so
the verbal uses of *to thin*, *to yellow* are listed, not generated. -/
theorem listedness :
    english.IsLicensed .thin .aFrame ∧ english.IsLicensed .red .aFrame ∧
      english.IsLicensed .thin .vFrame ∧ ¬ english.IsLicensed .red .vFrame := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Borer2013
