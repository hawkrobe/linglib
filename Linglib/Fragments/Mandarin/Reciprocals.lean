import Linglib.Data.UD.Basic
import Linglib.Morphology.Word
import Linglib.Syntax.Reciprocal

/-!
# Mandarin Reciprocal Fragment
[nordlinger-2023] [konig-kokutani-2006]

Mandarin uses a compound verb strategy for reciprocity: V-lái-V-qù
(V-come-V-go), expressing mutual back-and-forth action. This is a
verbal strategy (monovalent) and is distinct from the reflexive "zìjǐ".

Example: "dǎ-lái-dǎ-qù" (beat-come-beat-go = 'beat each other')
[nordlinger-2023] ex. 13.

The adverb "hùxiāng" ('mutually') can also mark reciprocity but is
not the primary morphosyntactic strategy.
-/

namespace Mandarin.Reciprocals

/-- Compound verb pattern for Mandarin reciprocals.
    The pattern is: V-lái-V-qù (V-come-V-go). -/
structure CompoundRecip where
  verb : String
  script : Option String := none
  deriving Repr, BEq

/-- Generate the compound reciprocal form. -/
def CompoundRecip.toForm (c : CompoundRecip) : String :=
  c.verb ++ "-lái-" ++ c.verb ++ "-qù"

/-- dǎ-lái-dǎ-qù — 'beat each other' ([nordlinger-2023] ex. 13). -/
def daLaiDaQu : CompoundRecip :=
  { verb := "dǎ", script := some "打来打去" }

/-- 互相 hùxiāng — adverb 'mutually'. -/
def huxiang : Word :=
  { form :="hùxiāng", cat := .ADV, features := {}}

/-- 自己 zìjǐ — reflexive pronoun (for contrast). -/
def ziji : Word :=
  { form :="zìjǐ", cat := .PRON, features := { person := some .third }}

/-- Compound reciprocal form is distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    daLaiDaQu.toForm ≠ ziji.form := by decide

open Reciprocal

/-- The V-lái-V-qù compound as a reciprocal marker (form derived from
    `daLaiDaQu`). The adverbial *hùxiāng* is outside the strategy
    vocabulary ([evans-2008]'s adverbial strategy). -/
def compound : ReciprocalMarker :=
  { form := daLaiDaQu.toForm, script := daLaiDaQu.script
  , strategy := .compoundVerb }

/-- Marker inventory. -/
def markers : List ReciprocalMarker := [compound]

end Mandarin.Reciprocals
