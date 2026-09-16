import Linglib.Syntax.Category.Verb.Basic

/-!
# Korean causative verbs

Korean has two causatives. The periphrastic *-ke ha-* 'make do' is purposive and not
implicative: *Keeho-ka Jinee-ka wus-ke ha-ess-ta* 'Keeho caused Jinee to smile' does not
entail that Jinee smiled. The morphological causative in *-i-* and its allomorphs is compact,
as in *cwuk-i-ta* 'kill' from *cwuk-ta* 'die', and entails the caused event.

## Main definitions

* `Korean.Verb` — a Korean verb, the root `Verb`
* `Korean.verbs` — the inventory

## References

* [song-1996]
-/

namespace Korean

open ArgumentStructure

/-- A Korean verb, the root entry with its citation form in *-ta*. -/
structure Verb extends _root_.Verb where
  deriving Repr, BEq

/-- *wus-ke ha-ta* 'cause to smile', the periphrastic causative. -/
def wus_ke_ha : Verb where
  form := "wus-ke ha-ta"
  frames := [Frame.infinitival]
  readings := [{ frame := Frame.infinitival, control := some .objectControl }]
  causative := some .cause

/-- *ilk-ke ha-ta* 'cause to read', the periphrastic causative. -/
def ilk_ke_ha : Verb where
  form := "ilk-ke ha-ta"
  frames := [Frame.infinitival]
  readings := [{ frame := Frame.infinitival, control := some .objectControl }]
  causative := some .cause

/-- *cwuk-i-ta* 'kill', the morphological causative of *cwuk-ta* 'die'. -/
def cwuk_i : Verb where
  form := "cwuk-i-ta"
  frames := [Frame.np]
  causative := some .make

/-- The inventory. -/
def verbs : List Verb := [wus_ke_ha, ilk_ke_ha, cwuk_i]

end Korean
