import Linglib.Fragments.Mandarin.Verbs
import Linglib.Morphology.Word.Tree

/-!
# Mandarin resultative compounds

A Mandarin V-V resultative compound pairs a verb describing the causing event with a verb
describing its result: *dǎ-pò* 打破 'hit-break', *kū-lèi* 哭累 'cry-tired'. This file enters
the component verbs and the compounds built from them, so a compound's argument structure is
read off its verbs rather than stipulated: the result verb of every entry is monovalent, a
change-of-state verb such as *pò* 'break' or a stative such as *lèi* 'tired'
(`valency_v2`). Which argument the result is predicated of is not a property of the entry:
*zhuī-lèi* 'chase-tired' with an object is read with either the chaser or the chased tired,
so orientation belongs to a sentence, and the studies state it about the sentences they
analyze. Tay's account of the compounds as words built in morphology lives in
`Studies/Tay2024.lean`.

## Main definitions

* `Mandarin.Resultative` — a V-V resultative compound, its causing verb and its result verb.
* `Mandarin.Resultative.tree` — the compound as a root compound of its verbs.
* `Mandarin.resultatives` — the inventory of the entries.

## References

* [tay-2024]
-/

namespace Mandarin

open ArgumentStructure

/-! ### Component verbs -/

/-- 打 *dǎ* 'hit'. -/
def da : Verb := { form := "da", frames := [ArgumentFrame.np], vendlerClass := some .activity }

/-- 哭 *kū* 'cry'. -/
def ku : Verb :=
  { form := "ku", frames := [ArgumentFrame.intransitive], vendlerClass := some .activity }

/-- 吃 *chī* 'eat'. -/
def chi : Verb :=
  { form := "chi", frames := [ArgumentFrame.np, ArgumentFrame.intransitive],
    vendlerClass := some .activity }

/-- 喝 *hē* 'drink'. -/
def he : Verb :=
  { form := "he", frames := [ArgumentFrame.np, ArgumentFrame.intransitive],
    vendlerClass := some .activity }

/-- 推 *tuī* 'push'. -/
def tui : Verb :=
  { form := "tui", frames := [ArgumentFrame.np], vendlerClass := some .activity }

/-- 追 *zhuī* 'chase'. -/
def zhui : Verb :=
  { form := "zhui", frames := [ArgumentFrame.np], vendlerClass := some .activity }

/-- 射 *shè* 'shoot'. -/
def she : Verb :=
  { form := "she", frames := [ArgumentFrame.np], vendlerClass := some .activity }

/-- 破 *pò* 'break', intransitive. -/
def po : Verb :=
  { form := "po", frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement }

/-- 死 *sǐ* 'die'. -/
def si : Verb :=
  { form := "si", frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement }

/-- 开 *kāi* 'open', intransitive. -/
def kai : Verb :=
  { form := "kai", frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement }

/-- 累 *lèi* 'tired'. -/
def lei : Verb :=
  { form := "lei", frames := [ArgumentFrame.intransitive], vendlerClass := some .state }

/-- 饱 *bǎo* 'full'. -/
def bao : Verb :=
  { form := "bao", frames := [ArgumentFrame.intransitive], vendlerClass := some .state }

/-- 湿 *shī* 'wet'. -/
def shi : Verb :=
  { form := "shi", frames := [ArgumentFrame.intransitive], vendlerClass := some .state }

/-- 醉 *zuì* 'drunk'. -/
def zui : Verb :=
  { form := "zui", frames := [ArgumentFrame.intransitive], vendlerClass := some .state }

/-! ### Compounds -/

/-- A V-V resultative compound: a verb describing the causing event and a verb describing its
result. -/
structure Resultative where
  /-- The first verb, describing the causing event. -/
  v1 : Verb
  /-- The second verb, describing the result. -/
  v2 : Verb
  deriving BEq

/-- *dǎ-pò* 打破 'hit-break', 'break by hitting', Tay's (668). -/
def da_po : Resultative := ⟨da, po⟩

/-- *shè-sǐ* 射死 'shoot-die', 'shoot dead', Tay's (107). -/
def she_si : Resultative := ⟨she, si⟩

/-- *tuī-kāi* 推开 'push-open', Tay's (60). -/
def tui_kai : Resultative := ⟨tui, kai⟩

/-- *kū-lèi* 哭累 'cry-tired', 'cry oneself tired', Tay's (219). -/
def ku_lei : Resultative := ⟨ku, lei⟩

/-- *kū-shī* 哭湿 'cry-wet', 'become wet from crying', Tay's (221). -/
def ku_shi : Resultative := ⟨ku, shi⟩

/-- *zhuī-lèi* 追累 'chase-tired', read with either the chaser or the chased tired, Tay's (362)
after Li. -/
def zhui_lei : Resultative := ⟨zhui, lei⟩

/-- *chī-bǎo* 吃饱 'eat-full', 'become full from eating', Tay's (3). -/
def chi_bao : Resultative := ⟨chi, bao⟩

/-- *hē-zuì* 喝醉 'drink-drunk', 'drink oneself drunk', Tay's (360). -/
def he_zui : Resultative := ⟨he, zui⟩

/-- The inventory of the compounds. -/
def resultatives : List Resultative :=
  [da_po, she_si, tui_kai, ku_lei, ku_shi, zhui_lei, chi_bao, he_zui]

namespace Resultative

/-- The compound as a root compound of its two verbs. -/
def tree (c : Resultative) : Morphology.Word.Tree Verb := .compound (.root c.v1) (.root c.v2)

@[simp] theorem toList_tree (c : Resultative) : c.tree.toList = [c.v1, c.v2] := rfl

/-- The result verb of every compound is monovalent. -/
theorem valency_v2 : ∀ c ∈ resultatives, ∀ fr ∈ c.v2.frames, fr.valency = 1 := by decide

end Resultative

end Mandarin
