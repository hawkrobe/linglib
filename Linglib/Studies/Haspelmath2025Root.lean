import Mathlib.Order.WithBot
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.UD.Basic
import Linglib.Morphology.Construction.Sister
import Linglib.Morphology.Root.Basic
import Linglib.Morphology.Root.Consonantal

/-!
# Haspelmath (2025): Roots and root classes in comparative grammar

This file formalizes the definition of the root as a comparative concept in
[haspelmath-2025-root]. `IsRootIn` is definition (1): a contentful form (`Form`, a morph
with its meaning class) that occurs in a free form with no other contentful form, relative
to a fragment's free-form inventory. The qualifying clause separates roots from contentful
affixes (the Japanese causative `-ase`) and neoclassical combining forms (`geo-`), which
are morphological cores under the formal base definition of `Morphology/Root/Basic.lean`
but not roots; it admits bound roots (Sorbian `žon-`) and excludes free forms without a
lexical meaning (`hello`, fn. 10). Roots are concrete forms (§4), so the four Arabic forms
sharing the skeleton k-t-b are four roots (`arabic_four_roots`) and the German ablaut pair
`lauf` ~ `lief` two. `RootClass.upos` is (10), word classes as comparative concepts, and
`RootClass.unmarkedFunction` the prototypical combinations of (9).

§6 adopts the heterosemy view: `hammer` (noun) and `hammer` (verb) are two roots with one
shape (`hammer_two_roots`), related by the sister schemas of (21) (`nounVerbSisters`, on
`Morphology.Construction.Sister`), which the pair instantiates (`hammer_sisters`) and
`hammer`/`dance` does not.

## Implementation notes

* `Form` pairs a substrate `Morph`, the shape side, with an `Option RootClass` standing in
  for its meaning, which is all definition (1) and the lexical meaning of (11) need.
  Relatedness of meaning within a heterosemous root set is carried by the schema of (21),
  not by the forms.
* `IsStemIn` is the stem definition of fn. 6, with the Latin `laud-ab-` case.

## References

* [haspelmath-2025-root]
* [jackendoff-audring-2020]
-/

namespace Haspelmath2025Root

open Morphology

/-! ### Root classes (§5) -/

/-- The three root classes (§5): roots denoting actions, objects and properties, the
lexical meanings of (11). -/
inductive RootClass where
  | action
  | object
  | property
  deriving DecidableEq, Fintype, Repr

/-- (10): word classes as comparative concepts. A verb is an action-denoting root, a noun
an object-denoting root, an adjective a property-denoting root. -/
def RootClass.upos : RootClass → UD.UPOS
  | .action => .VERB
  | .object => .NOUN
  | .property => .ADJ

/-- The discourse functions of (9). -/
inductive DiscourseFunction where
  | predication
  | reference
  | modification
  deriving DecidableEq, Fintype, Repr

/-- (9): the discourse function in which a root class needs no function indicator: no
copula or verbalizer for action roots in predication, no nominalizer for object roots in
reference, no relativizer or genitive for property roots in modification. -/
def RootClass.unmarkedFunction : RootClass → DiscourseFunction
  | .action => .predication
  | .object => .reference
  | .property => .modification

/-! ### Definition (1) -/

/-- A form (§2, §4): a morph, the pairing of a shape with a meaning, recorded with its root
class when it denotes an action, an object or a property and `none` otherwise. -/
structure Form where
  /-- The morph. -/
  shape : Morph
  /-- The root class the form denotes, if any. -/
  meaning : Option RootClass
  deriving DecidableEq, Repr

/-- A form is contentful when it denotes an action, an object or a property (§2). -/
def Form.IsContentful (f : Form) : Prop := f.meaning ≠ none

instance (f : Form) : Decidable f.IsContentful := inferInstanceAs (Decidable (_ ≠ _))

/-- Definition (1): a root is a contentful form that can occur as part of a free form
without another contentful form. -/
def IsRootIn (freeForms : List (List Form)) (f : Form) : Prop :=
  f.IsContentful ∧ ∃ w ∈ freeForms, f ∈ w ∧ ∀ g ∈ w, g ≠ f → ¬ g.IsContentful

instance (freeForms : List (List Form)) (f : Form) : Decidable (IsRootIn freeForms f) :=
  inferInstanceAs (Decidable (_ ∧ ∃ w ∈ freeForms, _))

/-- A form is bound when it is not itself a free form (fn. 2). -/
def IsBoundIn (freeForms : List (List Form)) (f : Form) : Prop := [f] ∉ freeForms

instance (freeForms : List (List Form)) (f : Form) : Decidable (IsBoundIn freeForms f) :=
  inferInstanceAs (Decidable (_ ∉ _))

/-- The shapes of the forms of a word, for the formal definitions of
`Morphology/Root/Basic.lean`. -/
def shapes (w : List Form) : List Morph := w.map Form.shape

/-- Fn. 6: a stem is a contiguous string of at least one root and possibly some affixes that
can be combined with an affix. -/
def IsStemIn (words freeForms : List (List Form)) (s : List Form) : Prop :=
  (∃ f ∈ s, IsRootIn freeForms f) ∧
    (∀ f ∈ s, IsRootIn freeForms f ∨ f.shape.attachment? = some .affix) ∧
    ∃ w ∈ words, ∃ a ∈ w,
      a.shape.attachment? = some .affix ∧ (w = s ++ [a] ∨ w = a :: s)

instance (words freeForms : List (List Form)) (s : List Form) :
    Decidable (IsStemIn words freeForms s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ w ∈ words, ∃ a ∈ w, _))

/-! ### Contentful affixes and combining forms (§2) -/

/-- The Japanese action root `yom` 'read'. -/
def yom : Form := ⟨.root "yom", some .action⟩
/-- The Japanese causative suffix `-ase`, which denotes an action. -/
def ase : Form := ⟨.suff "ase", some .action⟩
/-- The Japanese nonpast suffix `-u`. -/
def u : Form := ⟨.suff "u", none⟩
/-- The Japanese nonpast suffix `-ru`. -/
def ru : Form := ⟨.suff "ru", none⟩

/-- The Japanese free forms `yom-u` 'read' and `yom-ase-ru` 'make read'. -/
def japanese : List (List Form) := [[yom, u], [yom, ase, ru]]

/-- §2: the causative `-ase` is contentful but never occurs without another contentful
form, so it is not a root, while `yom` is. -/
theorem ase_not_root : ase.IsContentful ∧ ¬ IsRootIn japanese ase ∧ IsRootIn japanese yom := by
  decide

/-- The neoclassical combining form `geo-`. -/
def geo : Form := ⟨.root "geo", some .object⟩
/-- The neoclassical combining form `-logy`. -/
def logy : Form := ⟨.root "logy", some .object⟩
/-- The English interjection `hello` (fn. 10). -/
def hello : Form := ⟨.free "hello", none⟩
/-- The English object root `hammer` (12a). -/
def hammerN : Form := ⟨.root "hammer", some .object⟩
/-- The English action root `hammer` (12b). -/
def hammerV : Form := ⟨.root "hammer", some .action⟩
/-- The English plural suffix. -/
def s : Form := ⟨.suff "s", none⟩
/-- The English past suffix. -/
def ed : Form := ⟨.suff "ed", none⟩

/-- English free forms: `geology`, `hello`, and the *hammer* forms. -/
def english : List (List Form) :=
  [[geo, logy], [hello], [hammerN], [hammerN, s], [hammerV], [hammerV, ed]]

/-- §2: `geo-` is contentful but only occurs with another contentful form, so it is not
a root, although it is a morphological core under the formal base definition. -/
theorem geo_not_root :
    ¬ IsRootIn english geo ∧
      geo.shape.IsCoreIn (english.map shapes) (english.map shapes) := by
  decide

/-- Fn. 10: `hello` is a free form without a lexical meaning, hence not a root, although
it is a morphological core. -/
theorem hello_not_root :
    ¬ IsRootIn english hello ∧
      hello.shape.IsCoreIn (english.map shapes) (english.map shapes) := by
  decide

/-- The Sorbian object root `žon-` 'wife'. -/
def žon : Form := ⟨.root "žon", some .object⟩
/-- The Sorbian nominative suffix. -/
def a : Form := ⟨.suff "a", none⟩
/-- The Sorbian genitive suffix. -/
def y : Form := ⟨.suff "y", none⟩
/-- The Sorbian accusative suffix. -/
def uAcc : Form := ⟨.suff "u", none⟩

/-- The Sorbian free forms `žon-a`, `žon-y`, `žon-u` (§3). -/
def sorbian : List (List Form) := [[žon, a], [žon, y], [žon, uAcc]]

/-- §3, fn. 2: `žon-` always occurs with an inflectional affix, yet it is a root. -/
theorem žon_bound_root : IsRootIn sorbian žon ∧ IsBoundIn sorbian žon := by decide

/-! ### Roots as concrete forms (§4) -/

/-- The German action root `lauf` 'run'. -/
def lauf : Form := ⟨.root "lauf", some .action⟩
/-- The German ablaut root `lief` 'ran'. -/
def lief : Form := ⟨.root "lief", some .action⟩
/-- The German first-singular suffix. -/
def e : Form := ⟨.suff "e", none⟩
/-- The German plural and participial suffix. -/
def en : Form := ⟨.suff "en", none⟩
/-- The German participial prefix. -/
def ge : Form := ⟨.pref "ge", none⟩

/-- The German verb forms of (5): `lauf-e`, `lauf-en`, `lauf`, `ge-lauf-en`, `lief`. -/
def german : List (List Form) := [[lauf, e], [lauf, en], [lauf], [ge, lauf, en], [lief]]

/-- §4: with no replacive morphs, `lauf` and `lief` are two roots. -/
theorem lauf_lief_roots : IsRootIn german lauf ∧ IsRootIn german lief ∧ lauf ≠ lief := by
  decide

/-- The consonantal skeleton of a form: its shape with the vowels removed. -/
def skeleton (f : Form) : ConsonantalRoot Char :=
  ⟨f.shape.form.toList.filter (· ∉ ['a', 'i', 'u'])⟩

/-- The Arabic action root `katab` 'wrote'. -/
def katab : Form := ⟨.root "katab", some .action⟩
/-- The Arabic action root `ktub` 'write'. -/
def ktub : Form := ⟨.root "ktub", some .action⟩
/-- The Arabic object root `kaatib` 'writer'. -/
def kaatib : Form := ⟨.root "kaatib", some .object⟩
/-- The Arabic object root `kitaab` 'book'. -/
def kitaab : Form := ⟨.root "kitaab", some .object⟩
/-- The Arabic first-plural suffix. -/
def naa : Form := ⟨.suff "naa", none⟩
/-- The Arabic first-plural prefix. -/
def na : Form := ⟨.pref "na", none⟩

/-- The Arabic forms of (6): `katab-naa`, `na-ktub-u`, `kaatib`, `kitaab`. -/
def arabic : List (List Form) := [[katab, naa], [na, ktub, u], [kaatib], [kitaab]]

/-- §4: the forms of (6) contain four distinct roots sharing the skeleton k-t-b, which
is not itself a root. -/
theorem arabic_four_roots :
    (∀ f ∈ [katab, ktub, kaatib, kitaab],
        IsRootIn arabic f ∧ skeleton f = ⟨['k', 't', 'b']⟩) ∧
      [katab, ktub, kaatib, kitaab].Nodup := by
  decide

/-- The Latin action root `laud` 'praise'. -/
def laud : Form := ⟨.root "laud", some .action⟩
/-- The Latin imperfect suffix. -/
def ab : Form := ⟨.suff "ab", none⟩
/-- The Latin first-singular imperfect suffix. -/
def am : Form := ⟨.suff "am", none⟩
/-- The Latin first-singular present suffix. -/
def o : Form := ⟨.suff "o", none⟩

/-- The Latin forms `laud-o` 'I praise' and `laud-ab-am` 'I was praising'. -/
def latin : List (List Form) := [[laud, o], [laud, ab, am]]

/-- Fn. 6: `laud-ab-` is an imperfect stem, a root with a tense suffix that combines with a
person suffix. -/
theorem laudab_stem : IsStemIn latin latin [laud, ab] ∧ IsStemIn latin latin [laud] := by
  decide

/-! ### Heterosemy (§6) -/

/-- §6: `hammer` (noun) and `hammer` (verb) are two roots with one shape. -/
theorem hammer_two_roots :
    IsRootIn english hammerN ∧ IsRootIn english hammerV ∧
      hammerN ≠ hammerV ∧ hammerN.shape = hammerV.shape := by
  decide

/-- The tiers of the schemas of (18)–(21). -/
inductive Tier where
  | semantics
  | morphosyntax
  | phonology
  deriving DecidableEq, Fintype, Repr

/-- A tier value: a meaning, a word class, or a shape. -/
inductive Value where
  | meaning (m : String)
  | category (c : RootClass)
  | shape (s : String)
  deriving DecidableEq, Repr

/-- Tier values are discrete: a constant is dominated only by itself. -/
instance : PartialOrder Value where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h h' := h.trans h'
  le_antisymm _ _ h _ := h

instance : DecidableLE Value := λ a b => inferInstanceAs (Decidable (a = b))

/-- A tier description: a value, or `⊥` for an open variable. -/
abbrev Slot := WithBot Value

/-- (21a) `X (noun)`: an object meaning related to `X`, a noun, with the open shape `Y`. -/
def nounSchema : Construction.Schema Tier Slot where
  body
    | .semantics => ⊥
    | .morphosyntax => ↑(Value.category .object)
    | .phonology => ⊥
  opens := {.semantics, .phonology}

/-- (21b) `X (verb)`: doing in relation to `X`, a verb, with the open shape `Y`. -/
def verbSchema : Construction.Schema Tier Slot where
  body
    | .semantics => ⊥
    | .morphosyntax => ↑(Value.category .action)
    | .phonology => ⊥
  opens := {.semantics, .phonology}

/-- (21): the two sister schemas, linked at the shape `Y` (index 2). -/
def nounVerbSisters : Construction.Sister Tier Tier Slot where
  fst := nounSchema
  snd := verbSchema
  link t₁ t₂ := t₁ = .phonology ∧ t₂ = .phonology

/-- (20a): `hammer` (noun). -/
def hammerNoun : Tier → Slot
  | .semantics => ↑(Value.meaning "HAMMER")
  | .morphosyntax => ↑(Value.category .object)
  | .phonology => ↑(Value.shape "hæmər")

/-- (20b): `hammer` (verb). -/
def hammerVerb : Tier → Slot
  | .semantics => ↑(Value.meaning "HIT (WITH SOMETHING LIKE HAMMER)")
  | .morphosyntax => ↑(Value.category .action)
  | .phonology => ↑(Value.shape "hæmər")

/-- `dance` (verb), whose shape differs from `hammer`'s. -/
def danceVerb : Tier → Slot
  | .semantics => ↑(Value.meaning "DANCE")
  | .morphosyntax => ↑(Value.category .action)
  | .phonology => ↑(Value.shape "dæns")

/-- (20): the two *hammer* roots instantiate the sister schemas of (21) as a pair, their
shapes filled alike; neither is derived from the other or from an abstract root. -/
theorem hammer_sisters : nounVerbSisters.Pairs hammerNoun hammerVerb :=
  ⟨λ t => by cases t <;> decide, λ t => by cases t <;> decide,
    λ _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; rfl⟩

/-- `hammer` (noun) and `dance` (verb) instantiate the schemas but not as a pair: the
linked shapes differ. -/
theorem hammer_dance_not_sisters : ¬ nounVerbSisters.Pairs hammerNoun danceVerb :=
  λ h => by simpa [hammerNoun, danceVerb] using h.2.2 ⟨rfl, rfl⟩

end Haspelmath2025Root
