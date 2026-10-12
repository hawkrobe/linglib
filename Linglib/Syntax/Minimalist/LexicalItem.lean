/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Notation
public import Linglib.Syntax.Minimalist.Category.Basic

/-!
# Lexical items

The leaves of syntactic objects are drawn from `SO₀`, the lexical items and syntactic features. A
lexical item is a category with its selectional stack, its phonological form and its [wh] and [E]
features, and a token of it is the item with the index that tells its tokens apart. The carrier
built over tokens is `SyntacticObject/Basic.lean`.

## Main definitions

* `Minimalist.LexicalItem`, `Minimalist.LexicalItem.Token`

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1)
* [merchant-2001]
-/

@[expose] public section

namespace Minimalist

/-- A lexical item is a category with its selectional stack, a phonological form, empty for a
silent item, and the [wh] and [E] features. -/
structure LexicalItem where
  /-- The category. -/
  cat : Cat
  /-- The selectional stack, consumed left to right. -/
  sel : SelStack
  /-- The phonological form, empty for a silent item. -/
  phonForm : String
  /-- The [wh] feature, read by wh-movement and the multiple-wh-fronting parameter. -/
  wh : Bool
  /-- The [E] feature, which leaves the head's complement unpronounced ([merchant-2001]). -/
  ellipsis : Bool
  deriving Repr, DecidableEq

/-- The lexical item of a category and selectional stack, silent and without [wh] or [E] unless
the optional arguments say otherwise. -/
def LexicalItem.of (cat : Cat) (sel : SelStack) (phonForm : String := "") (wh : Bool := false)
    (ellipsis : Bool := false) : LexicalItem :=
  ⟨cat, sel, phonForm, wh, ellipsis⟩

/-- The phonological form of a pronounced item, `none` for a silent one. -/
def LexicalItem.phonForm? (li : LexicalItem) : Option String :=
  if li.phonForm.isEmpty then none else some li.phonForm

/-- A token of a lexical item. Syntactic objects are compared as values, so two occurrences of
one item, the two *the*s of a transitive clause, are different leaves only through their tokens;
the index tells apart the tokens of one item, and tokens of different items differ anyway. -/
structure LexicalItem.Token where
  /-- The lexical item. -/
  item : LexicalItem
  /-- The index among the tokens of `item`. -/
  id : ℕ
  deriving Repr, DecidableEq

/-- The placeholder head of a bare trace, which remembers no token. Selection reads it as a
saturated silent noun, and its index lies above those lexical tokens use, so it equals none of
them. -/
def LexicalItem.Token.bareTrace : LexicalItem.Token := ⟨.of .N [], 10000⟩

end Minimalist
