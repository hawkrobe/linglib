/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Replace
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Substitution on syntactic objects

`SyntacticObject.replace s target replacement` substitutes every subterm of `s` equal to
`target` by `replacement`; it is `Nonplanar.replace` closed under well-formedness, which holds
because substitution preserves the arity of every vertex. The copy-theory use is
`s.replace mover traceLeaf`, leaving a trace where a mover was. This is a structural operation:
the Merge-algebraic Internal Merge is the coproduct composition of `Merge/Internal.lean`, with
traces as cut remainders and chains held at the workspace level, and `replace` supports the
transformational view that study files are written in. It is noncomputable; concrete cases
reduce by `replace_self`, `replace_node_of_ne`, and the leaf lemmas.

## Main definitions

* `Minimalist.SyntacticObject.replace`
-/

namespace Minimalist

open RoseTree RoseTree.Nonplanar SyntacticObject

/-- Substitution preserves well-formedness. -/
theorem isSO_replace (target replacement s : SyntacticObject) :
    IsSO (Nonplanar.replace target.val replacement.val s.val) := by
  induction s using ind with
  | lex tok =>
    rw [show (lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl, Nonplanar.replace_leaf]
    split
    · exact replacement.2
    · exact (lexLeaf tok).2
  | trace =>
    rw [show traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl, Nonplanar.replace_leaf]
    split
    · exact replacement.2
    · exact traceLeaf.2
  | node l r ihl ihr =>
    rw [node_val, Nonplanar.replace_node_pair]
    split
    · exact replacement.2
    · show isSO (Nonplanar.node (Sum.inr ())
        {Nonplanar.replace target.val replacement.val l.val,
          Nonplanar.replace target.val replacement.val r.val}) = true
      rw [isSO_node_pair, ihl, ihr]; rfl

namespace SyntacticObject

/-- Replace every subterm of `s` equal to `target` by `replacement`. -/
noncomputable def replace (s target replacement : SyntacticObject) : SyntacticObject :=
  ⟨Nonplanar.replace target.val replacement.val s.val, isSO_replace target replacement s⟩

@[simp] theorem replace_val (s target replacement : SyntacticObject) :
    (replace s target replacement).val = Nonplanar.replace target.val replacement.val s.val := rfl

@[simp] theorem replace_self (target replacement : SyntacticObject) :
    replace target target replacement = replacement :=
  Subtype.ext (by rw [replace_val, Nonplanar.replace_self])

/-- At a node other than the target, substitution recurses into both daughters. -/
theorem replace_node_of_ne {l r target replacement : SyntacticObject} (h : node l r ≠ target) :
    replace (node l r) target replacement
      = node (replace l target replacement) (replace r target replacement) := by
  apply Subtype.ext
  rw [replace_val, node_val, Nonplanar.replace_node_pair, if_neg, node_val, replace_val,
    replace_val]
  rw [← node_val]
  exact fun heq => h (Subtype.ext heq)

theorem replace_lexLeaf_of_ne {tok : LIToken} {target replacement : SyntacticObject}
    (h : lexLeaf tok ≠ target) : replace (lexLeaf tok) target replacement = lexLeaf tok := by
  apply Subtype.ext
  rw [replace_val, show (lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
      Nonplanar.replace_leaf, if_neg]
  exact fun heq => h (Subtype.ext heq)

theorem replace_traceLeaf_of_ne {target replacement : SyntacticObject}
    (h : traceLeaf ≠ target) : replace traceLeaf target replacement = traceLeaf := by
  apply Subtype.ext
  rw [replace_val, show traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
      Nonplanar.replace_leaf, if_neg]
  exact fun heq => h (Subtype.ext heq)

/-- Moving the daughter `r` out of `[l r]` and leaving a trace yields `[l′ t]`, with `l′` the
    substituted left daughter; a tree is never its own daughter, taken here as a hypothesis. -/
example (l r : SyntacticObject) (h : node l r ≠ r) :
    replace (node l r) r traceLeaf = node (replace l r traceLeaf) traceLeaf := by
  rw [replace_node_of_ne h, replace_self]

end SyntacticObject

end Minimalist
