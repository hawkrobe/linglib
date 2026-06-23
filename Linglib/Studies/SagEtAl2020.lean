/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Construction

/-!
# Sag et al. (2020): the Aux-Initial (Subject-Auxiliary Inversion) construction
[sag-etal-2020] [sag-2010]

The **second paper-anchored consumer** of the SBCG construct type hierarchy
(`Syntax/HPSG/Construction.lean`). [sag-etal-2020] analyzes the English auxiliary system in
Sign-Based Construction Grammar; its **Aux-Initial Construction** ((39)) is a `headed-cxt` subtype —
a *sibling* of the filler-gap supertype `filler-head-cxt` — whose head daughter is an inverted
`[INV +]` word (an invertible finite auxiliary).

Following Fillmore (1999), aux-initial constructions share **no** semantics ([sag-etal-2020] fn. 34);
a particular SAI's clausal meaning comes only from cross-classification with the clausal dimension. So
the **interrogative SAI** ("Has Lee eaten apples?") is `aux-initial-cxt ⊓ interrogative-cl`, and a
worked construct inherits the inverted head (from `aux-initial-cxt`) *and* the question semantics (from
`interrogative-cl`) from one sort — by the *same* multiple-inheritance machinery as [sag-2010]'s
filler-gap constructions.

That two paper-anchored studies (this and `Studies/Sag2010.lean`) consume one construct hierarchy is
the justification for its theory-layer home. The aux-initial / inversion sort nodes and the `INV`
feature live in the substrate; the construction's own *principle* and worked constructs are here.

## Scope

The single distinguishing constraint modeled is the head's `[INV +]` value. The richer apparatus of
the paper — the `MTR`/`DTRS` `SYN` token-sharing of (39), the valence list `VAL`/`⊕` amalgamation, the
`AUX`/`GRAM` features, and the ellipsis interactions — is deferred, as are the other SAI subtypes
(polar-interrogative, exclamative, conditional inversion).
-/

namespace SagEtAl2020

open HPSG.RSRL HPSG.Construction

/-- The **Aux-Initial Construction** ([sag-etal-2020] (39)): the head daughter is an inverted
(`[INV +]`) word — an invertible finite auxiliary. Unlike the filler-gap constructions it carries no
shared semantics (Fillmore 1999, [sag-etal-2020] fn. 34); its clausal meaning comes only from
cross-classification. -/
def auxInitialPrinciple : Desc sig :=
  .imp (.sortAssign .colon .auxInitialCxt) (.sortAssign (.path [.HDDTR, .INV]) .invPlus)

/-- The filler-gap grammar of `Construction.lean` extended with the inversion construction. -/
def saiGrammar : Grammar sig := grammar ++ [auxInitialPrinciple]

/-- `aux-initial-cxt` is a sibling of `filler-head-cxt` under `headed-cxt`, and the interrogative SAI
cross-classifies it with `interrogative-cl` — the same machinery as [sag-2010]'s filler-gap
constructions, now for the second paper's construction. -/
theorem sai_cross_classify :
    ((Srt.auxInitialCxt ≤ .headedCxt) ∧ (Srt.fillerHeadCxt ≤ .headedCxt)) ∧
      ((Srt.interrogativeSAI ≤ .auxInitialCxt) ∧ (Srt.interrogativeSAI ≤ .interrogativeCl)) := by
  decide

/-! ### A worked interrogative SAI -/

/-- Entities of a worked aux-initial construct: the construct, its mother and (inverted) head daughter,
and the inversion- and semantic-value objects. (Aux-initial constructs have no filler daughter.) -/
inductive SAIEnt
  | cxt | mtr | hd | invE | semE
  deriving DecidableEq, Fintype, Repr

/-- A well-formed interrogative SAI (sort `interrogative-SAI`): inverted head, interrogative mother. -/
@[reducible] def goodInterrogativeSAI : Interpretation sig where
  U := SAIEnt
  S := fun
    | .cxt => .interrogativeSAI
    | .mtr => .sign | .hd => .sign
    | .invE => .invPlus
    | .semE => .question
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .INV, .hd => some .invE     -- head is [INV +]
    | .SEM, .mtr => some .semE    -- interrogative semantics, inherited from interrogative-cl
    | _, _ => none
  R := noRel

instance : Fintype goodInterrogativeSAI.U := inferInstanceAs (Fintype SAIEnt)
instance : DecidableEq goodInterrogativeSAI.U := inferInstanceAs (DecidableEq SAIEnt)

/-- The interrogative SAI satisfies the grammar — the inverted head (from `aux-initial-cxt`) and the
question semantics (from `interrogative-cl`) are both inherited from one sort, like [sag-2010]'s
filler-gap keystone but for the second paper's construction. -/
example : goodInterrogativeSAI.Models saiGrammar := by decide

/-- The inverted-head restriction binds: an aux-initial construct with an `[INV −]` head violates the
aux-initial principle. -/
@[reducible] def saiUninverted : Interpretation sig where
  U := SAIEnt
  S := fun
    | .cxt => .interrogativeSAI
    | .mtr => .sign | .hd => .sign
    | .invE => .invMinus    -- head not inverted
    | .semE => .question
  A := goodInterrogativeSAI.A
  R := noRel

instance : Fintype saiUninverted.U := inferInstanceAs (Fintype SAIEnt)
instance : DecidableEq saiUninverted.U := inferInstanceAs (DecidableEq SAIEnt)

example : ¬ saiUninverted.Models saiGrammar := by decide

end SagEtAl2020
