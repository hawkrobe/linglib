import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Prosody.Tree

/-!
# Prosodic words (ω)
[selkirk-1980] [nespor-vogel-1986] [liberman-prince-1977] [hayes-1995] [ito-mester-2009]
[mccarthy-prince-1993]

The canonical prosodic word ω: a **recursive, headed** constituent. Its daughters are
feet, **sub-words** (an ω-over-ω, the *extended prosodic word* / ω-adjunction of
[ito-mester-2009]), and stray (unfooted) syllables; one daughter is the distinguished
`head` (a constituent — a foot or a sub-word, never a stray). Recursion is **intrinsic
to ω** ([ito-mester-2009]; cf. [mccarthy-prince-1993]: ω, unlike the *intrinsic* foot and
syllable, is *extrinsic*/mapping-defined and so admits recursion), built directly into
the type — a single nested inductive over `List (Word.Daughter S)`.

Because the `head` is a constituent, the head-projection chain (`headFoot` →
`headSyllable`) bottoms out in a foot by construction, so the **minimal word**
([mccarthy-prince-1993]) — that an ω contains a foot — is a total function, not a
constraint. Foot binarity, exhaustive parsing, and `No-Recursion` are violable
constraints, *not* part of the type; ill-formed candidates (a footless ω, a stray under
φ) are exactly what a violable OT carrier (`Prosody.Tree`) represents, and `toProsTree`
re-represents this well-formed ω into that carrier.

## Main definitions

* `Word` — the recursive headed ω; `Word.Daughter` / `Word.Head` (foot / sub-ω / stray).
* `Word.headFoot` / `headSyllable` — the head-projection chain (the ω-DTE), recursive.
* `Word.daughters` / `feet` / `strays` — the daughter list and its foot/stray parts.
* `Word.recursionCount` — the `No-Recursion` violation count (ω-over-ω depth).
* `Word.toProsTree` — re-representation into `Prosody.Tree`, marking the head daughter.
-/

namespace Prosody

open Features.Prosody

/-! ### The recursive prosodic word -/

/-- The canonical prosodic word ω ([selkirk-1980]; [hayes-1995]; [ito-mester-2009]): a
    single nested inductive — a `head` constituent with `before`/`after` daughter lists,
    each daughter a foot, a sub-word (ω-over-ω), or a stray σ. -/
inductive Word (S : Type*) where
  | mk (before : List (Foot S ⊕ Word S ⊕ S)) (head : Foot S ⊕ Word S)
       (after : List (Foot S ⊕ Word S ⊕ S))
  deriving Repr

namespace Word
variable {S : Type*}

/-- A daughter of ω: a foot, a sub-word (ω-over-ω), or a stray (unfooted) σ. -/
abbrev Daughter (S : Type*) := Foot S ⊕ Word S ⊕ S
/-- The head of ω — a constituent (foot or sub-word), never a stray; this is what makes
    `headFoot` total and the minimal word hold by construction. -/
abbrev Head (S : Type*) := Foot S ⊕ Word S

@[match_pattern] def Daughter.foot (f : Foot S) : Daughter S := .inl f
@[match_pattern] def Daughter.sub  (w : Word S) : Daughter S := .inr (.inl w)
@[match_pattern] def Daughter.leaf (s : S)      : Daughter S := .inr (.inr s)
@[match_pattern] def Head.foot (f : Foot S) : Head S := .inl f
@[match_pattern] def Head.sub  (w : Word S) : Head S := .inr w

/-- The head viewed as a daughter (foot/sub, never a leaf). -/
def Head.toDaughter : Head S → Daughter S
  | Head.foot f => Daughter.foot f
  | Head.sub w  => Daughter.sub w

/-- All daughters in linear order (head included). -/
def daughters : Word S → List (Daughter S)
  | .mk before head after => before ++ Head.toDaughter head :: after

/-- The top-level feet (head foot included if the head is a foot). -/
def feet (w : Word S) : List (Foot S) :=
  w.daughters.filterMap (fun | Daughter.foot f => some f | _ => none)

/-- The stray (unfooted) syllables. -/
def strays (w : Word S) : List S :=
  w.daughters.filterMap (fun | Daughter.leaf s => some s | _ => none)

/-- A minimal ω consisting of a single foot. -/
def ofFoot (f : Foot S) : Word S := .mk [] (Head.foot f) []

/-! ### The head-projection chain (the ω-DTE) -/

/-- The head foot — descend the head chain through sub-words to the bottom foot. Total
    by construction (a `Head` is a constituent), so every ω contains a foot: this *is*
    the minimal word ([mccarthy-prince-1993]). -/
def headFoot : Word S → Foot S
  | .mk _ (Head.foot f) _ => f
  | .mk _ (Head.sub w) _  => headFoot w

/-- The ω-DTE: the primary-stressed syllable, the head σ of the head foot
    ([liberman-prince-1977]; the head chain projects to the bottom). -/
def headSyllable (w : Word S) : S := w.headFoot.headSyllable

/-! ### No-Recursion (ω-over-ω) -/

/-- The `No-Recursion` violation count ([ito-mester-2009]): the number of sub-word
    daughters, recursively — i.e. how many times ω is parsed into ω. The list-recursion
    aux is a local `where` (Lean can't auto-terminate recursion under `List.map`). -/
def recursionCount : Word S → Nat
  | .mk before head after => hRec head + lAux before + lAux after
where
  hRec : Head S → Nat
    | Head.foot _ => 0
    | Head.sub w  => 1 + recursionCount w
  lAux : List (Daughter S) → Nat
    | [] => 0
    | Daughter.sub w :: ds => 1 + recursionCount w + lAux ds
    | _ :: ds => lAux ds

/-! ### Re-representation into the prosodic tree -/

/-- Re-represent ω as a `Prosody.Tree` ([ito-mester-2009]): an `.ω` node over the
    daughters' subtrees, the **head** daughter marked `isHead` (the head foot via
    `Foot.toProsTree _ _ true`; a head sub-word recursively). Composes `Foot.toProsTree`. -/
def toProsTree (wt : S → Syllable.Weight) : Word S → Tree
  | .mk before head after => .node .om (lTree before ++ hTree head :: lTree after)
where
  hTree : Head S → Tree
    | Head.foot f => Foot.toProsTree wt f true
    | Head.sub w  => toProsTree wt w
  lTree : List (Daughter S) → List Tree
    | [] => []
    | d :: ds => dTree d :: lTree ds
  dTree : Daughter S → Tree
    | Daughter.foot f => Foot.toProsTree wt f
    | Daughter.sub w  => toProsTree wt w
    | Daughter.leaf s => .node (.syl (wt s) false) []

end Word

/-! ### Worked examples -/

-- A heavy monosyllabic stem foot, a flat ω over it, and an ω-over-ω (extended PWord).
private def stemFt : Foot Nat := Foot.monosyllable 2
private def innerW : Word Nat := .mk [] (Word.Head.foot stemFt) []
private def flatW  : Word Nat := .mk [Word.Daughter.leaf 1] (Word.Head.foot stemFt) []
private def recW   : Word Nat := .mk [Word.Daughter.leaf 1] (Word.Head.sub innerW) []

-- No-Recursion: the extended PWord scores one ω-over-ω; the flat ω scores zero.
example : flatW.recursionCount = 0 := by
  simp [flatW, Word.recursionCount, Word.recursionCount.hRec, Word.recursionCount.lAux]
example : recW.recursionCount = 1 := by
  simp [recW, innerW, Word.recursionCount, Word.recursionCount.hRec, Word.recursionCount.lAux]

-- The head-projection chain descends to the stem foot's head σ (the ω-DTE).
example : recW.headSyllable = 2 := by
  simp [recW, innerW, Word.headSyllable, Word.headFoot, stemFt, Foot.headSyllable,
    Foot.monosyllable]
example : flatW.headSyllable = 2 := by
  simp [flatW, Word.headSyllable, Word.headFoot, stemFt, Foot.headSyllable, Foot.monosyllable]

end Prosody
