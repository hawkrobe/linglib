/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-!
# Gap amalgamation and islands in RSRL
[sag-2010] [bouma-malouf-sag-2001] [richter-2000]

The **list-valued `GAP` (SLASH) feature** of [sag-2010] §4 — whose amalgamation mechanism follows
[bouma-malouf-sag-2001] — formalized on the RSRL feature-structure substrate, with the model-theoretic
derivation of **islands** ([sag-2010] §5.1, (67)–(68)).

A `GAP` value is a genuine HPSG list — `elist` (empty) or `nelist` with `FIRST`/`REST` ([sag-2010]'s
`⟨…⟩` notation). The **filler-head construction** binds the head daughter's *first* gap (token identity
between the filler's category and `GAP|FIRST`) and **amalgamates the rest** onto the mother
(`MTR|GAP = HD-DTR|GAP|REST`) — so a clause with two undischarged gaps passes the second up, modeling
the overlapping F-G dependencies of [sag-2010] (53), (59).

**Islands fall out of this** rather than from a stipulated Subjacency. An *island* construction (e.g.
topicalization, [sag-2010] (67)) additionally constrains its mother to `[GAP ⟨⟩]` (`elist`). Combined
with amalgamation, this forces the head daughter's `GAP|REST` to be empty — i.e. the head has *exactly
one* gap, the one the filler binds. A would-be **second** gap passing through the island makes the
amalgamated mother `GAP` non-empty, contradicting `[GAP ⟨⟩]`, so the construct is rejected. That is the
model-theoretic content of "topicalization is an absolute extraction island" — a theorem about the
`Models` relation, not a universal locality principle.

## Scope

`GAP` elements are bare categories (not full local objects); the worked lists are length ≤ 2; the
wh/rel exception to the filler↔gap identity, the lexical ARG-ST→DEPS→SLASH amalgamation of
[bouma-malouf-sag-2001] (modeled here only at the construction level), and weak/relativized islands are
deferred. Decidability stays inside `Models` over fixed finite interpretations (Kepser 2004).
-/

namespace HPSG.GapAmalgamation

open HPSG.RSRL

/-! ### Sorts: categories, `GAP` lists, signs, and the filler-head / island constructs -/

/-- Sorts: categories (`cat > {nominal-cat, prep-cat}`, the NP/PP distinction weak islands are
sensitive to), the `GAP`-list sorts (`list > {elist, nelist}`), `sign`, and the construct types
(`{island-cxt, weak-island-cxt} < filler-head-cxt < construct`). -/
inductive GSort
  | top
  | cat | nominalCat | prepCat
  | list | elist | nelist
  | sign
  | construct | fillerHeadCxt | islandCxt | weakIslandCxt
  deriving DecidableEq, Fintype, Repr

/-- Direct subsumption ("covers"): the `~|GSort|` **DAG edges** (a is *directly* more specific than b),
not the transitive closure. The order is `ReflTransGen gCovers`. -/
def gCovers : GSort → GSort → Bool
  | .cat, .top => true
  | .list, .top => true
  | .sign, .top => true
  | .construct, .top => true
  | .nominalCat, .cat => true
  | .prepCat, .cat => true
  | .elist, .list => true
  | .nelist, .list => true
  | .fillerHeadCxt, .construct => true
  | .islandCxt, .fillerHeadCxt => true
  | .weakIslandCxt, .fillerHeadCxt => true
  | _, _ => false

/-- Specificity depth; every covers edge strictly increases it (so `gCovers a b → gRank b < gRank a`),
giving antisymmetry. -/
def gRank : GSort → Nat
  | .top => 0
  | .cat => 1 | .list => 1 | .sign => 1 | .construct => 1
  | .elist => 2 | .nelist => 2 | .fillerHeadCxt => 2
  | .nominalCat => 2 | .prepCat => 2
  | .islandCxt => 3 | .weakIslandCxt => 3

instance : PartialOrder GSort :=
  partialOrderOfCovers (gCovers · · = true) gRank (by decide)

instance : DecidableLE GSort := fun a b =>
  decidableLEOfCovers (covers := (gCovers · · = true))
    [.top, .cat, .nominalCat, .prepCat, .list, .elist, .nelist, .sign,
     .construct, .fillerHeadCxt, .islandCxt, .weakIslandCxt]
    (by decide) a b

/-! ### Attributes and the signature -/

/-- Attributes: a construct's daughters (`MTR`/`HDDTR`/`FILLERDTR`); a sign's `CAT` and (list-valued)
`GAP`; a nonempty list's `FIRST` (a category) and `REST` (a list). -/
inductive GAttr
  | MTR | HDDTR | FILLERDTR | CAT | GAP | FIRST | REST
  deriving DecidableEq, Fintype, Repr

/-- Appropriateness: constructs have the three daughters; a sign has `CAT` (a category) and `GAP` (a
list); a `nelist` has `FIRST` (a category) and `REST` (a list); `elist` and categories are
attributeless. -/
def gApprop : GSort → GAttr → Option GSort
  | .construct, .MTR => some .sign
  | .construct, .HDDTR => some .sign
  | .construct, .FILLERDTR => some .sign
  | .fillerHeadCxt, .MTR => some .sign
  | .fillerHeadCxt, .HDDTR => some .sign
  | .fillerHeadCxt, .FILLERDTR => some .sign
  | .islandCxt, .MTR => some .sign
  | .islandCxt, .HDDTR => some .sign
  | .islandCxt, .FILLERDTR => some .sign
  | .weakIslandCxt, .MTR => some .sign
  | .weakIslandCxt, .HDDTR => some .sign
  | .weakIslandCxt, .FILLERDTR => some .sign
  | .sign, .CAT => some .cat
  | .sign, .GAP => some .list
  | .nelist, .FIRST => some .cat
  | .nelist, .REST => some .list
  | _, _ => none

private theorem gApprop_propagates : ∀ (σ₁ σ₂ : GSort) (α : GAttr),
    σ₂ ≤ σ₁ → (gApprop σ₁ α).isSome = true → gApprop σ₂ α = gApprop σ₁ α := by decide

/-- The gap-amalgamation signature (no relations). -/
@[reducible] def gSig : Signature GSort where
  Attr := GAttr
  Rel := Empty
  arity := fun e => e.elim
  approp := gApprop
  approp_inherits := fun hle happ => approp_inh_of_propagates gApprop_propagates hle happ

/-! ### Principles -/

/-- **Gap amalgamation** ([sag-2010] §4, (58); after [bouma-malouf-sag-2001]): in a filler-head
construct, the filler's category is token-identical to the head daughter's first gap (`GAP|FIRST` — the
bound dependency), and the mother's
`GAP` is the head daughter's `GAP|REST` (the remaining gaps pass up). -/
def amalgamationPrinciple : Desc gSig :=
  .imp (.sortAssign .colon .fillerHeadCxt)
    (.and (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP, .FIRST]))
      (.pathEq (.path [.MTR, .GAP]) (.path [.HDDTR, .GAP, .REST])))

/-- **Island constraint** ([sag-2010] (67)): an island construction's mother is `[GAP ⟨⟩]` — no
dependency penetrates beyond the one its filler binds. -/
def islandPrinciple : Desc gSig :=
  .imp (.sortAssign .colon .islandCxt) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- **Weak-island constraint**: a weak island is *selectively* permeable — an NP dependency passes
through, a PP (more generally, non-nominal) dependency does not ([sag-wasow-bender-2003] Ch. 15 on weak
islands; the `npOnly` case of the computational `GapRestriction`). Stated on the *passing* gap: if a
weak-island construct's mother `GAP|FIRST` is a `prep-cat`, the mother must be `[GAP ⟨⟩]` — so a PP
cannot penetrate, while a `nominal-cat` mother gap is unconstrained and passes. -/
def weakIslandPrinciple : Desc gSig :=
  .imp (.and (.sortAssign .colon .weakIslandCxt)
             (.sortAssign (.path [.MTR, .GAP, .FIRST]) .prepCat))
    (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- The grammar: amalgamation, the absolute-island and the weak-island constraints. -/
def gGrammar : Grammar gSig := [amalgamationPrinciple, islandPrinciple, weakIslandPrinciple]

/-! ### Worked constructs

Entities: the construct, its mother and two daughters, two list cells, the empty list, and two
categories. A `GAP` list `⟨c₁, c₂⟩` is `cell1[FIRST c₁, REST cell2]`, `cell2[FIRST c₂, REST nilE]`. -/

/-- Entities of the worked constructs. -/
inductive GEnt
  | cxt | mtr | hd | fl | cell1 | cell2 | nilE | c1 | c2
  deriving DecidableEq, Fintype, Repr

/-- Common species assignment: the two cells are `nelist`, `nilE` is `elist`, `c1`/`c2` categories. -/
private def baseS : GEnt → GSort
  | .mtr => .sign | .hd => .sign | .fl => .sign
  | .cell1 => .nelist | .cell2 => .nelist | .nilE => .elist
  | .c1 => .cat | .c2 => .cat
  | .cxt => .fillerHeadCxt

/-- A single-gap filler-head construct: head `GAP ⟨c₁⟩`, filler binds `c₁`, mother `GAP ⟨⟩`. -/
def goodSingleGap : Interpretation gSig where
  U := GEnt
  S := baseS
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .GAP, .hd => some .cell1
    | .FIRST, .cell1 => some .c1
    | .REST, .cell1 => some .nilE     -- head GAP = ⟨c₁⟩
    | .CAT, .fl => some .c1            -- filler binds the gap
    | .GAP, .mtr => some .nilE         -- mother GAP = REST = ⟨⟩
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodSingleGap.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq goodSingleGap.U := inferInstanceAs (DecidableEq GEnt)

example : goodSingleGap.Models gGrammar := by decide

/-- **Amalgamation of overlapping dependencies** ([sag-2010] (53), (59)): a head with two gaps
`⟨c₁, c₂⟩`; the filler binds `c₁` and the second gap `c₂` passes up — the mother's `GAP` is `⟨c₂⟩`. -/
def goodTwoGap : Interpretation gSig where
  U := GEnt
  S := baseS
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .GAP, .hd => some .cell1
    | .FIRST, .cell1 => some .c1
    | .REST, .cell1 => some .cell2    -- head GAP = ⟨c₁, c₂⟩
    | .FIRST, .cell2 => some .c2
    | .REST, .cell2 => some .nilE
    | .CAT, .fl => some .c1            -- filler binds the first gap
    | .GAP, .mtr => some .cell2        -- mother GAP = ⟨c₂⟩ (the second dependency)
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodTwoGap.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq goodTwoGap.U := inferInstanceAs (DecidableEq GEnt)

example : goodTwoGap.Models gGrammar := by decide

/-- A single-gap **island** construct (sort `island-cxt`): the one gap is bound, the mother is
`[GAP ⟨⟩]`, consistent with the island constraint. -/
def goodIsland : Interpretation gSig where
  U := GEnt
  S := fun u => match u with | .cxt => .islandCxt | u => baseS u
  A := goodSingleGap.A
  R := fun e => e.elim

instance : Fintype goodIsland.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq goodIsland.U := inferInstanceAs (DecidableEq GEnt)

example : goodIsland.Models gGrammar := by decide

/-- **The island theorem** ([sag-2010] (67)–(68)). A *second* gap cannot penetrate an island: an
`island-cxt` construct with a two-gap head amalgamates a non-empty mother `GAP ⟨c₂⟩`, contradicting the
island's `[GAP ⟨⟩]` — so the construct is rejected. Topicalization is an absolute extraction island,
derived from the `[GAP ⟨⟩]` constraint plus amalgamation, not from Subjacency. -/
def islandTwoGap : Interpretation gSig where
  U := GEnt
  S := fun u => match u with | .cxt => .islandCxt | u => baseS u
  A := goodTwoGap.A
  R := fun e => e.elim

instance : Fintype islandTwoGap.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq islandTwoGap.U := inferInstanceAs (DecidableEq GEnt)

example : ¬ islandTwoGap.Models gGrammar := by decide

/-! ### Weak islands: the NP/PP asymmetry

A *weak* island (`weak-island-cxt`) is selectively permeable. The constructs below reuse the two-gap
amalgamation geometry of `goodTwoGap` — the filler binds the first gap, the second passes up — but the
passing gap's category decides whether it survives the weak-island constraint. -/

/-- **NP extraction through a weak island is licensed.** A weak-island construct whose passing
(second) gap is a `nominal-cat` amalgamates a non-empty mother `GAP ⟨NP⟩`; the weak-island antecedent
(`prep-cat` mother gap) is false, so the constraint is vacuous and the structure is well-formed. -/
def weakIslandNPGap : Interpretation gSig where
  U := GEnt
  S := fun u => match u with | .cxt => .weakIslandCxt | .c2 => .nominalCat | u => baseS u
  A := goodTwoGap.A
  R := fun e => e.elim

instance : Fintype weakIslandNPGap.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq weakIslandNPGap.U := inferInstanceAs (DecidableEq GEnt)

example : weakIslandNPGap.Models gGrammar := by decide

/-- **PP extraction through a weak island is blocked.** The same geometry with a `prep-cat` passing
gap makes the mother `GAP ⟨PP⟩`; the weak-island constraint then forces `[GAP ⟨⟩]`, contradicting the
non-empty mother gap — so the construct is rejected. The NP/PP asymmetry, derived from the constraint,
not stipulated. -/
def weakIslandPPGap : Interpretation gSig where
  U := GEnt
  S := fun u => match u with | .cxt => .weakIslandCxt | .c2 => .prepCat | u => baseS u
  A := goodTwoGap.A
  R := fun e => e.elim

instance : Fintype weakIslandPPGap.U := inferInstanceAs (Fintype GEnt)
instance : DecidableEq weakIslandPPGap.U := inferInstanceAs (DecidableEq GEnt)

example : ¬ weakIslandPPGap.Models gGrammar := by decide

end HPSG.GapAmalgamation
