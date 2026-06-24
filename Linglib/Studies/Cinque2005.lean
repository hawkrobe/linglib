import Linglib.Syntax.Minimalist.Derivation

/-!
# Cinque 2005: Deriving Greenberg's Universal 20 [cinque-2005]

[cinque-2005] derives the cross-linguistic typology of the four DP-internal
elements **demonstrative, numeral, adjective, noun** from a single universal
Merge order plus constrained phrasal movement:

- **Universal Merge order** `[ Dem [ Num [ A [ NP ]]]]` (Dem > Num > A > N), the
  same for every language — the prenominal order of [greenberg-1963]'s Universal
  20.
- **Movement**: only the NP, or an XP *containing* the NP, raises leftward,
  Spec-to-Spec, around the modifiers (with/without pied-piping; total/partial).
  No movement of a phrase not containing the NP (no remnant movement).

Of the 4! = 24 logically possible orders, exactly **14 are attested** and all 14
are derivable; the 10 unattested are exactly the underivable ones (each would
require a *wrong Merge order* of the modifiers).

## What this file establishes

This study runs Cinque's derivations on the **real MCB Merge substrate**
(`Syntax/Minimalist/Derivation.lean`): each order is a `Derivation` (fixed-order
External Merge to build the base, then `Step.im` leftward movements), and the
surface order is read off by the computable `Derivation.surfaceCats`
(derivation-grounded externalization — MCB σ_L, not `Quot.out`). The orders are
verified by `decide`.

**Eight of the fourteen attested orders are derived explicitly here** (the
bare-NP-raising series a–d and the pied-piping cases n, o, t, x), demonstrating
the mechanism end-to-end on the substrate. The full enumeration of the legal
derivation space proves **reachable = exactly the 14 attested** (so the 10
unattested are underivable: `u20_reachable_iff_attested`). The
markedness-tracks-frequency result ([cinque-2005] (7b)) is the final section.

## Encoding note

The substrate `Cat` enum has `.Num`, `.A`, `.N` but no dedicated demonstrative
constructor, so **`.D` encodes the demonstrative slot** here. A dedicated
`Cat.Dem` (with its extended-projection F-level and ±V/±N features) is a deferred
substrate refinement; it does not affect the combinatorial result, which only
needs four distinct categories.
-/

namespace Cinque2005

open Minimalist

/-! ### The four elements (head-initial leaves) -/

/-- Noun (the raising NP). -/
def noun : SyntacticObject := mkLeaf .N [] 1
/-- Adjective. -/
def adj : SyntacticObject := mkLeaf .A [] 2
/-- Numeral. -/
def numl : SyntacticObject := mkLeaf .Num [] 3
/-- Demonstrative (encoded as `.D`; see module note). -/
def dem : SyntacticObject := mkLeaf .D [] 4

/-! ### Frequency buckets and the 24-order attestation table ([cinque-2005] (6))

Transcribed from the paper. `√` rows are attested; `*` rows unattested. Frequency
is the paper's cross-linguistic bucket (number of languages instantiating the
order). `.D` stands for the demonstrative. -/

/-- Cross-linguistic frequency of an order ([cinque-2005] (6)). -/
inductive Freq | veryMany | many | few | veryFew | unattested
  deriving DecidableEq, Repr

/-- One row of Cinque's typology table: an order of {Dem,Num,A,N}, whether it is
    attested, and its frequency bucket. -/
structure OrderRow where
  order : List Cat
  attested : Bool
  freq : Freq
  deriving DecidableEq, Repr

/-- [cinque-2005] table (6), rows a–x. -/
def table : List OrderRow :=
  [ ⟨[.D, .Num, .A, .N], true,  .veryMany⟩   -- a
  , ⟨[.D, .Num, .N, .A], true,  .many⟩       -- b
  , ⟨[.D, .N, .Num, .A], true,  .veryFew⟩    -- c
  , ⟨[.N, .D, .Num, .A], true,  .few⟩        -- d
  , ⟨[.Num, .D, .A, .N], false, .unattested⟩ -- e
  , ⟨[.Num, .D, .N, .A], false, .unattested⟩ -- f
  , ⟨[.Num, .N, .D, .A], false, .unattested⟩ -- g
  , ⟨[.N, .Num, .D, .A], false, .unattested⟩ -- h
  , ⟨[.A, .D, .Num, .N], false, .unattested⟩ -- i
  , ⟨[.A, .D, .N, .Num], false, .unattested⟩ -- j
  , ⟨[.A, .N, .D, .Num], true,  .veryFew⟩    -- k
  , ⟨[.N, .A, .D, .Num], true,  .few⟩        -- l
  , ⟨[.D, .A, .Num, .N], false, .unattested⟩ -- m
  , ⟨[.D, .A, .N, .Num], true,  .veryFew⟩    -- n
  , ⟨[.D, .N, .A, .Num], true,  .many⟩       -- o
  , ⟨[.N, .D, .A, .Num], true,  .veryFew⟩    -- p
  , ⟨[.Num, .A, .D, .N], false, .unattested⟩ -- q
  , ⟨[.Num, .A, .N, .D], true,  .veryFew⟩    -- r
  , ⟨[.Num, .N, .A, .D], true,  .few⟩        -- s
  , ⟨[.N, .Num, .A, .D], true,  .few⟩        -- t
  , ⟨[.A, .Num, .D, .N], false, .unattested⟩ -- u
  , ⟨[.A, .Num, .N, .D], false, .unattested⟩ -- v
  , ⟨[.A, .N, .Num, .D], true,  .veryFew⟩    -- w
  , ⟨[.N, .A, .Num, .D], true,  .veryMany⟩ ] -- x

/-- [cinque-2005]: exactly 14 of the 24 orders are attested. -/
theorem attested_count : (table.filter (·.attested)).length = 14 := by decide

/-- The 10 unattested orders. -/
theorem unattested_count : (table.filter (¬ ·.attested)).length = 10 := by decide

/-- Every attested order is `.unattested`-free; every unattested order has freq
    `.unattested` (table internal consistency). -/
theorem table_freq_consistent :
    table.all (fun r => r.attested = (r.freq ≠ .unattested)) := by decide

/-! ### Derivations on the MCB substrate

Built bottom-up: `initial := noun`, then head-initial External Merge of A, Num,
Dem (`emL`), interleaved with `Step.im` leftward raising. `surfaceCats` reads off
the order via the computable derivation-grounded externalization.

Movers: a bare NP raise passes `noun`; a pied-piping raise passes the
NP-containing constituent (which contains the earlier traces). -/

/-- (a) Dem Num A N — no movement. -/
def derA : Derivation := { initial := noun, steps := [.emL adj, .emL numl, .emL dem] }

/-- (b) Dem Num N A — NP raises around A (bare). -/
def derB : Derivation :=
  { initial := noun, steps := [.emL adj, .im noun 1, .emL numl, .emL dem] }

/-- (c) Dem N Num A — NP raises around A then Num (partial, bare). -/
def derC : Derivation :=
  { initial := noun, steps := [.emL adj, .im noun 1, .emL numl, .im noun 2, .emL dem] }

/-- (d) N Dem Num A — NP raises around A, Num, Dem (total, bare). -/
def derD : Derivation :=
  { initial := noun
    steps := [.emL adj, .im noun 1, .emL numl, .im noun 2, .emL dem, .im noun 3] }

/-- (n) Dem A N Num — pied-pipe `[A N]` around Num (no sub-raise). -/
def derN : Derivation :=
  { initial := noun, steps := [.emL adj, .emL numl, .im (adj * noun) 2, .emL dem] }

/-- (o) Dem N A Num — raise N around A, then pied-pipe `[N A]` around Num. -/
def derO : Derivation :=
  { initial := noun
    steps := [.emL adj, .im noun 1, .emL numl, .im (noun * (adj * mkTrace 1)) 2, .emL dem] }

/-- (t) N Num A Dem — bare raise around A and Num, then pied-pipe `[N Num A]`
    around Dem. -/
def derT : Derivation :=
  { initial := noun
    steps := [.emL adj, .im noun 1, .emL numl, .im noun 2, .emL dem,
              .im (noun * (numl * (mkTrace 2 * (adj * mkTrace 1)))) 3] }

/-- (x) N A Num Dem — successive pied-piping all the way up (the roll-up). -/
def derX : Derivation :=
  { initial := noun
    steps := [.emL adj, .im noun 1, .emL numl, .im (noun * (adj * mkTrace 1)) 2,
              .emL dem, .im ((noun * (adj * mkTrace 1)) * (numl * mkTrace 2)) 3] }

/-! ### The eight derivations produce their attested orders (kernel-checked) -/

theorem derA_order : derA.surfaceCats = [.D, .Num, .A, .N] := by decide
theorem derB_order : derB.surfaceCats = [.D, .Num, .N, .A] := by decide
theorem derC_order : derC.surfaceCats = [.D, .N, .Num, .A] := by decide
theorem derD_order : derD.surfaceCats = [.N, .D, .Num, .A] := by decide
theorem derN_order : derN.surfaceCats = [.D, .A, .N, .Num] := by decide
theorem derO_order : derO.surfaceCats = [.D, .N, .A, .Num] := by decide
theorem derT_order : derT.surfaceCats = [.N, .Num, .A, .D] := by decide
theorem derX_order : derX.surfaceCats = [.N, .A, .Num, .D] := by decide

/-- Each of the eight derived orders is an **attested** order in Cinque's table
    (the constructive half of Universal 20: these orders arise by NP-movement
    from the universal base). -/
theorem derived_orders_attested :
    [derA, derB, derC, derD, derN, derO, derT, derX].all
      (fun d => (table.filter (·.attested)).any (·.order = d.surfaceCats)) := by
  decide

/-! ### The restrictive result: reachable orders = exactly the 14 attested

The constructive theorems above derive specific attested orders. Here we
enumerate the **whole** legal derivation space and show its surface orders are
*exactly* the 14 attested ones — so the 10 unattested orders are **underivable**
(each would require a "wrong Merge order"; [cinque-2005], cf. Abels & Neeleman
2012's leftward-movement characterization).

The enumeration runs on the substrate's planar externalization type
`FreeMagma (LIToken ⊕ Nat)` (what `Derivation.externalizeP?` produces) with
`linearizePlanar` (the substrate's planar yield). Building the base bottom-up,
at each of the three specs (around A, Num, Dem) we optionally raise an
N-containing **proper** subtree to the left edge — leftward movement of an
N-containing constituent, no remnant movement. Fully computable; `decide`-checked. -/

private abbrev FM := FreeMagma (LIToken ⊕ Nat)
private def tokN : LIToken := ⟨.simple .N [], 1⟩
private def tokA : LIToken := ⟨.simple .A [], 2⟩
private def tokNum : LIToken := ⟨.simple .Num [], 3⟩
private def tokD : LIToken := ⟨.simple .D [], 4⟩
private def fmTr : FM := .of (.inr 0)

/-- Does the planar structure contain the noun leaf? -/
private def fmHasN : FM → Bool
  | .of (.inl t) => t == tokN
  | .of (.inr _) => false
  | .mul l r => fmHasN l || fmHasN r

/-- Eligible movers: N-containing proper subtrees (no remnant movement; can't
    raise the whole node to its own spec). Uses the shared planar-tree toolkit
    (`planarSubtrees`, `Syntax/Minimalist/Derivation.lean`). -/
private def fmMovers (cur : FM) : List FM :=
  (planarSubtrees cur).filter (fun s => fmHasN s && s != cur)

/-- At a spec: keep, or raise one eligible mover (leftward, via the shared
    `planarMoveLeft`). -/
private def fmOpt (cur : FM) : List FM :=
  cur :: (fmMovers cur).filterMap (fun s => planarMoveLeft (· == s) fmTr cur)

/-- The whole legal derivation space (planar externalizations): merge A, Num, Dem
    head-initially with an optional raise at each spec. -/
private def space : List FM :=
  ([(.of (.inl tokN) : FM)].map (fun c => .mul (.of (.inl tokA)) c)).flatMap fmOpt
    |>.map (fun c => .mul (.of (.inl tokNum)) c) |>.flatMap fmOpt
    |>.map (fun c => .mul (.of (.inl tokD)) c)   |>.flatMap fmOpt

/-- The distinct surface orders reachable by Cinque's movement. -/
def reachableOrders : List (List Cat) :=
  (space.map (fun fm => (linearizePlanar fm).map (·.item.outerCat))).eraseDups

/-- The 14 attested orders. -/
def attestedOrders : List (List Cat) := (table.filter (·.attested)).map (·.order)

/-- Exactly 14 orders are reachable. -/
theorem reachable_count : reachableOrders.length = 14 := by decide

/-- **Universal 20 (restrictive core):** an order is reachable by Cinque's
    constrained NP-movement **iff** it is attested — over all 24 orders. The 14
    attested are derivable; the 10 unattested are underivable. -/
theorem u20_reachable_iff_attested :
    table.all (fun r => decide (r.order ∈ reachableOrders) = r.attested) := by decide

/-- The reachable set is exactly the attested set. -/
theorem reachable_eq_attested :
    reachableOrders.all (· ∈ attestedOrders) ∧ attestedOrders.all (· ∈ reachableOrders) := by
  decide

/-! ### Markedness tracks frequency ([cinque-2005] (7b), (6))

Each derivable order has a count of **marked options** in its cheapest derivation.
Cinque's (7b) ranks the movement parameters: *no movement*, *whose-picture*
pied-piping, and *total* movement are **unmarked**; *partial* movement,
movement *without pied-piping*, and *picture-of-who* pied-piping are **marked**.
The counts below are transcribed from the per-order analysis (6a–6x). Cinque's
claim is that markedness **tracks** frequency — cleanly at the extremes (zero
marked options ⇒ most frequent; two ⇒ rarest), with a mixed one-marked-option
middle (the residual exceptions Universal 20 leaves; cf. the per-order footnotes). -/

/-- The number of marked movement options ([cinque-2005] (7b)) in the cheapest
    derivation of each **attested** order, transcribed from the per-order analysis
    (6a–6x); `none` for the 10 unattested orders (no derivation). (6p) is the
    paper's "especially marked"/possibly-spurious case (fn 27), encoded as 2. -/
def markedOptions : List Cat → Option Nat
  | [.D, .Num, .A, .N] => some 0   -- (6a) no marked option
  | [.D, .Num, .N, .A] => some 0   -- (6b) unmarked (vacuous whose-picture) deriv
  | [.D, .N, .Num, .A] => some 2   -- (6c) partial + without-pied-piping
  | [.N, .D, .Num, .A] => some 1   -- (6d) without-pied-piping (total)
  | [.A, .N, .D, .Num] => some 2   -- (6k) picture-of-who + without-pied-piping
  | [.N, .A, .D, .Num] => some 1   -- (6l) without-pied-piping past Dem
  | [.D, .A, .N, .Num] => some 2   -- (6n) partial + picture-of-who
  | [.D, .N, .A, .Num] => some 1   -- (6o) partial
  | [.N, .D, .A, .Num] => some 2   -- (6p) especially marked (fn 27)
  | [.Num, .A, .N, .D] => some 2   -- (6r) partial + picture-of-who
  | [.Num, .N, .A, .D] => some 2   -- (6s) partial + picture-of-who (fn 32)
  | [.N, .Num, .A, .D] => some 1   -- (6t) without-pied-piping (partial)
  | [.A, .N, .Num, .D] => some 1   -- (6w) picture-of-who
  | [.N, .A, .Num, .D] => some 0   -- (6x) successive whose-picture (roll-up)
  | _ => none

/-- Markedness is defined exactly on the derivable orders: every attested order
    has a marked-option count, every unattested order has none. -/
theorem markedOptions_isSome_iff_attested :
    table.all (fun r => (markedOptions r.order).isSome = r.attested) := by decide

/-- **Markedness predicts frequency at the extremes** ([cinque-2005] (6)–(7)):
    the most frequent orders (very many) are derivable with **no** marked option,
    and any order needing **two** marked options is rare (few / very few). The
    one-marked-option middle is mixed — Universal 20's residual exceptions. -/
theorem markedness_extremes :
    (table.filter (·.attested)).all (fun r =>
      (r.freq = .veryMany → markedOptions r.order = some 0) ∧
      (markedOptions r.order = some 2 → r.freq = .few ∨ r.freq = .veryFew)) := by
  decide

/-! ### TODO (follow-up)

A `Cat.Dem` constructor (replacing the `.D` stand-in) once its
extended-projection F-level / ±V±N features are settled — a substrate refinement
orthogonal to the combinatorial and markedness results above. -/

end Cinque2005
