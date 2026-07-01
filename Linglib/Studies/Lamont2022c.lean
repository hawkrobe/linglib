import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Constraints.Directional
import Linglib.Core.Optimization.Evaluation

/-!
# Lamont (2022): footing in directional Harmonic Serialism
[lamont-2022c]

[lamont-2022c] develops a theory of quantity-insensitive footing in Harmonic Serialism
(HS; [prince-smolensky-1993]) where CON contains only **directionally evaluated**
constraints ([lamont-2022b]; Eisner 2000): a constraint maps a candidate to a
per-position violation *vector*, and candidates are ordered lexicographically by the
*location* of violations rather than their total count. The central result is that
`Parse(σ)` — penalising unfooted syllables — under directional evaluation both motivates
iterative footing **and** decides where feet surface, obviating alignment constraints
([mccarthy-prince-1993]); having `Trochee`/`Iamb` penalise monosyllabic feet additionally
obviates `FtBin` ([martinez-paricio-kager-2015]).

This file formalises the central QI result. GEN parses **one foot per step**
([pruitt-2010]; [pruitt-2012]): a single unfooted σ into a monosyllabic foot, or two
adjacent unfooted σ into a disyllabic foot. We reuse the canonical `Prosody.Foot`
(`S = Unit`, since QI footing strips weight) assembled **flatly** — a footing is a
sequence of feet and stray syllables with no designated head foot, because Lamont does
not distinguish primary from secondary stress (so the headed `Prosody.Word` ω, which is
a footing *plus* a head foot, is deliberately *not* the candidate type here). `Parse(σ)`
is a `Constraints.directionalBlock` over σ-positions; `Trochee`/`Iamb` read the foot
head off `Foot.head`.

## Main results

* `murinbata_exhaustive` / `pintupi_inexhaustive` — the headline contrast: the same
  5σ step parses exhaustively under `Parse(σ) ≫ Trochee` ([street-mollinjin-1981]) but
  stays faithful (final σ unfooted) under `Trochee ≫ Parse(σ)` ([hansen-hansen-1969]).
* `ftbin_obviated` — a monosyllabic-foot candidate is harmonically bounded with no
  `FtBin` in CON ([martinez-paricio-kager-2015]).

## Deferred (prose)

The paper's bidirectional Waorani case study (§3 — a head foot at the right edge with
secondary feet built left-to-right) is its showcase and the natural next extension;
Macedonian (`Hd(ω)`/`NonFinality`), Garawa, and Cayuvava ternarity (`*FootFoot`) each
need further constraints; the software-computed factorial typology (§4) is a meta-claim,
not a per-string prediction. All are noted here, not formalised.
-/

namespace Lamont2022c

open Prosody Core.Optimization.Evaluation

/-! ### Footings

A footing here is the canonical `Prosody.Footing Unit` (quantity-insensitive, so feet
are `Foot Unit`): a flat sequence of feet and unfooted stray σ, no designated head foot
([lamont-2022c], abstracting from primary stress). `Parse(σ)` reads `Footing.strayMarks`;
`Trochee`/`Iamb` read each foot's head (`Foot.head`). -/

/-- A monosyllabic foot `(σ́)`. -/
def mono : Foot Unit := ⟨[()], 0⟩
/-- A (left-headed) trochee `(σ́σ)`. -/
def troch : Foot Unit := ⟨[(), ()], 0⟩
/-- A (right-headed) iamb `(σσ́)`. -/
def iamb : Foot Unit := ⟨[(), ()], 1⟩

/-! ### The directional constraints

`Parse(σ)` ([lamont-2022c] (10)) is a `Constraints.directionalBlock`: a per-position
block of binary constraints, `position i ↦ ⟦σ i is unfooted⟧`. `Trochee` (15) and
`Iamb` (18) penalise feet by head position — `Trochee` a foot whose head is rightmost
(= `Foot.IsIambic`, true of iambs and monosyllables), `Iamb` a foot whose head is
leftmost (= `Foot.IsTrochaic`, true of trochees and monosyllables); a monosyllabic foot
violates both, doing `FtBin`'s work. -/

/-- `Parse(σ)` as a directional block over `n` σ-positions. -/
def parse (n : Nat) : List (Constraints.Constraint (Footing Unit)) :=
  Constraints.directionalBlock n (fun (i : Fin n) (fc : Footing Unit) => (fc.strayMarks).getD i.val 0 = 1)

/-- `Trochee`: one violation per foot whose head is rightmost (= `Foot.IsIambic`). -/
def trochee (fc : Footing Unit) : Nat :=
  ((fc.feet).filter (fun f => decide f.IsIambic)).length
/-- `Iamb`: one violation per foot whose head is leftmost (= `Foot.IsTrochaic`). -/
def iambC (fc : Footing Unit) : Nat :=
  ((fc.feet).filter (fun f => decide f.IsTrochaic)).length

/-- The violation vector of a footing under a ranking (a list of constraints), as the
    concatenated per-constraint violations — ordered lexicographically (`LexLE`). -/
def profile (ranking : List (Constraints.Constraint (Footing Unit))) (fc : Footing Unit) : List Nat :=
  ranking.map (fun c => c fc)

/-- Murinbata ranking `Parse(σ) ≫ Trochee ≫ Iamb` ([street-mollinjin-1981]). -/
def murinbata (n : Nat) : List (Constraints.Constraint (Footing Unit)) :=
  parse n ++ [fun fc => trochee fc, fun fc => iambC fc]
/-- Pintupi ranking `Trochee ≫ Parse(σ) ≫ Iamb` ([hansen-hansen-1969]). -/
def pintupi (n : Nat) : List (Constraints.Constraint (Footing Unit)) :=
  (fun fc => trochee fc) :: parse n ++ [fun fc => iambC fc]

/-! ### The headline: exhaustive vs inexhaustive (the decisive step)

The same 5σ string at the step from `(σ́σ)(σ́σ)σ`: GEN can parse the final stray σ into
a monosyllabic foot (`exhaustive`) or leave it (`faithful`, converged). -/

/-- `(σ́σ)(σ́σ)σ` — two trochees and a final unfooted σ. -/
def faithful : Footing Unit := [.inl troch, .inl troch, .inr ()]
/-- `(σ́σ)(σ́σ)(σ́)` — the final σ parsed into a monosyllabic foot. -/
def exhaustive : Footing Unit := [.inl troch, .inl troch, .inl mono]

/-- **Murinbata** ([street-mollinjin-1981]): under `Parse(σ) ≫ Trochee`, the exhaustive
    parse wins — the final σ is footed into a monosyllable (final monosyllabic feet,
    exhaustive parsing). -/
theorem murinbata_exhaustive :
    LexLE (profile (murinbata 5) exhaustive) (profile (murinbata 5) faithful)
    ∧ ¬ LexLE (profile (murinbata 5) faithful) (profile (murinbata 5) exhaustive) := by decide

/-- **Pintupi** ([hansen-hansen-1969]): under `Trochee ≫ Parse(σ)`, the faithful parse
    wins — parsing a monosyllable would violate the dominant `Trochee`, so the final σ
    stays unfooted (inexhaustive parsing). The derivation has converged. -/
theorem pintupi_inexhaustive :
    LexLE (profile (pintupi 5) faithful) (profile (pintupi 5) exhaustive)
    ∧ ¬ LexLE (profile (pintupi 5) exhaustive) (profile (pintupi 5) faithful) := by decide

/-! ### Parsimony: `FtBin` is obviated

In even-parity `/σσσσ/`, the monosyllabic-foot candidate `(σ́)σσσ` is harmonically
bounded by the disyllabic `(σ́σ)σσ` under `Parse(σ) ≫ Trochee ≫ Iamb` — *without* any
`FtBin` in CON. `Trochee` and `Iamb` both penalising monosyllables do `FtBin`'s work
([martinez-paricio-kager-2015]). -/

/-- `(σ́σ)σσ` — one leftmost trochee in `/σσσσ/`. -/
def disyll4 : Footing Unit := [.inl troch, .inr (), .inr ()]
/-- `(σ́)σσσ` — one leftmost monosyllable in `/σσσσ/`. -/
def monosyll4 : Footing Unit := [.inl mono, .inr (), .inr (), .inr ()]

/-- **`FtBin` obviation**: the disyllabic-foot candidate strictly beats the
    monosyllabic-foot candidate with no `FtBin` in CON — the monosyllable both fails
    `Parse(σ)` more and violates `Trochee`. -/
theorem ftbin_obviated :
    LexLE (profile (murinbata 4) disyll4) (profile (murinbata 4) monosyll4)
    ∧ ¬ LexLE (profile (murinbata 4) monosyll4) (profile (murinbata 4) disyll4) := by decide

/-! ### The footing functor: head (= stress) survives into grid and tree

Lamont's `Trochee`/`Iamb` read each foot's head off `Foot.head`. Re-representing a foot
into the prosodic `Tree` (`Foot.toProsTree`) and the head-flag row (`Foot.headFlags`)
recovers *exactly* that head — `Foot.headFlags_toProsTree` proves the tree's σ-leaves
carry the same head profile — and the tree always lands in the well-formed
f/σ band (`Foot.isFoot_toProsTree`). So the head, the stress these constraints penalise,
survives both re-representations. QI footing strips weight, so the tree reads any
constant σ-weight. -/

/-- QI footing is weight-blind: a `Foot Unit`'s σ read one (light) mora. -/
def qiWeight : Unit → Syllable.Weight := fun _ => Syllable.Weight.light

/-- **Well-formedness through the functor**: every QI foot Lamont assembles re-represents
    as a well-formed prosodic-tree foot (`Foot.isFoot_toProsTree`) — the flat `Footing`
    candidates are built from feet that are legal `f`-over-σ subtrees of the OT `Tree`
    carrier. -/
theorem qiFeet_areFootTrees :
    IsFoot (mono.toProsTree qiWeight) ∧ IsFoot (troch.toProsTree qiWeight)
      ∧ IsFoot (iamb.toProsTree qiWeight) :=
  ⟨Foot.isFoot_toProsTree qiWeight mono, Foot.isFoot_toProsTree qiWeight troch,
   Foot.isFoot_toProsTree qiWeight iamb⟩

/-- **Head survives into flags and tree**: the head-flag row marks the foot head — leftmost
    for the trochee (the foot Lamont's `Iamb` penalises), rightmost for the iamb (the foot
    `Trochee` penalises) — and the prosodic tree carries the *same* head profile, reduced
    here through `Foot.headFlags_toProsTree`. The trochaic vs iambic stress survives the
    functor identically. -/
theorem head_survives :
    Foot.headFlags troch = [true, false] ∧ Foot.headFlags iamb = [false, true] := by
  rw [← Foot.headFlags_toProsTree qiWeight troch, ← Foot.headFlags_toProsTree qiWeight iamb]
  decide

end Lamont2022c
