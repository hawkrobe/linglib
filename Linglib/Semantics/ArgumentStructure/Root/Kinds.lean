import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Closure
import Mathlib.Tactic.DeriveFintype

/-!
# Root kind signatures

The four-feature vocabulary of [beavers-koontz-garboden-2020]'s root
typology (ch. 5): `LexKind` with the book's collocational order
(`state < result < cause`, `manner` isolated), and a root's **kind
signature** — the kinds of lexical entailment it carries — as a
`Finset LexKind`, so signatures inherit the Boolean lattice of finite
sets (`≤` is "carries at most these kinds"). Well-formedness is
downward-closedness in the collocational order, and `close` — the
induced lower closure, packaged as a mathlib `ClosureOperator` —
repairs any signature to a well-formed one.

This file is `Root`-free: consumers that map other objects to signatures
(e.g. Levin classes, the salience classifier) can import it without the
root substrate.

## Main declarations

* `LexKind`, with its collocational `PartialOrder`
* `Root.Kinds := Finset LexKind`
* `Root.Kinds.close`, `Root.Kinds.closeOp`, `Root.Kinds.WellFormed`
* canonical signatures (`propertyConcept`, `pureResult`,
  `causativeResult`, `pureManner`, `mannerResult`, `fullSpec`,
  `minimal`)
-/

namespace Verb

/-! ### Lexical entailment kinds -/

/-- The four kinds of lexical entailment of
    [beavers-koontz-garboden-2020]'s root typology. -/
inductive LexKind where
  | state
  | manner
  | result
  | cause
  deriving DecidableEq, Fintype, Repr

namespace LexKind

/-- Boolean table for the collocational order. -/
private def leB : LexKind → LexKind → Bool
  | .state,  .state  => true
  | .state,  .result => true
  | .state,  .cause  => true
  | .result, .result => true
  | .result, .cause  => true
  | .cause,  .cause  => true
  | .manner, .manner => true
  | _,       _       => false

/-- The collocational order of [beavers-koontz-garboden-2020]:
    `state < result < cause` (a cause presupposes a result, a result
    presupposes a state), with `manner` incomparable to the chain. -/
instance : PartialOrder LexKind where
  le a b := leB a b = true
  le_refl a := by cases a <;> rfl
  le_trans a b c := by revert a b c; decide
  le_antisymm a b := by revert a b; decide

instance : DecidableLE LexKind := fun _ _ => inferInstanceAs (Decidable (_ = true))

end LexKind

/-! ### Kind signatures -/

/-- A root kind signature: the set of entailment kinds carried.
    `≤` (= `⊆`) and the lattice operations come from `Finset`. -/
abbrev Root.Kinds := Finset LexKind

namespace Root.Kinds

/-- The collocational closure: a signature carrying `cause` is
    completed with `result` and `state`; one carrying `result` is
    completed with `state`. This is the lower closure under the
    `LexKind` order (`mem_close_iff`). -/
def close (s : Root.Kinds) : Root.Kinds :=
  s ∪ (if .cause ∈ s then {.result, .state} else ∅)
    ∪ (if .result ∈ s then {.state} else ∅)

theorem le_close : ∀ s : Root.Kinds, s ≤ close s := by decide

theorem close_idem : ∀ s : Root.Kinds, close (close s) = close s := by
  decide

theorem close_mono : ∀ {s t : Root.Kinds}, s ≤ t → close s ≤ close t := by
  decide

/-- `close` is the lower closure under the collocational order:
    `k` is in the closure iff some kind in `s` dominates it. -/
theorem mem_close_iff : ∀ (s : Root.Kinds) (k : LexKind),
    k ∈ close s ↔ ∃ j ∈ s, k ≤ j := by decide

/-- The collocational closure as a mathlib `ClosureOperator`. -/
def closeOp : ClosureOperator Root.Kinds where
  toFun := close
  monotone' _ _ := close_mono
  le_closure' := le_close
  idempotent' := close_idem

/-- A signature is well-formed iff it already satisfies the
    collocational constraints (it is a fixed point of `close`). -/
def WellFormed (s : Root.Kinds) : Prop := close s = s

instance (s : Root.Kinds) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ = _))

/-- Well-formedness is downward-closedness in the `LexKind` order. -/
theorem wellFormed_iff_isLowerSet (s : Root.Kinds) :
    s.WellFormed ↔ IsLowerSet (↑s : Set LexKind) := by
  constructor
  · intro hwf a b hba ha
    have hb : b ∈ close s := (mem_close_iff s b).mpr ⟨a, Finset.mem_coe.mp ha, hba⟩
    rw [hwf] at hb
    exact Finset.mem_coe.mpr hb
  · intro h
    refine le_antisymm (fun k hk => ?_) (le_close s)
    obtain ⟨j, hj, hkj⟩ := (mem_close_iff s k).mp hk
    exact Finset.mem_coe.mp (h hkj (Finset.mem_coe.mpr hj))

/-- Closure output is always well-formed — the collocational
    constraints hold of closed signatures *by construction*. -/
theorem close_wellFormed : ∀ s : Root.Kinds, (close s).WellFormed :=
  close_idem

/-! ### Canonical signatures

The attested rows of the root typology of [beavers-koontz-garboden-2020]
ch. 5 (their example display (12), §5.4). -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Complement position. -/
def propertyConcept : Root.Kinds := {.state}

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Complement position. -/
def pureResult : Root.Kinds := {.state, .result}

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation. If roots subdivide by
    entailed causation, this may underlie Levin & Rappaport Hovav's
    (1995) externally vs internally caused change-of-state distinction
    ([beavers-koontz-garboden-2020], hedged as a possibility).
    Complement position. -/
def causativeResult : Root.Kinds := {.state, .result, .cause}

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Adjoined position. -/
def pureManner : Root.Kinds := {.manner}

/-- +S +M +R −C: manner + result without cause. Well-formed per the
    constraints; [beavers-koontz-garboden-2020] leave its attestation
    an open question ("whether a change and a manner can exist together
    in a single meaning without causation"), with candidate witnesses
    *slide* and motion-in-sound-emission *buzz*. -/
def mannerResult : Root.Kinds := {.state, .manner, .result}

/-- +S +M +R +C: fully specified roots (√HAND adjoined, √DROWN and the
    other manner-of-killing roots in complement position;
    [beavers-koontz-garboden-2020] chs. 3–4). These are the attested
    MRC violators. The adjoined/complement contrast is carried by
    `Root.Position`, not by the signature. -/
def fullSpec : Root.Kinds := {.state, .manner, .result, .cause}

/-- −S −M −R −C: minimal roots — no structural entailments.
    Conservative default for classes not yet studied under B&KG's
    framework. Not a row in B&KG's typology (which only lists roots
    with at least one positive feature). -/
def minimal : Root.Kinds := ∅

/-- Every canonical signature is well-formed. -/
theorem canonical_wellFormed :
    propertyConcept.WellFormed ∧ pureResult.WellFormed ∧
    causativeResult.WellFormed ∧ pureManner.WellFormed ∧
    mannerResult.WellFormed ∧ fullSpec.WellFormed ∧ minimal.WellFormed := by
  decide

end Root.Kinds

end Verb
