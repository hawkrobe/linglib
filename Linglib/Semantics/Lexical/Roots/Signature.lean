import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Closure

/-!
# Root Feature Signatures

The four-feature vocabulary of [beavers-koontz-garboden-2020]'s root
typology (ch. 5): a root's **feature signature** records which *kinds*
of lexical entailment it carries — state, manner, result, cause — as a
`Finset LexKind`, so signatures inherit the Boolean lattice of finite
sets (`≤` is "carries at most these kinds").

`LexKind` carries the book's collocational order (`state < result <
cause`, with `manner` isolated): "+result entails being +state, since
become′ entails something that has come about… +cause entails being
+result, since cause′ entails that there is a caused event. These are
not root-specific stipulations." Well-formedness of a signature is
downward-closedness in this order, and `close` — the induced lower
closure, packaged as a mathlib `ClosureOperator` — repairs any
signature to a well-formed one.

This file is `Root`-free: consumers that map other objects to
signatures (e.g. Levin classes) can import it without the root
substrate.

## Main declarations

* `LexKind`, with its collocational `PartialOrder`
* `Verb.Root.FeatureSignature := Finset LexKind`
* `Verb.Root.FeatureSignature.close`, `Verb.Root.FeatureSignature.closeOp`,
  `Verb.Root.FeatureSignature.WellFormed`
* canonical signatures (`propertyConcept`, `pureResult`,
  `causativeResult`, `pureManner`, `mannerResult`, `fullSpec`,
  `minimal`)
* `Verb.Root.FeatureSignature.ViolatesBifurcation`,
  `Verb.Root.FeatureSignature.HasMannerAndResult`
-/

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

/-! ### Feature signatures -/

/-- A root feature signature: the set of entailment kinds carried.
    `≤` (= `⊆`) and the lattice operations come from `Finset`. -/
abbrev Verb.Root.FeatureSignature := Finset LexKind

namespace Verb.Root.FeatureSignature

/-- The collocational closure: a signature carrying `cause` is
    completed with `result` and `state`; one carrying `result` is
    completed with `state`. This is the lower closure under the
    `LexKind` order (`mem_close_iff`). -/
def close (s : Verb.Root.FeatureSignature) : Verb.Root.FeatureSignature :=
  s ∪ (if .cause ∈ s then {.result, .state} else ∅)
    ∪ (if .result ∈ s then {.state} else ∅)

theorem le_close : ∀ s : Verb.Root.FeatureSignature, s ≤ close s := by decide

theorem close_idem : ∀ s : Verb.Root.FeatureSignature, close (close s) = close s := by
  decide

theorem close_mono : ∀ {s t : Verb.Root.FeatureSignature}, s ≤ t → close s ≤ close t := by
  decide

/-- `close` is the lower closure under the collocational order:
    `k` is in the closure iff some kind in `s` dominates it. -/
theorem mem_close_iff : ∀ (s : Verb.Root.FeatureSignature) (k : LexKind),
    k ∈ close s ↔ ∃ j ∈ s, k ≤ j := by decide

/-- The collocational closure as a mathlib `ClosureOperator`. -/
def closeOp : ClosureOperator Verb.Root.FeatureSignature where
  toFun := close
  monotone' _ _ := close_mono
  le_closure' := le_close
  idempotent' := close_idem

/-- A signature is well-formed iff it already satisfies the
    collocational constraints (it is a fixed point of `close`). -/
def WellFormed (s : Verb.Root.FeatureSignature) : Prop := close s = s

instance (s : Verb.Root.FeatureSignature) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ = _))

/-- Well-formedness is downward-closedness in the `LexKind` order. -/
theorem wellFormed_iff_isLowerSet (s : Verb.Root.FeatureSignature) :
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
theorem close_wellFormed : ∀ s : Verb.Root.FeatureSignature, (close s).WellFormed :=
  close_idem

/-! ### Canonical signatures

The attested rows of the root typology of [beavers-koontz-garboden-2020]
ch. 5 (their example display (12), §5.4). -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Complement position. -/
def propertyConcept : Verb.Root.FeatureSignature := {.state}

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Complement position. -/
def pureResult : Verb.Root.FeatureSignature := {.state, .result}

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation. If roots subdivide by
    entailed causation, this may underlie Levin & Rappaport Hovav's
    (1995) externally vs internally caused change-of-state distinction
    ([beavers-koontz-garboden-2020], hedged as a possibility).
    Complement position. -/
def causativeResult : Verb.Root.FeatureSignature := {.state, .result, .cause}

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Adjoined position. -/
def pureManner : Verb.Root.FeatureSignature := {.manner}

/-- +S +M +R −C: manner + result without cause. Well-formed per the
    constraints; [beavers-koontz-garboden-2020] leave its attestation
    an open question ("whether a change and a manner can exist together
    in a single meaning without causation"), with candidate witnesses
    *slide* and motion-in-sound-emission *buzz*. -/
def mannerResult : Verb.Root.FeatureSignature := {.state, .manner, .result}

/-- +S +M +R +C: fully specified roots (√HAND adjoined, √DROWN and the
    other manner-of-killing roots in complement position;
    [beavers-koontz-garboden-2020] chs. 3–4). These are the attested
    MRC violators. The adjoined/complement contrast is carried by
    `Root.Position`, not by the signature. -/
def fullSpec : Verb.Root.FeatureSignature := {.state, .manner, .result, .cause}

/-- −S −M −R −C: minimal roots — no structural entailments.
    Conservative default for classes not yet studied under B&KG's
    framework. Not a row in B&KG's typology (which only lists roots
    with at least one positive feature). -/
def minimal : Verb.Root.FeatureSignature := ∅

/-- Every canonical signature is well-formed. -/
theorem canonical_wellFormed :
    propertyConcept.WellFormed ∧ pureResult.WellFormed ∧
    causativeResult.WellFormed ∧ pureManner.WellFormed ∧
    mannerResult.WellFormed ∧ fullSpec.WellFormed ∧ minimal.WellFormed := by
  decide

/-! ### The two theses, at signature level -/

/-- The ontological kinds — all the Bifurcation Thesis allows a root
    to carry. -/
def ontological : Verb.Root.FeatureSignature := {.state, .manner}

/-- A signature violates the Bifurcation Thesis ([embick-2009]; the
    assumption of [arad-2005]) iff it carries templatic (eventive)
    content — it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Verb.Root.FeatureSignature) : Prop := ¬ s ≤ ontological

instance (s : Verb.Root.FeatureSignature) : Decidable s.ViolatesBifurcation :=
  inferInstanceAs (Decidable (¬ _ ≤ _))

/-- Violation is carrying a `result` or `cause` kind. -/
theorem violatesBifurcation_iff :
    ∀ s : Verb.Root.FeatureSignature,
      s.ViolatesBifurcation ↔ .result ∈ s ∨ .cause ∈ s := by decide

/-- Bifurcation violation is monotone: adding entailments cannot
    repair a violation. (Equivalently, the thesis carves out a lower
    set of the signature lattice.) -/
theorem violatesBifurcation_mono :
    ∀ {s t : Verb.Root.FeatureSignature}, s ≤ t →
      s.ViolatesBifurcation → t.ViolatesBifurcation := by decide

/-- A signature has both manner and result — the configuration
    Manner/Result Complementarity ([rappaport-hovav-levin-2010])
    claims no root realizes. -/
def HasMannerAndResult (s : Verb.Root.FeatureSignature) : Prop :=
  {LexKind.manner, LexKind.result} ≤ s

instance (s : Verb.Root.FeatureSignature) : Decidable s.HasMannerAndResult :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- MRC violation is monotone in the signature order. -/
theorem hasMannerAndResult_mono :
    ∀ {s t : Verb.Root.FeatureSignature}, s ≤ t →
      s.HasMannerAndResult → t.HasMannerAndResult := by decide

/-- Both theses are invariant under collocational closure: `close`
    only adds `state`/`result` kinds forced by `cause`, never `manner`,
    and a closed signature violates Bifurcation iff its base does. -/
theorem violatesBifurcation_close_iff :
    ∀ s : Verb.Root.FeatureSignature,
      (close s).ViolatesBifurcation ↔ s.ViolatesBifurcation := by decide

theorem hasMannerAndResult_close_iff :
    ∀ s : Verb.Root.FeatureSignature,
      (close s).HasMannerAndResult ↔
        s.HasMannerAndResult ∨ (.manner ∈ s ∧ .cause ∈ s) := by decide

end Verb.Root.FeatureSignature
