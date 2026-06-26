import Mathlib.Order.Nat
import Mathlib.Logic.Relation
import Linglib.Features.Case.Basic
import Linglib.Core.Relation.ReflTransGen
/-!
# Case Grammaticalization
[heine-2009]

The case-marker grammaticalization cline (lexical > adposition > case
affix > loss) and the extension paths from Heine (2009) Table 29.6.
Three extension targets in Table 29.6 are not representable as `Case`
values and are omitted: **purposive** (from allative, benefactive),
**manner** (from comitative, instrumental), **agent** (from locative;
collapses with ergative in our system).

Extension is the relation `Case.Extends : Case → Case → Prop` (Heine's
Table 29.6 row pattern). Multi-step extension is just
`Relation.TransGen Case.Extends` from mathlib — there is no separate
two-step or n-step predicate to maintain.
-/

/-! ## Case-marker cline -/

/-- Source category of a case marker on the grammaticalization cline
    ([heine-2009] §29.1 eq. (1), §29.2).

    noun, verb (> adverb) > adposition > case affix > loss

    Parallel to `Grammaticalization.GramStage` (for verbal
    elements), but specific to case-marker development. -/
inductive CaseGramStage where
  /-- Lexical noun or verb source (§29.2.1–29.2.2). -/
  | lexical
  /-- Free adposition: preposition or postposition (§29.2.3). -/
  | adposition
  /-- Bound case affix: suffix or prefix (§29.2.3 endpoint). -/
  | caseAffix
  /-- Case marker lost: erosion endpoint or merger. -/
  | lost
  deriving DecidableEq, Repr

/-- Boundedness increases monotonically along the case cline. -/
def CaseGramStage.boundedness : CaseGramStage → Nat
  | .lexical    => 0
  | .adposition => 1
  | .caseAffix  => 2
  | .lost       => 3

instance : LinearOrder CaseGramStage :=
  LinearOrder.lift' CaseGramStage.boundedness
    (fun a b h => by cases a <;> cases b <;> simp_all [CaseGramStage.boundedness])

theorem caseGramCline_ordered :
    CaseGramStage.lexical < CaseGramStage.adposition ∧
    CaseGramStage.adposition < CaseGramStage.caseAffix ∧
    CaseGramStage.caseAffix < CaseGramStage.lost :=
  ⟨by decide, by decide, by decide⟩



/-! ## Case-extension dot-methods

These live under `namespace Features` so they project onto the `Case`
type via dot-notation (mirroring `Case.hierarchyRank` in
`Features/Case/Basic.lean`). -/

namespace Features

/-- Direct extension between case functions ([heine-2009] Table 29.6).

    `Case.Extends c₁ c₂` holds iff a single row of Heine's table licenses
    extending a `c₁`-marker to `c₂` uses. Direction is concrete/peripheral
    → abstract/core: the source function is less grammaticalized than the
    target.

    See also `Possession.Source` for
    [heine-2009] Table 29.5 (possessive case sources, adapted from
    [heine-1997]). -/
def _root_.Case.Extends : Case → Case → Prop
  | .abl,  .caus | .abl,  .gen  | .abl,  .part | .abl,  .inst => True
  | .all,  .ben  | .all,  .dat  | .all,  .acc                 => True
  | .com,  .inst | .com,  .erg  | .com,  .gen                 => True
  | .dat,  .acc                                                => True
  | .inst, .erg                                                => True
  | .loc,  .com  | .loc,  .erg  | .loc,  .inst                => True
  | _,     _                                                   => False

instance : DecidableRel Case.Extends := fun c₁ c₂ => by
  unfold Case.Extends; split <;> infer_instance

/-- Direct-extension targets of `c`, as a `Finset` derived from
    `Case.Extends`. Useful for membership queries by `decide`. -/
def _root_.Case.extensionTargets (c : Case) : Finset Case :=
  (Finset.univ : Finset Case).filter (Case.Extends c)

theorem _root_.Case.mem_extensionTargets {c₁ c₂ : Case} :
    c₂ ∈ c₁.extensionTargets ↔ Case.Extends c₁ c₂ := by
  simp [Case.extensionTargets]

/-! `Case.Extends` itself is the public Table 29.6 spec — concrete
    extension facts (`Case.Extends .abl .inst`, `¬ Case.Extends .nom .acc`,
    etc.) are immediate by `decide` against the `def` and need not be
    re-stated as a thicket of named theorems. The chain theorems below
    bundle multiple table rows into the named Heine (2009) eq. (2)
    chains. -/

/-- Chain (2a): allative > benefactive > purposive.
    Only the first step is representable as Case → Case. -/
theorem chain_all_ben : Case.Extends .all .ben := by decide

/-- Chain (2b): allative > dative > accusative/O.
    Both steps are direct extensions. -/
theorem chain_all_dat_acc :
    Case.Extends .all .dat ∧ Case.Extends .dat .acc := by decide

/-- Chain (2c): locative > comitative > instrumental > manner.
    The first two steps are representable as Case → Case. -/
theorem chain_loc_com_inst :
    Case.Extends .loc .com ∧ Case.Extends .com .inst := by decide

/-- Multi-step extension reachability — the transitive closure of
    `Case.Extends`. Composing chain rows of Table 29.6 produces an
    extension path of any finite length. -/
abbrev _root_.Case.ExtensionReachable : Case → Case → Prop :=
  Relation.TransGen Case.Extends

/-- `Case.ExtensionReachable` is decidable via the
`Core.Relation.ReflTransGen` substrate's `TransGen` `Fintype` headline.
The step function is `Case.extensionTargets`. -/
instance : DecidableRel Case.ExtensionReachable := fun c₁ c₂ =>
  Relation.ReflTransGen.decidable_TransGen_of_fintype_step
    Case.extensionTargets
    (fun a b => (Case.mem_extensionTargets (c₁ := a) (c₂ := b)).symm) c₁ c₂

/-- Accusative is reachable from allative via dative (chain 2b). -/
theorem acc_reachable_from_all : Case.ExtensionReachable .all .acc :=
  .tail (.single (a := (.all : Case)) (b := (.dat : Case)) (by decide))
    (show Case.Extends .dat .acc by decide)

/-- Instrumental is reachable from locative via comitative (chain 2c). -/
theorem inst_reachable_from_loc : Case.ExtensionReachable .loc .inst :=
  .tail (.single (a := (.loc : Case)) (b := (.com : Case)) (by decide))
    (show Case.Extends .com .inst by decide)

end Features
