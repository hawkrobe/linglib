import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Paradigm.Linkage
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The PFM1 paradigm function
[stump-2001] [stump-2016] [bonami-stump-2016] [kiparsky-1973]

The standard Paradigm Function Morphology engine ([bonami-stump-2016]'s
streamlined PFM1, after [stump-2001]): a paradigm function is a set of
**realization rules** organized into ordered **blocks**. A rule
`⟨klass, props, payload⟩` applies to a cell `⟨L, σ⟩` when the lexeme `L`
belongs to `klass` and the property set `props` is contained in `σ`; among the
applicable rules of a block, the narrowest wins ([kiparsky-1973]'s Elsewhere
Condition, PFM's Pāṇinian Determinism). A single payload-polymorphic carrier
`Rule L P F` serves all three rule types: rules of exponence and referral take
`F := Action Z P`, rules of basic stem choice take `F := Z`; stem-choice
conflicts are arbitrated by the same narrowness order.

Narrowness (`Rule`'s `≤`) is [stump-2001]'s two clauses: same class with a
larger property set, or a properly smaller class. It is **intensional** — for
same-class rules it collapses to applicability-set inclusion (`applySet_mono`),
but across classes a smaller class outranks a larger one whatever the property
sets, so the order is strictly finer than the extensional
[stump-2016]/[stump-2022] domain-subset order of `Exponence/Basic.lean`.

The **Identity Function Default** — every block has a rule leaving the stem
unchanged — is assumed as a universal principle in PFM; here it is a definition
(`identityDefault`) and its consequences are theorems (it is `≤`-maximal, and a
block containing it always selects). Two implicative devices are kept distinct
([bonami-stump-2016]): a **rule of referral** (`Action.referral`) models
block-confined syncretism, competing inside its block; whole-word syncretism is
a clause of the paradigm function, outside any block. Overabundance (one cell,
several forms) is out of scope: the realized paradigm is function-valued, one
form per cell. Morphophonological metageneralizations (the `-a`-loss and umlaut
rules of the Icelandic fragment) are phonological substance and live in
`Phonology/`; here stem alternants like *köll* enter as data-level stem values,
not string operations.

Because payloads are functions, `Exponence.Coherent` and `Realizes` over
`Action Z P` are `funext` propositions rather than decidable checks; a study
decides realized **values**, not payload equality.

## Main declarations

* `Action`, `Rule` — the payload (exponence or referral) and the
  payload-polymorphic realization rule
* `Rule`'s `Exponence` and `Preorder` instances — applicability and two-clause
  narrowness; `Rule.applies_iff`, `Rule.le_iff`, `Rule.applySet_mono`
* `identityDefault`, `le_identityDefault`,
  `selectMinimal_isSome_of_mem_identityDefault` — the IFD and its consequences
* `evalBlock`, `paradigmFunction`, `stemChoiceOf` — narrowest-rule block
  evaluation and the block cascade
* `evalPortmanteau`, `evalPortmanteau_eq_comp_of_not_applies` — portmanteau
  blocks and the Function Composition Default
* `Linkage.realize_eq_paradigmFunction` — the PFM2 realization of a linkage's
  block cascade is this paradigm function
-/

namespace Morphology.PFM

open Morphology Morphology.Exponence

variable {L Z P F : Type*}

/-- The payload of a realization rule: a rule of **exponence** carries a form
operation `f : Z → Z`, a rule of **referral** carries a property-set retargeting
`P → P` whose block is re-consulted at the retargeted cell. -/
inductive Action (Z P : Type*)
  | expo (f : Z → Z)
  | referral (retarget : P → P)

/-- A realization rule in [bonami-stump-2016]'s format `⟨klass, props, payload⟩`
(the chapter's `n, X_C, τ → f(X)`), payload-polymorphic à la
`Containment.SpanRule`: rules of exponence and referral instantiate
`F := Action Z P`, rules of basic stem choice `F := Z`. `klass` is the lexeme
class `C`, `props` the realized property set `τ`. -/
structure Rule (L P F : Type*) where
  /-- The lexeme class the rule applies in. -/
  klass : Finset L
  /-- The property set the rule realizes. -/
  props : P
  /-- The form operation (exponence/referral) or stem the rule supplies. -/
  payload : F

section Narrowness
variable [PartialOrder P]

/-- Applicability ([bonami-stump-2016]'s rule format): a rule applies to a cell
`⟨L, σ⟩` when `L` is in its class and its property set is contained in `σ`. -/
instance : Exponence (Rule L P F) (L × P) F where
  exponent := Rule.payload
  Applies r c := c.1 ∈ r.klass ∧ r.props ≤ c.2

@[simp] theorem Rule.applies_iff {r : Rule L P F} {c : L × P} :
    Exponence.Applies (F := F) r c ↔ c.1 ∈ r.klass ∧ r.props ≤ c.2 :=
  Iff.rfl

/-- Two-clause Pāṇinian narrowness ([stump-2001]) as the carrier's order: `r` is
at least as narrow as `s` when either they share a class and `s` realizes a
subset of `r`'s properties, or `r`'s class is properly smaller. Intensional —
strictly finer than applicability-set inclusion (see `Rule.applySet_mono`; the
converse fails). -/
instance : Preorder (Rule L P F) where
  le r s := (r.klass = s.klass ∧ s.props ≤ r.props) ∨ r.klass ⊂ s.klass
  le_refl _ := Or.inl ⟨rfl, le_refl _⟩
  le_trans r s t hrs hst := by
    rcases hrs with ⟨hk, hp⟩ | hk <;> rcases hst with ⟨hk', hp'⟩ | hk'
    · exact Or.inl ⟨hk.trans hk', hp'.trans hp⟩
    · exact Or.inr (hk ▸ hk')
    · exact Or.inr (hk' ▸ hk)
    · exact Or.inr (hk.trans hk')

theorem Rule.le_iff {r s : Rule L P F} :
    r ≤ s ↔ (r.klass = s.klass ∧ s.props ≤ r.props) ∨ r.klass ⊂ s.klass :=
  Iff.rfl

/-- For same-class rules, narrowness is applicability-set inclusion: the narrower
rule applies in a subset of the contexts — [stump-2001]'s two-clause narrowness
collapsing to [stump-2016]'s single-clause domain-subset precedence. Across
classes the order is strictly intensional (a smaller class outranks a larger one
whatever the property sets), so a class hypothesis is required. -/
theorem Rule.applySet_mono {r s : Rule L P F} (hk : r.klass = s.klass) (h : r ≤ s) :
    Exponence.applySet (F := F) r ⊆ Exponence.applySet (F := F) s := by
  rcases h with ⟨_, hp⟩ | hlt
  · intro c hc
    rw [Exponence.mem_applySet] at hc ⊢
    exact ⟨hk ▸ hc.1, hp.trans hc.2⟩
  · exact absurd hk hlt.ne

end Narrowness

/-! ### Selection over the narrowness order -/

section Selection
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

instance (c : L × P) :
    DecidablePred (fun r : Rule L P F => Exponence.Applies (F := F) r c) :=
  fun r => inferInstanceAs (Decidable (c.1 ∈ r.klass ∧ r.props ≤ c.2))

instance : DecidableLE (Rule L P F) := fun r s =>
  inferInstanceAs (Decidable ((r.klass = s.klass ∧ s.props ≤ r.props) ∨ r.klass ⊂ s.klass))

instance : DecidableLT (Rule L P F) := fun r s =>
  inferInstanceAs (Decidable (r ≤ s ∧ ¬ s ≤ r))

/-! ### The Identity Function Default -/

section IdentityDefault
variable [Fintype L] [OrderBot P]

/-- The **Identity Function Default** ([bonami-stump-2016]): the rule applying to
every lexeme and every property set, changing nothing. PFM assumes a rule of
this form in every block as a universal principle; here it is a definition whose
consequences are theorems. -/
def identityDefault : Rule L P (Action Z P) where
  klass := Finset.univ
  props := ⊥
  payload := .expo id

omit [DecidableEq L] [DecidableLE P] in
theorem identityDefault_applies (c : L × P) :
    Exponence.Applies (F := Action Z P) (identityDefault (L := L) (Z := Z) (P := P)) c :=
  ⟨Finset.mem_univ _, bot_le⟩

omit [DecidableLE P] in
/-- The IFD is `≤`-maximal: every rule is at least as narrow. It is a top element
of the narrowness order without an `OrderTop` instance (which would force
`Fintype`/`OrderBot` globally). -/
theorem le_identityDefault (r : Rule L P (Action Z P)) :
    r ≤ identityDefault (Z := Z) (P := P) := by
  by_cases h : r.klass = Finset.univ
  · exact Or.inl ⟨h, bot_le⟩
  · exact Or.inr (Finset.ssubset_univ_iff.mpr h)

/-- A block containing the IFD always selects a rule — the totality of Nar
([bonami-stump-2016]'s (14)) that [stump-2001] secures by stipulating the IFD. -/
theorem selectMinimal_isSome_of_mem_identityDefault
    {v : List (Rule L P (Action Z P))} {c : L × P}
    (h : identityDefault (Z := Z) (P := P) ∈ v) : (selectMinimal v c).isSome :=
  selectMinimal_isSome_of_exists_applicable
    ⟨identityDefault (P := P), h, identityDefault_applies c⟩

end IdentityDefault

/-! ### Blocks and the paradigm function -/

/-- A **rule block** ([bonami-stump-2016]): rules of exponence and referral in
paradigmatic opposition, only the narrowest applying. -/
abbrev Block (L Z P : Type*) := List (Rule L P (Action Z P))

/-- The rules of exponence in a block (referral rules dropped), the target of a
referral's re-selection. -/
def expoFragment (b : Block L Z P) : Block L Z P :=
  b.filter (fun r => r.payload matches .expo _)

/-- The form produced by evaluating a block at a cell: select the narrowest
applicable rule; an exponence rule applies its form operation, a referral rule
re-selects among the block's exponence rules at the retargeted property set (one
hop). The stem is left unchanged when nothing applies. -/
def evalBlockForm (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) : Z :=
  match selectMinimal b (Lindex wσ.1, wσ.2) with
  | some r =>
    match r.payload with
    | .expo f => f wσ.1
    | .referral retarget =>
      match selectMinimal (expoFragment b) (Lindex wσ.1, retarget wσ.2) with
      | some s =>
        match s.payload with
        | .expo g => g wσ.1
        | .referral _ => wσ.1
      | none => wσ.1
  | none => wσ.1

/-- Evaluate a block at a form-state, keeping the property set ([bonami-stump-2016]'s
rule format outputs `⟨f(W), σ⟩`). -/
def evalBlock (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) : Z × P :=
  (evalBlockForm Lindex b wσ, wσ.2)

@[simp] theorem evalBlock_snd (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) :
    (evalBlock Lindex b wσ).2 = wσ.2 :=
  rfl

/-- Thread a form-state through a block cascade (blocks listed inner-first). -/
def blocksEval (Lindex : Z → L) (blocks : List (Block L Z P)) (wσ : Z × P) : Z × P :=
  blocks.foldl (fun w b => evalBlock Lindex b w) wσ

@[simp] theorem blocksEval_snd (Lindex : Z → L) (blocks : List (Block L Z P))
    (wσ : Z × P) : (blocksEval Lindex blocks wσ).2 = wσ.2 := by
  induction blocks generalizing wσ with
  | nil => rfl
  | cons b bs ih => exact (ih (evalBlock Lindex b wσ)).trans (evalBlock_snd Lindex b wσ)

/-- The **paradigm function** ([bonami-stump-2016]'s (13)): basic stem choice,
then the stipulated block cascade. `blocks` are listed inner-first, so
`[I, II, III]` realizes `[iii : [ii : [i : Stem]]]`. `Lindex : Z → L` recovers a
stem's covert lexemic index (fn. 7); L-index persistence holds by construction,
since selection threads a fixed lexeme through `L × P`. -/
def paradigmFunction (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) (c : L × P) : Z × P :=
  blocksEval Lindex blocks (stemChoice c, c.2)

/-- Basic stem choice ([bonami-stump-2016]'s (7)) as narrowest-rule selection over
stem-choice rules (`payload := Z`), falling back to a per-lexeme default. Rule
conflicts (the chapter's `greip`/`grip`/`gríp`) are resolved by the same
narrowness order. -/
def stemChoiceOf (sv : List (Rule L P Z)) (default : L → Z) : L × P → Z :=
  fun c => ((selectMinimal sv c).map Rule.payload).getD (default c.1)

/-- A **portmanteau block** `[m, n]` ([bonami-stump-2016]'s (20)–(24)): its rules
compete with the composition of blocks `m` and `n`; when none applies, the
**Function Composition Default** falls back to that composition. -/
def evalPortmanteau (Lindex : Z → L) (bmn bm bn : Block L Z P) (wσ : Z × P) : Z × P :=
  if (applicable bmn (Lindex wσ.1, wσ.2)).isEmpty
  then evalBlock Lindex bm (evalBlock Lindex bn wσ)
  else evalBlock Lindex bmn wσ

/-- The **Function Composition Default** ([bonami-stump-2016]'s (24)): where no
portmanteau rule applies, the portmanteau block is the composition of its
component blocks. -/
theorem evalPortmanteau_eq_comp_of_not_applies (Lindex : Z → L) (bmn bm bn : Block L Z P)
    (wσ : Z × P) (h : applicable bmn (Lindex wσ.1, wσ.2) = []) :
    evalPortmanteau Lindex bmn bm bn wσ = evalBlock Lindex bm (evalBlock Lindex bn wσ) := by
  simp [evalPortmanteau, h]

/-- With property-preserving property mapping and PFM1 basic stem choice, the
PFM2 realization of a paradigm linkage's block cascade ([stump-2016]'s
`PF(⟨L, σ⟩) = PF(Corr(⟨L, σ⟩))`) is this paradigm function — `Linkage.realize`'s
form-realization hole filled true by construction. -/
theorem Linkage.realize_eq_paradigmFunction (ℓ : Linkage L Z P) (Lindex : Z → L)
    (stemChoice : L × P → Z) (blocks : List (Block L Z P)) (l : L) (σ : P)
    (h : ℓ.IsPropertyPreserving) (hstem : ∀ l σ, ℓ.stem l σ = stemChoice (l, σ)) :
    ℓ.realize (fun z τ => (blocksEval Lindex blocks (z, τ)).1) l σ
      = paradigmFunction Lindex stemChoice blocks (l, σ) := by
  have hpm : ℓ.pm σ = σ := h σ
  simp only [Linkage.realize, Linkage.corr, hpm, hstem, paradigmFunction]
  exact Prod.ext rfl (blocksEval_snd Lindex blocks (stemChoice (l, σ), σ)).symm

end Selection

end Morphology.PFM
