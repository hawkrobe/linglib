import Linglib.Semantics.Presupposition.Trivalent
import Linglib.Core.Logic.Trivalent
import Linglib.Semantics.Dynamic.UpdateSemantics.Basic
import Linglib.Semantics.Dynamic.Partial
import Linglib.Studies.Geurts2005
import Linglib.Studies.Karttunen1973
import Mathlib.Tactic.DeriveFintype

/-!
# Conflicting Presuppositions in Disjunction
[yagi-2025]

Squib-replication of [yagi-2025] (S&P 18:7) on disjunctions
`φ_p ∨ ψ_q` with `p ∧ q = ⊥`. Yagi argues:

  (2a) the disjunction presupposes `p ∨ q`;
  (2b) it can be false (when both disjuncts are false).

§2 surveys four projection theories — Strong Kleene, two-dimensional
[karttunen-peters-1979], dynamic update ([heim-1982],
[veltman-1996], [beaver-2001]), and [schlenker-2009]'s
local contexts — each failing (2b). §3 considers two reactions:
[beaver-krahmer-2001]'s 𝒜-operator (loses presupposition),
and [geurts-2005]'s flexible accommodation (captures (2a–b) at the
cost of an underspecified accommodation mechanism that interacts oddly
with negation, and at the cost of overgenerating non-projection in
non-conflicting cases like (18)).

[aloni-2022]'s bilateral state semantics is a substantively
different account that also delivers a "split" disjunction; we mention
it here because Yagi cites it alongside Geurts as a flexible-accommodation
co-developer, but it is formalised separately at
`Studies/Aloni2022.lean` and not engaged here.

Yagi's example (8) — "Either baldness is not hereditary, or all of Bill's
children are bald" ([karttunen-1974]) — appears in §2.2 as a
counterexample to the K&P modification `Π(φ ∨ ψ) := Π(φ) ∨ Π(ψ)` (eq. 7).
This formula is exactly what `PartialProp.orFlex.presup` computes. The
flexible-accommodation framework Yagi defends in §3.2 evades the eq. (7)
problem via the `χ = ω = ⊤` accommodation default, which we have not
formalised here (we have only the static `orFlex` connective, not the
parametric dynamic update `s[χ][φ] ∪ s[ω][ψ]` of Yagi's eq. 13).

The §3.2 discussion of how dynamic negation requires genuineness to hold
within negation scope ("peculiar, given that we end up negating both
disjuncts") motivated the strengthening of `PartialProp.genuineness` from a
singleton-survival check (now `PartialProp.liveness`) to the two-conjunct
definition with disjunction-update survival.

## Connective inventory used

- `⊔` on `Trivalent` (Strong Kleene): never false (`strong_kleene_never_false`)
- `PartialProp.or` (classical): never defined (`classical_never_defined`)
- `PartialProp.orPositive` (symmetric, positive-antecedent filtering of
  [kalomoiros-schwarz-2021]): wrong presupposition
  (`filter_wrong_at_kingOpens`)
- `PartialProp.orKPSymmetric` (symmetric, negative-antecedent K&P of Yagi Def 2):
  presupposition entails assertion (`kp_presup_entails_assertion`)
- `Geurts2005.exhaustivity_implies_uninformative`:
  the *consequence* (not the derivation) of [schlenker-2009] §2.4
  via the Geurts-modal-disjunction substrate
  (`truthset_uninformative_geurts_route`)
- `Prop3.metaAssert`: allows falsity, no presupposition
  (`metaAssert_allows_falsity`, `metaAssert_no_gap`)
- `PartialProp.orFlex` = `PartialProp.orBelnap` (substrate identity from
  `Semantics/Presupposition/Basic.lean`): correct (2a) and (2b), with a
  discriminating world `noHeadOfState` to prove the presupposition is
  non-trivial
- `PartialProp.orFlex.presup` overgenerates trivial-truth in eq. (7) shape:
  `eq7_too_weak_for_ex8` exhibits the empirical mismatch at world `noChild`
- For example (18), `orFlex` predicts non-projection only because the left
  disjunct is presuppositionless (`ex18_orFlex_no_projection_via_vacuous_left`,
  `ex18_unprincipled_in_right_presup_failure`); the principled K1973
  asymmetric route (`ex18_asymmetric_K1973_principled`) goes via
  `PartialProp.disjFilterLeft_eliminates_presup_when_neg_entails`
-/

namespace Yagi2025

open Trivalent (isDefined metaAssert Prop3)
open Semantics.Presupposition

/-! ## World type

[yagi-2025] ex. (1c), after [beaver-2001]: "Either the King
of Buganda is now opening parliament or the President of Buganda is
conducting the ceremony." A nation has either a king or a president
(presuppositions conflict), and the head of state may or may not be
performing the relevant ceremonial duty. We add a fifth world
`noHeadOfState` so the disjunctive presupposition `p ∨ q` is non-trivial
— without it, every world would satisfy the expected presupposition and
`flex_correct_presup` would degenerate to `True ↔ True`. -/
inductive W where
  | kingOpens
  | kingDoesnt
  | presidentConducts
  | presidentDoesnt
  | noHeadOfState
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Presupposition `p`: the nation has a king. -/
def hasKing : W → Prop
  | .kingOpens | .kingDoesnt => True
  | _ => False

instance : DecidablePred hasKing
  | .kingOpens | .kingDoesnt => isTrue trivial
  | .presidentConducts | .presidentDoesnt | .noHeadOfState => isFalse id

/-- Presupposition `q`: the nation has a president. -/
def hasPresident : W → Prop
  | .presidentConducts | .presidentDoesnt => True
  | _ => False

instance : DecidablePred hasPresident
  | .presidentConducts | .presidentDoesnt => isTrue trivial
  | .kingOpens | .kingDoesnt | .noHeadOfState => isFalse id

/-- `p ∧ q = ⊥`: the presuppositions conflict. -/
theorem presups_conflict : ∀ w, ¬(hasKing w ∧ hasPresident w) := by
  decide

/-- φ_p: "The King is opening parliament" — presupposes `hasKing`. -/
def kingOpensParl : PartialProp W where
  presup := hasKing
  assertion w := w = .kingOpens

/-- ψ_q: "The President is conducting the ceremony" — presupposes `hasPresident`. -/
def presConductsCeremony : PartialProp W where
  presup := hasPresident
  assertion w := w = .presidentConducts


/-! ## Empirical observations

[yagi-2025] (2a–b). Note that (2a) is non-trivial here — the
discriminating world `noHeadOfState` falsifies `expectedPresup`. -/

/-- The expected presupposition: the nation has some head of state. -/
def expectedPresup : W → Prop := fun w => hasKing w ∨ hasPresident w

instance : DecidablePred expectedPresup := fun w => by
  unfold expectedPresup; infer_instance

/-- (2a) holds at every world *with* a head of state. The fifth world
`noHeadOfState` falsifies it — the test is now non-trivial. -/
theorem presup_iff_has_head_of_state :
    ∀ w, expectedPresup w ↔ w ≠ W.noHeadOfState := by decide

/-- (2a) is falsified at `noHeadOfState`. -/
theorem presup_fails_at_no_head : ¬expectedPresup W.noHeadOfState := by decide

/-- (2b): the disjunction can be false. At `kingDoesnt` the presupposition
is satisfied but both disjuncts fail. -/
theorem can_be_false :
    expectedPresup W.kingDoesnt ∧
    ¬kingOpensParl.assertion W.kingDoesnt ∧
    ¬presConductsCeremony.assertion W.kingDoesnt :=
  ⟨Or.inl trivial,
   show W.kingDoesnt ≠ W.kingOpens by decide,
   show W.kingDoesnt ≠ W.presidentConducts by decide⟩


/-! ## Failure 1: Strong Kleene ([yagi-2025] §2.1, Definition 1) -/

/-- Strong Kleene disjunction of the two presuppositional propositions. -/
noncomputable def skDisj : Prop3 W :=
  kingOpensParl.eval ⊔ presConductsCeremony.eval

/-- Strong Kleene never produces false for this disjunction. Because
presuppositions conflict, at least one disjunct is always undefined, so
the table never reaches the 0 ∨ 0 = 0 row. -/
theorem strong_kleene_never_false : ∀ w, skDisj w ≠ .false := by
  intro w
  cases w <;>
    (simp [skDisj, PartialProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident] <;> try decide)


/-! ## Failure 2: Two-dimensional semantics ([yagi-2025] §2.2)

[karttunen-peters-1979], with [yagi-2025]'s symmetric Definition 2
(per fn 2, citing [kalomoiros-schwarz-2021] for empirical support of
symmetry). The substrate `PartialProp.orKPSymmetric` matches Yagi's Def 2 directly:

  Π(φ ∨ ψ) = (¬A(ψ) → Π(φ)) ∧ (¬A(φ) → Π(ψ))

`PartialProp.orPositive` is a *different* symmetric variant with positive-antecedent
conditionals plus an extra `Π(φ) ∨ Π(ψ)` disjunct, which is **strictly
stronger** than `orKPSymmetric` (worked counterexample: at a world with `A(φ)=⊤`,
`A(ψ)=⊥`, `Π(φ)=⊤`, `Π(ψ)=⊥`, `orKPSymmetric` is defined, `orPositive` is not).
The two are not predictionally equivalent, and neither is the asymmetric
[karttunen-1973] rule (24b) used as `PartialProp.disjFilterLeft` —
see `Studies/Karttunen1973.lean`. -/

/-- Classical disjunction requires both presuppositions: presup = `p ∧ q`. -/
def classicalDisj : PartialProp W := PartialProp.or kingOpensParl presConductsCeremony

/-- `PartialProp.or` is never defined when presuppositions conflict. -/
theorem classical_never_defined : ∀ w, ¬classicalDisj.presup w := fun w h =>
  presups_conflict w h

/-- The symmetric positive-antecedent filtering disjunction
(`PartialProp.orPositive`). Encodes
`(A(φ) → Π(ψ)) ∧ (A(ψ) → Π(φ)) ∧ (Π(φ) ∨ Π(ψ))` — strictly stronger
than `orKPSymmetric`. The conjunct `Π(φ) ∨ Π(ψ)` matches the eq. (7) modification
discussed by [yagi-2025] §2.2 (after Def 3) as a candidate fix. -/
def filterDisj : PartialProp W := PartialProp.orPositive kingOpensParl presConductsCeremony

/-- `orPositive` predicts presupposition failure at `kingOpens`, where the
disjunction should clearly be true: the filtering condition demands the
president-presupposition hold when the king-assertion is true. -/
theorem filter_wrong_at_kingOpens : ¬filterDisj.presup W.kingOpens := by
  intro h
  -- The failing implication: at `kingOpens`, the king-assertion is true
  -- while the president-presupposition is false, so `A(p) → Π(q)` fails.
  have hp_assert : kingOpensParl.assertion W.kingOpens := rfl
  exact (h.1 hp_assert : presConductsCeremony.presup W.kingOpens)

/-- The expected presupposition is satisfied at `kingOpens`. -/
theorem expected_satisfied_at_kingOpens : expectedPresup W.kingOpens := Or.inl trivial

/-- K&P two-dimensional disjunction applied to the Buganda scenario. -/
def kpDisj : PartialProp W := PartialProp.orKPSymmetric kingOpensParl presConductsCeremony

/-- K&P's presupposition entails the assertion when presuppositions conflict:
whenever Π = 1, A = 1. Derived from the substrate
`PartialProp.orKPSymmetric_presup_entails_when_conflicting`. [yagi-2025] §2.2 (5)–(6). -/
theorem kp_presup_entails_assertion :
    ∀ w, kpDisj.presup w → kpDisj.assertion w := by
  intro w h
  exact PartialProp.orKPSymmetric_presup_entails_when_conflicting _ _ w (presups_conflict w) h


/-! ## Failure 3: Update semantics ([yagi-2025] §2.3)

Bridges to `UpdateSemantics.Basic`, which
collapses the [heim-1982]/[veltman-1996]/[beaver-2001]
treatments of presuppositional disjunction into a single `PUpdate.disjPresup`
operator. -/

section UpdateSemantics

open UpdateSemantics

/-! ### Presuppositional updates over `Option`-states

[yagi-2025]'s Definition 4-5 apparatus, single-consumer and hence
study-local: `Option (State W)` renders Definition 5's failure value as
`none`. The canonical `Part`-based partiality layer is
`DynamicSemantics.CCP.Partial`; `PUpdate.presup_ne_none_iff_admits`
identifies the two where they overlap, and the `Option` form survives for
the disjunction machinery (`disjPresup`, `disjFlex`) below. -/

section PolymorphicState
variable {V : Type*}

/-- The designated undefined state: update failure.

    [yagi-2025] Definition 5: when a presupposition is not satisfied,
    the update yields ∗. We model ∗ as `none` via `Option (State V)`. -/
abbrev PState (V : Type*) := Option (State V)

open Classical in
/-- Presuppositional update: update by φ_p is defined only when the
    presupposition p is supported (i.e. `s[p] = s`).

    [yagi-2025] Definition 5:
      s[φ_p] = ∗  if s[p] ≠ s
             = s[φ]  otherwise

    [heim-1982] [beaver-2001] [veltman-1996] -/
noncomputable def PUpdate.presup (p φ : V → Prop) : PState V → PState V
  | none => none
  | some s =>
    if Update.prop p s = s then
      some (Update.prop φ s)
    else
      none

/-- `PUpdate.presup` is the `Option`-valued shadow of
    `DynamicSemantics.CCP.Partial.ofPartialProp`: defined (≠ `none`) at `some s` exactly
    when `s` admits the corresponding partial update. `CCP.Partial` is the
    canonical `Part`-based form; this clause survives for the
    [yagi-2025] disjunction machinery below. -/
theorem PUpdate.presup_ne_none_iff_admits (p φ : V → Prop) (s : State V) :
    PUpdate.presup p φ (some s) ≠ none ↔
      (DynamicSemantics.CCP.Partial.ofPartialProp ⟨p, φ⟩).admits s := by
  simp only [PUpdate.presup]
  split_ifs with h
  · refine ⟨fun _ w hw => ?_, fun _ => Option.some_ne_none _⟩
    have hm : w ∈ Update.prop p s := h.symm ▸ hw
    exact hm.2
  · refine ⟨fun hne => absurd rfl hne, fun hadm => absurd ?_ h⟩
    have hadm' : ∀ w ∈ s, p w := hadm
    exact Set.ext fun w => ⟨fun hw => hw.1, fun hw => ⟨hw, hadm' w hw⟩⟩

/-- Negation extended to PState: s[¬φ] = s/s[φ].

    [yagi-2025] Definition 4: s[¬φ] = s \ s[φ]. -/
def PUpdate.neg (φ : V → Prop) : PState V → PState V
  | none => none
  | some s => some (s \ Update.prop φ s)

/-- Disjunction extended to PState: s[φ ∨ ψ] = s[φ] ∪ s[¬φ][ψ].

    [yagi-2025] Definition 4, [heim-1982].
    Extended with ∗ ∪ s = s ∪ ∗ = ∗. -/
def PUpdate.disj (φ ψ : V → Prop) : PState V → PState V
  | none => none
  | some s =>
    let left := Update.prop φ s
    let negLeft := s \ left
    let right := Update.prop ψ negLeft
    some (left ∪ right)

/-- Presuppositional disjunction: s[φ_p ∨ ψ_q].
    Apply presupposition checks to each disjunct.

    This is the standard Heim/Beaver definition:
      s[φ_p ∨ ψ_q] = s[φ_p] ∪ s[¬φ_p][ψ_q]

    Both presuppositional updates must be defined for the result to be
    defined: s[φ_p] requires s ⊨ p, and s[¬φ_p][ψ_q] requires s[¬φ_p] ⊨ q. -/
noncomputable def PUpdate.disjPresup (p φ q ψ : V → Prop) :
    PState V → PState V
  | none => none
  | some s =>
    -- Left disjunct: s[φ_p]
    let left := PUpdate.presup p φ (some s)
    -- Right context: s[¬φ_p] — but ¬φ_p requires negating the presuppositional φ
    -- Following Yagi: s[¬φ_p] = s \ s[φ_p], but s[φ_p] may be ∗
    match left with
    | none => none  -- left undefined → whole disjunction undefined
    | some leftResult =>
      let negLeftCtx := s \ leftResult
      -- Right disjunct: s[¬φ_p][ψ_q]
      let right := PUpdate.presup q ψ (some negLeftCtx)
      match right with
      | none => none
      | some rightResult => some (leftResult ∪ rightResult)

/-- **Flexible accommodation disjunction** (dynamic version).

    [yagi-2025] (13) / [geurts-2005] / [aloni-2022]:
      s[φ ∨ ψ] = s[χ][φ] ∪ s[ω][ψ], where s[χ] ∪ s[ω] = s

    The propositions χ and ω *split* the state s into two substates.
    By default χ = ω = ⊤ (both tautological), but when the default
    violates genuineness ([zimmermann-2000]), the split becomes
    non-trivial: χ = ¬q and ω = ¬p for conflicting presuppositions. -/
noncomputable def PUpdate.disjFlex (χ φ_presup φ ω ψ_presup ψ : V → Prop)
    (_h_split : ∀ s : State V, Update.prop χ s ∪ Update.prop ω s = s) :
    PState V → PState V
  | none => none
  | some s =>
    let leftCtx := Update.prop χ s
    let rightCtx := Update.prop ω s
    let left := PUpdate.presup φ_presup φ (some leftCtx)
    let right := PUpdate.presup ψ_presup ψ (some rightCtx)
    match left, right with
    | some l, some r => some (l ∪ r)
    | _, _ => none  -- ∗ poisons: if either side is undefined, result is ∗

/-! ### Yagi's core observations -/

/-- Presuppositional disjunction update is uninformative when both
    presuppositions are already supported: if s ⊨ p and s ⊨ q and the
    disjunction φ ∨ ψ is already true throughout s, the update returns
    s unchanged.

    Note: this applies to **non-conflicting** presuppositions. When
    p ∧ q = ⊥, the hypotheses hp and hq are jointly unsatisfiable
    (unless s = ∅). For the conflicting case, see
    `update_yields_undefined` in the Yagi2025 study, which shows the
    update is undefined (∗) rather than uninformative. -/
theorem presup_disj_uninformative_when_supported (p φ q ψ : V → Prop) (s : State V)
    (hp : Update.prop p s = s) (hq : Update.prop q s = s)
    (h_or : ∀ w, w ∈ s → (φ w ∨ ψ w)) :
    PUpdate.disjPresup p φ q ψ (some s) = some s := by
  unfold PUpdate.disjPresup PUpdate.presup
  -- Helper: q holds at every world in s (from hq)
  have hq_at : ∀ w, w ∈ s → q w := by
    intro w hw
    have : w ∈ Update.prop q s := hq.symm ▸ hw
    exact this.2
  -- Helper: q is supported on any subset of s
  have hq_sub : ∀ t : State V, t ⊆ s → Update.prop q t = t := by
    intro t ht; ext w
    exact ⟨fun h => h.1, fun hw => ⟨hw, hq_at w (ht hw)⟩⟩
  -- Helper: ψ holds everywhere in s \ Update.prop φ s (by h_or + φ failure)
  have hψ_sub : ∀ w, w ∈ s \ Update.prop φ s → ψ w := by
    intro w ⟨hw, hnφ⟩
    cases h_or w hw with
    | inl h => exact absurd (show w ∈ Update.prop φ s from ⟨hw, h⟩) hnφ
    | inr h => exact h
  have h_q_neg : Update.prop q (s \ Update.prop φ s) = s \ Update.prop φ s :=
    hq_sub _ (fun _ h => h.1)
  simp only [hp, ↓reduceIte, h_q_neg]
  -- Result: Update.prop φ s ∪ Update.prop ψ (s \ Update.prop φ s) = s
  suffices h : Update.prop φ s ∪ Update.prop ψ (s \ Update.prop φ s) = s by
    exact congrArg some h
  apply Set.Subset.antisymm
  · intro w hw
    cases hw with
    | inl h => exact h.1
    | inr h => exact h.1.1
  · intro w hw
    by_cases hφ : φ w
    · exact Set.mem_union_left _ ⟨hw, hφ⟩
    · exact Set.mem_union_right _ ⟨⟨hw, fun h => hφ h.2⟩, hψ_sub w ⟨hw, fun h => hφ h.2⟩⟩


end PolymorphicState

/-- The ideal input state for (1c): all worlds with a head of state. The
`noHeadOfState` world is excluded — Yagi's discussion presupposes a context
where the disjunctive presupposition `p ∨ q` is satisfied. -/
def bugandaState : State W :=
  { W.kingOpens, W.kingDoesnt, W.presidentConducts, W.presidentDoesnt }

/-- Presupposition `p` (`hasKing`) is NOT supported in `bugandaState`:
updating by `p` eliminates the president-worlds. -/
theorem hasKing_not_supported :
    Update.prop hasKing bugandaState ≠ bugandaState := by
  intro h
  have hmem : W.presidentConducts ∈ Update.prop hasKing bugandaState := by
    rw [h]; right; right; left; rfl
  exact hmem.2

/-- Presupposition `q` (`hasPresident`) is NOT supported in `bugandaState`. -/
theorem hasPresident_not_supported :
    Update.prop hasPresident bugandaState ≠ bugandaState := by
  intro h
  have hmem : W.kingOpens ∈ Update.prop hasPresident bugandaState := by
    rw [h]; left; rfl
  exact hmem.2

/-- The presuppositional disjunction update yields `∗` (none) on
`bugandaState`. [yagi-2025] §2.3: the update `s[φ_p ∨ ψ_q]` results
in undefinedness because the presupposition check for the first disjunct
(`s[p] = s`) fails. -/
theorem update_yields_undefined :
    PUpdate.disjPresup hasKing kingOpensParl.assertion hasPresident
      presConductsCeremony.assertion (some bugandaState) = none := by
  simp only [PUpdate.disjPresup, PUpdate.presup, if_neg hasKing_not_supported]

/-- Both presuppositions fail on `bugandaState`: combined with
`update_yields_undefined`, the standard dynamic definition has no
defined-and-informative output for conflicting presuppositions. -/
theorem neither_presup_supported :
    Update.prop hasKing bugandaState ≠ bugandaState ∧
    Update.prop hasPresident bugandaState ≠ bugandaState :=
  ⟨hasKing_not_supported, hasPresident_not_supported⟩

end UpdateSemantics


/-! ## Failure 4: [schlenker-2009]'s incremental evaluation
([yagi-2025] §2.4)

Yagi's §2.4 derivation: Schlenker's pragmatic condition on local contexts
admits a context-world `w` only if `w` survives the local-context update
of the second disjunct's presupposition; walking through the cases for
the conflicting-presupposition setup, Yagi concludes that `s_0` ends up
containing **only** worlds where some disjunct's assertion-plus-presupposition
holds — at which point the disjunction is trivially true and uninformative.

What we actually formalise here is the **consequence**, not Yagi's
derivation. We stipulate the truth-set `truthSet` directly (kingOpens +
presidentConducts — the worlds where some disjunct is defined-and-true)
and show via the substrate's
`Geurts2005.exhaustivity_implies_uninformative` that
the disjunction is true throughout `truthSet`. This is an instance of
Geurts's exhaustivity-implies-uninformativity, which Yagi argues coincides
with Schlenker's verdict on the same context. The actual Schlenker
local-context derivation would require a `localContext` operator on
`PUpdate` (s/s[¬φ]) that we have not formalised; the present theorem is
the static reduction.

Note: `truthSet`-uninformativity is structurally trivial — any proposition
is uninformative on its own truth-set. The substantive Schlenker move is
*deriving* that `s_0` reduces to the truth-set; we punt on that derivation. -/

/-- The truth-set of the Buganda disjunction: the worlds where some
disjunct's presupposition-and-assertion holds. Yagi §2.4 argues
Schlenker's pragmatic condition forces `s_0 ⊆ truthSet`. -/
def truthSet : Set W := { W.kingOpens, W.presidentConducts }

/-- Geurts exhaustivity holds on `truthSet`: every truth-set world is in
some disjunct's modal cell (`domain ∩ content` = `presup ∧ assertion`). -/
theorem truthSet_exhausted :
    Geurts2005.exhaustivity truthSet
      (Geurts2005.fromPartialProp kingOpensParl presConductsCeremony) := by
  intro w hw
  rcases hw with rfl | rfl
  · -- Witness: the king-disjunct, with cell membership at `kingOpens`.
    refine ⟨{ domain := kingOpensParl.presup,
              force := .possibility,
              content := kingOpensParl.assertion },
            by simp [Geurts2005.fromPartialProp], ?_⟩
    exact ⟨trivial, rfl⟩
  · -- Witness: the president-disjunct, with cell membership at `presidentConducts`.
    refine ⟨{ domain := presConductsCeremony.presup,
              force := .possibility,
              content := presConductsCeremony.assertion },
            by simp [Geurts2005.fromPartialProp], ?_⟩
    exact ⟨trivial, rfl⟩

/-- Trivalent-set uninformativity via Geurts (the *consequence* of Yagi §2.4,
not Schlenker's actual local-context derivation): the disjunction is true
throughout the stipulated `truthSet`. Discharged via the substrate's
`exhaustivity_implies_uninformative`. A faithful Schlenker formalisation
would derive `s_0 ⊆ truthSet` from a `localContext` PUpdate operator we
have not built. -/
theorem truthset_uninformative_geurts_route :
    ∀ w ∈ truthSet,
      (PartialProp.orFlex kingOpensParl presConductsCeremony).assertion w := by
  intro w hw
  exact Geurts2005.exhaustivity_implies_uninformative
    kingOpensParl presConductsCeremony truthSet
    truthSet_exhausted w hw


/-! ## Reaction 1: Meta-assertion ([yagi-2025] §3.1, [beaver-krahmer-2001])

Yagi §3.1 has two prongs: (i) the truth-functional behavior of `𝒜` (we
formalize this), and (ii) the *licensing constraint* on when `𝒜` may be
inserted (Beaver & Krahmer's condition: insert iff the formula would be
undefined OR a part is replaceable by `⊥`/`⊤` without semantic effect).
Yagi argues this constraint licenses the [beaver-krahmer-2001]
analysis (10) `𝒜φ_p ∨_w 𝒜ψ_q` but does NOT license the Strong-Kleene
counterpart (11) `φ_p ∨_s 𝒜ψ_q`, leaving Yagi's verdict on §3.1 partly
negative ("I cannot offer a constraint now").

We formalize the truth-functional content; the licensing constraint
remains prose-only because it requires a "replaceability" predicate
that is itself an open theoretical question. -/

/-- The disjunction `𝒜φ_p ∨ 𝒜ψ_q` of Yagi (10), with `𝒜` the
meta-assertion operator of Yagi Definition 6 (truth table `1↦1, 0↦0,
∗↦0`). We use `Prop3.or` (Strong Kleene join) — since `metaAssert`
maps each disjunct to a bivalent value, Strong and Weak Kleene agree
on the result, and Yagi's discussion uses Weak Kleene (Def 7) only as
a notational matter. -/
noncomputable def metaAssertDisj : Prop3 W :=
  Prop3.metaAssert kingOpensParl.eval ⊔ Prop3.metaAssert presConductsCeremony.eval

/-- Meta-assertion allows falsity (unlike Strong Kleene). Satisfies (2b). -/
theorem metaAssert_allows_falsity :
    metaAssertDisj W.kingDoesnt = .false := by
  simp [metaAssertDisj, PartialProp.eval, kingOpensParl, presConductsCeremony,
    hasKing, hasPresident]

/-- Meta-assertion loses the presupposition: `𝒜φ_p` has no presupposition
(it maps `∗` to `0`), so the Strong Kleene disjunction `𝒜φ_p ∨_s ψ_q`
only presupposes `¬𝒜ψ_q → p` per Yagi (11), not `p ∨ q`. -/
theorem metaAssert_always_defined : ∀ w, (metaAssertDisj w).isDefined := by
  intro w; cases w <;>
    simp [metaAssertDisj, PartialProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident, Trivalent.isDefined]

/-- The meta-assertion disjunction is bivalent — no gap, no presupposition
via the standard gap mechanism. -/
theorem metaAssert_no_gap : ∀ w, metaAssertDisj w ≠ .indet := by
  intro w; cases w <;>
    simp [metaAssertDisj, PartialProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident]


/-! ## Reaction 2: Flexible accommodation ([yagi-2025] §3.2,
[geurts-2005], [aloni-2022])

Uses the substrate `PartialProp.orFlex`, with the discriminating world
`noHeadOfState` ensuring the (2a) test is non-trivial. -/

/-- The flexible accommodation disjunction. -/
def flexDisj : PartialProp W := PartialProp.orFlex kingOpensParl presConductsCeremony

/-- (2a) at the discriminating world: `flexDisj.presup` *fails* at
`noHeadOfState`. Without this world, `expectedPresup` would be a
tautology and `flex_correct_presup_iff_expected` would degenerate to
`True ↔ True`. -/
theorem flex_presup_fails_at_no_head : ¬flexDisj.presup W.noHeadOfState := by
  rintro (h | h) <;> exact h

/-- (2a) at a head-of-state world: `flexDisj.presup` *holds* at `kingOpens`. -/
theorem flex_presup_holds_at_kingOpens : flexDisj.presup W.kingOpens :=
  Or.inl trivial

/-- (2a) globally: `flexDisj.presup` matches `expectedPresup` at every
world. With `noHeadOfState` in the world model, this is a non-trivial
biconditional (both sides fail there; both sides hold elsewhere). -/
theorem flex_correct_presup_iff_expected :
    ∀ w, flexDisj.presup w ↔ expectedPresup w := fun _ => Iff.rfl

/-- Complete truth table: flexible accommodation predicts the right value
at every head-of-state world. (At `noHeadOfState` the disjunction is
undefined.) -/
theorem flex_truth_table :
    flexDisj.eval W.kingOpens = .true ∧
    flexDisj.eval W.kingDoesnt = .false ∧
    flexDisj.eval W.presidentConducts = .true ∧
    flexDisj.eval W.presidentDoesnt = .false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [flexDisj, PartialProp.orFlex, PartialProp.orBelnap, PartialProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident]

/-- Flexible accommodation is undefined at the discriminating world
`noHeadOfState`. -/
theorem flex_undefined_at_no_head :
    flexDisj.eval W.noHeadOfState = .indet := by
  simp [flexDisj, PartialProp.orFlex, PartialProp.orBelnap, PartialProp.eval, kingOpensParl, presConductsCeremony,
    hasKing, hasPresident]

/-- (2b): `flexDisj` is false at `kingDoesnt` (king present but not opening). -/
theorem flex_can_be_false : flexDisj.eval W.kingDoesnt = .false := flex_truth_table.2.1


/-! ### Genuineness

[yagi-2025] Definition 8 (after [zimmermann-2000]): each
disjunct must contribute a "live possibility" — there is `w ∈ s` with
`{w}[φ] = {w}` AND `w ∈ s[φ ∨ ψ]`. The substrate
`PartialProp.genuineness disj p q s` parameterises on the disjunction
connective `disj` whose update we test against; the simpler
singleton-survival check is now `PartialProp.liveness`. Under `orFlex`,
`liveness ⇒ genuineness` (`liveness_implies_genuineness_orFlex`), so
discharging genuineness reduces to discharging liveness. -/

/-- Genuineness for the Buganda flex disjunction holds against the
two-element witness state `{kingOpens, presConducts}`: each disjunct's
witness world survives both its own update and the joint orFlex update. -/
theorem flex_genuineness :
    PartialProp.genuineness PartialProp.orFlex kingOpensParl presConductsCeremony
      ⟨[W.kingOpens, W.presidentConducts], by simp⟩ := by
  apply PartialProp.liveness_implies_genuineness_orFlex
  exact ⟨⟨W.kingOpens, by simp, trivial, rfl⟩,
         ⟨W.presidentConducts, by simp, trivial, rfl⟩⟩


/-! ### Substrate observation: orFlex = orBelnap

NOT a Yagi claim — [belnap-1970] is not in his references.
In the substrate, `orFlex` is *definitionally* `orBelnap` (an abbrev in
`Semantics/Presupposition/Basic.lean`), and
`Studies/Geurts2005.lean` extends the identity three ways with
[geurts-2005]'s modal-disjunction view. We instantiate it at the
Buganda case for clarity. -/

/-- Substrate identity at the Buganda case: `flexDisj = orBelnap`. -/
theorem flexDisj_eq_orBelnap :
    flexDisj = PartialProp.orBelnap kingOpensParl presConductsCeremony :=
  rfl


/-! ### Negation interaction ([yagi-2025] §3.2 final paragraphs)

Yagi's *static* negation works fine — preserves presupposition, flips
assertion. His *dynamic* negation `s[¬(φ_p ∨ ψ_q)] = s/(s[χ][φ_p] ∪ s[χ][ψ_q])`
requires genuineness to hold within the scope of negation, which Yagi
calls "peculiar, given that we end up negating both disjuncts". The
peculiarity surfaces only at the dynamic level — at the static
`PartialProp.neg` connective, the assertion just flips and presupposition is
preserved (`neg_presup`); there is no genuineness check to violate.

We do not formalise the dynamic version here because it would require
the Update-Semantics state operator `s[¬φ] = s/s[φ]` paired with the
parametric flex update `s[χ][φ] ∪ s[ω][ψ]` of Yagi's eq. (13), neither
of which we have built. The static `negFlexDisj` truth-table below shows
the *intended* truth conditions (negation true at king-doesn't and
president-doesn't, where both disjuncts fail); Yagi's "peculiarity"
diagnosis lives at the dynamic level above this static reduction. -/

/-- Negation of the flexible accommodation disjunction. -/
def negFlexDisj : PartialProp W := PartialProp.neg flexDisj

/-- Static negation preserves the presupposition (substrate `neg_presup`). -/
theorem neg_flex_presup_preserved :
    negFlexDisj.presup = flexDisj.presup := PartialProp.neg_presup flexDisj

/-- Static negation gives the right truth values at the head-of-state worlds:
true at king-doesn't and president-doesn't (both disjuncts false). -/
theorem neg_flex_truth_table :
    negFlexDisj.eval W.kingOpens = .false ∧
    negFlexDisj.eval W.kingDoesnt = .true ∧
    negFlexDisj.eval W.presidentConducts = .false ∧
    negFlexDisj.eval W.presidentDoesnt = .true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [negFlexDisj, PartialProp.neg, flexDisj, PartialProp.orFlex, PartialProp.orBelnap, PartialProp.eval,
      kingOpensParl, presConductsCeremony, hasKing, hasPresident]


/-! ## [yagi-2025] example (8) Karttunen 1974: eq. (7) is too weak

[yagi-2025] §2.2 (between Def 3 and §2.3) considers a modification
to K&P, `Π(φ ∨ ψ) := Π(φ) ∨ Π(ψ)` (eq. (7)). This formula IS what
`PartialProp.orFlex.presup` computes. Yagi shows it correctly predicts (1c)
Buganda but is "too weak" for (8) [karttunen-1974]: "Either baldness
is not hereditary, or all of Bill's children are bald." Eq. (7) predicts
the tautological presupposition `⊤ ∨ Π(ψ) = ⊤`, but the empirical
intuition is that (8) presupposes Bill has children.

Important scope note: Yagi's §3.2 flexible-accommodation framework is
NOT subject to this critique — it handles the analog (14) correctly via
the `χ = ω = ⊤` accommodation default (only when that violates an
independent pragmatic principle does the split become non-trivial). The
critique here applies to the *static* `orFlex.presup` formula (which
matches eq. (7) at the presup level), not to the dynamic flex update
`s[χ][φ] ∪ s[ω][ψ]` of eq. (13), which we have not formalised. -/

/-- Worlds for example (8). -/
inductive W8 where
  | hasChildAllBald
  | hasChildSomeNotBald
  | noChild
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- "Bill has a child" — presupposition trigger for "all of Bill's children ...". -/
def billHasChild : W8 → Prop
  | .hasChildAllBald | .hasChildSomeNotBald => True
  | .noChild => False

instance : DecidablePred billHasChild
  | .hasChildAllBald | .hasChildSomeNotBald => isTrue trivial
  | .noChild => isFalse id

/-- "Baldness is not hereditary" — no presupposition. -/
def baldnessNotHereditary : PartialProp W8 where
  presup _ := True
  assertion _ := True

/-- "All of Bill's children are bald" — factive on `billHasChild`. -/
def allBillsChildrenBald : PartialProp W8 where
  presup := billHasChild
  assertion w := w = .hasChildAllBald

/-- The static flex disjunction for (8) — assertion ignored, only the
presup formula matters here. -/
def ex8FlexDisj : PartialProp W8 := PartialProp.orFlex baldnessNotHereditary allBillsChildrenBald

/-- The empirical presupposition Karttunen attributes to (8): "Bill has
children". This is the predicate that any adequate theory of disjunctive
projection should derive. -/
def ex8ExpectedPresup : W8 → Prop := billHasChild

/-- Eq. (7) predicts a tautological presupposition for (8): `orFlex.presup`
is universally `True` because the first disjunct is presuppositionless. -/
theorem ex7_presup_trivial_for_ex8 : ∀ w, ex8FlexDisj.presup w :=
  fun _ => Or.inl trivial

/-- The empirical presupposition is non-trivial: it fails at `noChild`. -/
theorem expected_presup_fails_at_noChild : ¬ex8ExpectedPresup W8.noChild := id

/-- [yagi-2025]'s eq. (7) critique made formal: the eq. (7) formula
(= `orFlex.presup`) does NOT match the empirical presupposition. Witness:
at `noChild`, eq. (7) says `True` (presup satisfied), but the empirical
intuition says `False` (presup failure — "Bill has children" doesn't hold).
This is the contrast Yagi flags as making eq. (7) "too weak". -/
theorem eq7_too_weak_for_ex8 :
    ex8FlexDisj.presup ≠ ex8ExpectedPresup := fun h =>
  expected_presup_fails_at_noChild (h ▸ ex7_presup_trivial_for_ex8 _)


/-! ## [yagi-2025] example (18) Beaver 2001:115: the unprincipled success

"Either John didn't solve the problem or Mary realized that the problem
is solved." The factive presupposition of "realize" does NOT project.
[yagi-2025] §3.2 final paragraphs: standard update semantics
correctly predicts non-projection here, while flexible accommodation may
predict it correctly *but for the wrong reason* — the incompatibility
that motivates accommodation in (1c) and (15) is absent in (18), so
genuineness should not even fire. The success is unprincipled.

Linglib's [karttunen-1973] formalisation
(`Studies/Karttunen1973.lean`) handles (18) via
the **asymmetric** `disjFilterLeft` rule (24b): when `¬A` entails `Π(B)`,
the presupposition is filtered. This is the principled alternative
that the symmetric variants (`orKPSymmetric`, `orPositive`) cannot offer. -/

/-- Worlds for example (18). -/
inductive W18 where
  | solvedRealized
  | solvedNotRealized
  | notSolved
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- "John solved the problem". -/
def solved : W18 → Prop
  | .solvedRealized | .solvedNotRealized => True
  | .notSolved => False

instance : DecidablePred solved
  | .solvedRealized | .solvedNotRealized => isTrue trivial
  | .notSolved => isFalse id

/-- "Mary realized the problem is solved" — factive: presupposes problem is solved. -/
def maryRealized : PartialProp W18 where
  presup := solved
  assertion w := w = .solvedRealized

/-- "John didn't solve the problem" — no presupposition. -/
def johnDidntSolve : PartialProp W18 where
  presup _ := True
  assertion w := ¬solved w

/-- The symmetric positive-antecedent `orPositive` overgenerates here:
predicts presupposition failure at `notSolved`, where the disjunction
should be defined-and-true. -/
theorem ex18_symmetric_orPositive_overgenerates :
    ¬(PartialProp.orPositive johnDidntSolve maryRealized).presup W18.notSolved := by
  rintro ⟨h, _, _⟩
  exact (h (fun (h' : solved W18.notSolved) => h') : solved W18.notSolved)

/-- `orFlex` predicts non-projection at `notSolved`. The proof goes
through the LEFT disjunct of `Π(φ) ∨ Π(ψ)`: `johnDidntSolve.presup` is
universally `True` (no presupposition). -/
theorem ex18_orFlex_no_projection_via_vacuous_left :
    (PartialProp.orFlex johnDidntSolve maryRealized).presup W18.notSolved :=
  Or.inl trivial

/-- The structural reason for `ex18_orFlex_no_projection_via_vacuous_left`:
`johnDidntSolve` has NO presupposition, so any `orFlex.presup` involving
it is universally satisfied — independently of `maryRealized.presup`. -/
theorem ex18_left_presup_vacuous : ∀ w, johnDidntSolve.presup w := fun _ => trivial

/-- [yagi-2025] §3.2's "unprincipled success" diagnosis made
structural: at `notSolved`, the right disjunct's presupposition `solved`
*fails*, so `(orFlex _ maryRealized).presup` would have NO support if
the left disjunct also had a presupposition. The success at (18) rides
entirely on the left disjunct being presuppositionless — which is an
accident of (18)'s lexical content, not a consequence of genuineness or
accommodation. The contrast: in (1c) Buganda, BOTH disjuncts carry
presuppositions, so `orFlex.presup` provides genuine accommodation work;
in (18), only the right disjunct does, so the left disjunct's vacuous
`True` carries the prediction unilaterally. -/
theorem ex18_unprincipled_in_right_presup_failure :
    ¬maryRealized.presup W18.notSolved ∧
    (PartialProp.orFlex johnDidntSolve maryRealized).presup W18.notSolved ∧
    (∀ w, johnDidntSolve.presup w) :=
  ⟨id, ex18_orFlex_no_projection_via_vacuous_left, ex18_left_presup_vacuous⟩

/-- [karttunen-1973]'s asymmetric rule (24b) — formalised in
`Studies/Karttunen1973.lean` as
`PartialProp.disjFilterLeft` — gives a *principled* derivation: `¬(¬solved) =
solved` entails the factive presupposition, so it is filtered. We invoke
the K1973 sibling theorem
`Karttunen1973.disjFilterLeft_eliminates_presup_when_neg_entails`. -/
theorem ex18_asymmetric_K1973_principled :
    (PartialProp.disjFilterLeft (fun w => ¬solved w) maryRealized).presup
      = fun _ => True := by
  apply Karttunen1973.disjFilterLeft_eliminates_presup_when_neg_entails
  intro w hw
  -- hw : ¬¬solved w, so solved w.
  exact (Classical.not_not.mp hw : maryRealized.presup w)


/-! ## Summary

Compact API restating the core verdicts. We keep only the headline
results — the per-failure detail theorems above already document the
content. -/

/-- `orFlex` satisfies both Yagi headline observations: (2a) correct
presupposition at the discriminating world, (2b) can be false. -/
theorem orFlex_satisfies_both :
    (∀ w, flexDisj.presup w ↔ expectedPresup w) ∧
    flexDisj.eval W.kingDoesnt = .false :=
  ⟨flex_correct_presup_iff_expected, flex_truth_table.2.1⟩

/-- The substrate-canonical orFlex / orBelnap / Geurts three-way
identity, instantiated at the Buganda case. The substrate-side identity
is definitional (`orFlex` is an abbrev for `orBelnap`); the Geurts side
is `Geurts2005.fromPartialProp_cell_iff_orBelnap`. -/
theorem orFlex_eq_orBelnap_at_buganda :
    PartialProp.orFlex (W := W) = PartialProp.orBelnap :=
  rfl

end Yagi2025
