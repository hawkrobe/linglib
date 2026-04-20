import Linglib.Core.SelectionFunction
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.FinitePMF

/-!
# Selectional Semantics for *will*
@cite{cariani-santorio-2018}

A **selectional** treatment of the future modal *will*: rather than
quantifying universally or existentially over a modal base of historical
alternatives, *will* applies its prejacent at a single **selected**
world picked out by a Stalnaker-style selection function indexed by a
modal parameter `f`.

`⟦will_f A⟧^{w,s,g} = 1  iff  ⟦A⟧^{s(w, g(f)), s, g} = 1`

where `s : SelectionFunction W` is a contextually supplied selection
function and `g(f)` is the relevant set of historical alternatives.

## Three constraints @cite{cariani-santorio-2018}

@cite{cariani-santorio-2018} argue that an adequate theory of *will*
must satisfy three constraints:

1. **Modal character**: *will* takes scope, interacts with negation and
   quantifiers, and embeds under attitudes — so it cannot be a pure
   present-tense or pure future-tense reference operator.
2. **Scopelessness**: under negation in matrix uses, `will ¬A` and
   `¬will A` are equivalent (Negation Swap, `negation_swap`). Universal
   quantification over a non-trivial modal base cannot deliver this
   (`universal_negation_swap_fails`).
3. **Cognitive role**: a sincere assertion of `will A` is licensed by
   ordinary, non-extreme credence in `A`, not credence 1
   (`cognitive_role`). A homogeneity / domain-width condition that
   requires uniform truth across the modal base would make assertion
   conditions too strong (`universalWill` collapses credence to 0/1).

## What's here

- `willSem`, `willSem_def`: the selectional truth-condition.
- `negation_swap`, `will_excluded_middle`, `unembedded_collapse`:
  the three core scopelessness/CEM/factivity-on-base theorems.
- `will_eq_A_on_modalParam`: **content transparency** §8.1 footnote 30.
  As `Set W`, `‖will A‖` and `‖A‖` agree on every world in the modal
  parameter `f`. This is the substantive transparency claim from
  which the cognitive-role prediction follows.
- `Valid2`: validity₂ from paper §6 (truth at every ⟨s, f, w⟩, not
  just at the context). `valid2_will_excluded_middle` and
  `valid2_negation_swap` recast the matrix theorems in this stronger
  validity notion.
- `willHistorical`: `will` over the metaphysical modal base from
  `Core/Modality/HistoricalAlternatives.lean` — the bridge to the
  branching-time substrate.
- `universalWill`: the universal-quantifier reading used as a foil
  in @cite{cariani-santorio-2018}'s arguments. Shown to violate
  Negation Swap (`universal_negation_swap_fails`).
- `cognitive_role`: under any credence supported on the modal
  parameter, `μ(‖will A‖) = μ(‖A‖)` — the §8.1 prediction that
  decisively distinguishes selectional from universal accounts.
-/

set_option autoImplicit false

namespace Semantics.Modality.Selectional

open _root_.Core (SelectionFunction FinitePMF)
open _root_.Core.Modality.HistoricalAlternatives

variable {W : Type*}

/-! ## §1. The selectional truth-condition -/

/-- Selectional truth-condition for *will* @cite{cariani-santorio-2018}.

    `willSem s A f w` is true iff the prejacent `A` holds at the world
    selected by `s` from the modal parameter `f` at `w`.

    Reading: "will A" at `w` says A holds at the unique selected
    historical alternative `s.sel w f`. -/
def willSem (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) : Prop :=
  A (s.sel w f)

@[simp] theorem willSem_def (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ↔ A (s.sel w f) := Iff.rfl

/-- `willSem` is decidable when its prejacent is. -/
instance willSem_decidable (s : SelectionFunction W) (A : W → Prop)
    [DecidablePred A] (f : Set W) (w : W) :
    Decidable (willSem s A f w) :=
  inferInstanceAs (Decidable (A _))

/-- Bool-valued selectional `will` — useful for credence calculations
    via `Core.FinitePMF.probOf` (which takes Bool predicates). -/
def willSemBool (s : SelectionFunction W) (A : W → Bool)
    (f : Set W) (w : W) : Bool :=
  A (s.sel w f)

@[simp] theorem willSemBool_def (s : SelectionFunction W) (A : W → Bool)
    (f : Set W) (w : W) :
    willSemBool s A f w = A (s.sel w f) := rfl

/-! ## §2. Scopelessness, CEM, and unembedded collapse -/

/-- **Negation Swap** @cite{cariani-santorio-2018}: under selectional
    semantics, *will* commutes with negation. `will ¬A ↔ ¬ will A`.

    Derived from `Core.SelectionFunction.sel_neg_swap` — the structural
    origin is single-valuedness of selection: the selected world either
    satisfies `A` or it doesn't. -/
theorem negation_swap (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s (fun w' => ¬ A w') f w ↔ ¬ willSem s A f w :=
  s.sel_neg_swap A f w

/-- **Will Excluded Middle** @cite{cariani-santorio-2018}: `will A ∨
    will ¬A` holds at every point of evaluation.

    Derived from `Core.SelectionFunction.sel_em` — the disjunction
    holds because `s.sel w f` is a single world, on which `A` is
    either true or false. This is the selectional analogue of
    Conditional Excluded Middle for Stalnaker counterfactuals; both
    share the same structural origin in `sel_em`. -/
theorem will_excluded_middle (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ∨ willSem s (fun w' => ¬ A w') f w :=
  s.sel_em A f w

/-- **Unembedded collapse** @cite{cariani-santorio-2018} eq. (17):
    when the evaluation world is itself in the modal parameter,
    Centering forces the selected world to be `w`, so `will A`
    reduces to `A w`.

    This explains the apparent factivity of unembedded *will*-claims
    when the speaker presupposes that the actual world is among the
    historical alternatives. -/
theorem unembedded_collapse (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) (hw : w ∈ f) :
    willSem s A f w ↔ A w := by
  unfold willSem
  rw [s.centering w f hw]

/-! ## §3. Content transparency

The substantive transparency claim of @cite{cariani-santorio-2018}
§8.1 footnote 30: as a *proposition* (set of worlds), `‖will A‖` is
not just `‖A‖` — they may diverge outside the modal parameter. But
*restricted to the modal parameter*, they agree. This is the
content-level fact from which the cognitive-role prediction follows. -/

/-- **Content transparency** @cite{cariani-santorio-2018} §8.1: on the
    modal parameter `f`, the truth set of `will A` coincides with the
    truth set of `A`. Pointwise consequence of Centering. -/
theorem will_eq_A_on_modalParam (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) :
    ∀ w ∈ f, willSem s A f w ↔ A w :=
  fun w hw => unembedded_collapse s A f w hw

/-- Conjunction transparency: on `f`, `will (A ∧ B)` and `will A ∧
    will B` coincide pointwise. -/
theorem will_and_eq_will_and_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' => A w' ∧ B w') f w ↔
              (willSem s A f w ∧ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-- Disjunction transparency: on `f`, `will (A ∨ B)` and `will A ∨
    will B` coincide pointwise. -/
theorem will_or_eq_will_or_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' => A w' ∨ B w') f w ↔
              (willSem s A f w ∨ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-- **Set-level Content Transparency** @cite{cariani-santorio-2018}
    §8.1: as *propositions* (sets of worlds), `‖will_f A‖` and `‖A‖`
    coincide on the modal parameter `f`. The cognitive-role argument
    (paper §8.1) hinges on this set equality, not just on pointwise
    truth: it is the equality of truth-sets — restricted to `f` — that
    underwrites `cognitive_role`. -/
theorem will_inter_modalParam_eq (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) :
    {w | willSem s A f w} ∩ f = {w | A w} ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · exact fun ⟨h1, h2⟩ => ⟨(unembedded_collapse s A f w h2).mp h1, h2⟩
  · exact fun ⟨h1, h2⟩ => ⟨(unembedded_collapse s A f w h2).mpr h1, h2⟩

/-- **Conjunction transparency at the set level** @cite{cariani-santorio-2018}
    §8.1: on `f`, the truth-set of `will (A ∧ B)` coincides with the
    intersection of the truth-sets of `will A` and `will B`.
    Equivalently: `‖will (A ∧ B)‖_f = ‖will A‖_f ∩ ‖will B‖_f`.
    Follows from single-valuedness of selection: at each world, all three
    propositions are evaluated at the same point `s.sel w f`. -/
theorem will_and_inter_modalParam_eq (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    {w | willSem s (fun w' => A w' ∧ B w') f w} ∩ f =
      ({w | willSem s A f w} ∩ {w | willSem s B f w}) ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · exact fun ⟨⟨hA, hB⟩, hw⟩ => ⟨⟨hA, hB⟩, hw⟩
  · exact fun ⟨⟨hA, hB⟩, hw⟩ => ⟨⟨hA, hB⟩, hw⟩

/-- **Disjunction transparency at the set level** @cite{cariani-santorio-2018}
    §8.1: on `f`, the truth-set of `will (A ∨ B)` coincides with the
    union of the truth-sets of `will A` and `will B`. Selectional `will`
    distributes over disjunction at the set level — a substantively
    stronger claim than the universal account, which over-distributes. -/
theorem will_or_union_modalParam_eq (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    {w | willSem s (fun w' => A w' ∨ B w') f w} ∩ f =
      ({w | willSem s A f w} ∪ {w | willSem s B f w}) ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · exact fun ⟨h, hw⟩ => ⟨h, hw⟩
  · exact fun ⟨h, hw⟩ => ⟨h, hw⟩

/-! ## §4. Validity₂ (paper §6)

@cite{cariani-santorio-2018} distinguish *validity₁* (truth at the
context of utterance) from *validity₂* (truth at *every* index
⟨w, s, g⟩). The matrix scopelessness theorems are validity₁ claims;
the more interesting ones are validity₂. -/

/-- **Validity₂**: a propositional schema is valid₂ when it holds at
    every ⟨selection function, modal parameter, world⟩ triple. -/
def Valid2 (φ : SelectionFunction W → Set W → W → Prop) : Prop :=
  ∀ s f w, φ s f w

/-- **Validity₁** (paper §6): a propositional schema is valid₁ at a
    given context — fixed selection function `sCtx`, modal parameter
    `fCtx`, and world `wCtx` determined by the utterance — when it
    holds at *that* index.

    This is the weaker of the two validity notions @cite{cariani-santorio-2018}
    distinguish in §6. The postsemantic indeterminacy phenomena live
    here: a schema can be valid₁ at every context without being valid₂.

    Marked `@[reducible]` so it unfolds automatically at use sites:
    `Valid1 φ sCtx fCtx wCtx` is just `φ sCtx fCtx wCtx`, and treating
    it as a wrapper would force every downstream user to `unfold Valid1`. -/
@[reducible] def Valid1 (φ : SelectionFunction W → Set W → W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) : Prop :=
  φ sCtx fCtx wCtx

/-- **Validity₂ implies Validity₁ at every context** (paper §6): if a
    schema holds at every index, it holds in particular at the
    contextually-determined index. The converse fails — postsemantic
    indeterminacy is precisely the gap between the two. -/
theorem valid2_implies_valid1 {φ : SelectionFunction W → Set W → W → Prop}
    (h : Valid2 φ) (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1 φ sCtx fCtx wCtx :=
  h sCtx fCtx wCtx

/-- Negation Swap is **valid₂** (paper §6). -/
theorem valid2_negation_swap (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willSem s (fun w' => ¬ A w') f w ↔ ¬ willSem s A f w :=
  fun s f w => negation_swap s A f w

/-- Will Excluded Middle is **valid₂** (paper §6, §7). -/
theorem valid2_will_excluded_middle (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willSem s A f w ∨ willSem s (fun w' => ¬ A w') f w :=
  fun s f w => will_excluded_middle s A f w

/-- **Postsemantic Will Excluded Middle** (paper §7): the disjunction
    `will A ∨ will ¬A` holds at the context of utterance, derived as
    a Validity₁ specialization of `valid2_will_excluded_middle`. The
    paper distinguishes Postsemantic CEM (Validity₁) from Compositional
    CEM (Validity₂); under a single contextually-fixed selection
    function, the former follows from the latter. -/
theorem postsemantic_will_excluded_middle (A : W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1 (W := W) (fun s f w =>
      willSem s A f w ∨ willSem s (fun w' => ¬ A w') f w)
      sCtx fCtx wCtx :=
  valid2_implies_valid1 (valid2_will_excluded_middle A) sCtx fCtx wCtx

/-! ## §5. Bridge to historical alternatives

Selectional `will` parameterized by the metaphysical modal base of
@cite{condoravdi-2002} — the historical-alternatives substrate from
`Core/Modality/HistoricalAlternatives.lean`. -/

/-- **Selectional `will` over historical alternatives.** Evaluates
    the prejacent at the world selected from the metaphysical modal
    base at ⟨w, t⟩. -/
def willHistorical {Time : Type*} (s : SelectionFunction W)
    (history : WorldHistory W Time) (A : W → Prop)
    (w : W) (t : Time) : Prop :=
  willSem s A (metaphysicalBase history w t) w

/-- When the world-history relation is reflexive (the standard case
    @cite{condoravdi-2002} §4.1 condition (i)), `willHistorical`
    collapses to its prejacent: `will_t A` at `w` reduces to `A w`. -/
theorem willHistorical_reflexive_collapse {Time : Type*}
    (s : SelectionFunction W) {history : WorldHistory W Time}
    (hRefl : history.reflexive) (A : W → Prop) (w : W) (t : Time) :
    willHistorical s history A w t ↔ A w := by
  unfold willHistorical
  apply unembedded_collapse
  exact hRefl ⟨w, t⟩

/-! ## §6. The universal-quantifier foil

The universal-quantifier reading is what @cite{cariani-santorio-2018}
argue against. Section 8.1's cognitive-role argument is decisive
because the selectional account validates `μ(‖will A‖) = μ(A)` while
the universal account collapses credence into a 0/1 step function. -/

/-- The universal-quantifier reading of `will`: true at `w` iff `A`
    holds at every world in the modal parameter. The world `w` itself
    is *not* used — universal `will` is index-independent. -/
def universalWill (A : W → Prop) (f : Set W) (_w : W) : Prop :=
  ∀ w' ∈ f, A w'

/-- **Negation Swap fails for universal `will`.** When the modal
    parameter contains both an `A`-world and a `¬A`-world, the
    universal-quantifier reading violates `¬∀ ↔ ∀¬`.

    Witness: ∀A is false (some w₂ ∉ A), but ∀¬A is also false (some
    w₁ ∈ A). So the biconditional is `false ↔ true`. -/
theorem universal_negation_swap_fails {A : W → Prop} {f : Set W} {w : W}
    (h : ∃ w₁ ∈ f, ∃ w₂ ∈ f, A w₁ ∧ ¬ A w₂) :
    ¬ (universalWill (fun w' => ¬ A w') f w ↔ ¬ universalWill A f w) := by
  obtain ⟨w₁, hw₁f, w₂, hw₂f, hA1, hnA2⟩ := h
  unfold universalWill
  intro hiff
  have hLHS_false : ¬ (∀ w' ∈ f, ¬ A w') :=
    fun hAll => hAll w₁ hw₁f hA1
  have hRHS_true : ¬ (∀ w' ∈ f, A w') :=
    fun hAll => hnA2 (hAll w₂ hw₂f)
  exact hLHS_false (hiff.mpr hRHS_true)

/-! ## §7. Cognitive role (paper §8.1)

The selectional analysis predicts `μ(‖will A‖_f) = μ(‖A‖_f)` whenever
the credence `μ` is supported on the modal parameter `f`. This
matches the empirically attested gradedness of *will*-credences and
distinguishes selectional from universal accounts. -/

/-- **Cognitive role** @cite{cariani-santorio-2018} §8.1: under any
    credence `μ` supported on the modal parameter `f` (every world
    outside `f` has zero mass), the credence assigned to `will A`
    equals the credence assigned to `A` itself.

    Reading: assertion of `will A` is licensed by ordinary, non-extreme
    credence in `A`. The universal-quantifier reading instead forces
    `μ(‖∀ A‖) ∈ {0, 1}` (collapsing into a step function on whether
    `f ⊆ A`), which is empirically wrong. -/
theorem cognitive_role [Fintype W] (s : SelectionFunction W)
    (A : W → Bool) (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => A (s.sel w f)) = μ.probOf A := by
  unfold FinitePMF.probOf
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  by_cases hw : w ∈ f
  · congr 1
    rw [s.centering w f hw]
  · rw [h_supp w hw]; simp

/-- **Cognitive role for conjunctions** @cite{cariani-santorio-2018}
    §8.1: the transparency identity lifts to compositional prejacents.
    `μ(‖will (A ∧ B)‖) = μ(‖A ∧ B‖)`. Direct corollary of
    `cognitive_role` applied to the pointwise conjunction `fun w => A w && B w`. -/
theorem cognitive_role_and [Fintype W] (s : SelectionFunction W)
    (A B : W → Bool) (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => (A (s.sel w f)) && (B (s.sel w f))) =
      μ.probOf (fun w => A w && B w) :=
  cognitive_role s (fun w => A w && B w) f μ h_supp

/-- **Cognitive role for disjunctions** @cite{cariani-santorio-2018}
    §8.1: `μ(‖will (A ∨ B)‖) = μ(‖A ∨ B‖)`. Direct corollary of
    `cognitive_role` applied to the pointwise disjunction. -/
theorem cognitive_role_or [Fintype W] (s : SelectionFunction W)
    (A B : W → Bool) (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => (A (s.sel w f)) || (B (s.sel w f))) =
      μ.probOf (fun w => A w || B w) :=
  cognitive_role s (fun w => A w || B w) f μ h_supp

/-- **Cognitive role for negations** @cite{cariani-santorio-2018} §8.1:
    `μ(‖will ¬A‖) = μ(‖¬A‖)`. By Negation Swap and transparency, the
    credence in *will ¬A* matches the credence in `¬A`. -/
theorem cognitive_role_not [Fintype W] (s : SelectionFunction W)
    (A : W → Bool) (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => !(A (s.sel w f))) = μ.probOf (fun w => !(A w)) :=
  cognitive_role s (fun w => !(A w)) f μ h_supp

/-! ### Prop-friendly cognitive role bridge

Wrappers that accept `Prop`-valued prejacents with a `DecidablePred` instance,
coercing through `decide` so callers can stay in the Prop layer (matching the
rest of `Selectional.lean`). Internally these delegate to the Bool variants
because `FinitePMF.probOf` is Bool-typed by design (an intrinsic computational
boundary, not a Bool stand-in for Prop content). -/

/-- Prop-friendly variant of `cognitive_role`: under any credence supported on
    `f`, `μ(‖will A‖) = μ(‖A‖)` for any decidable `Prop` prejacent. -/
theorem cognitive_role_prop [Fintype W] (s : SelectionFunction W)
    (A : W → Prop) [DecidablePred A] (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => decide (A (s.sel w f))) = μ.probOf (fun w => decide (A w)) :=
  cognitive_role s (fun w => decide (A w)) f μ h_supp

/-- Prop-friendly variant of `cognitive_role_and`. -/
theorem cognitive_role_and_prop [Fintype W] (s : SelectionFunction W)
    (A B : W → Prop) [DecidablePred A] [DecidablePred B]
    (f : Set W) (μ : FinitePMF W) (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => decide (A (s.sel w f)) && decide (B (s.sel w f))) =
      μ.probOf (fun w => decide (A w) && decide (B w)) :=
  cognitive_role s (fun w => decide (A w) && decide (B w)) f μ h_supp

/-- Prop-friendly variant of `cognitive_role_or`. -/
theorem cognitive_role_or_prop [Fintype W] (s : SelectionFunction W)
    (A B : W → Prop) [DecidablePred A] [DecidablePred B]
    (f : Set W) (μ : FinitePMF W) (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => decide (A (s.sel w f)) || decide (B (s.sel w f))) =
      μ.probOf (fun w => decide (A w) || decide (B w)) :=
  cognitive_role s (fun w => decide (A w) || decide (B w)) f μ h_supp

/-- Prop-friendly variant of `cognitive_role_not`. -/
theorem cognitive_role_not_prop [Fintype W] (s : SelectionFunction W)
    (A : W → Prop) [DecidablePred A] (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => !(decide (A (s.sel w f)))) =
      μ.probOf (fun w => !(decide (A w))) :=
  cognitive_role s (fun w => !(decide (A w))) f μ h_supp

/-! ## §9. Multi-premise validity (paper §6)

@cite{cariani-santorio-2018} §6 distinguishes Validity₁ (truth at the
context) from Validity₂ (truth at every index). Both notions extend
to multi-premise consequence: an argument `H₁, …, Hₙ ⊨ C` is valid₂
when every index that satisfies all premises also satisfies the
conclusion. -/

/-- **Multi-premise validity₂**: an argument `premises ⊨ conclusion`
    holds at every ⟨s, f, w⟩ — if all premises are true at the index,
    the conclusion is too. -/
def Valid2Arg (premises : List (SelectionFunction W → Set W → W → Prop))
    (conclusion : SelectionFunction W → Set W → W → Prop) : Prop :=
  ∀ s f w, (∀ φ ∈ premises, φ s f w) → conclusion s f w

/-- **Multi-premise validity₁** at a context: at the contextually-fixed
    `⟨sCtx, fCtx, wCtx⟩`, if all premises hold then so does the
    conclusion. -/
@[reducible] def Valid1Arg
    (premises : List (SelectionFunction W → Set W → W → Prop))
    (conclusion : SelectionFunction W → Set W → W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) : Prop :=
  (∀ φ ∈ premises, φ sCtx fCtx wCtx) → conclusion sCtx fCtx wCtx

/-- **Validity₂Arg implies Validity₁Arg at every context**: if an
    argument is valid₂, it is valid₁ at the context of utterance. -/
theorem valid2Arg_implies_valid1Arg
    {premises : List (SelectionFunction W → Set W → W → Prop)}
    {conclusion : SelectionFunction W → Set W → W → Prop}
    (h : Valid2Arg premises conclusion)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1Arg premises conclusion sCtx fCtx wCtx :=
  h sCtx fCtx wCtx

/-- **Modus ponens for selectional `will`** is valid₂: from
    `will A ↔ will B` and `will A`, conclude `will B`. A trivial
    illustration of the multi-premise architecture. -/
theorem valid2_will_modus_ponens (A B : W → Prop) :
    Valid2Arg (W := W)
      [fun s f w => willSem s A f w ↔ willSem s B f w,
       fun s f w => willSem s A f w]
      (fun s f w => willSem s B f w) := by
  intro s f w hPrem
  have hIff : willSem s A f w ↔ willSem s B f w :=
    hPrem (fun s f w => willSem s A f w ↔ willSem s B f w) (by simp)
  have hA : willSem s A f w :=
    hPrem (fun s f w => willSem s A f w) (by simp)
  exact hIff.mp hA

/-! ## §8. *Would* as past-tense morphological derivative of *will*
@cite{cariani-santorio-2018} §5.3.2

@cite{cariani-santorio-2018} §5.3.2 argues that *would* is not a separate
modal operator but the past-tense morphological form of *will*. Both
share the same selectional truth-condition; they differ only in the
modal parameter `f` made available by tense — present *will*
parameterises `f` to the historical alternatives at the speech time;
past *would* parameterises `f` to a counterfactual base, typically
supplied by an *if*-clause.

The shared truth-condition means every theorem about *will* lifts
automatically to *would*: Negation Swap, Will Excluded Middle, the
collapse-on-membership theorem, the cognitive-role prediction. This
is the formal payoff of analysing *would* as a tense form of *will*
rather than as an independent operator: the entire §2–§7 architecture
is reused unchanged. -/

/-- **Selectional `would`** @cite{cariani-santorio-2018} §5.3.2:
    definitionally identical to `willSem`. The morphological past-tense
    distinction does not change the semantic clause; it only changes
    which modal parameter is supplied by context. -/
def wouldSem (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willSem s A f w

@[simp] theorem wouldSem_def (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    wouldSem s A f w ↔ A (s.sel w f) := Iff.rfl

/-- **Past-tense morphology = parameter shift, not semantic shift**
    @cite{cariani-santorio-2018} §5.3.2: *would* and *will* have the
    same selectional truth-condition. The difference is purely in the
    modal parameter `f` supplied by the tense morpheme. -/
theorem wouldSem_eq_willSem (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    wouldSem s A f w = willSem s A f w := rfl

/-- **Would Excluded Middle**, lifted from `will_excluded_middle` via
    the morphological identity. -/
theorem would_excluded_middle (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    wouldSem s A f w ∨ wouldSem s (fun w' => ¬ A w') f w :=
  will_excluded_middle s A f w

/-- **Would Negation Swap**, lifted from `negation_swap`. -/
theorem would_negation_swap (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    wouldSem s (fun w' => ¬ A w') f w ↔ ¬ wouldSem s A f w :=
  negation_swap s A f w

/-- **Would-Centering / unembedded collapse for *would***: when `w` is
    in the modal parameter, *would A* collapses to `A w`, lifted from
    `unembedded_collapse`. -/
theorem would_unembedded_collapse (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) (hw : w ∈ f) :
    wouldSem s A f w ↔ A w :=
  unembedded_collapse s A f w hw

/-- **Would Excluded Middle is valid₂**, by the same argument as
    `valid2_will_excluded_middle`. -/
theorem valid2_would_excluded_middle (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      wouldSem s A f w ∨ wouldSem s (fun w' => ¬ A w') f w :=
  fun s f w => would_excluded_middle s A f w

/-- **Would Negation Swap is valid₂**. -/
theorem valid2_would_negation_swap (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      wouldSem s (fun w' => ¬ A w') f w ↔ ¬ wouldSem s A f w :=
  fun s f w => would_negation_swap s A f w

end Semantics.Modality.Selectional
