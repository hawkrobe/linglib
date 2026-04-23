import Linglib.Core.Mereology
import Linglib.Theories.Semantics.Truthmaker.Inexact
import Linglib.Theories.Semantics.Truthmaker.Entailment

/-! # Bondarenko & Elliott (2026) @cite{bondarenko-elliott-2026}

**Monotonicity via mereology in the semantics of attitude reports.**
*Semantics and Pragmatics* 19(2). DOI: 10.3765/sp.19.2.

## Empirical puzzle (@cite{sharvit-2024})

NPI licensing in negated belief reports patterns differently for
complement clauses vs. relative clauses inside a singular definite
(@cite{bondarenko-elliott-2026} eq. 2):

```
*Katya doesn't believe [the rumor [that Anton has ever spread]].
 Katya doesn't believe [the rumor [that Anton has ever snowboarded]].
```

The puzzle: weak NPIs (any/ever) require a **Strawson Downward-Entailing**
(SDE, eq. 18a) and **not Strawson Upward-Entailing** (not-SUE, eq. 18b)
environment per the licensing condition (eq. 21). Two existing approaches
both fail (@cite{bondarenko-elliott-2026} §3.2):

- **Subset semantics** (`CONT(x) ⊆ ⟦S⟧`): *uniqueness collapse* (eq. 24)
  makes singular definites both SUE and SDE, so NPIs should be allowed
  even in positive belief reports — wrong.
- **Equality semantics** (`CONT(x) = ⟦S⟧`): *functionality* makes the
  environment neither SUE nor SDE — NPIs blocked everywhere — wrong.

## Proposal (@cite{bondarenko-elliott-2026} §4)

Adopt EQUALITY semantics (eq. 10) and add three mereological constraints:

- **MSI** (eq. 44): `CONT` preserves proper parthood. Every proper
  informational part `p' < CONT(x)` is the content of some proper sub-x.
- **MSO** (eq. 48): `THEME` preserves sub-eventualities. Every proper
  sub-`e` has a corresponding proper sub-`THEME(e)`.
- **TECM** (eq. 59): For believe-class predicates,
  `CONT(e) = CONT(THEME(e))`.

**Result** (Section 5, eqs. 66–73): the Sharvit configuration becomes
- Positive `Katya believes the rumor that p` is **SUE not SDE** (eq. 66) —
  doesn't license NPIs.
- Negative `Katya doesn't believe the rumor that p` is **SDE not SUE**
  (eq. 67) — licenses NPIs.

The contrast in (2) follows.

## Main results

- `believes_closure_under_entailment` (paper eq. 45) — MSI ⇒ positive
  belief is closed under informational entailment (direct-CP version).
- `not_believes_reverses` (eq. 46) — MSI ⇒ negation reverses the
  direction (direct-CP version).
- **`positive_sharvit_closure`** (paper eq. 69, §5) — the full Sharvit
  configuration: under MSI/MSO/TECM/BelievingDIV/RumorDIV/WorldLocatedDIV,
  if `M believes the rumor that p` and `p' < p` then `M believes the
  rumor that p'`. The chain `TECM ∘ MSI ∘ BelievingDIV ∘ WorldLocatedDIV
  ∘ MSO ∘ RumorDIV ∘ TECM`.
- **`negated_sharvit_SDE`** (paper eq. 72, §5) — contrapositive: the
  negated configuration is SDE wrt the restrictor.
- **`negated_sharvit_not_SUE`** (paper eq. 73, §5) — concrete witness
  model showing the negated configuration is *not* SUE wrt the
  restrictor. Combined with `negated_sharvit_SDE` this gives the
  **full SDE-and-not-SUE monotonicity profile** that the NPI licensing
  condition (paper eq. 21) requires. **The strongest theorem of the
  paper** — captures Sharvit's empirical contrast in (2).
- `believes_closure_under_conjunction` (§6.1, eq. 79) — summation
  closure on believings + content-of-sum-is-meet ⇒ closure under ∧.
- `Mereology.not_isContentPart_of_singleton_not_le` (§6.3, eq. 95) —
  generic Mereology lemma; the paper's discriminating witness for
  conjunctive parthood (Jago Def 5) is a one-line application.
- `believes_does_not_always_close_under_intersection` — cross-framework:
  B&E's mereological `Believes` does NOT close under conjunction the way
  Hintikka's `boxAt` does, witnessed by a non-believings-closed model.

## Implementation notes

- *Informational parthood* (paper eq. 43, `p ≤ q iff p ⊇ q`) is the
  direction-flip of pointwise `≤` on `Set W`. We use the paper's
  convention via `propLE` for paper fidelity.
- The §5 theorems use the world parameter `w` via an abstract
  `located : V → W → Prop` relation with a `WorldLocatedDIV`
  downward-closure axiom (paper fn. 2: "possible worlds are maximal
  eventualities"). The simpler direct-CP closure lemmas (§4 / eqs.
  45-46) drop the world since it threads uniformly.
- `RumorDIV` (parts of rumors are rumors) is an explicit axiom; the
  paper handwaves it in §4.4 ("rumors, much like more concrete
  entities, have a mereological structure") without formalizing.

-/

namespace Phenomena.Attitudes.Studies.BondarenkoElliott2026

-- ════════════════════════════════════════════════════
-- § 1. Informational Parthood (paper eq. 43)
-- ════════════════════════════════════════════════════

section InfoParthood
variable {W : Type*}

/-- **Informational parthood for propositions** (paper eq. 43):
    `p ≤_BE q` iff `p` is semantically entailed by `q` (`p ⊇ q`).
    Smaller `p` = bigger world set = weaker proposition.

    Thin alias for the *swapped* `Set W` order: `propLE p q := q ≤ p`.
    Reflexivity, transitivity, and `<`-extraction lemmas all come from
    mathlib's `Preorder (Set W)` via this alias. We expose the
    paper-named symbols for docstring fidelity, not as a new ontology. -/
abbrev propLE (p q : Set W) : Prop := q ≤ p

/-- Proper informational parthood: `propLT p q := q < p`. -/
abbrev propLT (p q : Set W) : Prop := q < p

end InfoParthood

-- ════════════════════════════════════════════════════
-- § 2. Constraints on the lexical maps
-- ════════════════════════════════════════════════════

section Constraints
variable {V E W : Type*} [Preorder V] [Preorder E]

/-- **MSI** — *Mapping to Sub-parts of the Input* (paper eq. 44).
    A content function preserves proper informational parthood:
    every proper part `p' <_BE CONT(x)` is the content of some proper sub-`x`.

    See `MSI_iff_strictPartReflecting` for the identification with the
    generic `Mereology.StrictPartReflecting` (instantiated at the
    `OrderDual` of `Set W`'s subset order, since paper eq. 43 uses the
    flipped convention `p' <_BE p` iff `p ⊊ p'`). -/
def MSI (CONT : V → Option (Set W)) : Prop :=
  ∀ ⦃x p p'⦄, CONT x = some p → propLT p' p →
    ∃ x', x' < x ∧ CONT x' = some p'

/-- **MSO** — *Mapping to Sub-parts of the Output* (paper eq. 48).
    A theme function preserves proper sub-eventualities:
    every proper sub-`e` has a corresponding proper sub-`THEME(e)`.

    Equivalent to `Mereology.StrictPartPreserving` (the relationship is
    `Iff.rfl` since both use the standard `<` on `E`). -/
def MSO (THEME : V → Option E) : Prop :=
  ∀ ⦃e e' te⦄, e' < e → THEME e = some te →
    ∃ x', x' < te ∧ THEME e' = some x'

/-- MSO is exactly `Mereology.StrictPartPreserving`. -/
theorem MSO_iff_strictPartPreserving (THEME : V → Option E) :
    MSO THEME ↔ Mereology.StrictPartPreserving THEME := Iff.rfl

/-- **TECM** — *Theme-Event Content Matching* (paper eqs. 59, 65).
    For `believe`-class predicates `P`, the content of an event equals
    the content of its theme.

    Stated as `Option`-equality (faithful to the paper's eq. 65 form
    `CONT(e) = CONT(THEME(e))`). The paper restricts to
    `e ∈ Dom(CONT) ∩ Dom(THEME)`; this restriction is implicit here
    since when both `CONT_v e` and `CONT_e te` are `none`, the
    equality is vacuous. -/
def TECM (P : V → Prop) (CONT_v : V → Option (Set W))
    (CONT_e : E → Option (Set W)) (THEME : V → Option E) : Prop :=
  ∀ ⦃e te⦄, P e → THEME e = some te → CONT_v e = CONT_e te

/-- The believe-predicate's holder is preserved under parthood. -/
def HolderPreservedUnderParts (HOLDER : V → Option E) : Prop :=
  ∀ ⦃e e' M⦄, HOLDER e = some M → e' ≤ e → HOLDER e' = some M

/-- **Believing-DIV** (paper footnote 18). All parts of a believing-event
    are themselves believing-events with the same holder. The mereological
    analogue of *divisive reference* (@cite{cheng-1973} for mass nouns).

    Factored as the conjunction of two reusable conditions:
    `Mereology.DIV believe` (every part of a believing is itself a
    believing — the actual divisive-reference clause) and
    `HolderPreservedUnderParts HOLDER` (the same holder threads through
    all parts of a single eventuality). -/
def BelievingDIV (believe : V → Prop) (HOLDER : V → Option E) : Prop :=
  Mereology.DIV believe ∧ HolderPreservedUnderParts HOLDER

end Constraints

-- ════════════════════════════════════════════════════
-- § 3. Equality semantics for "M believes p"
-- ════════════════════════════════════════════════════

/-- Equality semantics for `Mitya believes p` (paper eq. 11, simplified):
    there exists a believing-eventuality with holder `M` and content `p`.

    The paper has `∃e ≤ w[…]` for "located in world `w`"; for the
    Strawson-entailment claims about *propositions* (sets of worlds) the
    world parameter doesn't enter the proof structure, so we drop it. -/
def Believes {V E W : Type*} (believe : V → Prop) (HOLDER : V → Option E)
    (CONT : V → Option (Set W)) (M : E) (p : Set W) : Prop :=
  ∃ e, believe e ∧ HOLDER e = some M ∧ CONT e = some p

-- ════════════════════════════════════════════════════
-- § 4. Closure under entailment from MSI (paper eqs. 45–46)
-- ════════════════════════════════════════════════════

section Closure
variable {V E W : Type*} [Preorder V]
  {believe : V → Prop} {HOLDER : V → Option E} {CONT : V → Option (Set W)}

/-- **Lemma — paper eq. 45**: MSI implies positive belief is closed under
    informational entailment. If `M` believes `p` and `p' <_BE p`
    (i.e., `p ⊋ p'` as sets — `p'` is properly weaker), then `M`
    believes `p'`.

    Proof (paper sketch): from `Believes M p` get a believing-`e` with
    `CONT(e) = p`. By MSI applied to `p' < p = CONT(e)`, find `e' < e`
    with `CONT(e') = p'`. By BelievingDIV, `e'` is itself a believing
    with holder `M`. -/
theorem believes_closure_under_entailment
    (h_msi : MSI CONT) (h_div : BelievingDIV believe HOLDER)
    {M : E} {p p' : Set W}
    (h_lt : propLT p' p) (h_bel : Believes believe HOLDER CONT M p) :
    Believes believe HOLDER CONT M p' := by
  obtain ⟨e, hbel, hhol, hcont⟩ := h_bel
  obtain ⟨e', hlt, hcont'⟩ := h_msi hcont h_lt
  refine ⟨e', h_div.1 e e' hbel (le_of_lt hlt),
          h_div.2 hhol (le_of_lt hlt), hcont'⟩

/-- **Lemma — paper eq. 46**: MSI implies negated belief is *downward*
    entailing in the propositional argument. If `¬Believes M p'` and
    `p' <_BE p`, then `¬Believes M p`. -/
theorem not_believes_reverses
    (h_msi : MSI CONT) (h_div : BelievingDIV believe HOLDER)
    {M : E} {p p' : Set W}
    (h_lt : propLT p' p)
    (h_neg : ¬ Believes believe HOLDER CONT M p') :
    ¬ Believes believe HOLDER CONT M p :=
  fun h_bel => h_neg
    (believes_closure_under_entailment h_msi h_div h_lt h_bel)

end Closure

-- ════════════════════════════════════════════════════
-- § 5. The Sharvit configuration: `believes the rumor that p`
-- ════════════════════════════════════════════════════

/-! Section 5 of @cite{bondarenko-elliott-2026}.

The full LF for "Mitya believes the rumor that `p`" combines four
ingredients (paper eqs. 62–65):

1. Equality semantics for the `that`-clause (eq. 62).
2. MSI on `CONT` (eq. 63).
3. MSO on `THEME` (eq. 64).
4. TECM tying `believe`-events' content to their theme's content (eq. 65).

The paper's main result (Section 5) is that the configuration

    `Mitya believes the rumor that p`

is **Strawson Upward-Entailing (SUE) but not SDE** with respect to the
restrictor of the indefinite inside the `that`-clause, and the negated
version

    `Mitya doesn't believe the rumor that p`

is **SDE but not SUE**. The latter satisfies the NPI licensing condition
(eq. 21); the former does not. The contrast in (2) follows.

We prove the **SDE direction for the negated configuration** below
(`negated_sharvit_SDE`). The "not-SUE" direction (functionality of `CONT`
under uniqueness presupposition) is documented in the paper's eq. 73 and
relies on functionality of `CONT` rather than on MSI/MSO/TECM — a sketch
follows the theorem.

-/

section Sharvit
variable {V E W : Type*} [Preorder V]

/-- Equality-semantics rendering of "the rumor that p" — the unique
    rumor with content `p` (paper eqs. 60a/61a's iota construction,
    simplified). Existence and uniqueness are the standard Fregean
    presuppositions of `the`. -/
def TheRumorThat (rumor : E → Prop) (CONT_e : E → Option (Set W))
    (p : Set W) (r : E) : Prop :=
  rumor r ∧ CONT_e r = some p

/-- "Mitya believes the rumor that p" (paper eq. 60a, equality version).
    Existential over believing-events whose theme is the unique
    `p`-rumor. -/
def BelievesTheRumorThat (believe : V → Prop) (HOLDER : V → Option E)
    (THEME : V → Option E) (rumor : E → Prop) (CONT_e : E → Option (Set W))
    (M : E) (p : Set W) : Prop :=
  ∃ e r, believe e ∧ HOLDER e = some M ∧
         THEME e = some r ∧ TheRumorThat rumor CONT_e p r

end Sharvit

-- ════════════════════════════════════════════════════
-- § 5b. Section 5 main theorem: negated_sharvit_SDE
-- ════════════════════════════════════════════════════

/-! Paper §5 chains MSI ∘ MSO ∘ TECM ∘ BelievingDIV ∘ RumorDIV ∘
WorldLocatedDIV to derive the SDE-not-SUE asymmetry that captures
Sharvit's NPI contrast. We prove the closure direction
(`positive_sharvit_closure`) and the SDE direction
(`negated_sharvit_SDE`) via contraposition.

The world parameter (`∃e ≤ w[…]`, paper fn. 2: "possible worlds are
maximal eventualities") is reintroduced via an abstract `located : V → W → Prop`
relation with downward-closure under the eventuality preorder. -/

section SharvitFull
variable {V E W : Type*} [Preorder V] [Preorder E]

/-- Parts of rumors are rumors — the rumor-side analogue of
    `BelievingDIV`. Implicit in paper §4.4 ("rumors, much like more
    concrete entities, have a mereological structure"). -/
def RumorDIV (rumor : E → Prop) : Prop :=
  ∀ ⦃r r' : E⦄, rumor r → r' ≤ r → rumor r'

/-- "Located at world w" is preserved under parts of eventualities.
    Paper fn. 2 grounds this: worlds are maximal eventualities, so
    `located e w := e ≤ w` for events and worlds in a shared lattice;
    here we abstract that as a preorder-down-closed binary relation. -/
def WorldLocatedDIV (located : V → W → Prop) : Prop :=
  ∀ ⦃e e' : V⦄ ⦃w : W⦄, e' ≤ e → located e w → located e' w

/-- Equality semantics for "Mitya believes the rumor that p" at world `w`
    (paper eqs. 60a/61a, with the `∃e ≤ w` world parameter restored). -/
def BelievesTheRumorThatAt
    (believe : V → Prop) (HOLDER : V → Option E)
    (located : V → W → Prop) (THEME : V → Option E)
    (rumor : E → Prop) (CONT_e : E → Option (Set W))
    (M : E) (p : Set W) (w : W) : Prop :=
  ∃ e r, located e w ∧ believe e ∧ HOLDER e = some M ∧
         THEME e = some r ∧ rumor r ∧ CONT_e r = some p

/-- **Theorem (paper eq. 69, Strawson direction)**: under MSI/MSO/TECM
    + BelievingDIV + RumorDIV + WorldLocatedDIV, the Sharvit
    configuration's positive sentence is closed under (proper)
    informational entailment: if `M` believes the rumor that `p` and
    `p' < p` (informationally weaker), then `M` believes the rumor
    that `p'`.

    This is the SUE direction for the positive sentence (paper eq. 66a).
    Proof structure: TECM ∘ MSI ∘ BelievingDIV ∘ WorldLocatedDIV ∘ MSO
    ∘ RumorDIV ∘ TECM. -/
theorem positive_sharvit_closure
    {believe : V → Prop} {HOLDER : V → Option E}
    {CONT_v : V → Option (Set W)} {CONT_e : E → Option (Set W)}
    {THEME : V → Option E} {rumor : E → Prop} {located : V → W → Prop}
    (h_msi : MSI CONT_v) (h_mso : MSO THEME)
    (h_tecm : TECM believe CONT_v CONT_e THEME)
    (h_div : BelievingDIV believe HOLDER)
    (h_rumor_div : RumorDIV rumor)
    (h_world_div : WorldLocatedDIV located)
    {M : E} {p p' : Set W} {w : W}
    (h_lt : propLT p' p)
    (h_pos : BelievesTheRumorThatAt believe HOLDER located THEME rumor
                                    CONT_e M p w) :
    BelievesTheRumorThatAt believe HOLDER located THEME rumor CONT_e M p' w := by
  obtain ⟨e, r₁, h_loc, h_bel, h_hol, h_thm, h_rum, h_cont_r₁⟩ := h_pos
  -- Step 1 (TECM): CONT_v e = CONT_e r₁ = some p.
  have h_cont_e : CONT_v e = some p :=
    (h_tecm h_bel h_thm).trans h_cont_r₁
  -- Step 2 (MSI): get e' < e with CONT_v e' = some p'.
  obtain ⟨e', h_e'_lt, h_cont_e'⟩ := h_msi h_cont_e h_lt
  -- Step 3 (BelievingDIV): e' is a believing of M.
  have h_bel' : believe e' := h_div.1 e e' h_bel (le_of_lt h_e'_lt)
  have h_hol' : HOLDER e' = some M := h_div.2 h_hol (le_of_lt h_e'_lt)
  -- Step 4 (WorldLocatedDIV): e' is located at w too.
  have h_loc' : located e' w := h_world_div (le_of_lt h_e'_lt) h_loc
  -- Step 5 (MSO): get r' < r₁ with THEME e' = some r'.
  obtain ⟨r', h_r'_lt, h_thm'⟩ := h_mso h_e'_lt h_thm
  -- Step 6 (RumorDIV): r' is a rumor.
  have h_rum' : rumor r' := h_rumor_div h_rum (le_of_lt h_r'_lt)
  -- Step 7 (TECM on e'): CONT_e r' = CONT_v e' = some p'.
  have h_cont_r' : CONT_e r' = some p' :=
    (h_tecm h_bel' h_thm').symm.trans h_cont_e'
  exact ⟨e', r', h_loc', h_bel', h_hol', h_thm', h_rum', h_cont_r'⟩

/-- **Theorem (paper eq. 72, SDE direction)**: under the §5 axioms,
    the *negated* Sharvit configuration is Strawson Downward-Entailing
    wrt the restrictor of the indefinite inside the embedded CP.
    Concretely: if `M` does not believe the rumor that `p'` and
    `p' < p` (informationally weaker), then `M` does not believe the
    rumor that `p`.

    The proof is the contrapositive of `positive_sharvit_closure`.
    This is the direction that licenses NPIs in *Katya doesn't believe
    the rumor that Anton has ever snowboarded* (paper eq. 67b). -/
theorem negated_sharvit_SDE
    {believe : V → Prop} {HOLDER : V → Option E}
    {CONT_v : V → Option (Set W)} {CONT_e : E → Option (Set W)}
    {THEME : V → Option E} {rumor : E → Prop} {located : V → W → Prop}
    (h_msi : MSI CONT_v) (h_mso : MSO THEME)
    (h_tecm : TECM believe CONT_v CONT_e THEME)
    (h_div : BelievingDIV believe HOLDER)
    (h_rumor_div : RumorDIV rumor)
    (h_world_div : WorldLocatedDIV located)
    {M : E} {p p' : Set W} {w : W}
    (h_lt : propLT p' p)
    (h_neg : ¬ BelievesTheRumorThatAt believe HOLDER located THEME rumor
                                      CONT_e M p' w) :
    ¬ BelievesTheRumorThatAt believe HOLDER located THEME rumor CONT_e M p w :=
  fun h_pos => h_neg
    (positive_sharvit_closure h_msi h_mso h_tecm h_div h_rumor_div
                              h_world_div h_lt h_pos)

end SharvitFull

-- ════════════════════════════════════════════════════
-- § 5c. not-SUE counterexample (paper eq. 73)
-- ════════════════════════════════════════════════════

/-! Paper eq. 73 establishes the *not-SUE* direction of the negated
Sharvit configuration: the implication ¬B(stronger) → ¬B(weaker) does
NOT hold under the §5 axioms. Equivalently, there exists a model
satisfying MSI/MSO/TECM/BelievingDIV/RumorDIV/WorldLocatedDIV where
the agent believes the weaker rumor but not the stronger.

Combined with `negated_sharvit_SDE` (eq. 72), this pins down the FULL
monotonicity profile of the negated configuration: **SDE and not SUE**
— exactly what the NPI licensing condition (paper eq. 21) requires.
The contrast between (67a) and (67b) — and hence Sharvit's empirical
puzzle — follows.
-/

/-- Auxiliary three-element type for the not-SUE counterexample. -/
private inductive NotSUESubj where
  | Sk    -- "Katya"
  | Sr1   -- the unique rumor with stronger content `{true}`
  | Sr2   -- the unique rumor with weaker content `Set.univ`
  deriving DecidableEq

/-- Discrete preorder on `NotSUESubj`: `r ≤ r'` iff `r = r'`. Makes
    `RumorDIV` (parts of rumors are rumors) trivially satisfied. -/
private instance : Preorder NotSUESubj where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans

/-- **Theorem (paper eq. 73)**: the negated Sharvit configuration is
    NOT Strawson Upward-Entailing wrt the embedded restrictor.

    There exists a model satisfying all §5 axioms (MSI, MSO, TECM,
    BelievingDIV, RumorDIV, WorldLocatedDIV) and a pair `p, p'` with
    `propLT p' p` (p' weaker than p) such that the agent believes the
    rumor that `p'` (weaker) but does NOT believe the rumor that `p`
    (stronger).

    Witness: `V = Unit`, `W = Bool`; one event with content `Set.univ`
    themed to the unique `Set.univ`-rumor; `Set.univ` has no proper
    supersets so MSI is vacuous; the `{true}`-rumor exists in the
    lexicon (`NotSUESubj.Sr1`) but no event has it as theme.

    Combined with `negated_sharvit_SDE`, this gives the FULL
    monotonicity profile (SDE *and not* SUE) that the NPI licensing
    condition (paper eq. 21) requires. -/
theorem negated_sharvit_not_SUE :
    ∃ (V E W : Type) (_ : Preorder V) (_ : Preorder E)
      (believe : V → Prop) (HOLDER : V → Option E)
      (CONT_v : V → Option (Set W)) (CONT_e : E → Option (Set W))
      (THEME : V → Option E) (rumor : E → Prop)
      (located : V → W → Prop)
      (M : E) (p p' : Set W) (w : W),
    MSI CONT_v ∧ MSO THEME ∧ TECM believe CONT_v CONT_e THEME ∧
    BelievingDIV believe HOLDER ∧ RumorDIV rumor ∧
    WorldLocatedDIV located ∧
    propLT p' p ∧
    BelievesTheRumorThatAt believe HOLDER located THEME rumor CONT_e M p' w ∧
    ¬ BelievesTheRumorThatAt believe HOLDER located THEME rumor CONT_e M p w := by
  let CONT_e_def : NotSUESubj → Option (Set Bool) := fun s => match s with
    | NotSUESubj.Sk => none
    | NotSUESubj.Sr1 => some {true}
    | NotSUESubj.Sr2 => some Set.univ
  refine ⟨Unit, NotSUESubj, Bool, inferInstance, inferInstance,
          fun _ => True, fun _ => some NotSUESubj.Sk,
          fun _ => some Set.univ, CONT_e_def,
          fun _ => some NotSUESubj.Sr2,
          fun s => s = NotSUESubj.Sr1 ∨ s = NotSUESubj.Sr2,
          fun _ _ => True,
          NotSUESubj.Sk, ({true} : Set Bool), (Set.univ : Set Bool), true,
          ?MSI, ?MSO, ?TECM, ?BDIV, ?RDIV, ?WDIV, ?propLT, ?Bp', ?notBp⟩
  case MSI =>
    -- Vacuous: CONT_v is constantly some Set.univ; Set.univ has no
    -- proper supersets in `Set Bool`.
    intro _ p₀ q hcont hlt
    have hp : p₀ = Set.univ := (Option.some.inj hcont).symm
    rw [hp] at hlt
    -- hlt : Set.univ < q, which requires ¬ q ⊆ Set.univ
    exact absurd (Set.subset_univ q) hlt.2
  case MSO =>
    -- Vacuous: V = Unit, no proper sub-eventualities.
    intro e e' _ he'lt _
    rw [Subsingleton.elim e e'] at he'lt
    exact absurd he'lt (lt_irrefl _)
  case TECM =>
    -- CONT_v ⟨⟩ = some Set.univ; THEME ⟨⟩ = some Sr2;
    -- CONT_e_def Sr2 = some Set.univ. Equal.
    intro _ te _ hthm
    have hte : te = NotSUESubj.Sr2 := (Option.some.inj hthm).symm
    rw [hte]
  case BDIV =>
    refine ⟨?_, ?_⟩
    · -- DIV believe: believe is constantly True.
      intro _ _ _ _; trivial
    · -- HolderPreservedUnderParts: HOLDER is constantly some Sk.
      intro _ _ _ hhol _; exact hhol
  case RDIV =>
    -- Discrete preorder makes r' ≤ r equivalent to r' = r.
    intro r r' hrum hle
    rw [show r' = r from hle]
    exact hrum
  case WDIV =>
    intro _ _ _ _ _; trivial
  case propLT =>
    -- propLT Set.univ {true} = {true} < Set.univ
    refine ⟨Set.subset_univ _, ?_⟩
    -- ¬ Set.univ ⊆ {true}: false ∈ Set.univ but false ∉ {true}
    intro hsubset
    exact (hsubset (Set.mem_univ false) : (false : Bool) = true)
      |> Bool.false_ne_true
  case Bp' =>
    -- Witness: e = (), r = Sr2.
    exact ⟨(), NotSUESubj.Sr2, trivial, trivial, rfl, rfl, Or.inr rfl, rfl⟩
  case notBp =>
    -- THEME forces r = Sr2; CONT_e_def Sr2 = some Set.univ ≠ some {true}.
    rintro ⟨_, r, _, _, _, hthm, _, hcont⟩
    have hr : r = NotSUESubj.Sr2 := (Option.some.inj hthm).symm
    rw [hr] at hcont
    -- hcont : CONT_e_def Sr2 = some {true}; but CONT_e_def Sr2 = some Set.univ
    have huniv_eq : (Set.univ : Set Bool) = ({true} : Set Bool) :=
      Option.some.inj hcont
    -- false ∈ Set.univ but false ∉ {true}
    have : (false : Bool) ∈ ({true} : Set Bool) :=
      huniv_eq ▸ Set.mem_univ false
    exact Bool.false_ne_true this

-- ════════════════════════════════════════════════════
-- § 6. §6.1 Closure under conjunction (paper eqs. 78, 79)
-- ════════════════════════════════════════════════════

/-! Paper §6.1 introduces a second closure property — closure under
conjunction (eq. 76) — that classical Hintikkan modal semantics enjoys
but the file's MSI-only account does not derive on its own. The fix
adds two principles:

- **Summation of contentful entities** (eq. 78):
  `CONT(x ⊕ y) = CONT(x) ∩ CONT(y)`. Paper notes: "Once we assume that
  an attitude holder's believings are closed under mereological
  summation, we guarantee that the existence of a believing with content
  `p` and a believing with content `q` guarantees the existence of a
  believing with content `p ∩ q`." (eq. 79.)
- **Believings closed under summation** (implicit in eq. 79.c):
  the sum of two believings of the same holder is a believing of that
  holder.
-/

section ClosureUnderConjunction
variable {V E W : Type*} [SemilatticeSup V]
  {believe : V → Prop} {HOLDER : V → Option E} {CONT : V → Option (Set W)}

/-- **Content-of-sum-is-intersection** (paper eq. 78). When both summands
    are contentful, the content of their mereological sum is the
    intersection of their contents. -/
def CONTSum (CONT : V → Option (Set W)) : Prop :=
  ∀ ⦃x y px py⦄, CONT x = some px → CONT y = some py →
    CONT (x ⊔ y) = some (px ∩ py)

/-- **Believings closed under summation** (implicit in paper eq. 79.c).
    The mereological sum of two believings of the same holder is itself
    a believing of that holder. -/
def BelievingsClosedUnderSum (believe : V → Prop) (HOLDER : V → Option E) :
    Prop :=
  ∀ ⦃e e' M⦄, believe e → believe e' →
    HOLDER e = some M → HOLDER e' = some M →
    believe (e ⊔ e') ∧ HOLDER (e ⊔ e') = some M

/-- **Theorem (paper eq. 79)**: closure under conjunction.
    If the agent believes `p` and believes `q`, then under summation
    closure on contents (eq. 78) and on believings, the agent believes
    `p ∩ q` (the propositional conjunction). -/
theorem believes_closure_under_conjunction
    (h_cont_sum : CONTSum CONT)
    (h_bel_sum : BelievingsClosedUnderSum believe HOLDER)
    {M : E} {p q : Set W}
    (h_p : Believes believe HOLDER CONT M p)
    (h_q : Believes believe HOLDER CONT M q) :
    Believes believe HOLDER CONT M (p ∩ q) := by
  obtain ⟨e, hbel_e, hhol_e, hcont_e⟩ := h_p
  obtain ⟨e', hbel_e', hhol_e', hcont_e'⟩ := h_q
  obtain ⟨hbel_sum, hhol_sum⟩ := h_bel_sum hbel_e hbel_e' hhol_e hhol_e'
  exact ⟨e ⊔ e', hbel_sum, hhol_sum, h_cont_sum hcont_e hcont_e'⟩

end ClosureUnderConjunction

-- ════════════════════════════════════════════════════
-- § 7. §6.3 demonstration: conjunctive parthood discriminates
-- ════════════════════════════════════════════════════

/-! Section 6.3 of @cite{bondarenko-elliott-2026} notes that
informational parthood via classical entailment (eq. 88) faces the
*disjunction-introduction* problem (eq. 91):

```
Mitya believes that Jessica married an American philosopher.
↛ Mitya believes that Jessica married a linguist or a philosopher.
```

even though `Jessica married an American philosopher` classically
entails `Jessica married a linguist or a philosopher`. The paper
proposes Fine's *conjunctive parthood* (eq. 94, footnote 27) as a
refinement.

This is exactly `Mereology.IsContentPart` (Jago Def 5, re-exported
through `Theories/Semantics/Truthmaker/Basic.lean`). With argument
order matching the paper's convention "Q' is conjunctive part of Q",
we have:

  paper "Q' is conjunctive part of Q"  ↔  `Mereology.IsContentPart Q Q'`

Below we exhibit the paper's witness (eq. 95): with Q = {p₃} ("Jessica
married an American linguist") and Q' = {p₁, p₂} ("Jessica married a
linguist", "Jessica married a philosopher"), Q' is **not** a conjunctive
part of Q because p₃ ⊄ p₂ ("being an American linguist doesn't entail
being a philosopher").

-/

section ConjunctiveParthoodDemo
variable {W : Type*}

/-- **§6.3 discriminating witness** (paper eq. 95). Given three
    propositions `p₁` (linguist), `p₂` (philosopher), `p₃` (American
    linguist) with the natural entailment relations, the alternative
    set `{p₁, p₂}` is NOT a conjunctive part of `{p₃}` — even though
    classically `{p₃} ⊨ {p₁, p₂}` via union.

    What fails: the **second conjunct of paper eq. 94** ("every `p' ∈ Q'`
    has some `p ∈ Q` with `p ⊆ p'`"). Take `p₂ ∈ Q' = {p₁, p₂}`; the
    only candidate `p ∈ Q = {p₃}` is `p₃` itself, but `p₃ ⊆ p₂` is
    false. The proof is a one-line application of the generic
    `Mereology.not_isContentPart_of_singleton_not_le`. -/
theorem conjunctive_parthood_blocks_disj_intro
    (p₁ p₂ p₃ : Set W)
    (_h_p3_p1 : p₃ ⊆ p₁)        -- "American linguist" ⊆ "linguist"
    (h_not_p3_p2 : ¬ p₃ ⊆ p₂) :  -- "American linguist" ⊄ "philosopher"
    ¬ Mereology.IsContentPart (· = p₃) ({p₁, p₂} : Set (Set W)) :=
  Mereology.not_isContentPart_of_singleton_not_le
    (q := p₃) (p := ({p₁, p₂} : Set (Set W)))
    (Set.mem_insert_iff.mpr (Or.inr rfl)) h_not_p3_p2

end ConjunctiveParthoodDemo

-- ════════════════════════════════════════════════════
-- § 8. Cross-framework: B&E vs Hintikka
-- ════════════════════════════════════════════════════

/-! Paper §1 motivates the content-based approach by contrast with the
classical Hintikka-style modal semantics: Hintikka's `□p ↔ ∀w' accessible,
p(w')` always *closes under classical entailment*, whereas the empirical
data (paper §1, esp. *be surprised that p ∧ q* ↛ *be surprised that p*)
shows that some attitude verbs do NOT close.

In the B&E framework, closure under conjunction is contingent on the
extra axioms `CONTSum` + `BelievingsClosedUnderSum` (paper §6.1). For
verbs like *be surprised* that fail those axioms, B&E correctly predicts
non-closure. Hintikka's framework cannot accommodate this.

We make the divergence visible as a Lean theorem: Hintikka **always**
closes under intersection; B&E does **not** always close (witnessed by
a model where `CONTSum` is violated).

A self-contained `hintikkaBox` is used here rather than importing
`Theories/Semantics/Attitudes/Doxastic.boxAt` directly — same definition,
no transitive deps. -/

section CrossFramework

/-- Hintikka-style box modality: `p` is believed iff every accessible
    world makes `p` true. Equivalent to `Doxastic.boxAt`; defined here
    self-contained to avoid the heavyweight Doxastic import. -/
def hintikkaBox {W E : Type*} (R : E → W → W → Prop) (x : E) (w : W)
    (worlds : List W) (p : Set W) : Prop :=
  ∀ w' ∈ worlds, R x w w' → w' ∈ p

/-- **Hintikka closes under intersection** (universal-quantifier
    distribution). This is the over-closure that B&E §1 argues against
    on empirical grounds. -/
theorem hintikkaBox_inter {W E : Type*} (R : E → W → W → Prop) (x : E)
    (w : W) (worlds : List W) (p q : Set W) :
    hintikkaBox R x w worlds p → hintikkaBox R x w worlds q →
    hintikkaBox R x w worlds (p ∩ q) :=
  fun hp hq w' hw' hR => ⟨hp w' hw' hR, hq w' hw' hR⟩

/-- **B&E's `Believes` does NOT always close under intersection**
    (the headline cross-framework refutation). Witness: a model with
    two believing-events of the same holder, contents `{true}` and
    `{false}` over `Bool`-worlds, but no event with content `∅`. The
    contents fail `CONTSum`; the agent "believes" each disjoint
    proposition but not their (empty) intersection.

    This makes the B&E vs Hintikka clash a Lean theorem rather than
    a docstring claim. -/
theorem believes_does_not_always_close_under_intersection :
    ∃ (V E W : Type) (_ : Preorder V) (believe : V → Prop)
      (HOLDER : V → Option E) (CONT : V → Option (Set W))
      (M : E) (p q : Set W),
    Believes believe HOLDER CONT M p ∧
    Believes believe HOLDER CONT M q ∧
    ¬ Believes believe HOLDER CONT M (p ∩ q) := by
  refine ⟨Bool, Unit, Bool, inferInstance,
          fun _ => True, fun _ => some (),
          fun e => some (if e then {true} else {false}),
          (), {true}, {false}, ?_, ?_, ?_⟩
  · -- Believes M {true}: witness e = true (CONT true = some {true})
    exact ⟨true, trivial, rfl, rfl⟩
  · -- Believes M {false}: witness e = false (CONT false = some {false})
    exact ⟨false, trivial, rfl, rfl⟩
  · -- ¬ Believes M ({true} ∩ {false}): no event has CONT = some ∅
    rintro ⟨e, _, _, hcont⟩
    cases e
    · -- e = false, CONT false = some {false}; reduced equation:
      -- ({false} : Set Bool) = ({true} : Set Bool) ∩ {false}
      simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hcont
      have h1 : false ∈ ({false} : Set Bool) := rfl
      rw [hcont] at h1
      exact absurd h1.1 (by decide)
    · -- e = true, CONT true = some {true}; reduced equation:
      -- ({true} : Set Bool) = ({true} : Set Bool) ∩ {false}
      simp only [Option.some.injEq, ↓reduceIte] at hcont
      have h1 : true ∈ ({true} : Set Bool) := rfl
      rw [hcont] at h1
      exact absurd h1.2 (by decide)

end CrossFramework

end Phenomena.Attitudes.Studies.BondarenkoElliott2026
