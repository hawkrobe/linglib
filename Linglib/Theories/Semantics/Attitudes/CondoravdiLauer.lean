import Linglib.Core.Order.PreferenceStructure
import Linglib.Core.Order.PreferenceStructure.EffectivePreference
import Linglib.Core.Order.PreferenceStructure.MaxInducedOrdering

/-!
# Condoravdi & Lauer: The Effective Preference Theory of *want*
@cite{condoravdi-lauer-2012} @cite{lauer-2013} @cite{condoravdi-lauer-2016}
@cite{condoravdi-lauer-2011} @cite{lauer-condoravdi-2014}

The C&L analysis treats `want` as parameterized by a *preferential
background* — analogous to Kratzer's modal base/ordering source. The
distinguished background is the agent's effective preference function `EP`
(`Core.Order.EffectivePreference`).

## Layout

* `PreferentialBackground`, `EffectivePreferentialBackground` — types.
* `wantP{Exact, Success, QH}` — the three readings from
  @cite{condoravdi-lauer-2016} eq. 71. Exact-match is canonical
  (eq. 69) and implies the other two (`wantPExact_implies_*`).
* `wantEP` — exact-match against the effective preferential background.
* `maxOrderingSource` — `Set`-valued `max[EP(Ad, w)]` (eq. 88), the
  ordering source consumed by the inner modal in the double-modal
  anankastic analysis.

Anankastic-conditional analyses live in `Phenomena/Conditionals/Studies/`;
imperative analyses (C&L 2012, contra @cite{roberts-2023}'s
modal-in-LF account) in `Phenomena/Directives/Studies/`;
discourse-particle uses (@cite{deo-2025-bara}) in
`Phenomena/SentenceMood/Studies/`.
-/

namespace Semantics.Attitudes.CondoravdiLauer

open Core.Order

universe u

variable {Agent W : Type u}

/-- A **preferential background**: a function from agents and worlds to
    preference structures. The C&L analog of Kratzer's `ConvBackground`. -/
abbrev PreferentialBackground (Agent W : Type u) :=
  Agent → W → PreferenceStructure W

/-- An **effective preferential background** returns, at each world, the
    agent's *effective* preference structure (consistent + realistic).
    @cite{condoravdi-lauer-2016} (68): `EP(a, w)`. -/
abbrev EffectivePreferentialBackground (Agent W : Type u)
    (B : Agent → W → Set W) :=
  ∀ (a : Agent) (w : W), EffectivePreference W (B a w)

/-! ## The semantics of `want` — three readings (@cite{condoravdi-lauer-2016} (71)) -/

/-- Exact-match (eq. 71c, the canonical reading; eq. 69):
    `wantP(a, φ)` iff `φ ∈ max[P(a, w)]`. -/
def wantPExact (P : PreferentialBackground Agent W)
    (a : Agent) (φ : Set W) (w : W) : Prop :=
  φ ∈ (P a w).maxElts

/-- Success-oriented (eq. 71a): "satisfied if `φ` is true."
    Some maximal preference is entailed by `φ`. -/
def wantPSuccess (P : PreferentialBackground Agent W)
    (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, φ ⊆ p

/-- Quine-Hintikka (eq. 71b): "satisfied only if `φ` is true."
    Some maximal preference entails `φ`. -/
def wantPQH (P : PreferentialBackground Agent W)
    (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, p ⊆ φ

theorem wantPExact_implies_success {P : PreferentialBackground Agent W}
    {a : Agent} {φ : Set W} {w : W} (h : wantPExact P a φ w) :
    wantPSuccess P a φ w :=
  ⟨φ, h, subset_rfl⟩

theorem wantPExact_implies_QH {P : PreferentialBackground Agent W}
    {a : Agent} {φ : Set W} {w : W} (h : wantPExact P a φ w) :
    wantPQH P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-! ## Monotonicity in φ (@cite{condoravdi-lauer-2016} p. 31)

The three readings differ in their entailment direction in the
propositional argument:

* `wantPSuccess` is **downward-entailing** in φ (Zimmermann's note,
  cited p. 31): if `φ ⊆ ψ` and `wantPSuccess` holds for the *weaker*
  ψ, it holds for the *stronger* φ.
* `wantPQH` is **upward-entailing** in φ (explicit on p. 31): if
  `φ ⊆ ψ` and `wantPQH` holds for the *stronger* φ, it holds for the
  *weaker* ψ.
* `wantPExact` is *neither* upward- nor downward-entailing — see C&L's
  discussion of (62)/(63)/(64) on pp. 27–28. Counterexample-construction
  deferred. -/

theorem wantPSuccess_downward_entailing
    {P : PreferentialBackground Agent W} {a : Agent} {φ ψ : Set W} {w : W}
    (hφψ : φ ⊆ ψ) (h : wantPSuccess P a ψ w) :
    wantPSuccess P a φ w := by
  obtain ⟨p, hpmax, hψp⟩ := h
  exact ⟨p, hpmax, fun _ hx => hψp (hφψ hx)⟩

theorem wantPQH_upward_entailing
    {P : PreferentialBackground Agent W} {a : Agent} {φ ψ : Set W} {w : W}
    (hφψ : φ ⊆ ψ) (h : wantPQH P a φ w) :
    wantPQH P a ψ w := by
  obtain ⟨p, hpmax, hpφ⟩ := h
  exact ⟨p, hpmax, fun _ hx => hφψ (hpφ hx)⟩

/-- Exact-match `want` against the effective preferential background. -/
def wantEP {B : Agent → W → Set W}
    (EP : EffectivePreferentialBackground Agent W B)
    (a : Agent) (φ : Set W) (w : W) : Prop :=
  wantPExact (fun a w => (EP a w).toPreferenceStructure) a φ w

/-- **Joint belief-consistency of EP-want** (@cite{condoravdi-lauer-2016}
    p. 30, end of § 5.4): "when `want` targets a preference structure
    `P(a,w)` that must be consistent — in particular, when it targets
    effective preferences — then `wantP(a, φ)` and `wantP(a, ψ)` are
    incompatible if `φ` and `ψ` are believed to be incompatible by agent
    `a` at `w`."

    Stated contrapositively: if both `wantEP EP a φ w` and
    `wantEP EP a ψ w` hold, then `φ ∩ ψ` is *not* belief-empty — the
    agent does not believe that φ and ψ cannot jointly hold.

    Proof: delegates to the abstract
    `PreferenceStructure.maxElts_pair_belief_compatible` lemma. The
    abstract version captures the same content at the order-theoretic
    level: any two maximal elements of a consistent preference structure
    are jointly belief-compatible. -/
theorem wantEP_jointly_belief_consistent
    {B : Agent → W → Set W}
    (EP : EffectivePreferentialBackground Agent W B)
    {a : Agent} {φ ψ : Set W} {w : W}
    (hφ : wantEP EP a φ w) (hψ : wantEP EP a ψ w) :
    (φ ∩ ψ) ∩ B a w ≠ ∅ :=
  (EP a w).toPreferenceStructure.maxElts_pair_belief_compatible
    (EP a w).isConsistent hφ hψ

/-- The **set-valued ordering source** at addressee `Ad` derived from an
    effective preferential background: at each world, the maximal
    preferences in `EP(Ad, w)`. @cite{condoravdi-lauer-2016}
    (88): `g_epA(w) = max[EP(Ad, w)]`. -/
def maxOrderingSource {B : Agent → W → Set W}
    (EP : EffectivePreferentialBackground Agent W B) (Ad : Agent) :
    W → Set (Set W) :=
  fun w => (EP Ad w).toPreferenceStructure.maxElts

end Semantics.Attitudes.CondoravdiLauer
