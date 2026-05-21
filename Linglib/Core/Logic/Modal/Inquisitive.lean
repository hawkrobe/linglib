import Linglib.Core.Logic.Modal.Kripke
import Linglib.Core.Logic.Team.Closure

/-!
# Inquisitive Modal Logic (InqML)

@cite{ciardelli-2022} @cite{ciardelli-2014}
@cite{ciardelli-groenendijk-roelofsen-2018}

Inquisitive modal logic extends classical modal logic with a treatment
of questions alongside statements, following the
Ciardelli-Groenendijk-Roelofsen tradition. The originating modal paper
is @cite{ciardelli-2014} (Advances in Modal Logic), with the
propositional inquisitive system InqB developed in
@cite{ciardelli-groenendijk-roelofsen-2018} (Oxford University Press)
and the modal preview in @cite{ciardelli-2022} Chapter 8.

Formulas are evaluated at **information states** (teams of worlds),
with two crucial novelties relative to BSML / MDL / MIL:

* The **inquisitive disjunction** `φ \\/ ψ` (written `inqDisj` here),
  which is supported by a team `s` iff `s ⊨ φ` *or* `s ⊨ ψ` (global
  disjunction, not the team-split `∨` of BSML).
* The **implication** `φ → ψ`, which is supported by `s` iff every
  subteam `t ⊆ s` satisfies `t ⊨ φ → t ⊨ ψ` (universal subteam
  quantification).
* The **Kripke modality** `□φ`, supported by `s` iff every `w ∈ s`
  has `M, R[w] ⊨ φ` (per-world full image of the accessibility
  relation, distinct from BSML's per-world *sub-witness* or MDL's
  single-witness or MIL's lax form).

Reference: @cite{ciardelli-2022} Chapter 8 (modal preview), with the
propositional InqB base from Chapter 3.

## Closure profile

| Property            | InqML formula     |
|---------------------|-------------------|
| `IsLowerSet`        | ✓ (persistence)   |
| `SupClosed`         | ✗ broken by `\\/` |
| `∅ ∈ support`       | ✓                 |

InqML inhabits the same closure cell as MDL (downward-closed + empty,
sup-closure broken) — but via a different syntactic mechanism: the
*inquisitive disjunction* `\\/` breaks union closure where MDL's
*dependence atom* does. This is the second inhabitant of this cell in
linglib, demonstrating that the architectural pattern "team-semantic
logic with non-classical disjunction-like connective fails union
closure" applies regardless of whether the connective is question-
flavored (InqML) or dependence-flavored (MDL).

## Main declarations

* `Formula` — InqML syntax (Ciardelli §8.2 modal + §3 propositional base).
* `eval` — single-relation team-semantic evaluation (only support,
  no anti-support). Negation derived as `φ → ⊥`, matching
  @cite{ciardelli-2022}.
* `Formula.neg`, `Formula.polarQ` — standard inquisitive abbreviations
  (`¬φ := φ → ⊥`, `?φ := φ \\/ ¬φ`).
* `Formula.modalDepth` — depth of nested `□`.
* `support_isLowerSet` — persistence property (Ciardelli §3 Lemma).
* `support_empty` — every formula supported on the empty team.
* `not_supClosed_inqDisj_of_witness` — constructive witness that
  inquisitive disjunction `\\/` breaks union closure.

## Implementation notes

The standard inquisitive connective set is `{⊥, ∧, →, \\/}` with
`¬φ := φ → ⊥`, `!φ := ¬¬φ` (declarative variant), and `?φ := φ \\/ ¬φ`
(polar question) as standard abbreviations. We include `\\/` and `→`
as primitives; `¬`, `!`, `?` can be added as helpers later when a
consumer needs them.

The modal extension adds only `□` per @cite{ciardelli-2022} §8.2.
Section 8.3 introduces a second modality `⊞` (properly inquisitive,
using a relation `R : W × ℘(W)` instead of `R : W × W`) — deferred to
a follow-up file/PR because it requires a different model carrier
than `KripkeModel`.

The KripkeModel carrier from `Core/Logic/Modal/Kripke.lean` is reused.
Per-world `□` semantics naturally fits the `R : W → Finset W` shape.

## Sibling logics in `Core/Logic/Modal/`

* `Modal/Kripke.lean` — the carrier type.
* `Modal/Dependence.lean` — MDL (Väänänen 2008), bilateral, dep atoms.
* `Modal/Inclusion.lean` — MIL (AHY 2024), unilateral, inclusion atoms.
* `Modal/Inquisitive.lean` (this file) — InqML, unilateral, inquisitive
  disjunction.

## Todo

* `⊞` modality (Ciardelli §8.3) — needs a `InquisitiveModalModel` with
  `R : W → Finset (Finset W)`. Add when a downstream consumer needs it.
* Declarative `!φ := ¬¬φ` and polar question `?φ := φ \\/ ¬φ`
  abbreviations + their closure-property lemmas.
* First-order inquisitive modal logic (InqBQ + modality) — Ciardelli
  §8 mentions but full development in subsequent literature.
* Bisim invariance — Ciardelli & Otto (2020) "Inquisitive bisimulation".
-/

namespace Core.Logic.Modal.Inquisitive

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

open Core.Logic.Modal (KripkeModel)

/-! ### Syntax (Ciardelli §3 + §8) -/

/-- InqML syntax: classical propositional base (atoms, `⊥`, `∧`, `→`)
    extended with inquisitive disjunction `\\/` and Kripke modality `□`. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Weak contradiction `⊥`. -/
  | bot
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Implication. -/
  | impl (φ ψ : Formula Atom)
  /-- Inquisitive disjunction `φ \\/ ψ`. -/
  | inqDisj (φ ψ : Formula Atom)
  /-- Kripke modality `□φ`. -/
  | nec (φ : Formula Atom)
  deriving Repr

/-! ### Semantics (Ciardelli §3.1 + §8.2) -/

/-- Inquisitive team-semantic evaluation. Single-relation semantics
    (only support, no anti-support); negation is derived as
    `impl φ bot`. -/
def eval (M : KripkeModel W Atom) : Formula Atom → Finset W → Prop
  | .atom p,        s => ∀ w ∈ s, M.val p w = true
  | .bot,           s => s = ∅
  | .conj φ ψ,      s => eval M φ s ∧ eval M ψ s
  | .impl φ ψ,      s => ∀ t : Finset W, t ⊆ s → eval M φ t → eval M ψ t
  | .inqDisj φ ψ,   s => eval M φ s ∨ eval M ψ s
  | .nec φ,        s => ∀ w ∈ s, eval M φ (M.access w)

/-- Support: alias for `eval`. InqML has a single support relation
    (no anti-support). -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (s : Finset W) : Prop :=
  eval M φ s

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (s : Finset W) :
    support M (.atom p) s ↔ ∀ w ∈ s, M.val p w = true := Iff.rfl

@[simp] lemma support_bot (M : KripkeModel W Atom) (s : Finset W) :
    support M (.bot : Formula Atom) s ↔ s = ∅ := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (s : Finset W) :
    support M (.conj φ ψ) s ↔ support M φ s ∧ support M ψ s := Iff.rfl

@[simp] lemma support_impl (M : KripkeModel W Atom) (φ ψ : Formula Atom) (s : Finset W) :
    support M (.impl φ ψ) s ↔
      ∀ t : Finset W, t ⊆ s → support M φ t → support M ψ t := Iff.rfl

@[simp] lemma support_inqDisj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (s : Finset W) :
    support M (.inqDisj φ ψ) s ↔ support M φ s ∨ support M ψ s := Iff.rfl

@[simp] lemma support_nec (M : KripkeModel W Atom) (φ : Formula Atom) (s : Finset W) :
    support M (.nec φ) s ↔ ∀ w ∈ s, support M φ (M.access w) := Iff.rfl

/-! ### Derived connectives -/

/-- Negation: `¬φ := φ → ⊥` (Ciardelli §3, Def 3.2.2). -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .impl φ .bot

/-- Polar question: `?φ := φ \\/ ¬φ` (Ciardelli §3, Def 3.2.2). The
    canonical inquisitive abbreviation for "whether φ". -/
abbrev Formula.polarQ (φ : Formula Atom) : Formula Atom :=
  .inqDisj φ φ.neg

/-! ### Modal depth -/

/-- Modal depth of an InqML formula. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .bot => 0
  | .conj φ ψ => max φ.modalDepth ψ.modalDepth
  | .impl φ ψ => max φ.modalDepth ψ.modalDepth
  | .inqDisj φ ψ => max φ.modalDepth ψ.modalDepth
  | .nec φ => φ.modalDepth + 1

/-! ### Persistence (Ciardelli §3 — downward closure) -/

/-- **Persistence**: every InqML formula's support is downward-closed
    under `⊆`. Ciardelli §3 (propositional case) + §8.2 (modal
    extension); the key structural property of inquisitive semantics. -/
theorem support_isLowerSet (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet { s : Finset W | support M φ s } := by
  induction φ with
  | atom p =>
    intro s t hts hs w hw
    exact hs w (hts hw)
  | bot =>
    intro s t hts hs
    show t = ∅
    rw [hs] at hts
    exact Finset.subset_empty.mp hts
  | conj φ ψ ihφ ihψ =>
    intro s t hts ⟨hsφ, hsψ⟩
    exact ⟨ihφ hts hsφ, ihψ hts hsψ⟩
  | impl φ ψ _ihφ _ihψ =>
    -- s ⊨ φ → ψ means ∀u ⊆ s, u ⊨ φ → u ⊨ ψ.
    -- For t ⊆ s, any u ⊆ t is also ⊆ s, so same property.
    intro s t hts hs u hut huφ
    exact hs u (hut.trans hts) huφ
  | inqDisj φ ψ ihφ ihψ =>
    intro s t hts hs
    rcases hs with hsφ | hsψ
    · exact Or.inl (ihφ hts hsφ)
    · exact Or.inr (ihψ hts hsψ)
  | nec φ ihφ =>
    intro s t hts hs w hw
    exact hs w (hts hw)

/-! ### Empty-team property (Ciardelli §3) -/

/-- Every InqML formula is supported on the empty team. -/
theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ := by
  induction φ with
  | atom p => intro w hw; exact absurd hw (Finset.notMem_empty w)
  | bot => rfl
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | impl φ ψ _ihφ ihψ =>
    -- ∀t ⊆ ∅, t ⊨ φ → t ⊨ ψ. Only t = ∅; conclude from ihψ.
    intro t hts _hφ
    have ht : t = ∅ := Finset.subset_empty.mp hts
    rw [ht]; exact ihψ
  | inqDisj φ ψ ihφ _ihψ => exact Or.inl ihφ
  | nec φ _ihφ => intro w hw; exact absurd hw (Finset.notMem_empty w)

/-! ### Inquisitive disjunction breaks union closure -/

/-- **Inquisitive disjunction breaks union closure**: a constructive
    counterexample. With two worlds `w₁, w₂` where `p` is true at `w₁`
    only and `q` is true at `w₂` only, the singletons `{w₁}` and `{w₂}`
    each support `p \\/ q` (the first supports `p`, the second supports
    `q`), but `{w₁, w₂}` supports neither. This is the canonical
    inquisitive UC-failure pattern. -/
theorem not_supClosed_inqDisj_of_witness {p q : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom}
    (hp₁ : M.val p w₁ = true) (hq₁ : M.val q w₁ = false)
    (hp₂ : M.val p w₂ = false) (hq₂ : M.val q w₂ = true) :
    ¬ SupClosed { s : Finset W | support M (.inqDisj (.atom p) (.atom q)) s } := by
  intro hSC
  -- {w₁} supports p \/ q because {w₁} ⊨ p (only world is w₁, p true there)
  have h₁ : support M (.inqDisj (.atom p) (.atom q)) ({w₁} : Finset W) := by
    refine Or.inl ?_
    intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact hp₁
  -- {w₂} supports p \/ q because {w₂} ⊨ q
  have h₂ : support M (.inqDisj (.atom p) (.atom q)) ({w₂} : Finset W) := by
    refine Or.inr ?_
    intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact hq₂
  -- By SupClosed, {w₁} ∪ {w₂} supports p \/ q
  have hunion : support M (.inqDisj (.atom p) (.atom q))
      (({w₁} : Finset W) ∪ {w₂}) :=
    hSC h₁ h₂
  -- But {w₁, w₂} supports neither p nor q
  rcases hunion with hp | hq
  · -- Suppose support p {w₁, w₂}: needs p true at w₂. But hp₂ says false.
    have : M.val p w₂ = true := hp w₂ (by
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
      exact Or.inr rfl)
    rw [hp₂] at this; exact Bool.noConfusion this
  · -- Suppose support q {w₁, w₂}: needs q true at w₁. But hq₁ says false.
    have : M.val q w₁ = true := hq w₁ (by
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
      exact Or.inl rfl)
    rw [hq₁] at this; exact Bool.noConfusion this

end Core.Logic.Modal.Inquisitive
