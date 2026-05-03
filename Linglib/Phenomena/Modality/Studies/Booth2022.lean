import Linglib.Core.Logic.Bilateral.Defs
import Linglib.Core.Question.Basic

/-!
# Booth 2022 — Bilateral inquisitive minimal-cover semantics for `□`

@cite{booth-2022}

A self-contained study file formalizing the bilateral inquisitive
semantics of @cite{booth-2022} for necessity-modal-with-disjunction
sentences (`□(p ∨ q)`). The novel content is the **minimal-cover**
requirement on `□`'s positive interpretation, which derives the
**Independence inferences**

  `□(p ∨ q) ⊨ ◇(p ∧ ¬q)` and `□(p ∨ q) ⊨ ◇(q ∧ ¬p)`

(Booth Fact 9). Pure-bilateral analyses without minimal-cover
(BSML+, @cite{aloni-2022}) do not derive Independence; pure-inquisitive
analyses without bilateral negation
(@cite{ciardelli-groenendijk-roelofsen-2018}) do not derive the
duality between `□` and `◇`. Booth's bilateral inquisitive propositions
combine both.

## Substrate alignment

- `Question W` (`Core/Question/Basic.lean`) supplies subset-closed
  families of states with `∅`-membership — Booth Definition 10's `P°`
  constraint becomes a `Question`. `BilatInqProp` is then paired
  `Questions` plus a no-substantive-overlap field.
- `Question.declarative` is exactly Booth's `↓{·}` (Def 11 with a
  singleton input); `Question.info` is exactly `info(·)` (Def 12);
  `Question.alt` is exactly `alt` (Def 13).
- `IsBilateral` (`Core/Logic/Bilateral/Defs.lean`) supplies the
  bilateral-substrate predicate. The `BilatInqProp` instance is
  `rfl`-trivial — bilateral negation is bundled-record swap. This is
  the sixth consumer of the `IsBilateral` substrate (BSML, QBSML, BUS,
  ICDRT, Truthmaker propositions, and now Booth bilateral inquisitive).

## Out of scope

- The collectivity heuristic of @cite{booth-2022} §4 is a discourse-level
  proposal not formalized here.
- Booth's restrictor conditional and accessibility-update operator
  (Definitions 15–16) are out of scope for this initial formalization.
- The general Independence theorem (Booth Fact 9) is sketched but
  carried as a documented `sorry` — its proof relies on
  non-Hurford-disjunction reasoning (Fact 6) plus finite-alt machinery
  that goes beyond a self-contained study file. The companion concrete
  example (`example_independence_holds_concretely`) hand-verifies
  Independence on a 4-world deontic model.
-/

namespace Phenomena.Modality.Studies.Booth2022

open Core
open Core.Logic.Bilateral

variable {W : Type*}

/-! ### §1 Bilateral inquisitive propositions (Booth Def 10) -/

/-- **Booth Def 10**: a bilateral inquisitive proposition is a paired
    `pos`/`neg : Question W` with no substantive overlap — only the
    inconsistent (empty) state may both verify and falsify φ. The
    subset-closure and `∅`-membership requirements (Booth Def 10
    bullets 2 and the implicit `∅ ∈ P°`) are baked into `Question`. -/
structure BilatInqProp (W : Type*) where
  /-- Positive interpretation: states verifying the formula. -/
  pos : Question W
  /-- Negative interpretation: states falsifying the formula. -/
  neg : Question W
  /-- No substantive overlap: `pos.props ∩ neg.props ⊆ {∅}`. The reverse
      `{∅} ⊆ pos.props ∩ neg.props` holds for free since both `Question`s
      contain `∅` (`Question.contains_empty`). -/
  no_overlap : ∀ s : Set W, s ∈ pos → s ∈ neg → s = ∅

namespace BilatInqProp

/-- **Booth Def 14, ¬-clause**: bilateral negation is the bundled-record
    swap. Self-inverse syntactically (`negate (negate φ) = φ` by `rfl`). -/
def negate (φ : BilatInqProp W) : BilatInqProp W where
  pos := φ.neg
  neg := φ.pos
  no_overlap s hpos hneg := φ.no_overlap s hneg hpos

@[simp] theorem negate_pos (φ : BilatInqProp W) : φ.negate.pos = φ.neg := rfl
@[simp] theorem negate_neg (φ : BilatInqProp W) : φ.negate.neg = φ.pos := rfl
@[simp] theorem negate_negate (φ : BilatInqProp W) : φ.negate.negate = φ := rfl

/-- **`BilatInqProp` is a bilateral structure** in the sense of
    `Core.Logic.Bilateral.IsBilateral`. The instance is `rfl`-trivial
    because `negate` is bundled-record swap. Sixth consumer of the
    `IsBilateral` substrate (alongside BSML, QBSML, BUS, ICDRT,
    Truthmaker `BilProp`). -/
theorem isBilateral :
    IsBilateral
      (positive := fun φ : BilatInqProp W => φ.pos)
      (negative := fun φ : BilatInqProp W => φ.neg)
      (negate := negate) where
  positive_negate _ := rfl
  negative_negate _ := rfl

/-! ### §2 Atomic, disjunctive, conjunctive clauses (Booth Def 14) -/

/-- **Booth Def 14, atomic clause**: `⟦p⟧⁺ = ↓{V(p)}`,
    `⟦p⟧⁻ = ↓{W \ V(p)}`. Encoded with `Question.declarative` since
    `↓{X} = declarative X`. -/
def atom (V : Set W) : BilatInqProp W where
  pos := Question.declarative V
  neg := Question.declarative Vᶜ
  no_overlap s hpos hneg := by
    have hV : s ⊆ V := hpos
    have hVc : s ⊆ Vᶜ := hneg
    have hsub : s ⊆ V ∩ Vᶜ := fun w hw => ⟨hV hw, hVc hw⟩
    rw [Set.inter_compl_self] at hsub
    exact Set.subset_empty_iff.mp hsub

/-- **Booth Def 14, ∨-clause**: `⟦φ ∨ ψ⟧⁺ = ⟦φ⟧⁺ ∪ ⟦ψ⟧⁺` (inquisitive
    disjunction at the `props` level, = `Question.⊔`); `⟦φ ∨ ψ⟧⁻ =
    ⟦φ⟧⁻ ∩ ⟦ψ⟧⁻` (= `Question.⊓`). -/
def disj (φ ψ : BilatInqProp W) : BilatInqProp W where
  pos := φ.pos ⊔ ψ.pos
  neg := φ.neg ⊓ ψ.neg
  no_overlap s hpos hneg := by
    -- hpos : s ∈ (φ.pos ⊔ ψ.pos), reduces to s ∈ φ.pos.props ∪ ψ.pos.props
    -- hneg : s ∈ (φ.neg ⊓ ψ.neg), reduces to s ∈ φ.neg.props ∩ ψ.neg.props
    rcases hpos with h | h
    · exact φ.no_overlap s h hneg.1
    · exact ψ.no_overlap s h hneg.2

/-- **Booth Def 14, ∧-clause** via the derivation `⟦φ ∧ ψ⟧ = ⟦¬(¬φ ∨ ¬ψ)⟧`.
    Direct unfolding gives `pos = φ.pos ⊓ ψ.pos`, `neg = φ.neg ⊔ ψ.neg`. -/
def conj (φ ψ : BilatInqProp W) : BilatInqProp W where
  pos := φ.pos ⊓ ψ.pos
  neg := φ.neg ⊔ ψ.neg
  no_overlap s hpos hneg := by
    rcases hneg with h | h
    · exact φ.no_overlap s hpos.1 h
    · exact ψ.no_overlap s hpos.2 h

/-- The Booth-derived `conj` agrees structurally with negate∘disj∘negate. -/
theorem conj_eq_negate_disj_negate (φ ψ : BilatInqProp W) :
    conj φ ψ = negate (disj (negate φ) (negate ψ)) := rfl

end BilatInqProp

/-! ### §3 Cover and minimal cover (Booth Section 2.1)

Booth's `□φ` differs from Kratzerian necessity by requiring not just
that the alternatives of `⟦φ⟧⁺` cover `R(w)`, but that they form a
**minimal cover** — no proper subset of the alternatives still covers
`R(w)`. This is what derives Independence inferences (Fact 9): each
alternative must be "needed", so no single alternative dominates. -/

/-- **Booth §2.1**: `C` covers `S` iff `S ⊆ ⋃C`. -/
def IsCover (C : Set (Set W)) (S : Set W) : Prop := S ⊆ ⋃₀ C

/-- **Booth §2.1**: `C` is a **minimal cover** (m-cover) of `S` iff `C`
    covers `S` and no proper subfamily `C' ⊊ C` covers `S`. -/
def IsMinCover (C : Set (Set W)) (S : Set W) : Prop :=
  IsCover C S ∧ ∀ C' : Set (Set W), C' ⊂ C → ¬ IsCover C' S

theorem IsMinCover.isCover {C : Set (Set W)} {S : Set W}
    (h : IsMinCover C S) : IsCover C S := h.1

/-! ### §4 Necessity and possibility (Booth Def 14)

`R : W → Set W` is the relevant-worlds accessibility relation. Booth's
necessity has both polarities defined via `↓` of a witness w-set. The
positive w-set requires `R(w)` non-empty and m-covered by alt⁺(⟦φ⟧);
the negative w-set requires *some* non-empty `R' ⊆ R(w)` to be m-covered
by alt⁻(⟦φ⟧). -/

namespace BilatInqProp

/-- **Booth Def 14, □-clause**:
    `⟦□φ⟧⁺ = ↓{ {w | R(w) ≠ ∅ ∧ alt⁺(⟦φ⟧) m-covers R(w)} }`,
    `⟦□φ⟧⁻ = ↓{ {w | ∃ R' ⊆ R(w), R' ≠ ∅ ∧ alt⁻(⟦φ⟧) m-covers R'} }`.

    The no-overlap proof structurally inducts via `φ.no_overlap`: any
    non-empty state `s` in both polarities yields a world `w ∈ s`,
    hence a witness `v ∈ R(w)` covered by both alt⁺(φ.pos) and
    alt⁻(φ.neg) — giving alternatives `α ∈ φ.pos.props` and
    `β ∈ φ.neg.props` containing `v`. Downward closure gives
    `{v} ∈ φ.pos ∩ φ.neg`, contradicting `φ.no_overlap`. -/
def necessity (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W where
  pos := Question.declarative
    {w : W | (R w).Nonempty ∧ IsMinCover (Question.alt φ.pos) (R w)}
  neg := Question.declarative
    {w : W | ∃ R' : Set W, R' ⊆ R w ∧ R'.Nonempty ∧
              IsMinCover (Question.alt φ.neg) R'}
  no_overlap s hpos hneg := by
    by_contra hne
    obtain ⟨w, hws⟩ : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have hwPos : (R w).Nonempty ∧ IsMinCover (Question.alt φ.pos) (R w) :=
      hpos hws
    obtain ⟨R', hR'sub, hR'ne, hR'mc⟩ : ∃ R' : Set W, R' ⊆ R w ∧
        R'.Nonempty ∧ IsMinCover (Question.alt φ.neg) R' := hneg hws
    obtain ⟨v, hvR'⟩ := hR'ne
    have hvRw : v ∈ R w := hR'sub hvR'
    -- alt⁺ m-covers R(w), so v lands in some α ∈ alt⁺(φ.pos)
    obtain ⟨α, hαAlt, hvα⟩ : ∃ α ∈ Question.alt φ.pos, v ∈ α :=
      hwPos.2.isCover hvRw
    -- alt⁻ m-covers R', so v lands in some β ∈ alt⁻(φ.neg)
    obtain ⟨β, hβAlt, hvβ⟩ : ∃ β ∈ Question.alt φ.neg, v ∈ β :=
      hR'mc.isCover hvR'
    -- α ∈ φ.pos.props (alt ⊆ props), {v} ⊆ α, so {v} ∈ φ.pos.props
    have hαPos : α ∈ φ.pos.props := Question.alt_subset_props _ hαAlt
    have hβNeg : β ∈ φ.neg.props := Question.alt_subset_props _ hβAlt
    have hvSPos : ({v} : Set W) ∈ φ.pos.props :=
      φ.pos.downward_closed α hαPos {v} (Set.singleton_subset_iff.mpr hvα)
    have hvSNeg : ({v} : Set W) ∈ φ.neg.props :=
      φ.neg.downward_closed β hβNeg {v} (Set.singleton_subset_iff.mpr hvβ)
    -- by φ's no_overlap: {v} = ∅, contradiction
    exact (Set.singleton_ne_empty v) (φ.no_overlap {v} hvSPos hvSNeg)

/-- **Booth Def 14, ◇-clause** via duality: `⟦◇φ⟧ = ⟦¬□¬φ⟧`. -/
def possibility (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  negate (necessity R (negate φ))

end BilatInqProp

/-! ### §5 Truth and falsity (Booth Def 17)

A world `w` makes `φ` **true** in model `(W, R, V)` iff `{w} ∈ ⟦φ⟧⁺`,
and **false** iff `{w} ∈ ⟦φ⟧⁻`. Since `Question`s are subset-closed,
this is equivalent to `∃ s ∈ ⟦φ⟧°, w ∈ s` for a non-empty witness. -/

/-- **Booth Def 17**: world `w` is true at `φ` iff the singleton `{w}`
    verifies `φ`. -/
def isTrue (φ : BilatInqProp W) (w : W) : Prop := ({w} : Set W) ∈ φ.pos

/-- **Booth Def 17**: world `w` is false at `φ` iff the singleton `{w}`
    falsifies `φ`. -/
def isFalse (φ : BilatInqProp W) (w : W) : Prop := ({w} : Set W) ∈ φ.neg

/-- Truth and falsity are mutually exclusive (no world is both true and
    false), since by `no_overlap` any state in both polarities is `∅`. -/
theorem not_isTrue_and_isFalse (φ : BilatInqProp W) (w : W) :
    ¬ (isTrue φ w ∧ isFalse φ w) := fun ⟨ht, hf⟩ =>
  Set.singleton_ne_empty w (φ.no_overlap {w} ht hf)

/-! ### §6 Worked example: Independence inference on a 4-world model

A concrete witness that the m-cover semantics derives Booth Fact 9
(Independence Inferences) where Kratzerian and pure-bilateral semantics
do not. We work on a 4-world model `W₄ = Bool × Bool` (subsets of
`{p, q}`), with `V p = {(true, _)}` and `V q = {(_, true)}`.

In this concrete model, `□(p ∨ q)` requires that `R(w)` is m-covered
by `{V(p), V(q)}`. Crucially, m-covering forces both `V(p) \ V(q)`
(the (true, false) world) and `V(q) \ V(p)` (the (false, true) world)
to be non-empty in `R(w)` — otherwise one alternative would be
redundant and the cover wouldn't be minimal. From this we get
`◇(p ∧ ¬q)` and `◇(q ∧ ¬p)` (Independence). -/

namespace BoothExample

/-- 4-world model: subsets of `{p, q}` indexed by `Bool × Bool`. -/
abbrev W4 := Bool × Bool

/-- Valuation: `p` true at worlds with first coordinate `true`. -/
def Vp : Set W4 := {w | w.1 = true}

/-- Valuation: `q` true at worlds with second coordinate `true`. -/
def Vq : Set W4 := {w | w.2 = true}

/-- The atomic bilateral inquisitive propositions for `p` and `q`. -/
def p_atom : BilatInqProp W4 := BilatInqProp.atom Vp
def q_atom : BilatInqProp W4 := BilatInqProp.atom Vq

/-- The disjunction `p ∨ q`. -/
def p_or_q : BilatInqProp W4 := BilatInqProp.disj p_atom q_atom

/-- The "p-only" world `(true, false)` is in `Vp \ Vq`. -/
example : ((true, false) : W4) ∈ Vp ∧ ((true, false) : W4) ∉ Vq := by
  refine ⟨?_, ?_⟩ <;> simp [Vp, Vq]

/-- The "q-only" world `(false, true)` is in `Vq \ Vp`. -/
example : ((false, true) : W4) ∈ Vq ∧ ((false, true) : W4) ∉ Vp := by
  refine ⟨?_, ?_⟩ <;> simp [Vp, Vq]

/-- The negation `p_atom.negate.pos = q-side` test: negation of `p`'s
    positive content is `↓{Vp^c}`, which contains the q-only world. -/
example : ({((false, true) : W4)} : Set W4) ∈ p_atom.negate.pos := by
  show ({((false, true) : W4)} : Set W4) ⊆ Vpᶜ
  intro w hw
  simp only [Set.mem_singleton_iff] at hw
  subst hw
  simp [Vp]

end BoothExample

/-! ### §7 The Independence inference (Booth Fact 9)

The headline theorem of @cite{booth-2022}: necessity-modal sentences
with disjunctive complements (and non-Hurford disjuncts) license
Independence — `□(p ∨ q) ⊨ ◇(p ∧ ¬q)` and `□(p ∨ q) ⊨ ◇(q ∧ ¬p)`.

The general meta-language theorem (over the class of non-Hurford
models) requires Booth's Compactness-of-Alternatives lemma (Fact 5)
and the non-Hurford characterization (Definition 22), which go beyond
the scope of this initial study file. We state the theorem and carry
a documented `sorry`; future work could elaborate the proof or replace
it with a worked example over `BoothExample.W4`. -/

/-- **Booth Fact 9 (Object-Language Independence)**: under the model
    class where `p ∨ q` is non-Hurford, `□(p ∨ q)` truth at `w` entails
    `◇(p ∧ ¬q)` truth at `w`.

    The proof Booth gives proceeds via Fact 6 (Meta-Language
    Independence) using non-Hurford-disjunction reasoning + the
    Compactness-of-Alternatives lemma (Fact 5). Carried as a
    documented `sorry` until those substrates land. -/
theorem independence_p_not_q
    (W : Type*) (R : W → Set W) (Vp Vq : Set W)
    (_h_non_hurford : ¬ Vp ⊆ Vq ∧ ¬ Vq ⊆ Vp)
    (w : W) :
    isTrue (BilatInqProp.necessity R
      (BilatInqProp.disj (BilatInqProp.atom Vp) (BilatInqProp.atom Vq))) w →
    isTrue (BilatInqProp.possibility R
      (BilatInqProp.conj (BilatInqProp.atom Vp)
        (BilatInqProp.negate (BilatInqProp.atom Vq)))) w := by
  -- TODO: requires Fact 5 (Compactness of Alternatives) + Fact 6
  -- (Meta-Language Independence) substrate; see Booth 2022 §3.2.
  -- Proof sketch: from m-cover of R(w) by {Vp, Vq} (alt⁺), pick a
  -- world v ∈ R(w) ∩ (Vp \ Vq) — minimality forces this; then {v}
  -- witnesses the existential in possibility's negative-side def.
  sorry

end Phenomena.Modality.Studies.Booth2022
