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
- `IsMinCover` is expressed as `Minimal (IsCover · S) C` using mathlib's
  `Minimal` predicate, mirroring how `Question.alt` uses `Maximal`
  (Booth's `alt` is the dual of his m-cover).

## Out of scope

- The collectivity heuristic of @cite{booth-2022} §4 is a discourse-level
  proposal not formalized here.
- Booth's restrictor conditional and accessibility-update operator
  (Definitions 15–16) are out of scope for this initial formalization.
- The general Independence theorem (Booth Fact 9) is sketched but
  carried as a documented `sorry` — its proof relies on
  non-Hurford-disjunction reasoning (Fact 6) plus finite-alt machinery
  that goes beyond a self-contained study file. The companion concrete
  example (`BoothExample.boothExample_independence`) hand-verifies
  Independence on a 3-world deontic model.
-/

namespace Phenomena.Modality.Studies.Booth2022

open Core
open Core.Logic.Bilateral

variable {W : Type*}

/-! ### §1 Cover and minimal cover (Booth Section 2.1)

Booth's `□φ` differs from Kratzerian necessity by requiring not just
that the alternatives of `⟦φ⟧⁺` cover `R(w)`, but that they form a
**minimal cover** — no proper subset of the alternatives still covers
`R(w)`. This is what derives Independence inferences (Fact 9): each
alternative must be "needed", so no single alternative dominates.

Expressed via mathlib's `Minimal` predicate (mirrors `Question.alt`'s
use of `Maximal` — Booth's `alt` and `m-cover` are dual instances of
the order-theoretic extremality pattern). -/

/-- **Booth §2.1**: `C` covers `S` iff `S ⊆ ⋃C`. -/
def IsCover (C : Set (Set W)) (S : Set W) : Prop := S ⊆ ⋃₀ C

/-- **Booth §2.1**: `C` is a **minimal cover** (m-cover) of `S` iff `C`
    covers `S` and no proper subfamily `C' ⊂ C` covers `S`. Expressed
    via mathlib's `Minimal`. -/
def IsMinCover (C : Set (Set W)) (S : Set W) : Prop :=
  Minimal (fun X => IsCover X S) C

theorem IsMinCover.isCover {C : Set (Set W)} {S : Set W}
    (h : IsMinCover C S) : IsCover C S := h.prop

/-! ### §2 Bilateral inquisitive propositions (Booth Def 10) -/

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
    rcases hpos with h | h
    · exact φ.no_overlap s h hneg.1
    · exact ψ.no_overlap s h hneg.2

/-- **Booth Def 14, ∧-clause** via the derivation `⟦φ ∧ ψ⟧ = ⟦¬(¬φ ∨ ¬ψ)⟧`
    — direct unfolding gives `pos = φ.pos ⊓ ψ.pos`, `neg = φ.neg ⊔ ψ.neg`.
    The Booth-equivalence `conj φ ψ = negate (disj (negate φ) (negate ψ))`
    holds by `rfl`. -/
def conj (φ ψ : BilatInqProp W) : BilatInqProp W where
  pos := φ.pos ⊓ ψ.pos
  neg := φ.neg ⊔ ψ.neg
  no_overlap s hpos hneg := by
    rcases hneg with h | h
    · exact φ.no_overlap s hpos.1 h
    · exact ψ.no_overlap s hpos.2 h

/-! ### §3 Necessity and possibility (Booth Def 14)

`R : W → Set W` is the relevant-worlds accessibility relation
(equivalent in expressive power to `Core.Logic.Intensional.AccessRel W
= W → W → Prop`; Booth uses the curried `W → Set W` form throughout
his Def 14, which we mirror). -/

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
    obtain ⟨α, hαAlt, hvα⟩ : ∃ α ∈ Question.alt φ.pos, v ∈ α :=
      hwPos.2.isCover hvRw
    obtain ⟨β, hβAlt, hvβ⟩ : ∃ β ∈ Question.alt φ.neg, v ∈ β :=
      hR'mc.isCover hvR'
    have hαPos : α ∈ φ.pos.props := Question.alt_subset_props _ hαAlt
    have hβNeg : β ∈ φ.neg.props := Question.alt_subset_props _ hβAlt
    have hvSPos : ({v} : Set W) ∈ φ.pos.props :=
      φ.pos.downward_closed α hαPos {v} (Set.singleton_subset_iff.mpr hvα)
    have hvSNeg : ({v} : Set W) ∈ φ.neg.props :=
      φ.neg.downward_closed β hβNeg {v} (Set.singleton_subset_iff.mpr hvβ)
    exact (Set.singleton_ne_empty v) (φ.no_overlap {v} hvSPos hvSNeg)

/-- **Booth Def 14, ◇-clause** via duality: `⟦◇φ⟧ = ⟦¬□¬φ⟧`. -/
def possibility (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  negate (necessity R (negate φ))

end BilatInqProp

/-! ### §4 Truth and falsity (Booth Def 17)

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

/-! ### §5 Worked example: Independence inference on a 3-world model

A concrete witness that the m-cover semantics derives Booth Fact 9
(Independence Inferences). We work on `W₄ = Bool × Bool` (subsets of
`{p, q}`), with `V p = {(true, _)}` and `V q = {(_, true)}`, and
constant accessibility `R₃ w := V(p) ∪ V(q)` (the 3 worlds where
`p ∨ q` is true).

In this model `{V(p), V(q)}` minimally covers `R₃ w` because removing
either alternative leaves a gap (`V(p)` alone misses `(false, true)`;
`V(q)` alone misses `(true, false)`). Thus `□(p ∨ q)` is true, and
the Vp-only world `(true, false)` lies in `R₃ w`, witnessing the
existential in `◇(p ∧ ¬q)`'s positive-side definition. -/

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

/-- The conjunction `p ∧ ¬q`. -/
def p_and_not_q : BilatInqProp W4 :=
  BilatInqProp.conj p_atom (BilatInqProp.negate q_atom)

/-- Constant 3-world accessibility: `R₃ w = Vp ∪ Vq`, the worlds where
    `p ∨ q` is true (excluding `(false, false)`). -/
def R₃ : W4 → Set W4 := fun _ => Vp ∪ Vq

/-! #### Pivotal world facts -/

private lemma true_true_in_Vp : ((true, true) : W4) ∈ Vp := by
  simp only [Vp, Set.mem_setOf_eq]
private lemma true_false_in_Vp : ((true, false) : W4) ∈ Vp := by
  simp only [Vp, Set.mem_setOf_eq]
private lemma false_true_in_Vq : ((false, true) : W4) ∈ Vq := by
  simp only [Vq, Set.mem_setOf_eq]
private lemma true_false_not_in_Vq : ((true, false) : W4) ∉ Vq := by
  simp only [Vq, Set.mem_setOf_eq]; decide
private lemma false_true_not_in_Vp : ((false, true) : W4) ∉ Vp := by
  simp only [Vp, Set.mem_setOf_eq]; decide

private lemma Vp_nsub_Vq : ¬ Vp ⊆ Vq :=
  fun h => true_false_not_in_Vq (h true_false_in_Vp)
private lemma Vq_nsub_Vp : ¬ Vq ⊆ Vp :=
  fun h => false_true_not_in_Vp (h false_true_in_Vq)

private lemma R₃_nonempty (w : W4) : (R₃ w).Nonempty :=
  ⟨(true, true), Or.inl true_true_in_Vp⟩

/-! #### Question-algebraic helpers -/

/-- Inf of two declaratives is the declarative of the intersection. Inline
    helper; mathlib has no analogue at `Question` level (and one isn't
    needed substrate-wide until a second consumer). -/
private lemma declarative_inf (A B : Set W4) :
    Question.declarative A ⊓ Question.declarative B = Question.declarative (A ∩ B) := by
  apply Question.ext
  intro q
  show q ⊆ A ∧ q ⊆ B ↔ q ⊆ A ∩ B
  rw [Set.subset_inter_iff]

/-- The alternatives of `(declarative Vp) ⊔ (declarative Vq)` are exactly
    `{Vp, Vq}` in our model — both are maximal because neither is a
    subset of the other (`Vp_nsub_Vq`, `Vq_nsub_Vp`). -/
private lemma alt_p_or_q_pos :
    Question.alt p_or_q.pos = ({Vp, Vq} : Set (Set W4)) := by
  show Question.alt (Question.declarative Vp ⊔ Question.declarative Vq) = _
  apply Set.eq_of_subset_of_subset
  · intro q hq
    have h := Question.alt_sup_subset_union (Question.declarative Vp)
              (Question.declarative Vq) hq
    rcases h with h | h
    · rw [Question.alt_declarative] at h
      rcases Set.mem_singleton_iff.mp h with rfl
      exact Set.mem_insert _ _
    · rw [Question.alt_declarative] at h
      rcases Set.mem_singleton_iff.mp h with rfl
      exact Set.mem_insert_of_mem _ rfl
  · intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq'
    · apply Question.mem_alt_sup_of_alt_left
        (P := Question.declarative Vp) (Q := Question.declarative Vq)
      · rw [Question.alt_declarative]; rfl
      · intro r hr hVpr
        exact absurd (hVpr.trans hr) Vp_nsub_Vq
    · rcases Set.mem_singleton_iff.mp hq' with rfl
      apply Question.mem_alt_sup_of_alt_right
        (P := Question.declarative Vp) (Q := Question.declarative Vq)
      · rw [Question.alt_declarative]; rfl
      · intro r hr hVqr
        exact absurd (hVqr.trans hr) Vq_nsub_Vp

/-- The alternatives of `(declarative Vp) ⊓ (declarative Vqᶜ)` are
    exactly `{Vp ∩ Vqᶜ}` — the meet collapses to a single declarative. -/
private lemma alt_p_and_not_q_pos :
    Question.alt p_and_not_q.pos = ({Vp ∩ Vqᶜ} : Set (Set W4)) := by
  show Question.alt (Question.declarative Vp ⊓ Question.declarative Vqᶜ) = _
  rw [declarative_inf]
  exact Question.alt_declarative _

/-! #### The Independence-witness theorems -/

/-- **`□(p ∨ q)` holds at `(true, true)` in the 3-world model.** Both
    `(R₃ w).Nonempty` and `IsMinCover {Vp, Vq} (Vp ∪ Vq)` are
    discharged: the latter requires that any cover-subset must contain
    both `Vp` (witnessed by `(true, false)` ∈ Vp \ Vq) and `Vq`
    (witnessed by `(false, true)` ∈ Vq \ Vp). -/
theorem boothExample_necessity_holds :
    isTrue (BilatInqProp.necessity R₃ p_or_q) ((true, true) : W4) := by
  show ({((true, true) : W4)} : Set W4) ⊆ _
  intro w hw
  rcases Set.mem_singleton_iff.mp hw with rfl
  refine ⟨R₃_nonempty _, ?_⟩
  rw [alt_p_or_q_pos]
  refine ⟨?_, ?_⟩
  · -- IsCover {Vp, Vq} (Vp ∪ Vq)
    intro v hv
    rcases hv with hv | hv
    · exact ⟨Vp, Set.mem_insert _ _, hv⟩
    · exact ⟨Vq, Set.mem_insert_of_mem _ rfl, hv⟩
  · -- Minimality
    intro Y hYcov hYsub X hXmem
    rcases Set.mem_insert_iff.mp hXmem with rfl | hX
    · -- Need Vp ∈ Y. (true, false) ∈ Vp ⊆ Vp ∪ Vq, must be in some Z ∈ Y ⊆ {Vp, Vq}.
      have h1 : ((true, false) : W4) ∈ Vp ∪ Vq := Or.inl true_false_in_Vp
      obtain ⟨Z, hZY, hZmem⟩ := hYcov h1
      have hZ_in : Z ∈ ({Vp, Vq} : Set (Set W4)) := hYsub hZY
      rcases Set.mem_insert_iff.mp hZ_in with rfl | hZ_or
      · exact hZY
      · rcases Set.mem_singleton_iff.mp hZ_or with rfl
        exact absurd hZmem true_false_not_in_Vq
    · rcases Set.mem_singleton_iff.mp hX with rfl
      have h1 : ((false, true) : W4) ∈ Vp ∪ Vq := Or.inr false_true_in_Vq
      obtain ⟨Z, hZY, hZmem⟩ := hYcov h1
      have hZ_in : Z ∈ ({Vp, Vq} : Set (Set W4)) := hYsub hZY
      rcases Set.mem_insert_iff.mp hZ_in with rfl | hZ_or
      · exact absurd hZmem false_true_not_in_Vp
      · rcases Set.mem_singleton_iff.mp hZ_or with rfl
        exact hZY

/-- **`◇(p ∧ ¬q)` holds at `(true, true)` in the 3-world model.** The
    Vp-only world `(true, false)` witnesses the existential in the
    possibility's positive-side def: it lies in `R₃ (true, true)` and
    `{(true, false)}` is m-covered by `{Vp ∩ Vqᶜ}`. -/
theorem boothExample_possibility_holds :
    isTrue (BilatInqProp.possibility R₃ p_and_not_q) ((true, true) : W4) := by
  show ({((true, true) : W4)} : Set W4) ⊆
    {w : W4 | ∃ R' : Set W4, R' ⊆ R₃ w ∧ R'.Nonempty ∧
              IsMinCover (Question.alt p_and_not_q.pos) R'}
  intro w hw
  rcases Set.mem_singleton_iff.mp hw with rfl
  refine ⟨{((true, false) : W4)}, ?_, ⟨(true, false), rfl⟩, ?_⟩
  · -- {(true, false)} ⊆ R₃ (true, true) = Vp ∪ Vq
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact Or.inl true_false_in_Vp
  · -- IsMinCover {Vp ∩ Vqᶜ} {(true, false)}
    rw [alt_p_and_not_q_pos]
    refine ⟨?_, ?_⟩
    · -- IsCover
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact ⟨Vp ∩ Vqᶜ, Set.mem_singleton _, true_false_in_Vp, true_false_not_in_Vq⟩
    · -- Minimality
      intro Y hYcov hYsub X hXmem
      rcases Set.mem_singleton_iff.mp hXmem with rfl
      have h1 : ((true, false) : W4) ∈ ({(true, false)} : Set W4) := rfl
      obtain ⟨Z, hZY, _hZmem⟩ := hYcov h1
      have hZ_in : Z ∈ ({Vp ∩ Vqᶜ} : Set (Set W4)) := hYsub hZY
      rcases Set.mem_singleton_iff.mp hZ_in with rfl
      exact hZY

/-- **Independence inference on the 3-world model**: `□(p ∨ q)` and
    `◇(p ∧ ¬q)` are jointly true at `(true, true)`. This is a concrete
    witness that the m-cover semantics derives Booth Fact 9 — Kratzerian
    cover semantics on the same model would validate `□(p ∨ q)` but
    leave `◇(p ∧ ¬q)` underivable. -/
theorem boothExample_independence :
    isTrue (BilatInqProp.necessity R₃ p_or_q) ((true, true) : W4) ∧
    isTrue (BilatInqProp.possibility R₃ p_and_not_q) ((true, true) : W4) :=
  ⟨boothExample_necessity_holds, boothExample_possibility_holds⟩

end BoothExample

/-! ### §6 The Independence inference, general meta-language form (Booth Fact 9)

The headline theorem of @cite{booth-2022}: necessity-modal sentences
with disjunctive complements (and non-Hurford disjuncts) license
Independence — `□(p ∨ q) ⊨ ◇(p ∧ ¬q)` and `□(p ∨ q) ⊨ ◇(q ∧ ¬p)`.

The general meta-language theorem (over the class of non-Hurford
models) requires Booth's Compactness-of-Alternatives lemma (Fact 5)
and the non-Hurford characterization (Definition 22), which go beyond
the scope of this initial study file. We state the theorem and carry
a documented `sorry`; the worked-example specialization
(`BoothExample.boothExample_independence`) discharges it on the 3-world
model. -/

/-- **Booth Fact 9 (Object-Language Independence)**: under the model
    class where `p ∨ q` is non-Hurford, `□(p ∨ q)` truth at `w` entails
    `◇(p ∧ ¬q)` truth at `w`.

    The proof Booth gives proceeds via Fact 6 (Meta-Language
    Independence) using non-Hurford-disjunction reasoning + the
    Compactness-of-Alternatives lemma (Fact 5). Carried as a
    documented `sorry` until those substrates land. -/
theorem independence_p_not_q
    (R : W → Set W) (Vp Vq : Set W)
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
  -- The worked example `BoothExample.boothExample_independence`
  -- discharges this for the constant `R₃ = Vp ∪ Vq` accessibility.
  sorry

end Phenomena.Modality.Studies.Booth2022
