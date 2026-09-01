/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Factors
import Linglib.Phonology.Autosegmental.Realization

/-!
# Local autosegmental configurations

The named building blocks of autosegmental representations. `AR.junction as bs` links
every melody node of `as` to every timing slot of `bs`; its planar specializations —
`single`, `bare`, `float`, `contour`, `spread` — are the local configurations of
autosegmental tonology, and `concat`-products of them build every representation in the
current tone studies (`Studies/Jardine2016a`, `Studies/Jardine2017`,
`Studies/Jardine2019`). Building through them (rather than raw structure literals)
carries the in-bounds proof at arbitrary alphabets, where the studies' `by decide`
cannot go, and gives every configuration a simp kit.

The keystone is `isPlanar_junction_iff`: a junction is planar iff one side has at most
one node, so among complete many-to-many associations the No-Crossing Constraint
([goldsmith-1976]) admits exactly the one-to-many (`spread`), many-to-one (`contour`)
and degenerate configurations. (Formaliser's synthesis: the literature treats the NCC
as a filter on representations, not as a characterisation of local generators.)

`concat` is the coproduct, so builder products reach exactly the block-diagonal link
relations; connected shared-node configurations (e.g. a spread-fed contour, H→μ₁ with
L→μ₁μ₂) are planar but not products. TODO: a gluing operation dual to `concat`
(identify a shared boundary slot) reaching them, with the completeness target *every
planar AR is a concat/glue expression over the builders*; at that point `junction`
becomes primary and the five kits derive from its (the
`SimpleGraph.completeBipartiteGraph` move).

## Main definitions

* `AR.junction` — complete many-to-many association of a melody onto a slot sequence.
* `AR.single`, `AR.bare`, `AR.float`, `AR.contour`, `AR.spread` — the planar local
  configurations: one-to-one, toneless slot, floating autosegment ([leben-1973]; the
  tier-with-floats object is `Floating.lean`), several nodes on one slot, one node over
  several slots.

## Main results

* `AR.isPlanar_junction_iff` — NCC-planarity of a junction: one side is at most a
  singleton.
* The junction simp kit — tier words and lengths (`AR.tierWord_junction_true`,
  `AR.tierLength_junction_true`, …) and links (`AR.link_junction`) — which the builders
  inherit as transparent aliases; per-builder planarity (`AR.isPlanar_single`, …).
-/

namespace Autosegmental

variable {α β : Type*} {a : α} {b : β} {as : List α} {bs : List β}



/-! ### The junction in coordinates

The complete association as a two-tier `AR` (`Bool`-indexed:
`true` the melody tier, `false` the timing tier), built by `ofData`; the
No-Crossing keystone in the foundational path form. -/

section CoordinateJunction

universe u
variable {α β : Type u}

/-- The two-tier alphabet: melody labels over `true`, timing labels over
    `false`. -/
abbrev TwoTier (α β : Type u) : Bool → Type u := fun b => bif b then α else β

instance [DecidableEq α] : DecidableEq (TwoTier α β true) := inferInstanceAs (DecidableEq α)

instance [DecidableEq β] : DecidableEq (TwoTier α β false) := inferInstanceAs (DecidableEq β)

/-- Complete many-to-many association of a melody onto a slot sequence, in
    coordinates. -/
def AR.junction (as : List α) (bs : List β) :
    AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool) :=
  AR.ofData
    (fun b => match b with
      | true => (as : List (TwoTier α β true))
      | false => (bs : List (TwoTier α β false)))
    (fun i j p q => i = true ∧ j = false ∧ p < as.length ∧ q < bs.length)

instance (as : List α) (bs : List β) :
    Finite (AR.junction as bs).obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

@[simp] theorem AR.tierWord_junction_true (as : List α) (bs : List β) :
    (AR.junction as bs).tierWord true = as :=
  AR.tierWord_ofData true

@[simp] theorem AR.tierWord_junction_false (as : List α) (bs : List β) :
    (AR.junction as bs).tierWord false = bs :=
  AR.tierWord_ofData false

@[simp] theorem AR.tierLength_junction_true (as : List α) (bs : List β) :
    (AR.junction as bs).tierLength true = as.length :=
  AR.tierLength_ofData true

@[simp] theorem AR.tierLength_junction_false (as : List α) (bs : List β) :
    (AR.junction as bs).tierLength false = bs.length :=
  AR.tierLength_ofData false

/-- Junction links are complete: every in-bounds melody–timing pair. -/
@[simp] theorem AR.link_junction (as : List α) (bs : List β) {b b' : Bool}
    {p q : ℕ} : (AR.junction as bs).link b b' p q ↔
      b = true ∧ b' = false ∧ p < as.length ∧ q < bs.length ∨
        b = false ∧ b' = true ∧ p < bs.length ∧ q < as.length := by
  unfold AR.junction
  rw [AR.link_ofData]
  constructor
  · rintro ⟨hne, hp, hq, (⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩)⟩
    · exact Or.inl ⟨rfl, rfl, h1, h2⟩
    · exact Or.inr ⟨rfl, rfl, by simpa using hp, by simpa using hq⟩
  · rintro (⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩)
    · exact ⟨by decide, by simpa using h1, by simpa using h2,
        Or.inl ⟨rfl, rfl, h1, h2⟩⟩
    · exact ⟨by decide, by simpa using h1, by simpa using h2,
        Or.inr ⟨rfl, rfl, h2, h1⟩⟩

/-- **The No-Crossing Constraint selects the one-sided junctions**: a complete
    association is planar iff one side has at most one node — the one-to-many
    `spread`, many-to-one `contour`, and degenerate cases. -/
theorem AR.isPlanar_junction_iff (as : List α) (bs : List β) :
    IsPlanar (AR.junction as bs).obj.edges (AR.junction as bs).obj.arcs ↔
      as.length ≤ 1 ∨ bs.length ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ha, hb⟩ := hc
    rw [Nat.not_le] at ha hb
    exact h (v := ⟨true, ⟨0, show 0 < as.length by omega⟩⟩)
      (v' := ⟨false, ⟨1, show 1 < bs.length by omega⟩⟩)
      (w := ⟨true, ⟨1, show 1 < as.length by omega⟩⟩)
      (w' := ⟨false, ⟨0, show 0 < bs.length by omega⟩⟩)
      ⟨by simp, Or.inl ⟨rfl, rfl, show (0 : ℕ) < as.length by omega,
        show (1 : ℕ) < bs.length by omega⟩⟩
      ⟨by simp, Or.inl ⟨rfl, rfl, show (1 : ℕ) < as.length by omega,
        show (0 : ℕ) < bs.length by omega⟩⟩
      ⟨rfl, show (0 : ℕ) < 1 by omega⟩ ⟨rfl, show (0 : ℕ) < 1 by omega⟩
  · rintro h ⟨bv, pv⟩ ⟨bv', pv'⟩ ⟨bw, pw⟩ ⟨bw', pw'⟩ hvv' hww' hvw hw'v'
    obtain ⟨hbvw, hpvw⟩ := hvw
    obtain ⟨hbw'v', hpw'v'⟩ := hw'v'
    cases hbvw
    cases hbw'v'
    have hv' : bv' = !bv := by
      rcases hvv' with ⟨hne, -⟩
      cases bv <;> cases bv' <;> simp_all
    subst hv'
    rcases h with h | h <;> cases bv
    · have h1 : (pv' : ℕ) < as.length := pv'.isLt
      have h2 : (pw' : ℕ) < as.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega
    · have h1 : (pv : ℕ) < as.length := pv.isLt
      have h2 : (pw : ℕ) < as.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv : ℕ) < bs.length := pv.isLt
      have h2 : (pw : ℕ) < bs.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv' : ℕ) < bs.length := pv'.isLt
      have h2 : (pw' : ℕ) < bs.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega

/-! #### The planar local configurations -/

/-- One-to-one association. -/
abbrev AR.single (a : α) (b : β) := AR.junction [a] [b]

/-- A bare (unassociated) timing slot. -/
abbrev AR.bare (b : β) := AR.junction ([] : List α) [b]

/-- A floating autosegment ([leben-1973]). -/
abbrev AR.float (a : α) := AR.junction [a] ([] : List β)

/-- Several melody nodes on one slot. -/
abbrev AR.contour (as : List α) (b : β) := AR.junction as [b]

/-- One melody node over several slots. -/
abbrev AR.spread (a : α) (bs : List β) := AR.junction [a] bs

theorem AR.isPlanar_single (a : α) (b : β) :
    IsPlanar (AR.single a b).obj.edges (AR.single a b).obj.arcs :=
  (AR.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem AR.isPlanar_bare (b : β) :
    IsPlanar (AR.bare (α := α) b).obj.edges (AR.bare (α := α) b).obj.arcs :=
  (AR.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem AR.isPlanar_float (a : α) :
    IsPlanar (AR.float (β := β) a).obj.edges (AR.float (β := β) a).obj.arcs :=
  (AR.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem AR.isPlanar_contour (as : List α) (b : β) :
    IsPlanar (AR.contour as b).obj.edges (AR.contour as b).obj.arcs :=
  (AR.isPlanar_junction_iff _ _).mpr (Or.inr (by simp))

theorem AR.isPlanar_spread (a : α) (bs : List β) :
    IsPlanar (AR.spread a bs).obj.edges (AR.spread a bs).obj.arcs :=
  (AR.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

/-- Two-tier factor embedding is a search over two bounded offsets. -/
theorem AR.factorEmbeds_iff_two_tier
    {F X : AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool)}
    [Finite F.obj.V] [Finite X.obj.V] :
    F.FactorEmbeds X ↔
      ∃ ot ≤ X.tierLength true, ∃ of ≤ X.tierLength false,
        F.IsFactorAt X (fun b => bif b then ot else of) := by
  rw [AR.factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, hfa⟩
    refine ⟨o true, hb true, o false, hb false, ?_⟩
    have he : (fun b => bif b then o true else o false) = o :=
      funext fun b => by cases b <;> rfl
    rwa [he]
  · rintro ⟨ot, hot, of, hof, hfa⟩
    exact ⟨_, fun b => by cases b <;> simpa, hfa⟩

/-- The data-level factor check: `wsF`/`LF` occurs in `wsX`/`LX` at some pair
    of bounded offsets — list windows match and links transport shifted. The
    decidable face of `FactorEmbeds` for `ofData`-presented forms. -/
def dataEmbeds (wsF wsX : ∀ b : Bool, List (TwoTier α β b))
    (LF LX : Bool → Bool → ℕ → ℕ → Prop) : Prop :=
  ∃ ot ≤ (wsX true).length, ∃ of ≤ (wsX false).length,
    (∀ p < (wsF true).length, (wsX true)[p + ot]? = (wsF true)[p]?) ∧
    (∀ p < (wsF false).length, (wsX false)[p + of]? = (wsF false)[p]?) ∧
    ∀ p < (wsF true).length, ∀ q < (wsF false).length,
      (LF true false p q ∨ LF false true q p) →
        (LX true false (p + ot) (q + of) ∨ LX false true (q + of) (p + ot))

instance {wsF wsX : ∀ b : Bool, List (TwoTier α β b)}
    {LF LX : Bool → Bool → ℕ → ℕ → Prop}
    [DecidableEq α] [DecidableEq β]
    [∀ i j p q, Decidable (LF i j p q)] [∀ i j p q, Decidable (LX i j p q)] :
    Decidable (dataEmbeds wsF wsX LF LX) := by
  unfold dataEmbeds
  infer_instance

/-- **The spec**: on `ofData`-presented two-tier forms, factor embedding is the
    data-level check — the bridge that turns banned-subgraph verdicts into
    kernel computations. -/
theorem AR.factorEmbeds_ofData_iff
    {wsF wsX : ∀ b : Bool, List (TwoTier α β b)}
    {LF LX : Bool → Bool → ℕ → ℕ → Prop} :
    (AR.ofData wsF LF).FactorEmbeds (AR.ofData wsX LX) ↔
      dataEmbeds wsF wsX LF LX := by
  rw [AR.factorEmbeds_iff_two_tier]
  simp only [AR.tierLength_ofData]
  constructor
  · rintro ⟨ot, hot, of, hof, hw, hl⟩
    refine ⟨ot, hot, of, hof, ?_, ?_, ?_⟩
    · intro p hp
      have := hw true p (by rw [AR.tierLength_ofData]; exact hp)
      rwa [AR.tierWord_ofData, AR.tierWord_ofData] at this
    · intro p hp
      have := hw false p (by rw [AR.tierLength_ofData]; exact hp)
      rwa [AR.tierWord_ofData, AR.tierWord_ofData] at this
    · intro p hp q hq hpq
      have hlk := hl true false p q ((AR.link_ofData true false p q).mpr
        ⟨by decide, hp, hq, hpq⟩)
      rcases (AR.link_ofData true false (p + ot) (q + of)).mp hlk with
        ⟨-, -, -, hres⟩
      exact hres
  · rintro ⟨ot, hot, of, hof, hwt, hwf, hlk⟩
    have hbt : ∀ p, p < (wsF true).length → p + ot < (wsX true).length := by
      intro p hp
      have h1 : (wsX true)[p + ot]? = some ((wsF true)[p]'hp) :=
        (hwt p hp).trans (List.getElem?_eq_getElem hp)
      exact (List.getElem?_eq_some_iff.mp h1).1
    have hbf : ∀ q, q < (wsF false).length → q + of < (wsX false).length := by
      intro q hq
      have h1 : (wsX false)[q + of]? = some ((wsF false)[q]'hq) :=
        (hwf q hq).trans (List.getElem?_eq_getElem hq)
      exact (List.getElem?_eq_some_iff.mp h1).1
    refine ⟨ot, hot, of, hof, ?_, ?_⟩
    · intro i p hp
      rw [AR.tierLength_ofData] at hp
      cases i
      · rw [show ((AR.ofData wsX LX).tierWord false)
            = wsX false from AR.tierWord_ofData false,
          show ((AR.ofData wsF LF).tierWord false)
            = wsF false from AR.tierWord_ofData false]
        exact hwf p hp
      · rw [show ((AR.ofData wsX LX).tierWord true)
            = wsX true from AR.tierWord_ofData true,
          show ((AR.ofData wsF LF).tierWord true)
            = wsF true from AR.tierWord_ofData true]
        exact hwt p hp
    · intro i j p q hl
      rcases (AR.link_ofData i j p q).mp hl with ⟨hne, hp, hq, hor⟩
      have hcases : i = true ∧ j = false ∨ i = false ∧ j = true := by
        cases i <;> cases j <;> simp_all
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hlk p hp q hq hor with hres | hres
        · exact (AR.link_ofData true false _ _).mpr
            ⟨by decide, hbt p hp, hbf q hq, Or.inl hres⟩
        · exact (AR.link_ofData true false _ _).mpr
            ⟨by decide, hbt p hp, hbf q hq, Or.inr hres⟩
      · rcases hlk q hq p hp hor.symm with hres | hres
        · exact (AR.link_ofData false true _ _).mpr
            ⟨by decide, hbf p hp, hbt q hq, Or.inr hres⟩
        · exact (AR.link_ofData false true _ _).mpr
            ⟨by decide, hbf p hp, hbt q hq, Or.inl hres⟩

/-! #### Two-tier representations from words -/

namespace TwoTier

/-- The tier words of a melody word and a timing word. -/
def words (as : List α) (bs : List β) : ∀ b : Bool, List (TwoTier α β b)
  | true => (as : List (TwoTier α β true))
  | false => (bs : List (TwoTier α β false))

@[simp] theorem words_true (as : List α) (bs : List β) : words as bs true = as := rfl

@[simp] theorem words_false (as : List α) (bs : List β) : words as bs false = bs := rfl

/-- Association lines from melody position `p` to timing position `q` under `L`. -/
def links (L : ℕ → ℕ → Prop) (i j : Bool) (p q : ℕ) : Prop := i = true ∧ j = false ∧ L p q

instance (L : ℕ → ℕ → Prop) [DecidableRel L] (i j : Bool) (p q : ℕ) :
    Decidable (links L i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end TwoTier

/-- The representation of a melody `as` over a timing word `bs`, associated by `L` on
positions: the general two-tier form, of which `junction` is the complete case. -/
def AR.ofWords (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) :
    AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool) :=
  AR.ofData (TwoTier.words as bs) (TwoTier.links L)

instance (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) : Finite (AR.ofWords as bs L).obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

@[simp] theorem AR.tierWord_ofWords_true (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) :
    (AR.ofWords as bs L).tierWord true = as :=
  AR.tierWord_ofData true

@[simp] theorem AR.tierWord_ofWords_false (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) :
    (AR.ofWords as bs L).tierWord false = bs :=
  AR.tierWord_ofData false

/-- Embedding between representations of words is the data-level check, hence decidable. -/
theorem AR.factorEmbeds_ofWords_iff (as as' : List α) (bs bs' : List β)
    (L L' : ℕ → ℕ → Prop) :
    (AR.ofWords as bs L).FactorEmbeds (AR.ofWords as' bs' L') ↔
      dataEmbeds (TwoTier.words as bs) (TwoTier.words as' bs') (TwoTier.links L)
        (TwoTier.links L') :=
  AR.factorEmbeds_ofData_iff

instance [DecidableEq α] [DecidableEq β] (as as' : List α) (bs bs' : List β)
    (L L' : ℕ → ℕ → Prop) [DecidableRel L] [DecidableRel L'] :
    Decidable ((AR.ofWords as bs L).FactorEmbeds (AR.ofWords as' bs' L')) :=
  decidable_of_iff _ (AR.factorEmbeds_ofWords_iff as as' bs bs' L L').symm

@[simp] theorem AR.tierLength_ofWords_true (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) :
    (AR.ofWords as bs L).tierLength true = as.length :=
  AR.tierLength_ofData true

@[simp] theorem AR.tierLength_ofWords_false (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) :
    (AR.ofWords as bs L).tierLength false = bs.length :=
  AR.tierLength_ofData false

/-- The lines of a representation of words: in bounds, and related by `L`. -/
theorem AR.link_ofWords (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) (p q : ℕ) :
    (AR.ofWords as bs L).link true false p q ↔ p < as.length ∧ q < bs.length ∧ L p q := by
  simp [AR.ofWords, AR.link_ofData, TwoTier.words, TwoTier.links]

/-- A representation of words with no lines. -/
theorem AR.not_link_ofWords_false (as : List α) (bs : List β) (i j : Bool) (p q : ℕ) :
    ¬ (AR.ofWords as bs fun _ _ => False).link i j p q := fun hl => by
  rcases (AR.link_ofData i j p q).mp hl with ⟨-, -, -, ⟨-, -, h⟩ | ⟨-, -, h⟩⟩ <;> exact h

/-- Two-tier links are determined by the melody-to-timing case. -/
theorem AR.link_iff_of_true_false {X Y : AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool)}
    [Finite X.obj.V] [Finite Y.obj.V]
    (h : ∀ p q, X.link true false p q ↔ Y.link true false p q) (i j : Bool) (p q : ℕ) :
    X.link i j p q ↔ Y.link i j p q := by
  cases i <;> cases j
  · exact iff_of_false (X.not_link_self_tier _ _ _) (Y.not_link_self_tier _ _ _)
  · exact ⟨fun hl => Y.link_symm ((h q p).mp (X.link_symm hl)),
      fun hl => X.link_symm ((h q p).mpr (Y.link_symm hl))⟩
  · exact h p q
  · exact iff_of_false (X.not_link_self_tier _ _ _) (Y.not_link_self_tier _ _ _)

/-! #### Realizations of word primitives

The realization of a string whose primitives are representations of words has the readers
of one representation of words: the tier words concatenate, and a line lives inside one
symbol's primitive, at that symbol's offsets. -/

section RealizeOfWords

variable {S : Type*} (as : S → List α) (bs : S → List β) (L : S → ℕ → ℕ → Prop)

/-- The offset of the `k`-th symbol's word in the concatenation. -/
def wordOffset {γ : Type*} (f : S → List γ) (w : List S) (k : ℕ) : ℕ :=
  ((w.take k).map fun s => (f s).length).sum

theorem wordOffset_add_length_le {γ : Type*} (f : S → List γ) {w : List S} {k : ℕ}
    (hk : k < w.length) : wordOffset f w k + (f w[k]).length ≤ (w.map f).flatten.length := by
  have h := List.sum_take_add_sum_drop (w.map fun s => (f s).length) k
  rw [List.drop_eq_getElem_cons (by simpa using hk), List.sum_cons] at h
  simp only [wordOffset, List.length_flatten, List.map_map, List.map_take, List.getElem_map,
    Function.comp_def] at h ⊢
  omega

/-- The lines of a concatenation of word primitives: inside one symbol's primitive, at its
offsets. -/
def blockLinks (w : List S) (p q : ℕ) : Prop :=
  ∃ k, ∃ hk : k < w.length, wordOffset as w k ≤ p ∧ wordOffset bs w k ≤ q ∧
    p - wordOffset as w k < (as w[k]).length ∧ q - wordOffset bs w k < (bs w[k]).length ∧
    L w[k] (p - wordOffset as w k) (q - wordOffset bs w k)

instance [∀ s, DecidableRel (L s)] (w : List S) : DecidableRel (blockLinks as bs L w) :=
  fun _ _ => by unfold blockLinks; infer_instance

theorem blockLinks_lt {w : List S} {p q : ℕ} (h : blockLinks as bs L w p q) :
    p < (w.map as).flatten.length ∧ q < (w.map bs).flatten.length := by
  obtain ⟨k, hk, hp, hq, hp', hq', -⟩ := h
  have := wordOffset_add_length_le as hk
  have := wordOffset_add_length_le bs hk
  omega

variable (g₀ : S → AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool)) [∀ s, Finite (g₀ s).obj.V]
  (hg : ∀ s, g₀ s = AR.ofWords (as s) (bs s) (L s))
include hg

theorem AR.tierWord_realize_true_of_eq_ofWords (w : List S) :
    (AR.realize g₀ w).tierWord true = (w.map as).flatten := by
  simp [AR.tierWord_realize, hg]

theorem AR.tierWord_realize_false_of_eq_ofWords (w : List S) :
    (AR.realize g₀ w).tierWord false = (w.map bs).flatten := by
  simp [AR.tierWord_realize, hg]

theorem AR.tierOffset_true_of_eq_ofWords (w : List S) (k : ℕ) :
    AR.tierOffset g₀ true w k = wordOffset as w k := by
  simp [AR.tierOffset, hg, wordOffset]

theorem AR.tierOffset_false_of_eq_ofWords (w : List S) (k : ℕ) :
    AR.tierOffset g₀ false w k = wordOffset bs w k := by
  simp [AR.tierOffset, hg, wordOffset]

theorem AR.link_realize_of_eq_ofWords (w : List S) (p q : ℕ) :
    (AR.realize g₀ w).link true false p q ↔ blockLinks as bs L w p q := by
  rw [AR.link_realize]
  simp only [AR.tierOffset_true_of_eq_ofWords as bs L g₀ hg,
    AR.tierOffset_false_of_eq_ofWords as bs L g₀ hg, hg, AR.link_ofWords, blockLinks]

/-- The realization of word primitives has the readers of one representation of words. -/
theorem AR.factorEmbeds_realize_iff_of_eq_ofWords
    (F : AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool)) [Finite F.obj.V] (w : List S) :
    F.FactorEmbeds (AR.realize g₀ w) ↔
      F.FactorEmbeds (AR.ofWords (w.map as).flatten (w.map bs).flatten (blockLinks as bs L w)) :=
  AR.factorEmbeds_congr (fun _ => rfl) (fun _ _ _ _ => Iff.rfl)
    (fun i => by
      cases i
      · exact (AR.tierWord_realize_false_of_eq_ofWords as bs L g₀ hg w).trans
          (AR.tierWord_ofWords_false _ _ _).symm
      · exact (AR.tierWord_realize_true_of_eq_ofWords as bs L g₀ hg w).trans
          (AR.tierWord_ofWords_true _ _ _).symm)
    (AR.link_iff_of_true_false fun p q => by
      rw [AR.link_realize_of_eq_ofWords as bs L g₀ hg, AR.link_ofWords]
      exact ⟨fun h => ⟨(blockLinks_lt as bs L h).1, (blockLinks_lt as bs L h).2, h⟩,
        fun h => h.2.2⟩)

theorem AR.free_realize_iff_of_eq_ofWords
    (B : List {F : AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool) // Finite F.obj.V})
    (w : List S) :
    (AR.realize g₀ w).Free B ↔
      (AR.ofWords (w.map as).flatten (w.map bs).flatten (blockLinks as bs L w)).Free B :=
  forall₂_congr fun _ _ => not_congr (AR.factorEmbeds_realize_iff_of_eq_ofWords as bs L g₀ hg _ w)

end RealizeOfWords

/-- A timing slot **surfaces with** melody label `a`: some `a`-labelled melody
    node links to it. -/
def AR.surfacesWith
    (X : AR (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool))
    [Finite X.obj.V] (a : α) (j : ℕ) : Prop :=
  ∃ k, X.link true false k j ∧ (X.tierWord true)[k]? = some a

end CoordinateJunction

end Autosegmental
