import Linglib.Core.Algebra.RootedTree.Bud
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Theta theory as a coloring algorithm

[marcolli-larson-2025] implements theta theory in the mathematical model
of Minimalism ([marcolli-chomsky-berwick-2025] §3.8) as a coloring
algorithm: structures freely formed by Merge are filtered by membership in
the language of a bud generating system ([giraudo-2019],
`Core/Algebra/RootedTree/Bud.lean`) whose colors are theta grids — tuples
of giver- or receiver-marked roles — and whose generators are the local
theta-discharge configurations. A grid injected at a predicate's leaf
propagates up the tree like a conserved quantity: at each generator node
one receiver peels off to the sister position, and the residue continues
toward the maximal projection.

## Main declarations

* `PolarizedRole`, `Color` — giver/receiver-marked roles, and the color
  set: bare grids (nonterminal; `[]` is the non-theta marker), lexically
  anchored grids (terminal), and the empty-tree marker.
* `IsGen`, `rules`, `system` — the generating set: external-role closure,
  hierarchy-ordered internal discharge, adjunct attachment, and movement
  landing ([marcolli-larson-2025]'s complete theta bud system).
* `IsGen.conservation` — the local conservation law each generator
  satisfies; `derives_thetaLocal` — every vertex of every derivable
  structure is a generator instance, hence conserves theta roles.
* `comb`, `comb_derivable` — the bare theta combs (complete grids
  discharged one role per node) are derivable in the complete system:
  the generator half of [marcolli-larson-2025]'s comparison of bare and
  complete systems.
* `rules_emptyTree_out` — a generator with an empty-tree input has a
  non-theta output: movement lands only in non-theta positions, the
  External/Internal Merge dichotomy at generator level.
-/

namespace Minimalist.Theta

/-- Whether a role occurrence gives or receives: [marcolli-larson-2025]'s
    `θ↑` and `θ↓` marks. -/
inductive Polarity where
  | giver
  | receiver
  deriving DecidableEq, Repr

/-- A theta role marked as given or received. -/
structure PolarizedRole where
  role : ThetaRole
  polarity : Polarity
  deriving DecidableEq, Repr

/-- The giver occurrence `θ↑`. -/
def PolarizedRole.up (ρ : ThetaRole) : PolarizedRole := ⟨ρ, .giver⟩

/-- The receiver occurrence `θ↓`. -/
def PolarizedRole.down (ρ : ThetaRole) : PolarizedRole := ⟨ρ, .receiver⟩

/-- A grid of giver occurrences: the undischarged residue a predicate
    carries. -/
def upGrid (g : List ThetaRole) : List PolarizedRole := g.map .up

@[simp] theorem upGrid_nil : upGrid [] = [] := rfl

@[simp] theorem upGrid_append (g h : List ThetaRole) :
    upGrid (g ++ h) = upGrid g ++ upGrid h := List.map_append ..

variable {L : Type*}

/-- The color set: a bare grid (nonterminal; the empty grid is the
    non-theta marker `θ0`), a lexically anchored grid (terminal), or the
    empty-tree marker `(1, θ0)`. -/
inductive Color (L : Type*) where
  | free (g : List PolarizedRole)
  | lex (item : L) (g : List PolarizedRole)
  | emptyTree
  deriving DecidableEq, Repr

/-- The non-theta marker `θ0`: the empty grid. -/
abbrev Color.nontheta : Color L := .free []

/-- Terminal colors: lexically anchored grids and the empty-tree marker. -/
def Color.IsTerminal : Color L → Prop
  | .free _ => False
  | .lex _ _ => True
  | .emptyTree => True

@[simp] theorem Color.isTerminal_free {g : List PolarizedRole} :
    ¬ (Color.free g : Color L).IsTerminal := id

/-- The grid a color carries, if any: lexical anchoring is transparent to
    theta structure. -/
def Color.grid? : Color L → Option (List PolarizedRole)
  | .free g => some g
  | .lex _ g => some g
  | .emptyTree => none

/-- The color carries exactly the grid `g`. -/
def Color.Matches (c : Color L) (g : List PolarizedRole) : Prop :=
  c.grid? = some g

@[simp] theorem Color.matches_free {g h : List PolarizedRole} :
    (Color.free g : Color L).Matches h ↔ g = h := by
  simp [Color.Matches, Color.grid?]

@[simp] theorem Color.matches_lex {α : L} {g h : List PolarizedRole} :
    (Color.lex α g).Matches h ↔ g = h := by
  simp [Color.Matches, Color.grid?]

@[simp] theorem Color.not_matches_emptyTree {g : List PolarizedRole} :
    ¬ (Color.emptyTree : Color L).Matches g := by
  simp [Color.Matches, Color.grid?]

section Rules

variable (hier : ThetaRole → ThetaRole → Prop)

/-- The generator shapes of the theta bud system, as a relation between
    the root grid and the two children's colors (children unordered; the
    rule set closes under swapping). The four cases are
    [marcolli-larson-2025]'s complete-system generators:

    * `close` — the external role discharges and the maximal projection is
      recolored arbitrarily;
    * `discharge` — one internal role, next in the hierarchy, peels off to
      the sister while the residue propagates;
    * `adjunct` — a non-theta position attaches without disturbing the
      color;
    * `move` — a movement landing site: the empty-tree marker attaches
      under a non-theta root. -/
inductive IsGen : List PolarizedRole → Color L → Color L → Prop
  | close (g₀ : List PolarizedRole) (ρE : ThetaRole) {a b : Color L}
      (ha : a.Matches [.down ρE]) (hb : b.Matches [.up ρE]) :
      IsGen g₀ a b
  | discharge (g : List ThetaRole) (ρ : ThetaRole) (hg : g ≠ [])
      (hchain : ((g ++ [ρ]).tail).IsChain hier) {a b : Color L}
      (ha : a.Matches [.down ρ]) (hb : b.Matches (upGrid (g ++ [ρ]))) :
      IsGen (upGrid g) a b
  | adjunct (g₀ : List PolarizedRole) : IsGen g₀ (.free g₀) .nontheta
  | move (c' : Color L) (hc' : c' ≠ .emptyTree) : IsGen [] c' .emptyTree

/-- A one-node colored operation. -/
def gen (c a b : Color L) : Bud.Tree (Color L) := .node c (.leaf a) (.leaf b)

/-- The rule set: the generator shapes in either orientation, rooted at a
    nonterminal color. -/
def rules : Set (Bud.Tree (Color L)) :=
  {t | ∃ g₀ a b, IsGen hier g₀ a b ∧
    (t = gen (.free g₀) a b ∨ t = gen (.free g₀) b a)}

/-- The complete theta bud system. -/
def system : Bud.System (Color L) := ⟨rules hier, {c | c.IsTerminal}⟩

variable {hier}

/-- The local conservation law: at every generator, either one child
    receives the last role of the other child's giver grid while the root
    keeps the residue, or the node is an adjunct attachment, or a movement
    landing under a non-theta root. -/
theorem IsGen.conservation {g₀ : List PolarizedRole} {a b : Color L}
    (h : IsGen (L := L) hier g₀ a b) :
    (∃ ρ g, a.Matches [.down ρ] ∧ b.Matches (upGrid g ++ [.up ρ]) ∧
      (g₀ = upGrid g ∨ g = [])) ∨
    (a = .free g₀ ∧ b = .nontheta) ∨
    (g₀ = [] ∧ b = .emptyTree) := by
  cases h with
  | close g₀ ρE ha hb => exact .inl ⟨ρE, [], ha, by simpa using hb, .inr rfl⟩
  | discharge g ρ hg hchain ha hb =>
    exact .inl ⟨ρ, g, ha, by simpa [upGrid] using hb, .inl rfl⟩
  | adjunct g₀ => exact .inr (.inl ⟨rfl, rfl⟩)
  | move c' hc' => exact .inr (.inr ⟨rfl, rfl⟩)

/-- The vertex-local law of the theta system: the vertex is a generator
    instance in some orientation. -/
def ThetaLocal (hier : ThetaRole → ThetaRole → Prop)
    (c a b : Color L) : Prop :=
  ∃ g₀, c = .free g₀ ∧ (IsGen hier g₀ a b ∨ IsGen hier g₀ b a)

theorem rules_nodeLocal {r : Bud.Tree (Color L)} (hr : r ∈ rules hier) :
    r.NodeLocal (ThetaLocal hier) := by
  obtain ⟨g₀, a, b, hg, hor⟩ := hr
  rcases hor with rfl | rfl
  · exact ⟨⟨g₀, rfl, .inl hg⟩, trivial, trivial⟩
  · exact ⟨⟨g₀, rfl, .inr hg⟩, trivial, trivial⟩

/-- Every vertex of every derivable structure is a generator instance:
    filtering by the coloring rules is checkable vertex-locally, the
    engine of [marcolli-larson-2025]'s recursive theta criterion. -/
theorem derives_thetaLocal {c : Color L} {x : Bud.Tree (Color L)}
    (h : (system (L := L) hier).Derives c x) :
    x.NodeLocal (ThetaLocal hier) :=
  h.nodeLocal fun _ hr => rules_nodeLocal hr

/-- Movement lands only in non-theta positions: a generator with an
    empty-tree input has the non-theta output. The External/Internal Merge
    dichotomy of theta theory, derived from the generator shapes. -/
theorem rules_emptyTree_out {r : Bud.Tree (Color L)} (hr : r ∈ rules hier)
    (h : Color.emptyTree ∈ r.inputs) : r.out = Color.nontheta := by
  obtain ⟨g₀, a, b, hg, hor⟩ := hr
  have hab : Color.emptyTree = a ∨ Color.emptyTree = b := by
    rcases hor with rfl | rfl <;>
      simpa [gen, or_comm] using h
  suffices hs : g₀ = [] by
    rcases hor with rfl | rfl <;> simp [gen, hs, Color.nontheta]
  cases hg with
  | close g₀' ρE ha hb =>
    rcases hab with rfl | rfl
    · exact absurd ha (Color.not_matches_emptyTree)
    · exact absurd hb (Color.not_matches_emptyTree)
  | discharge g ρ hg' hchain ha hb =>
    rcases hab with rfl | rfl
    · exact absurd ha (Color.not_matches_emptyTree)
    · exact absurd hb (Color.not_matches_emptyTree)
  | adjunct g₀' =>
    rcases hab with h' | h' <;> exact absurd h' (by simp [Color.nontheta])
  | move c' hc' =>
    rfl

end Rules

section Comb

variable {hier : ThetaRole → ThetaRole → Prop}

/-- The spine of a bare theta comb: the residue grid grows by one role per
    node on the path to the head leaf, which carries the complete grid. -/
def combSpine (g : List ThetaRole) : List ThetaRole → Bud.Tree (Color L)
  | [] => .leaf (.free (upGrid g))
  | ρ :: rest =>
      .node (.free (upGrid g)) (.leaf (.free [.down ρ]))
        (combSpine (g ++ [ρ]) rest)

/-- A bare theta comb ([marcolli-larson-2025]'s bare-system generators):
    an external role, hierarchy-ordered internal roles, one receiver per
    node, the full giver grid at the head leaf, and an arbitrary root
    recoloring. -/
def comb (g₀ : List PolarizedRole) (ρE : ThetaRole)
    (ρIs : List ThetaRole) : Bud.Tree (Color L) :=
  .node (.free g₀) (.leaf (.free [.down ρE])) (combSpine [ρE] ρIs)

theorem combSpine_derivable (g : List ThetaRole) (hg : g ≠ [])
    (rest : List ThetaRole)
    (hchain : ((g ++ rest).tail).IsChain hier) :
    (system (L := L) hier).Derives (.free (upGrid g)) (combSpine g rest) := by
  induction rest generalizing g with
  | nil => exact .unit (by simp [system, Color.IsTerminal])
  | cons ρ rest ih =>
    have hstep : ((g ++ [ρ]).tail).IsChain hier := by
      refine List.IsChain.prefix hchain ?_
      cases g with
      | nil => exact absurd rfl hg
      | cons a g' =>
        exact ⟨rest, by simp⟩
    have hrule : gen (.free (upGrid g)) (.free [.down ρ])
        (.free (upGrid (g ++ [ρ]))) ∈ rules (L := L) hier :=
      ⟨upGrid g, _, _,
        .discharge g ρ hg hstep (by simp) (by simp), .inl rfl⟩
    have hunit : (system (L := L) hier).Derives (.free (upGrid g))
        (.leaf (.free (upGrid g))) :=
      .unit (by simp [system, Color.IsTerminal])
    have hgen := hunit.graft 0 hrule (by simp [gen])
    have hgraft : (Bud.Tree.leaf ((Color.free (upGrid g) : Color L))).graft 0
        (gen (.free (upGrid g)) (.free [.down ρ])
          (.free (upGrid (g ++ [ρ])))) =
        gen (.free (upGrid g)) (.free [.down ρ])
          (.free (upGrid (g ++ [ρ]))) := rfl
    rw [hgraft] at hgen
    have hchain' : ((g ++ [ρ] ++ rest).tail).IsChain hier := by
      simpa [List.append_assoc] using hchain
    have hcomp := hgen.compose (i := 1) (by simp [gen])
      (by simp [gen]) (ih (g ++ [ρ]) (by simp) hchain')
    simpa [combSpine, gen, Bud.Tree.graft] using hcomp

/-- The bare theta combs are derivable in the complete system, provided
    the internal roles descend the hierarchy: the generator half of
    [marcolli-larson-2025]'s reduction of the bare system to the complete
    one. -/
theorem comb_derivable (g₀ : List PolarizedRole) (ρE : ThetaRole)
    (ρIs : List ThetaRole) (hchain : ρIs.IsChain hier) :
    (system (L := L) hier).Derives (.free g₀) (comb g₀ ρE ρIs) := by
  have hrule : gen (.free g₀) (.free [.down ρE]) (.free (upGrid [ρE]))
      ∈ rules (L := L) hier :=
    ⟨g₀, _, _, .close g₀ ρE (by simp) (by simp [upGrid]), .inl rfl⟩
  have hunit : (system (L := L) hier).Derives (.free g₀)
      (.leaf (.free g₀)) :=
    .unit (by simp [system, Color.IsTerminal])
  have hgen := hunit.graft 0 hrule (by simp [gen])
  have hgraft : (Bud.Tree.leaf ((Color.free g₀ : Color L))).graft 0
      (gen (.free g₀) (.free [.down ρE]) (.free (upGrid [ρE]))) =
      gen (.free g₀) (.free [.down ρE]) (.free (upGrid [ρE])) := rfl
  rw [hgraft] at hgen
  have hspine := combSpine_derivable (L := L) (hier := hier) [ρE]
    (by simp) ρIs (by simpa using hchain)
  have hcomp := hgen.compose (i := 1) (by simp [gen]) (by simp [gen]) hspine
  simpa [comb, gen, Bud.Tree.graft] using hcomp

end Comb

end Minimalist.Theta
