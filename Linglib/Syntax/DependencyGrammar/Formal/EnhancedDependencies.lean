import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Enhanced dependencies

Basic dependency trees are single-headed, so predicate-argument relations
that hold semantically — shared dependents in coordination, controlled
subjects, relative-clause gaps — cannot all be tree arcs. The UD
*enhanced* representation adds them as extra arcs
([de-marneffe-nivre-2019]). On this carrier an enhanced graph is just a
`Graph n` with more arcs, so basic-below-enhanced is the `Digraph`
lattice order (`Graph.toDigraph_mono`).

`enhance` adds an explicit arc list to a graph; `hasUnrepresentedArg`
detects a word whose enhanced head is absent from the basic graph.
-/

namespace DependencyGrammar

variable {n : ℕ}

/-- Add arcs to a graph (first label wins where both are present). -/
def Graph.enhance (g : Graph n)
    (extra : List (Fin n × Fin n × UD.DepRel)) : Graph n :=
  { g with label := λ v w =>
      g.label v w <|> (extra.find? λ a => a.1 == v && a.2.1 == w).map (·.2.2) }

/-- Enhancement only adds arcs. -/
theorem Graph.adj_enhance (g : Graph n)
    (extra : List (Fin n × Fin n × UD.DepRel)) {v w : Fin n} (h : g.Adj v w) :
    (g.enhance extra).Adj v w := by
  simp only [Graph.Adj, enhance] at h ⊢
  cases hl : g.label v w with
  | none => exact absurd (hl ▸ h) (by simp)
  | some r => simp [hl]

/-- The basic graph sits below its enhancement in the `Digraph` lattice. -/
theorem Graph.toDigraph_le_enhance (g : Graph n)
    (extra : List (Fin n × Fin n × UD.DepRel)) :
    g.toDigraph ≤ (g.enhance extra).toDigraph :=
  Graph.toDigraph_mono (λ _ _ h => g.adj_enhance extra h)

/-- Position `w` has an argument relation in the enhanced graph that the
    basic graph fails to encode. -/
def HasUnrepresentedArg (basic enhanced : Graph n) (w : Fin n) : Prop :=
  ∃ v, enhanced.Adj v w ∧ ¬ basic.Adj v w

instance (b e : Graph n) (w : Fin n) : Decidable (HasUnrepresentedArg b e w) :=
  inferInstanceAs (Decidable (∃ _, _))

end DependencyGrammar
