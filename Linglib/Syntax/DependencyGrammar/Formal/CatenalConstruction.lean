import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Syntax.DependencyGrammar.Formal.Catena

open Morphology (Word)

/-!
# Catenal Construction

The fundamental bridge type connecting Construction Grammar and Dependency
Grammar ([osborne-gross-2012]): a `CatenalCx` pairs a CxG `Construction`
(form–meaning description) with a DG catena witness (dependency tree plus a
set of node indices proven to form a catena).

## Main declarations

* `CatenalCx` — the bridge structure.
* `constituent_implies_catena` — every constituent is a catena, the
  containment establishing that catenae strictly generalise constituents.

## Implementation notes

Per-instance witnesses (specific idioms, LVCs, displacement constructions)
live in `Studies/OsborneGross2012/Data.lean`; their catena fields are
discharged by `decide` over the concrete tree.
-/

namespace DepGrammar.CatenalConstruction


open DepGrammar Catena ConstructionGrammar

/-! ### Core bridge type -/

/-- A tree word satisfies a slot filler — the lexicalized analogue of the
licensing layer's `SlotFiller.matches`, with POS read off the word itself.
A single word may realize a `phrasal` slot (it projects the phrase);
`semantic` constraints are not checkable at this level. -/
def _root_.ConstructionGrammar.SlotFiller.matchesWord :
    ConstructionGrammar.SlotFiller String → Word → Bool
  | .fixed lex, w => lex == w.form
  | .open_ cat, w => w.cat == cat
  | .headed lex _, w => lex == w.form
  | .semantic _, _ => true
  | .phrasal, _ => true

/-- A construction paired with a DG catena witness in some dependency tree.
The `realizes` field keeps the pairing honest: each catena node's word must
instantiate some slot of the construction's typed form, so a `CatenalCx`
cannot pair a construction with an unrelated tree. -/
structure CatenalCx where
  /-- CxG description of the construction. -/
  construction : Construction
  /-- A dependency tree instantiating the construction. -/
  tree : DepTree
  /-- Node indices that carry the construction. -/
  nodes : List Nat
  /-- The construction nodes form a catena. -/
  catena : isCatena tree.deps nodes = true
  /-- Every catena node's word instantiates some slot of the form. -/
  realizes : nodes.all (λ n => (tree.words[n]?).any
      (λ w => construction.form.any (·.filler.matchesWord w))) = true

/-! ### Constituent–catena containment -/

/-- Lift bidirectional reachability to a superset of allowed nodes. -/
private theorem bidir_lift {deps : List Dependency} {allowed allowed' : List Nat}
    {u v : Nat} (hsub : ∀ x, x ∈ allowed → x ∈ allowed')
    (h : BidirReachable deps allowed u v) :
    BidirReachable deps allowed' u v := by
  induction h with
  | here w hw => exact .here w (hsub w hw)
  | step a b _ ha hb hedge _ ih =>
    exact .step a b _ (hsub a ha) (hsub b hb) hedge ih

/-- If `Dominates deps root x`, then `x` is bidirectionally reachable from
`root` within `projection deps root`. -/
private theorem bidir_of_dominates (deps : List Dependency) (root x : Nat)
    (hdom : Dominates deps root x) :
    BidirReachable deps (projection deps root) root x := by
  induction hdom using Dominates.head_induction_on with
  | refl => exact .here x (root_mem_projection deps x)
  | @step v w hedge _ ih =>
    have hsubset : ∀ z, z ∈ projection deps w → z ∈ projection deps v := λ z hz =>
      mem_projection_of_dominates
        (Dominates.trans (Dominates.edge hedge) (dominates_of_mem_projection hz))
    have hv_mem := root_mem_projection deps v
    have hw_mem := child_mem_projection deps v w hedge
    have hedge' : ∃ d ∈ deps, (d.headIdx = v ∧ d.depIdx = w) ∨
                                (d.depIdx = v ∧ d.headIdx = w) := by
      obtain ⟨d, hd, h1, h2⟩ := hedge
      exact ⟨d, hd, Or.inl ⟨h1, h2⟩⟩
    exact .step v w _ hv_mem hw_mem hedge' (bidir_lift hsubset ih)

/-- Any two nodes in a projection are bidirectionally reachable via the root. -/
private theorem bidir_in_projection (deps : List Dependency) (root u v : Nat)
    (hu : u ∈ projection deps root) (hv : v ∈ projection deps root) :
    BidirReachable deps (projection deps root) u v :=
  bidir_trans
    (bidir_symm (bidir_of_dominates deps root u (dominates_of_mem_projection hu)))
    (bidir_of_dominates deps root v (dominates_of_mem_projection hv))

/-- **Constituent → Catena**: every constituent is a catena. Constituents are
complete subtrees (projections rooted at some node); the catena BFS traverses
edges bidirectionally, so any pair of constituent nodes is reachable via the
root. This is the containment behind {constituents} ⊂ {catenae} ⊂ {subsets}. -/
theorem constituent_implies_catena (deps : List Dependency) (n : Nat)
    (nodes : List Nat) (h : Catena.isConstituent deps n nodes = true) :
    isCatena deps nodes = true := by
  simp only [isConstituent] at h
  obtain ⟨root, _, hroot⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hroot
  obtain ⟨⟨hlen, hnodes_sub⟩, hsub_nodes⟩ := hroot
  have h_n2p : ∀ x, x ∈ nodes → x ∈ projection deps root := λ x hx =>
    List.mem_of_elem_eq_true (List.all_eq_true.mp hnodes_sub x hx)
  have h_p2n : ∀ x, x ∈ projection deps root → x ∈ nodes := λ x hx =>
    List.mem_of_elem_eq_true (List.all_eq_true.mp hsub_nodes x hx)
  have hne : nodes ≠ [] := by
    intro hemp
    have : (projection deps root).length = 0 := by
      rw [hemp] at hlen; simp at hlen; exact hlen.symm
    exact projection_nonempty deps root (List.eq_nil_of_length_eq_zero this)
  unfold isCatena
  have hnonempty : nodes.isEmpty = false := by cases nodes <;> simp_all
  simp only [hnonempty, Bool.not_false, Bool.true_and]
  unfold isConnected
  match hm : nodes, hne with
  | start :: rest, _ =>
    simp only [List.all_eq_true]
    intro x hx
    have hbidir : BidirReachable deps (start :: rest) start x :=
      bidir_lift h_p2n (bidir_in_projection deps root start x
        (h_n2p start List.mem_cons_self) (h_n2p x hx))
    exact List.elem_eq_true_of_mem (bfsReachable_complete deps _ start x hbidir)

end DepGrammar.CatenalConstruction
