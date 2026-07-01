/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Combinatorics.RootedTree.DecEq
import Linglib.Syntax.Minimalist.Defs

/-!
# The MCB-faithful syntactic-object carrier (skeleton)

[marcolli-chomsky-berwick-2025] §1.1. The single-carrier program
(`scratch/mcb-single-carrier-spec.md`) moves syntactic objects onto the **same**
`Nonplanar` carrier the Merge algebra already uses, exactly as the book intends
("syntactic objects… are the generators of the Hopf algebra", §1.2). This file is
P0's carrier skeleton: the well-formed subset of `Nonplanar (LIToken ⊕ Unit)`.

## Faithful labelling (§1.1.3.1: "no labels at any non-leaf vertices")

MCB's SO is a **binary, nonplanar** rooted tree with **leaves labelled by SO₀**
(lexical items + features) and **internal vertices bare** — the head is *not* on
the tree; it comes from a separate labelling algorithm (§1.15, the head function).
So on `Nonplanar (LIToken ⊕ Unit)` (the algebra's `α ⊕ β`, `β = Unit`), **role by arity**:

- a **lexical leaf** carries `Sum.inl tok` — a lexical item (`LIToken` ≈ SO₀);
- a **trace leaf** carries `Sum.inr ()` — bare (chain identity is workspace-level,
  MCB Def 1.2.1, not a per-leaf index; this replaces the legacy `⊕ Nat`);
- an **internal node** carries `Sum.inr ()` — **bare**, no head label (§1.15 supplies it).

`Sum.inr ()` is the single structural/bare marker; trace-leaf vs. internal is
childless vs. binary. `IsSO` pins this. This is the deliberate departure from the
legacy `toNonplanar` image, which decorated internal nodes with the head
(`Sum.inl headLeaf`) — that decoration is the head function applied, not the object.

## Scope

The carrier + `IsSO` + decidability + the `SO` subtype, with the faithful three-role
alphabet (lexical/trace leaves + bare internals). **Out of scope (later phases):**
workspaces + Merge on the carrier (EM + IM-via-coproduct, MCB Prop 1.4.2 — uses the
existing `comul{D,C}N`; P1 continued), the structural ops (`contains`/`subtrees` =
`Acc'`) + flip `SyntacticObject := SO` (P2), the head function + Phase API re-home
(P3), retiring `FreeCommMagma`/`toNonplanar` (P4). See `scratch/p1-spec-and-audit.md`.
-/

namespace Minimalist

open RootedTree

/-- The SO label alphabet, in the algebra's `α ⊕ β` form (`α = LIToken` lexical,
    `β = Unit` bare). Each **role is fixed by arity**, not by a third label:

    - `Sum.inl tok` on a **leaf** — a lexical item (`LIToken` ≈ SO₀);
    - `Sum.inr ()` on a **leaf** — a **trace** (bare; chain identity is workspace-level,
      MCB Def 1.2.1, not a per-leaf index — this replaces the legacy `⊕ Nat`);
    - `Sum.inr ()` on an **internal** node — **bare** (no head; §1.15 supplies it).

    `Sum.inr ()` is the single "structural/bare" marker; a trace and an internal
    vertex are the childless vs. binary occurrences of it. This is exactly the
    `Nonplanar (α ⊕ β)` (β = `Unit`) alphabet the existing `τ`-parameterised trace
    coproducts (`comul{D,C}N`) already speak. -/
abbrev SOLabel : Type := LIToken ⊕ Unit

/-! ### Well-formedness `IsSO` (binary, lexical/trace leaves, bare internals) -/

mutual
/-- Structural well-formedness of a *planar* syntactic object: a lexical node must
    be a leaf; a bare (`inr ()`) node is either a **trace leaf** (childless) or a
    **binary internal** node with well-formed children. Permutation-friendly so it
    lifts to the nonplanar quotient. -/
def isSOPlanar : Tree SOLabel → Bool
  | .node (.inl _) cs  => cs.isEmpty
  | .node (.inr ()) cs => (cs.length == 0 || cs.length == 2) && isSOPlanarList cs
/-- Auxiliary: all children well-formed. -/
def isSOPlanarList : List (Tree SOLabel) → Bool
  | []      => true
  | c :: cs => isSOPlanar c && isSOPlanarList cs
end

/-! ### `isSOPlanar` is `PermEquiv`-invariant (so it lifts) -/

/-- `isSOPlanarList` is a conjunction over children, hence permutation-invariant. -/
private theorem isSOPlanarList_perm (cs ds : List (Tree SOLabel)) (h : cs.Perm ds) :
    isSOPlanarList cs = isSOPlanarList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [isSOPlanarList]; rw [ih]
  | swap _ _ _ => simp only [isSOPlanarList, Bool.and_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Replacing one child by an `isSOPlanar`-equal child preserves `isSOPlanarList`. -/
private theorem isSOPlanarList_replace (pre post : List (Tree SOLabel))
    {old new : Tree SOLabel} (h : isSOPlanar old = isSOPlanar new) :
    isSOPlanarList (pre ++ old :: post) = isSOPlanarList (pre ++ new :: post) := by
  induction pre with
  | nil => simp only [List.nil_append, isSOPlanarList]; rw [h]
  | cons hd tl ih => simp only [List.cons_append, isSOPlanarList]; rw [ih]

private theorem isSOPlanar_permStep {t s : Tree SOLabel} (h : Tree.PermStep t s) :
    isSOPlanar t = isSOPlanar s := by
  induction h with
  | swapAtRoot =>
    rename_i a l r pre post
    cases a with
    | inl _ => simp only [isSOPlanar]; cases pre <;> simp [List.isEmpty_cons]
    | inr u => cases u
               simp only [isSOPlanar, List.length_append, List.length_cons,
                 isSOPlanarList_perm _ _ (List.Perm.append_left pre (.swap r l post))]
  | recurse _ ih =>
    rename_i a pre old new post _hstep
    cases a with
    | inl _ => simp only [isSOPlanar]; cases pre <;> simp [List.isEmpty_cons]
    | inr u => cases u
               simp only [isSOPlanar, List.length_append, List.length_cons,
                 isSOPlanarList_replace pre post ih]

/-- `isSOPlanar` is invariant under `PermEquiv`, hence descends to the quotient. -/
theorem isSOPlanar_permEquiv {t s : Tree SOLabel} (h : Tree.PermEquiv t s) :
    isSOPlanar t = isSOPlanar s := by
  induction h with
  | rel _ _ hstep => exact isSOPlanar_permStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### The carrier: `IsSO` on `Nonplanar` + the `SO` subtype -/

/-- Well-formed-SO check on the nonplanar carrier, lifted from `isSOPlanar`. -/
def isSO : Nonplanar SOLabel → Bool :=
  Nonplanar.lift isSOPlanar (fun _ _ h => isSOPlanar_permEquiv h)

@[simp] theorem isSO_mk (t : Tree SOLabel) : isSO (Nonplanar.mk t) = isSOPlanar t := rfl

/-- A tree on the carrier is a **syntactic object** ([marcolli-chomsky-berwick-2025]
    §1.1): binary, nonplanar; leaves are lexical (`Sum.inl tok`) or traces
    (`Sum.inr ()`), internal vertices bare (`Sum.inr ()`). Decidable (and
    `decide`-able, via `Core/…/DecEq`). -/
def IsSO (t : Nonplanar SOLabel) : Prop := isSO t = true

instance : DecidablePred IsSO := fun t => inferInstanceAs (Decidable (isSO t = true))

/-- The MCB-faithful **syntactic object** carrier: well-formed nonplanar trees over
    `SOLabel`. This is the target type that will become `SyntacticObject` once the
    operations (P2) and the head function / Phase API (P3) are ported onto it. -/
def SO : Type := { t : Nonplanar SOLabel // IsSO t }

instance : DecidableEq SO := Subtype.instDecidableEq

/-! ### Smart constructors: leaves and the bare binary node

The three faithful shapes (§1.1.3.1): a **lexical leaf** (`Sum.inl tok`), a
**trace leaf** (bare `Sum.inr ()`, index-free — chain identity is workspace-level,
MCB Def 1.2.1), and a **bare binary node** (`Sum.inr ()`, internal). `SO.node` is the
structural binary constructor; `Workspace.lean`'s `SO.merge`/`SO.intMerge` are its
Merge semantics. -/

/-- A **lexical leaf**: a childless `Sum.inl tok` (an SO₀ item). -/
def SO.lexLeaf (tok : LIToken) : SO := ⟨Nonplanar.leaf (Sum.inl tok), rfl⟩

/-- The **trace leaf**: a childless, **bare** `Sum.inr ()` vertex
    ([marcolli-chomsky-berwick-2025] Def 1.2.7's ρ-vertex), index-free. -/
def SO.traceLeaf : SO := ⟨Nonplanar.leaf (Sum.inr ()), by decide⟩

/-- `isSO` of a bare binary node is the conjunction of `isSO` on the two children:
    `Sum.inr ()` at arity 2 is well-formed exactly when both daughters are.
    `Quotient.inductionOn₂` reduces the smart `node` to a tree `.node` via
    `node_mk_tree_list`, then unfolds `isSOPlanar`'s binary arm. -/
theorem isSO_node_pair (a b : Nonplanar SOLabel) :
    isSO (Nonplanar.node (Sum.inr ()) ({a, b} : Multiset (Nonplanar SOLabel)))
      = (isSO a && isSO b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show isSO (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = (isSO (Nonplanar.mk pa) && isSO (Nonplanar.mk pb))
  rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]
  simp only [isSO_mk, isSOPlanar, isSOPlanarList, List.length_cons, List.length_nil,
             Nat.reduceAdd, Nat.reduceBEq, Bool.or_true, Bool.true_and, Bool.and_true]

/-- The **bare binary node** ([marcolli-chomsky-berwick-2025] §1.1.3.1): the
    well-formed internal vertex over two syntactic objects, with no head label.
    Noncomputable (it uses the smart `Nonplanar.node`); build concrete results via
    `node_mk` + `decide`. -/
noncomputable def SO.node (l r : SO) : SO :=
  ⟨Nonplanar.node (Sum.inr ()) {l.val, r.val}, by
    show isSO (Nonplanar.node (Sum.inr ()) {l.val, r.val}) = true
    have hl : isSO l.val = true := l.2
    have hr : isSO r.val = true := r.2
    rw [isSO_node_pair, hl, hr, Bool.and_self]⟩

@[simp] theorem SO.node_val (l r : SO) :
    (SO.node l r).val = Nonplanar.node (Sum.inr ()) {l.val, r.val} := rfl

/-- **Construction bridge**: a `node` of two `mk`-built objects is the single `Tree`
    binary node `mk (.node (inr ()) [pl, pr])` — built *without* the smart `node`'s
    `Quotient.out`, so concrete results are `decide`-able. -/
theorem SO.node_mk (pl pr : Tree SOLabel)
    (hl : IsSO (Nonplanar.mk pl)) (hr : IsSO (Nonplanar.mk pr)) :
    (SO.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩).val
      = Nonplanar.mk (.node (Sum.inr ()) [pl, pr]) := by
  rw [SO.node_val,
      show ({Nonplanar.mk pl, Nonplanar.mk pr} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([pl, pr].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]

/-! ### Induction and case analysis -/

/-- Every member of an `isSOPlanarList`-true list is itself `isSOPlanar`: the
    children of a well-formed node are well-formed. -/
theorem isSOPlanar_of_mem {cs : List (Tree SOLabel)} (h : isSOPlanarList cs = true) :
    ∀ c ∈ cs, isSOPlanar c = true := by
  induction cs with
  | nil => intro _ hc; exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    rw [isSOPlanarList, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact h.1
    · exact ih h.2 c hmem

/-- **Induction on syntactic objects** ([marcolli-chomsky-berwick-2025] §1.1.3.1).
    Every `SO` is a lexical leaf, the (bare) trace leaf, or a bare binary node of two
    syntactic objects — the faithful analogue of the legacy `SyntacticObject.ind`
    (leaf/trace/mul), with the `mul` case the bare `SO.node`. Proved by strong
    induction on the node count (`numNodes`; the two daughters of a binary node are
    strictly smaller). -/
@[elab_as_elim]
theorem SO.ind {motive : SO → Prop}
    (lex : ∀ tok, motive (SO.lexLeaf tok))
    (trace : motive SO.traceLeaf)
    (node : ∀ l r : SO, motive l → motive r → motive (SO.node l r))
    (s : SO) : motive s := by
  suffices H : ∀ n (p : Tree SOLabel) (hp : IsSO (Nonplanar.mk p)),
      p.numNodes = n → motive ⟨Nonplanar.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t => ∀ (ht : IsSO t), motive ⟨t, ht⟩)
      t (fun p ht => H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    have hpl : isSOPlanar (Tree.node lbl cs) = true := hp
    cases lbl with
    | inl tok =>
      rw [isSOPlanar] at hpl
      rcases cs with _ | ⟨c, cs'⟩
      · exact lex tok
      · simp at hpl
    | inr u =>
      cases u
      rw [isSOPlanar, Bool.and_eq_true] at hpl
      obtain ⟨hlen, hlist⟩ := hpl
      rcases cs with _ | ⟨pl, _ | ⟨pr, _ | ⟨x, rest⟩⟩⟩
      · exact trace
      · simp at hlen
      · have hl : isSOPlanar pl = true := isSOPlanar_of_mem hlist pl (by simp)
        have hr : isSOPlanar pr = true := isSOPlanar_of_mem hlist pr (by simp)
        have hnode : (⟨Nonplanar.mk (Tree.node (Sum.inr ()) [pl, pr]), hp⟩ : SO)
            = SO.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩ :=
          Subtype.ext (SO.node_mk pl pr hl hr).symm
        rw [hnode]
        simp only [Tree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hw
        exact node _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)
      · simp at hlen

/-- **Case analysis** ([marcolli-chomsky-berwick-2025] §1.1.3.1): every syntactic
    object is a lexical leaf, the bare trace leaf, or a bare binary node. -/
theorem SO.exists_form (s : SO) :
    (∃ tok, s = SO.lexLeaf tok) ∨ s = SO.traceLeaf ∨ (∃ l r, s = SO.node l r) := by
  induction s using SO.ind with
  | lex tok => exact Or.inl ⟨tok, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | node l r _ _ => exact Or.inr (Or.inr ⟨l, r, rfl⟩)

/-! ### The `SyntacticObject` carrier

`SyntacticObject` is the linguistic-facing name for the MCB-faithful `SO` carrier
([marcolli-chomsky-berwick-2025] §1.1.3.1: binary, nonplanar, rooted trees with
bare internal vertices). It is a reducible abbreviation, so dot-notation on a value
`s : SyntacticObject` dispatches to the `SO.*` API for free. The former
`FreeCommMagma (LIToken ⊕ Nat)` carrier (with head-decorated nodes and `⊕ Nat`
trace indices) has been retired in favour of this one. -/
abbrev SyntacticObject : Type := SO

end Minimalist
