import Linglib.Syntax.Minimalist.Defs

/-!
# Syntactic Object containment and subterm theory
[chomsky-2013] [marcolli-chomsky-berwick-2025]

Containment, subterm enumeration, terminal-node extraction, and Barker–Pullum
command relations over the `SyntacticObject` carrier defined in
`Minimalist.Defs` (imported and re-exported here, so importers of `Basic`
still see the full carrier API).

## Containment Relations

- **Immediate Containment**: X immediately contains Y iff Y is a member of X
- **Containment (Dominance)**: Transitive closure of immediate containment
- **C-command**: Standard asymmetric relation for binding and locality
-/

namespace Minimalist

-- ============================================================================
-- Subterm Enumeration
-- ============================================================================

/-! ### Subtree enumeration — `Multiset` (MCB-faithful)

Two operators, distinguished by whether the root is included:

- **`subtrees : SO → Multiset SO`** — *all* subtrees including the root.
  Useful for membership tests like "is `x` an internal node of `s`".
- **`Acc : SO → Multiset SO`** — accessible-terms-only (excludes the
  root). This is MCB's `Acc(T)` from Def 1.2.2 (book p. 28). Eq (1.2.5)
  `#V(F) = b₀(F) + #Acc(F)` only holds for the proper-accessible-terms
  version. Internal vertices (`V_int(T)`) by MCB's definition exclude
  the root.

Both are `Multiset`-valued (multiplicity-preserving) because MCB §1.6/§1.7
counting and the pre-Lie matching coefficient `c^T_{T_1,T_2}` (book p. 79)
require multiplicities. For linglib's typical use (distinct-`LIToken.id`
leaves), each subtree is a distinct value, so Multiset and Finset coincide
extensionally — but the substrate commits to Multiset for faithfulness.

Multiset addition (`+`) preserves multiplicity (additive union); cons
(`::ₘ`) adds an element regardless of presence. -/

private def subtreesAux : FreeMagma (LIToken ⊕ Nat) → Multiset SyntacticObject
  | a@(.of _) => {FreeCommMagma.mk a}
  | a@(.mul l r) =>
    (FreeCommMagma.mk a) ::ₘ (subtreesAux l + subtreesAux r)

private theorem subtreesAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : subtreesAux a = subtreesAux b := by
  induction h with
  | swap a b =>
    show (FreeCommMagma.mk (a * b)) ::ₘ (subtreesAux a + subtreesAux b)
       = (FreeCommMagma.mk (b * a)) ::ₘ (subtreesAux b + subtreesAux a)
    rw [FreeCommMagma.swap a b, add_comm]
  | @mul_left a b h_inner c ih =>
    show (FreeCommMagma.mk (a * c)) ::ₘ (subtreesAux a + subtreesAux c)
       = (FreeCommMagma.mk (b * c)) ::ₘ (subtreesAux b + subtreesAux c)
    rw [FreeCommMagma.sound (.mul_left h_inner _), ih]
  | @mul_right a b c h_inner ih =>
    show (FreeCommMagma.mk (a * b)) ::ₘ (subtreesAux a + subtreesAux b)
       = (FreeCommMagma.mk (a * c)) ::ₘ (subtreesAux a + subtreesAux c)
    rw [FreeCommMagma.sound (.mul_right _ h_inner), ih]

/-- All subtrees of a `SyntacticObject`, including the root itself.
    Returns a `Multiset` (multiplicity-preserving). For the MCB
    accessible-terms operator that excludes the root, see `Acc` below.
    Computable via `FreeCommMagma.lift` from a swap-respecting helper. -/
def SyntacticObject.subtrees : SyntacticObject → Multiset SyntacticObject :=
  FreeCommMagma.lift subtreesAux subtreesAux_respects

@[simp] theorem SyntacticObject.subtrees_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).subtrees = {SyntacticObject.leaf tok} := rfl

@[simp] theorem SyntacticObject.subtrees_trace (n : Nat) :
    (SyntacticObject.trace n).subtrees = {SyntacticObject.trace n} := rfl

@[simp] theorem SyntacticObject.subtrees_mul (l r : SyntacticObject) :
    (l * r).subtrees = (l * r) ::ₘ (l.subtrees + r.subtrees) := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-- MCB's accessible-terms operator `Acc(T)` (Def 1.2.2, book p. 28):
    the multiset of all proper subtrees of `T`, excluding the root.
    Defined as `subtrees - {self}` (Multiset difference subtracts one
    occurrence). This is the operator that satisfies the MCB
    vertex-counting identity `#V(F) = b₀(F) + #Acc(F)` (eq. 1.2.5). -/
def SyntacticObject.Acc (so : SyntacticObject) : Multiset SyntacticObject :=
  so.subtrees - {so}

@[simp] theorem SyntacticObject.Acc_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).Acc = 0 := by
  show ({SyntacticObject.leaf tok} : Multiset _) - {SyntacticObject.leaf tok} = 0
  simp

@[simp] theorem SyntacticObject.Acc_trace (n : Nat) :
    (SyntacticObject.trace n).Acc = 0 := by
  show ({SyntacticObject.trace n} : Multiset _) - {SyntacticObject.trace n} = 0
  simp

/-! ### Terminal nodes — planar `List`

`terminalNodesPlanar` enumerates the leaf-position subterms of a planar
`FreeMagma` representative, left-to-right. The selection-induced order is
recovered downstream by `HeadFunction.terminalNodes` (`leftSpine`/`rightSpine`),
computably and with no `Quot.out`. -/

/-- Underlying terminal-node enumeration on a planar `FreeMagma`
    representative. Public so `HeadFunction.terminalNodesWith` can compose
    it with a chosen `externalize` section. -/
def terminalNodesPlanar : FreeMagma (LIToken ⊕ Nat) →
    List (FreeMagma (LIToken ⊕ Nat))
  | a@(.of _) => [a]
  | .mul l r => terminalNodesPlanar l ++ terminalNodesPlanar r

/-- The root is always in its own subtrees. -/
theorem self_mem_subtrees (so : SyntacticObject) : so ∈ so.subtrees := by
  induction so with
  | leaf _ => simp
  | trace _ => simp
  | mul l r _ _ => simp [SyntacticObject.subtrees_mul]

/-- `subtrees` is downward-monotone along the subtree relation: if `t`
    is a subtree of `s` (at any multiplicity), then every subtree of
    `t` is also a subtree of `s` (`Multiset.Subset` ignores
    multiplicity, only membership). -/
theorem subtrees_subset_of_mem {t s : SyntacticObject}
    (h : t ∈ s.subtrees) : t.subtrees ⊆ s.subtrees := by
  induction s with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at h
    rw [h]; exact Multiset.Subset.refl _
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at h
    rw [h]; exact Multiset.Subset.refl _
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at h
    rcases h with rfl | hl | hr
    · intro _ h; exact h
    · intro x hx
      have := ihl hl hx
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inl this)
    · intro x hx
      have := ihr hr hx
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inr this)

-- ============================================================================
-- Containment Relations
-- ============================================================================

-- Part 1: Immediate Containment (Definition 13)

/-- X immediately contains Y iff Y is a member of X.

    "X immediately contains Y iff X = {Y, Z} for some SO Z" — since SOs
    are unordered binary sets (`l * r = r * l`), this means Y is one of
    the two immediate daughters of X.

    Defined via lift over a swap-respecting helper on `FreeMagma`. -/
private def immediatelyContainsAux (y : SyntacticObject) :
    FreeMagma (LIToken ⊕ Nat) → Prop
  | .of _ => False
  | .mul a b => y = (Quot.mk _ a : SyntacticObject) ∨ y = (Quot.mk _ b : SyntacticObject)

private theorem immediatelyContainsAux_respects (y : SyntacticObject)
    (a b : FreeMagma (LIToken ⊕ Nat)) (h : FreeMagma.CommRel a b) :
    immediatelyContainsAux y a = immediatelyContainsAux y b := by
  induction h with
  | swap a b => simp only [immediatelyContainsAux]; exact propext (Or.comm)
  | mul_left h_inner _ ih =>
    simp only [immediatelyContainsAux]
    have : (Quot.mk _ _ : SyntacticObject) = Quot.mk _ _ := Quot.sound h_inner
    rw [this]
  | mul_right _ h_inner ih =>
    simp only [immediatelyContainsAux]
    have : (Quot.mk _ _ : SyntacticObject) = Quot.mk _ _ := Quot.sound h_inner
    rw [this]

def immediatelyContains (x y : SyntacticObject) : Prop :=
  FreeCommMagma.lift (immediatelyContainsAux y)
    (immediatelyContainsAux_respects y) x

@[simp] theorem immediatelyContains_leaf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (.leaf tok) y := id

@[simp] theorem immediatelyContains_trace (n : Nat) (y : SyntacticObject) :
    ¬ immediatelyContains (.trace n) y := id

@[simp] theorem immediatelyContains_mul (l r y : SyntacticObject) :
    immediatelyContains (l * r) y ↔ y = l ∨ y = r := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

/-- Decidable immediate containment. Recurses via `Quot.recOnSubsingleton`
    on the underlying `FreeMagma` representative. -/
instance decImmediatelyContains (x y : SyntacticObject) :
    Decidable (immediatelyContains x y) :=
  Quot.recOnSubsingleton (motive := fun x => Decidable (immediatelyContains x y))
    x fun fm =>
      match fm with
      | .of _ => isFalse id
      | .mul _ _ => inferInstanceAs (Decidable (_ ∨ _))

-- Part 2: Containment / Dominance (Definition 14)

/-- Containment is the transitive closure of immediate containment

    "X contains Y iff X immediately contains Y or
    X immediately contains some SO Z such that Z contains Y"

    This is standard syntactic dominance. -/
inductive contains : SyntacticObject → SyntacticObject → Prop where
  | imm : ∀ x y, immediatelyContains x y → contains x y
  | trans : ∀ x y z, immediatelyContains x z → contains z y → contains x y

-- Part 3: Properties of Containment

/-- Immediate containment implies containment -/
theorem imm_implies_contains {x y : SyntacticObject}
    (h : immediatelyContains x y) : contains x y :=
  contains.imm x y h

/-- Containment is transitive -/
theorem contains_trans {x y z : SyntacticObject}
    (hxy : contains x y) (hyz : contains y z) : contains x z := by
  induction hxy with
  | imm x y himm =>
    exact contains.trans x z y himm hyz
  | trans x y w himm _ ih =>
    exact contains.trans x z w himm (ih hyz)

/-- Leaves contain nothing -/
theorem leaf_contains_nothing (tok : LIToken) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.leaf tok) y) := by
  intro h
  cases h with
  | imm _ _ himm => exact immediatelyContains_leaf _ _ himm
  | trans _ _ z himm _ => exact immediatelyContains_leaf _ _ himm

/-- Trace markers contain nothing. -/
theorem trace_contains_nothing (n : Nat) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.trace n) y) := by
  intro h
  cases h with
  | imm _ _ himm => exact immediatelyContains_trace _ _ himm
  | trans _ _ z himm _ => exact immediatelyContains_trace _ _ himm

-- Part 3b: Well-Foundedness via nodeCount

/-- Immediate containment strictly decreases nodeCount -/
theorem immediatelyContains_lt_nodeCount {x y : SyntacticObject}
    (h : immediatelyContains x y) : y.nodeCount < x.nodeCount := by
  induction x with
  | leaf _ => exact (immediatelyContains_leaf _ _ h).elim
  | trace _ => exact (immediatelyContains_trace _ _ h).elim
  | mul a b iha ihb =>
    rw [immediatelyContains_mul] at h
    simp only [SyntacticObject.nodeCount_mul]
    rcases h with rfl | rfl
    · omega
    · omega

/-- Containment strictly decreases nodeCount -/
theorem contains_lt_nodeCount {x y : SyntacticObject}
    (h : contains x y) : y.nodeCount < x.nodeCount := by
  induction h with
  | imm x y himm =>
    exact immediatelyContains_lt_nodeCount himm
  | trans x y z himm _ ih =>
    have h1 := immediatelyContains_lt_nodeCount himm
    omega

/-- No element contains itself (containment is irreflexive) -/
theorem contains_irrefl (x : SyntacticObject) : ¬contains x x := by
  intro h
  have hlt := contains_lt_nodeCount h
  exact Nat.lt_irrefl _ hlt

-- Part 3c: Decidability of containment

/-- `Quot.mk` distributes over the underlying `FreeMagma` multiplication
    (definitionally, since `FreeCommMagma.mul` is `Quot.lift₂` over
    `FreeMagma.mul`). -/
private theorem mk_mul (a b : FreeMagma (LIToken ⊕ Nat)) :
    (Quot.mk _ (a * b) : SyntacticObject)
      = FreeCommMagma.mul (Quot.mk _ a) (Quot.mk _ b) := rfl

/-- Helper: decide `contains (Quot.mk _ fm) y` by structural recursion on
    the underlying `FreeMagma` representative. -/
private def decContainsAux (y : SyntacticObject) :
    (fm : FreeMagma (LIToken ⊕ Nat)) → Decidable (contains (Quot.mk _ fm) y)
  | .of (.inl tok) => isFalse (leaf_contains_nothing tok y)
  | .of (.inr n) => isFalse (trace_contains_nothing n y)
  | .mul a b =>
    let qa : SyntacticObject := Quot.mk _ a
    let qb : SyntacticObject := Quot.mk _ b
    have ha' : Decidable (contains qa y) := decContainsAux y a
    have hb' : Decidable (contains qb y) := decContainsAux y b
    have hd : Decidable (contains (qa * qb) y) :=
      decidable_of_iff
        (qa = y ∨ qb = y ∨ contains qa y ∨ contains qb y) <| by
        constructor
        · rintro (rfl | rfl | hca | hcb)
          · exact contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl))
          · exact contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl))
          · exact contains.trans _ _ _
              ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)) hca
          · exact contains.trans _ _ _
              ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)) hcb
        · intro h
          cases h with
          | imm _ _ himm =>
              rw [immediatelyContains_mul] at himm
              rcases himm with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
          | trans _ _ z himm hcz =>
              rw [immediatelyContains_mul] at himm
              rcases himm with rfl | rfl
              · exact Or.inr (Or.inr (Or.inl hcz))
              · exact Or.inr (Or.inr (Or.inr hcz))
    -- Quot.mk _ (a * b) and qa * qb are defeq
    hd

/-- Containment is decidable by structural recursion on the containing SO's
    underlying `FreeMagma` representative (via `Quot.recOnSubsingleton` —
    `Decidable p` is a subsingleton up to propositional equality). -/
instance decContains (x y : SyntacticObject) : Decidable (contains x y) :=
  Quot.recOnSubsingleton (motive := fun x => Decidable (contains x y))
    x (fun a => decContainsAux y a)

-- Part 4: Membership in Derivation

/-- X is a term of Y iff X = Y or Y contains X

    "X is a term of SO Y iff X = Y or Y contains X"

    This is useful for stating when an element is "somewhere in" a structure -/
def isTermOf (x y : SyntacticObject) : Prop :=
  x = y ∨ contains y x

/-- Every SO is a term of itself -/
theorem self_is_term (x : SyntacticObject) : isTermOf x x :=
  Or.inl rfl

/-- If Y contains X, then X is a term of Y -/
theorem contained_is_term {x y : SyntacticObject} (h : contains y x) : isTermOf x y :=
  Or.inr h

instance decIsTermOf (x y : SyntacticObject) : Decidable (isTermOf x y) := by
  unfold isTermOf; infer_instance

-- Part 5: Root and Reflexive Containment

/-- Reflexive containment (useful for stating constraints) -/
def containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ contains x y

instance decContainsOrEq (x y : SyntacticObject) : Decidable (containsOrEq x y) := by
  unfold containsOrEq; infer_instance

/-- Every SO reflexively contains itself -/
theorem refl_containsOrEq (x : SyntacticObject) : containsOrEq x x :=
  Or.inl rfl

/-- Reflexive containment is transitive -/
theorem containsOrEq_trans {x y z : SyntacticObject}
    (hxy : containsOrEq x y) (hyz : containsOrEq y z) : containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (contains_trans hxy hyz)

-- Part 6: Tree-Relative Relations
--
-- The tree-free `areSisters` / `cCommands` definitions that were here
-- previously are unsound: sisterhood holds for ANY pair of distinct SOs
-- (witness: `node x y`), making asymmetric c-command trivially false.
-- The tree-relative versions below restrict witnesses to subtrees of a
-- given root, correctly capturing structural asymmetries.

/-! ### Subtree-Finset ↔ containment bridge

These theorems relate `subtrees : SO → Finset SO` to the propositional
`contains`/`containsOrEq` relations. With `subtrees` Finset-typed
(order-blind, computable), the bridges are provable by induction —
no `Quot.out` oracle dependence. -/

/-- Children of any subtree of `root` are themselves subtrees of `root`. -/
theorem mem_subtrees_of_imm_contains {root w z : SyntacticObject}
    (hw : w ∈ root.subtrees) (hwz : immediatelyContains w z) :
    z ∈ root.subtrees := by
  induction root with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at hw
    rw [hw] at hwz
    exact (immediatelyContains_leaf _ _ hwz).elim
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at hw
    rw [hw] at hwz
    exact (immediatelyContains_trace _ _ hwz).elim
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at hw
    rcases hw with rfl | hl | hr
    · -- w = l * r; immediatelyContains (l*r) z means z = l ∨ z = r
      rw [immediatelyContains_mul] at hwz
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      rcases hwz with rfl | rfl
      · exact Or.inr (Or.inl (self_mem_subtrees _))
      · exact Or.inr (Or.inr (self_mem_subtrees _))
    · simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inl (ihl hl))
    · simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inr (ihr hr))

/-- Containment implies subtree-Finset membership. -/
theorem mem_subtrees_of_contains {y z : SyntacticObject}
    (h : contains y z) : z ∈ y.subtrees := by
  induction h with
  | imm x y himm =>
    exact mem_subtrees_of_imm_contains (self_mem_subtrees _) himm
  | trans x y w himm hcwy ih =>
    -- ih : y ∈ w.subtrees; himm : immediatelyContains x w
    -- so w ∈ x.subtrees by mem_subtrees_of_imm_contains
    -- then w.subtrees ⊆ x.subtrees by subtrees_subset_of_mem
    -- so y ∈ x.subtrees
    exact subtrees_subset_of_mem
      (mem_subtrees_of_imm_contains (self_mem_subtrees _) himm) ih

/-- Subtree-Multiset membership implies term-of relation. -/
theorem isTermOf_of_mem_subtrees {y z : SyntacticObject}
    (h : z ∈ y.subtrees) : isTermOf z y := by
  induction y with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at h
    exact Or.inl h
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at h
    exact Or.inl h
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at h
    rcases h with rfl | hl | hr
    · exact Or.inl rfl
    · -- z ∈ l.subtrees → isTermOf z l → contains (l*r) z (via l)
      rcases ihl hl with rfl | hcontains
      · exact Or.inr (contains.imm _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)))
      · exact Or.inr (contains.trans _ _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)) hcontains)
    · -- symmetric on right
      rcases ihr hr with rfl | hcontains
      · exact Or.inr (contains.imm _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)))
      · exact Or.inr (contains.trans _ _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)) hcontains)

/-- `isTermOf z y` iff `z` is in `y.subtrees`. The bridge between the
    propositional term-of relation and the Finset-typed enumeration. -/
theorem isTermOf_iff_mem_subtrees (y z : SyntacticObject) :
    isTermOf z y ↔ z ∈ y.subtrees := by
  refine ⟨fun h => ?_, isTermOf_of_mem_subtrees⟩
  rcases h with rfl | hcontains
  · exact self_mem_subtrees _
  · exact mem_subtrees_of_contains hcontains

/-- X and Y are sisters IN tree `root`: they are distinct co-daughters of
    some node that is a subtree of `root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

instance decAreSistersIn (root x y : SyntacticObject) :
    Decidable (areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

/-- X c-commands Y IN tree `root`: X has a sister (in `root`) that
    contains-or-equals Y. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, areSistersIn root x z ∧ containsOrEq z y

/-- `cCommandsIn` is decidable: bounded existential over `root.subtrees`
    (Multiset). Computable since `subtrees` is. -/
instance decCCommandsIn (root x y : SyntacticObject) :
    Decidable (cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- X asymmetrically c-commands Y in tree `root`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬cCommandsIn root y x

instance decAsymCCommandsIn (root x y : SyntacticObject) :
    Decidable (asymCCommandsIn root x y) := by
  unfold asymCCommandsIn; infer_instance

/-! ## Note on Barker-Pullum command relations

An earlier draft of this file recast `cCommandsIn` as B&P c-command
(`Core.Order.commandRelation` over `FreeMagma.toTree`'s tree-order),
aiming to inherit B&P's antitonicity / intersection theorems "for
free" in the same lattice as HPSG `o-command` and DG `d-command`.

That recast does not work: B&P's `commandRelation` is universal
("every branching ancestor of α also dominates β") and admits pairs
that sister-form c-command excludes — e.g., on tree `(a, (b, c))`,
the leaf `a` B&P-commands itself and the root, since the only
branching strict ancestor is the root, which trivially dominates
everything. Reinhart c-command is sister-form (∃ sister of α
containing β); the two relations are not biconditionally equivalent
on `FreeMagma`.

The mathlib-style resolution: keep `cCommandsIn` value-side and
sister-form (it's what binding consumers need, and it reads directly
off bare phrase structure per [marcolli-chomsky-berwick-2025]).
Cross-tradition unification via B&P's parametric command lives in
`Core/Order/Command.lean` and is exercised by HPSG / DG, where its
universal shape matches the native primitive. Minimalism's c-command
does not reduce to it, so no bridge belongs here. -/

/-- The B&P branching-node positions of the bare tree `a * (b * c)`
    (the `FreeMagma` encoding, carrying the position tower of
    `Core/Order/Branching.lean`). Leaf `a` sits at `⟨[0]⟩`, the root at
    `⟨[]⟩`. -/
private abbrev bpDivergenceTree : FreeMagma Nat :=
  FreeMagma.mul (.of 0) (FreeMagma.mul (.of 1) (.of 2))

/-- The `SyntacticObject` encoding of the same bare tree `a * (b * c)`,
    on which `cCommandsIn` (sister-form c-command) is evaluated. -/
private abbrev sisterDivergenceTree : SyntacticObject :=
  SyntacticObject.leaf ⟨.simple .D [], 0⟩ *
    (SyntacticObject.leaf ⟨.simple .V [], 1⟩ * SyntacticObject.leaf ⟨.simple .D [], 2⟩)

/-- **B&P command ≠ sister-form c-command on `FreeMagma`.** On the bare
    tree `a * (b * c)`, leaf `a` *does* B&P c-command the root
    (`Core.Order.cCommand` over the dominance order: the only branching
    strict ancestor of `a` is the root, which dominates everything, so
    the defining universal holds), yet sister-form `cCommandsIn` rejects
    `(a, root)` (`a`'s sister `b * c` does not contain the root). The two
    relations are therefore not biconditionally equivalent, confirming
    the note above ([barker-pullum-1990], [reinhart-1976]). -/
theorem bp_command_ne_sister_cCommand :
    (⟨[0]⟩, ⟨[]⟩) ∈
      Core.Order.cCommand (Core.Order.Branching.toTreeOrder bpDivergenceTree) ∧
    ¬ cCommandsIn sisterDivergenceTree
        (SyntacticObject.leaf ⟨.simple .D [], 0⟩) sisterDivergenceTree := by
  refine ⟨?_, by decide⟩
  rw [Core.Order.cCommand, Core.Order.Branching.mem_commandRelation_toTreeOrder_iff]
  intro x hx hne _
  rw [List.mem_map] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have h0 : ([0] : List Nat).inits = [[], [0]] := by decide
  rw [h0] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact le_refl _
  · exact absurd rfl hne

/-! ## Multiset shape — abstract geometry over the nonplanar quotient

The unlabeled SO shape: replace every leaf token / trace marker with
`()`. The result lives in `FreeCommMagma Unit` — the canonical
*nonplanar* analog of the prior planar `TreeShape` (which was deleted
because `.node L R = .node R L` failed to hold under MCB §1.1.3,
book p. 23). Two SOs are *structurally isomorphic* iff their shapes
are equal as elements of `FreeCommMagma Unit`. -/

/-- The unlabeled multiset-shape of an SO: forget every leaf token
    and trace marker, keeping only the binary-tree structure modulo
    nonplanar quotient. Functorial via `FreeCommMagma.map`. -/
def SyntacticObject.shape : SyntacticObject → FreeCommMagma Unit :=
  FreeCommMagma.map (Function.const _ ())

/-- The unit shape — a single leaf in `FreeCommMagma Unit`. Useful
    abbreviation for stating shape equalities like
    `so.shape = leafShape * (leafShape * leafShape)`. Was previously
    duplicated as `private def leafShape` in three Studies files
    (Dendikken1995, HaddicanEtAl2026, Dendikken1995Causatives);
    hoisted to substrate to eliminate the triplicate. -/
abbrev leafShape : FreeCommMagma Unit := FreeCommMagma.of ()

@[simp] theorem SyntacticObject.shape_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).shape = FreeCommMagma.of () := rfl

@[simp] theorem SyntacticObject.shape_trace (n : Nat) :
    (SyntacticObject.trace n).shape = FreeCommMagma.of () := rfl

@[simp] theorem SyntacticObject.shape_mul (l r : SyntacticObject) :
    (l * r).shape = l.shape * r.shape :=
  MulHom.map_mul (FreeCommMagma.map _) l r

/-- Two SOs are structurally isomorphic iff they have the same
    nonplanar shape (ignoring all leaf labels). Replaces the prior
    `Bool`-valued `structurallyIsomorphic` from the planar substrate;
    `Prop`-valued + `DecidableEq` is more mathlib-aligned. -/
def structurallyIsomorphic (x y : SyntacticObject) : Prop :=
  x.shape = y.shape

instance (x y : SyntacticObject) :
    Decidable (structurallyIsomorphic x y) := by
  unfold structurallyIsomorphic; infer_instance

/-! ## Y-model branch to LF

The LF lift `SyntacticObject.toLFTree : SyntacticObject → Tree Unit String`
lives in `Syntax/Minimalism/SpellOut.lean`, where trace
detection and phonForm extraction are handled. PF (linearize /
phonYield) operates natively on `SyntacticObject` and does not require
a lift. -/

end Minimalist
