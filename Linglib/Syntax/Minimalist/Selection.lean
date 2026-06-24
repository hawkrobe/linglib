import Linglib.Syntax.Minimalist.Derivation
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Syntax.Minimalist.RepOrder

/-!
# C-Selection and Derivation Well-Formedness
[adger-2003] [marcolli-chomsky-berwick-2025]

Implements Adger's c-selectional checking system over linglib's Minimalism
substrate. `Syntax/Minimalism/Derivation.lean` defines free Merge
(`Step.apply`); this file adds the orthogonal layer of feature checking
that filters which derivations satisfy Full Interpretation.

## Adger's apparatus

- (104) **Full Interpretation**: the structure at the semantic interface
  contains no uninterpretable features
- (105) **Checking Requirement**: uninterpretable features must be checked,
  then they delete
- (106) **Checking under Sisterhood**: an uninterpretable feature [uF] on a
  syntactic object Y is checked when Y is sister to another syntactic object
  Z which bears a matching feature F
- (110) `kiss [V, uN]`: an interpretable [V] feature plus an uninterpretable
  c-selectional [uN] feature
- (132) Merge applies to two SOs forming a new SO; only at the root
- (133) **Definition of Head**: the head is the SO that selects in any
  Merge operation
- (137) **Headedness**: the item that projects is the item that selects

## M-C-B alignment: head info lives in the derivation

Per [marcolli-chomsky-berwick-2025] §1.13.3 / §1.15, NEW Minimalism
keeps `SyntacticObject` label-free (= `FreeMagma LIToken` here) and treats
head functions as **external partial maps** `Dom(h) ⊂ SO → LIToken`.
linglib follows this discipline:

- For derivation-based code, the head is **tracked through the derivation
  history** in `SelectionalState.head`. `Derivation.headLI?` and
  `Derivation.outerCat?` are then **total** for leaf-initial derivations
  (no heuristic involved).
- For arbitrary `SyntacticObject` values not coming from a derivation, the
  selection-driven `selCheck`/`selHead`/`outerCatC` (below) compute the head on
  the endocentric domain `Dom(h)`, and the selection-induced head function
  `HeadFunction.leftSpine` (defined below) realises this as a planar embedding
  (MCB Lemma 1.13.5).

`Step.emR item` is **first Merge** (complement): the head's outermost
selectional feature is checked against `item.outerCat`, and the complement
itself must be saturated (no remaining unchecked features). The projecting
head does not change. `Step.emL item` is **second Merge** (specifier): no
consumption — in linglib's flat encoding, specifiers are added by an
operation distinct from c-selection-driven first Merge (Adger's split
between V and little v puts the subject in spec,vP via EPP rather than via
V's c-selection). The projecting head does not change.

## Key definitions

- `SelectionalState` — bundles a `SyntacticObject` with the projecting
  head's `LIToken` and its remaining unchecked selectional features
- `SyntacticObject.checkedSel?` — recursively checks a built tree for
  internal c-selection consistency, returning the head's residual pending
  stack (heuristic-based, used internally for complex `emR` items)
- `Step.applyChecked` — applies a step under c-selection, returning `none`
  when checking fails (eq. 134 Checking Requirement); preserves head info
- `Derivation.checkedFinal?` — runs the derivation through `applyChecked`,
  seeding head from the initial leaf
- `Derivation.headLI?` / `Derivation.outerCat?` — **total** head accessors
  for derivation-based code (M-C-B §1.13.3 head function via derivation
  tracking)
- `Derivation.WellFormed` — Adger's Full Interpretation: derivation
  completes with empty pending stack
- `nullD` / `nullDWrap` — Adger ch. 7 (DP): silent D head wrapping a bare N
  to project a DP that satisfies a verb's [uD] c-selection

## Design notes

- **`Step.apply` is unchanged.** Free Merge and feature checking are
  separated, mirroring Adger's split between Merge as a structural
  operation (Ch 3 §3.2) and the Checking Requirement as a separate
  constraint (§3.5.3).
- **Complex complements are checked recursively** via `checkedSel?`, which
  enforces (a) internal saturation of the complement and (b) match between
  the head's pending feature and the complement's `outerCat`. This handles
  null-D-wrapped DPs (Adger ch. 7) where the complement is `(∅, NP)` with
  `∅`'s [uN] checked internally before the whole DP is offered to the verb.
- **Leftmost-leaf head heuristic** survives only for the partial extension
  to arbitrary `FreeMagma`s (in `outerCat` and `checkedSel?`). For
  derivation-based head info, see `Derivation.headLI?` / `outerCat?` —
  these are total via M-C-B §1.13.3 derivation tracking.
-/

namespace Minimalist

/-- A `SyntacticObject` paired with the projecting head's `LIToken` (per
    [marcolli-chomsky-berwick-2025] §1.13.3) and its remaining
    uninterpretable c-selectional features.

    Convention: features are consumed left-to-right by sister `emR`
    (complement Merge). The state is empty (`pending = []`) iff the head's
    selectional requirements have all been checked (Adger's Full
    Interpretation). -/
structure SelectionalState where
  /-- The current syntactic object. -/
  so : SyntacticObject
  /-- The projecting head's lexical item, tracked through the derivation
      (M-C-B §1.13.3 head function evaluated at the root vertex). -/
  head : LIToken
  /-- Remaining uninterpretable c-selectional features on the projecting
      head, in the order they will be checked. -/
  pending : List Cat
  deriving Repr, DecidableEq

/-! ### `checkedSel?` — parameterized over a head function

`checkedSel? h so` recursively checks an SO is built consistent with Adger 2003
c-selection (eq. 106 Checking under Sisterhood, eq. 132 Merge at root).
Returns the head's residual pending features after all internal checking,
or `none` if the structure is ill-built.

For a leaf, returns the leaf's `outerSel` untouched.

For a node `(l, r)` of `h.section_.σ so`, the convention is: `l` is the
projecting head (under harmonic head-initial), the complement `r` must be
saturated (its `checkedSelPlanar = some []`), `l`'s first pending feature is
consumed by matching against `r`'s outer category, and the residual is `l`'s
remaining stack. -/

/-- Underlying parameterized `checkedSel?` on a planar `FreeMagma`
    representative.

    For a binary node `(l, r)`, computes the right child's outer category
    by `leftmostLeafPlanar r |>.item.outerCat` (or `rightmostLeafPlanar r`
    under head-final), staying entirely in the planar world. This avoids
    the `externalize ∘ mk ≠ id` round-trip bug: re-applying `h.section_.σ`
    to `FreeCommMagma.mk r` would target a potentially DIFFERENT
    representative than the `r` we already have in hand. -/
def checkedSelWithPlanar (h : HeadFunction) :
    FreeMagma (LIToken ⊕ Nat) → Option (List Cat)
  | .of (.inl tok) => some tok.item.outerSel
  | .of (.inr _) => some []
  | .mul l r =>
    match checkedSelWithPlanar h l, checkedSelWithPlanar h r with
    | some (c :: rest), some [] =>
      let rHeadLeaf := match h.headSide with
        | .initial => leftmostLeafPlanar r
        | .final   => rightmostLeafPlanar r
      if rHeadLeaf.item.outerCat = c then some rest else none
    | _, _ => none

/-- Parameterized `checkedSel?`: under head function `h` (with externalize
    section), recursively check c-selection consistency on the planar
    representative `h.section_.σ so`. Computable when `h.section_.σ` is.

    Not given as a `SyntacticObject.checkedSelWith?` dot-notation method
    because `SyntacticObject := Quot _` doesn't admit dot-method projection
    through the quotient. Call as `checkedSelWith? h so`. -/
def checkedSelWith? (h : HeadFunction) (so : SyntacticObject) :
    Option (List Cat) :=
  checkedSelWithPlanar h (h.section_.σ so)

/-- For a leaf SO, `checkedSelWith?` returns the leaf's outer selection list
    (independent of head function). Routes through `Section.σ_of`. -/
@[simp] theorem checkedSelWith?_leaf (h : HeadFunction) (tok : LIToken) :
    checkedSelWith? h (.leaf tok) = some tok.item.outerSel := by
  show checkedSelWithPlanar h (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  rfl

/-- For a trace SO, `checkedSelWith?` returns `some []`. -/
@[simp] theorem checkedSelWith?_trace (h : HeadFunction) (n : Nat) :
    checkedSelWith? h (.trace n) = some [] := by
  show checkedSelWithPlanar h (h.section_.σ (FreeCommMagma.of (.inr n))) = _
  rw [h.section_.σ_of]
  rfl

-- Legacy `SyntacticObject.checkedSel?_trace` deleted in Phase 3.A.4 cleanup.
-- The parameterized `checkedSelWith?_trace` above (h : HeadFunction) subsumes it
-- via the keystone `Section.σ_of` helper.

/-! ### Computable selection-driven head function (MCB `Dom(h)`)

`selCheck` is the order-independent, fully **computable** counterpart of
`checkedSelWith?`. It identifies the projecting head by c-selection
([adger-2003] eq. 133 "the head is the SO that selects"; eq. 137 "the item that
projects is the item that selects" = [marcolli-chomsky-berwick-2025] Lemma
1.13.7) rather than by planar position, so it needs **no** `section_`/`Quot.out`.
It returns `some (head, residual)` on the endocentric domain `Dom(h)`
([marcolli-chomsky-berwick-2025] Def 1.13.6) and `none` at exocentric/symmetric
nodes where neither sister uniquely selects the other — exactly MCB's
partial-domain restriction (book p. 128, p. 131). This is what makes
`Derivation.WellFormed` genuinely `Decidable` without `classical`. -/

/-- Combine two sisters' selection-check results. Order-independent (symmetric,
    `selStep_comm`): whichever sister's head c-selects the *saturated* other
    projects, yielding its residual stack; `none` at exocentric nodes (neither
    or both qualify). -/
def selStep : Option (LIToken × List Cat) → Option (LIToken × List Cat) →
    Option (LIToken × List Cat)
  | some (ha, c :: rest), some (hb, []) =>
      if hb.item.outerCat = c then some (ha, rest) else none
  | some (ha, []), some (hb, c :: rest) =>
      if ha.item.outerCat = c then some (hb, rest) else none
  | _, _ => none

theorem selStep_comm (x y : Option (LIToken × List Cat)) :
    selStep x y = selStep y x := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some py => cases py with | mk hy sy => cases sy <;> rfl
  | some px =>
    cases px with
    | mk hx sx =>
      cases y with
      | none => cases sx <;> rfl
      | some py =>
        cases py with
        | mk hy sy => cases sx <;> cases sy <;> rfl

/-- Underlying selection check on a planar `FreeMagma` representative. -/
def selCheckAux : FreeMagma (LIToken ⊕ Nat) → Option (LIToken × List Cat)
  | .of (.inl tok) => some (tok, tok.item.outerSel)
  | .of (.inr n) => some (mkTraceToken n, [])
  | .mul l r => selStep (selCheckAux l) (selCheckAux r)

theorem selCheckAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : selCheckAux a = selCheckAux b := by
  induction h with
  | swap a b => exact selStep_comm _ _
  | mul_left _ _ ih => simp only [selCheckAux, ih]
  | mul_right _ _ ih => simp only [selCheckAux, ih]

/-- Computable selection-driven head function ([marcolli-chomsky-berwick-2025]
    Def 1.13.6 on `Dom(h)`): `some (projecting head, residual pending features)`,
    or `none` outside the endocentric domain. No `section_`/`Quot.out`. -/
def selCheck : SyntacticObject → Option (LIToken × List Cat) :=
  FreeCommMagma.lift selCheckAux selCheckAux_respects

@[simp] theorem selCheck_leaf (tok : LIToken) :
    selCheck (.leaf tok) = some (tok, tok.item.outerSel) := rfl

@[simp] theorem selCheck_trace (n : Nat) :
    selCheck (.trace n) = some (mkTraceToken n, []) := rfl

@[simp] theorem selCheck_mul (l r : SyntacticObject) :
    selCheck (l * r) = selStep (selCheck l) (selCheck r) := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-- Residual pending selectional features under `selCheck` (`some []` =
    saturated). The computable counterpart of `checkedSelWith?`. -/
def checkedSel (so : SyntacticObject) : Option (List Cat) := (selCheck so).map (·.2)

/-- The projecting head's lexical item on `Dom(h)`, computed by c-selection.
    Computable counterpart of `HeadFunction.head` for the endocentric case. -/
def selHead (so : SyntacticObject) : Option LIToken := (selCheck so).map (·.1)

@[simp] theorem checkedSel_leaf (tok : LIToken) :
    checkedSel (.leaf tok) = some tok.item.outerSel := rfl

@[simp] theorem selHead_leaf (tok : LIToken) : selHead (.leaf tok) = some tok := rfl

/-- The projecting head's **outer category** on `Dom(h)`, computed by
    c-selection ([adger-2003] eq. 137 / [marcolli-chomsky-berwick-2025]
    Lemma 1.13.7: "the item that projects becomes the head"). `none` at
    exocentric/symmetric nodes outside the endocentric domain.

    This is the computable, section-free counterpart of
    `HeadFunction.outerCat` (= the old `Quot.out`-based `leftSpine.outerCat`).
    Unlike the latter — which returns the *arbitrary* leftmost leaf of a
    `Quot.out` planar representative — `outerCatC` returns the category of the
    genuine **selector** head, so the value is MCB-faithful rather than an
    artifact of representative choice. Agrees with the old value on leaves
    (`outerCatC_leaf`). -/
def outerCatC (so : SyntacticObject) : Option Cat := (selHead so).map (·.item.outerCat)

@[simp] theorem outerCatC_leaf (tok : LIToken) :
    outerCatC (.leaf tok) = some tok.item.outerCat := rfl

@[simp] theorem outerCatC_trace (n : Nat) :
    outerCatC (.trace n) = some (mkTraceToken n).item.outerCat := rfl

/-- Computable, section-free c-selection between SOs: `a` selects `b` iff `a`'s
    projecting head c-selects `b`'s (both on `Dom(h)`). The computable
    counterpart of `HeadFunction.selects` — no `Quot.out`/`classical`. -/
def selectsC (a b : SyntacticObject) : Prop :=
  match selHead a, selHead b with
  | some ha, some hb => ha.selects hb
  | _, _ => False

instance (a b : SyntacticObject) : Decidable (selectsC a b) := by
  unfold selectsC; split <;> infer_instance

@[simp] theorem selectsC_leaf (s t : LIToken) :
    selectsC (.leaf s) (.leaf t) ↔ s.selects t := by
  simp only [selectsC, selHead_leaf]

/-- The head of `selStep x y` (when defined) is one of `x`/`y`'s heads. -/
theorem selStep_fst {x y : Option (LIToken × List Cat)} {r : LIToken}
    (h : (selStep x y).map (·.1) = some r) :
    x.map (·.1) = some r ∨ y.map (·.1) = some r := by
  unfold selStep at h
  split at h
  · split_ifs at h <;> simp_all
  · split_ifs at h <;> simp_all
  · simp at h

/-- Head Feature Principle (computable): a Merge node's head is one of its
    daughters' heads ([adger-2003] eq. 137 / [marcolli-chomsky-berwick-2025]
    Lemma 1.13.7). Holds for `selHead` because it projects the *selector* by
    construction — cf. the deliberately-absent unconditional version for a
    general section in `HeadFunction.lean`. -/
theorem selHead_mul {a b : SyntacticObject} {h : LIToken}
    (hab : selHead (a * b) = some h) :
    selHead a = some h ∨ selHead b = some h := by
  simp only [selHead, selCheck_mul] at hab ⊢
  exact selStep_fst hab

/-- On a Merge node, the MCB-exact head category is the head category of
    whichever daughter projects (the selector), mirroring the Head Feature
    Principle `selHead_mul` ([marcolli-chomsky-berwick-2025] Lemma 1.13.7). -/
theorem outerCatC_mul {a b : SyntacticObject} {c : Cat}
    (hab : outerCatC (a * b) = some c) :
    outerCatC a = some c ∨ outerCatC b = some c := by
  simp only [outerCatC, Option.map_eq_some_iff] at hab ⊢
  obtain ⟨tok, htok, hcat⟩ := hab
  rcases selHead_mul htok with h | h
  · exact Or.inl ⟨tok, h, hcat⟩
  · exact Or.inr ⟨tok, h, hcat⟩

/-! ### Selection-induced planar embedding (MCB Lemma 1.13.5)

[marcolli-chomsky-berwick-2025] Lemma 1.13.5: head functions on a tree are in
bijection with its planar embeddings. The externalization section σ_L realising a
given head function places the **projecting (selector) daughter** on the
convention side of each endocentric node. On `Dom(h)` (every node endocentric)
this embedding is canonical and selection-driven; at exocentric XP–YP nodes —
which MCB place *outside* `Dom(h)` and where σ_L is explicitly **noncanonical** —
the subtrees are ordered by the canonical structural comparison `smallerFirst`
(`RepOrder.lean`), which is comm-invariant, keeping the section **fully
computable** (no `Quot.out`). The head leaf of the resulting embedding is the
selector (`leftSpine_outerCat_eq_outerCatC`), the formal content of Lemma 1.13.7. -/

/-- Which daughter projects at a binary node under c-selection: `some true` = the
    **left** sister is the selector, `some false` = the **right**, `none` =
    exocentric (neither uniquely selects the saturated other). Mirrors `selStep`. -/
def selSide : Option (LIToken × List Cat) → Option (LIToken × List Cat) → Option Bool
  | some (_, c :: _), some (hb, []) => if hb.item.outerCat = c then some true else none
  | some (ha, []), some (_, c :: _) => if ha.item.outerCat = c then some false else none
  | _, _ => none

theorem selSide_comm (x y : Option (LIToken × List Cat)) :
    selSide x y = (selSide y x).map Bool.not := by
  cases x with
  | none => cases y with
    | none => rfl
    | some py => obtain ⟨hy, sy⟩ := py; cases sy <;> rfl
  | some px => obtain ⟨hx, sx⟩ := px; cases y with
    | none => cases sx <;> rfl
    | some py => obtain ⟨hy, sy⟩ := py
                 cases sx <;> cases sy <;> simp only [selSide, Option.map] <;>
                   split <;> rfl

/-- Place the head daughter on the convention side: `.initial` (head-initial) →
    head to the LEFT, `.final` (head-final) → head to the RIGHT. -/
def placeHead (s : ConventionDir) (head other : FreeMagma (LIToken ⊕ Nat)) :
    FreeMagma (LIToken ⊕ Nat) :=
  match s with
  | .initial => head * other
  | .final   => other * head

/-- Forgetting order, `placeHead` is just the product of its two arguments
    (commutativity of `FreeCommMagma`). -/
theorem mk_placeHead (s : ConventionDir) (head other : FreeMagma (LIToken ⊕ Nat)) :
    (FreeCommMagma.mk (placeHead s head other) : SyntacticObject)
      = FreeCommMagma.mk head * FreeCommMagma.mk other := by
  cases s
  · rfl
  · exact FreeCommMagma.swap other head

/-- The selection-induced planar embedding on a `FreeMagma` representative
    (MCB Lemma 1.13.5): at each endocentric node the projecting (selector) daughter
    is placed on the `s`-convention side; exocentric nodes — off `Dom(h)`, where
    σ_L is noncanonical — are ordered by the canonical structural comparison
    `smallerFirst` (`RepOrder.lean`). Fully **computable**: no `Quot.out`. -/
def selLinearizeAux (s : ConventionDir) :
    FreeMagma (LIToken ⊕ Nat) → FreeMagma (LIToken ⊕ Nat)
  | .of x => .of x
  | .mul l r =>
    match selSide (selCheckAux l) (selCheckAux r) with
    | some true  => placeHead s (selLinearizeAux s l) (selLinearizeAux s r)
    | some false => placeHead s (selLinearizeAux s r) (selLinearizeAux s l)
    | none       => smallerFirst (selLinearizeAux s l) (selLinearizeAux s r)

theorem selLinearizeAux_respects (s : ConventionDir) (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : selLinearizeAux s a = selLinearizeAux s b := by
  induction h with
  | swap a b =>
    show selLinearizeAux s (a * b) = selLinearizeAux s (b * a)
    simp only [selLinearizeAux, selSide_comm (selCheckAux b) (selCheckAux a)]
    cases selSide (selCheckAux a) (selCheckAux b) with
    | none => exact smallerFirst_comm _ _
    | some s' => cases s' <;> rfl
  | mul_left hr c ih =>
    rename_i a a'
    show selLinearizeAux s (a * c) = selLinearizeAux s (a' * c)
    simp only [selLinearizeAux, selCheckAux_respects a a' hr, ih]
  | mul_right a hr ih =>
    rename_i b c
    show selLinearizeAux s (a * b) = selLinearizeAux s (a * c)
    simp only [selLinearizeAux, selCheckAux_respects b c hr, ih]

/-- The selection-induced section σ_L (MCB §1.12.1 / Lemma 1.13.5), as a function
    on `SyntacticObject`. Fully **computable** — selection-driven on `Dom(h)`,
    structural-comparison-ordered (`smallerFirst`) at exocentric nodes. -/
def selLinearize (s : ConventionDir) :
    SyntacticObject → FreeMagma (LIToken ⊕ Nat) :=
  FreeCommMagma.lift (selLinearizeAux s) (selLinearizeAux_respects s)

/-- The selection-induced embedding distributes over Merge: the projecting
    (selector) daughter is placed on the `s`-convention side, with the exocentric
    fallback `smallerFirst`. Mirrors `selCheck_mul`. -/
theorem selLinearize_mul (s : ConventionDir) (l r : SyntacticObject) :
    selLinearize s (l * r) =
      match selSide (selCheck l) (selCheck r) with
      | some true  => placeHead s (selLinearize s l) (selLinearize s r)
      | some false => placeHead s (selLinearize s r) (selLinearize s l)
      | none       => smallerFirst (selLinearize s l) (selLinearize s r) := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-- When `selStep` returns a head, that head is the projecting daughter's head,
    and `selSide` agrees on which daughter projects. The bridge between the
    residual-tracking `selStep` and the order-determining `selSide`. -/
theorem selStep_eq_some {x y : Option (LIToken × List Cat)} {hd : LIToken}
    {res : List Cat} (h : selStep x y = some (hd, res)) :
    (selSide x y = some true ∧ x.map (·.1) = some hd) ∨
    (selSide x y = some false ∧ y.map (·.1) = some hd) := by
  match x, y with
  | some (ha, c :: rest'), some (hb, []) =>
    simp only [selStep] at h
    by_cases hcat : hb.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · rw [if_neg hcat] at h; exact absurd h (by simp)
  | some (ha, []), some (hb, c :: rest') =>
    simp only [selStep] at h
    by_cases hcat : ha.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · rw [if_neg hcat] at h; exact absurd h (by simp)
  | some (_, []), some (_, []) => simp [selStep] at h
  | some (_, _ :: _), some (_, _ :: _) => simp [selStep] at h
  | none, _ => simp [selStep] at h
  | some _, none => simp [selStep] at h

/-- The head leaf of the selection-induced head-initial embedding is the
    **selector** ([marcolli-chomsky-berwick-2025] Lemma 1.13.5/1.13.7): the
    leftmost leaf of `selLinearizeAux .initial fm` is `selCheckAux fm`'s
    projecting head (or `fm` is exocentric, off `Dom(h)`). -/
theorem selLinearizeAux_initial_leftmost (fm : FreeMagma (LIToken ⊕ Nat)) :
    (selCheckAux fm).map (·.1)
        = some (leftmostLeafPlanar (selLinearizeAux .initial fm))
      ∨ selCheckAux fm = none := by
  induction fm with
  | ih1 x => exact Or.inl (by cases x <;> rfl)
  | ih2 l r ihl ihr =>
    have hmul : selCheckAux (l * r) = selStep (selCheckAux l) (selCheckAux r) := rfl
    cases hstep : selStep (selCheckAux l) (selCheckAux r) with
    | none => exact Or.inr (by rw [hmul, hstep])
    | some p =>
      obtain ⟨hd, res⟩ := p
      refine Or.inl ?_
      rw [hmul, hstep, Option.map_some]
      obtain ⟨hsT, hxhd⟩ | ⟨hsF, hyhd⟩ := selStep_eq_some hstep
      · simp only [selLinearizeAux, hsT, placeHead, leftmostLeafPlanar]
        rcases ihl with hl | hl
        · rw [hxhd] at hl; exact hl
        · rw [hl] at hxhd; simp at hxhd
      · simp only [selLinearizeAux, hsF, placeHead, leftmostLeafPlanar]
        rcases ihr with hr | hr
        · rw [hyhd] at hr; exact hr
        · rw [hr] at hyhd; simp at hyhd

theorem selLinearizeAux_isSection (s : ConventionDir)
    (fm : FreeMagma (LIToken ⊕ Nat)) :
    (FreeCommMagma.mk (selLinearizeAux s fm) : SyntacticObject) = FreeCommMagma.mk fm := by
  have key : ∀ x y : FreeMagma (LIToken ⊕ Nat),
      (FreeCommMagma.mk (x * y) : SyntacticObject)
        = FreeCommMagma.mk x * FreeCommMagma.mk y := fun _ _ => rfl
  induction fm with
  | ih1 x => rfl
  | ih2 l r ihl ihr =>
    cases hs : selSide (selCheckAux l) (selCheckAux r) with
    | none =>
      show (FreeCommMagma.mk (selLinearizeAux s (l * r)) : SyntacticObject)
        = FreeCommMagma.mk (l * r)
      simp only [selLinearizeAux, hs, mk_smallerFirst, ihl, ihr, key]
    | some b => cases b with
      | true =>
        show (FreeCommMagma.mk (selLinearizeAux s (l * r)) : SyntacticObject)
          = FreeCommMagma.mk (l * r)
        simp only [selLinearizeAux, hs, mk_placeHead, ihl, ihr, key]
      | false =>
        show (FreeCommMagma.mk (selLinearizeAux s (l * r)) : SyntacticObject)
          = FreeCommMagma.mk (l * r)
        simp only [selLinearizeAux, hs, mk_placeHead, ihl, ihr, key]
        exact mul_comm _ _

theorem selLinearize_isSection (s : ConventionDir) :
    Function.LeftInverse
      (FreeCommMagma.mk : FreeMagma (LIToken ⊕ Nat) → SyntacticObject) (selLinearize s) :=
  fun T => Quot.inductionOn T (fun fm => selLinearizeAux_isSection s fm)

/-- The selection-induced externalization section ([marcolli-chomsky-berwick-2025]
    §1.12.1 / Lemma 1.13.5) for a given head-side convention. The genuine,
    selection-driven replacement for the retired `Quot.out` placeholder
    `FreeCommMagma.Section.out`. -/
def selSection (s : ConventionDir) :
    FreeCommMagma.Section (LIToken ⊕ Nat) where
  σ := selLinearize s
  isSection := selLinearize_isSection s

namespace HeadFunction

/-- The default **harmonic head-initial** head function, realised by the
    selection-induced planar embedding ([marcolli-chomsky-berwick-2025]
    Lemma 1.13.5/1.13.7): the head leaf is the genuine **selector**
    (`leftSpine_outerCat`), and the domain is the endocentric `Dom(h)` where
    c-selection resolves. Supersedes the retired `Quot.out` placeholder. -/
def leftSpine : HeadFunction where
  section_ := selSection .initial
  headSide := .initial
  Dom so := (selCheck so).isSome = true
  decDom := fun _ => inferInstance

/-- Right-headed dual of `leftSpine`: harmonic **head-final** (Japanese/Korean/
    Turkish), the selector placed to the right of the selection-induced embedding. -/
def rightSpine : HeadFunction where
  section_ := selSection .final
  headSide := .final
  Dom so := (selCheck so).isSome = true
  decDom := fun _ => inferInstance

end HeadFunction

/-- On `Dom(h)`, the head leaf of `leftSpine`'s selection-induced embedding is
    exactly the `selHead` selector — the planar-embedding ⇒ selection direction
    of [marcolli-chomsky-berwick-2025] Lemma 1.13.5/1.13.7. -/
theorem leftmost_selLinearize_eq_selHead (so : SyntacticObject) (h : LIToken)
    (hc : selHead so = some h) :
    leftmostLeafPlanar (selLinearize .initial so) = h := by
  induction so using Quot.inductionOn with
  | _ fm =>
    have hsel : selHead (FreeCommMagma.mk fm) = (selCheckAux fm).map (·.1) := rfl
    rw [hsel] at hc
    rcases selLinearizeAux_initial_leftmost fm with hl | hl
    · rw [hl] at hc; exact Option.some.inj hc
    · rw [hl] at hc; simp at hc

/-- The head function `leftSpine` evaluated on `Dom(h)` returns the `selHead`
    selector (MCB Lemma 1.13.7 — "the item that projects becomes the head"). -/
theorem leftSpine_head (so : SyntacticObject) (h : LIToken)
    (hc : selHead so = some h) : HeadFunction.leftSpine.head so = h :=
  leftmost_selLinearize_eq_selHead so h hc

/-- **Lemma 1.13.5/1.13.7 (head category).** On `Dom(h)`, the head category read
    off `leftSpine`'s selection-induced planar embedding equals the genuine
    selector's category `outerCatC` — the planar-embedding head function and the
    selection-driven head function coincide. -/
theorem leftSpine_outerCat_eq_outerCatC (so : SyntacticObject)
    (hso : (selCheck so).isSome) :
    some (HeadFunction.leftSpine.outerCat so) = outerCatC so := by
  obtain ⟨⟨hd, res⟩, hhd⟩ := Option.isSome_iff_exists.mp hso
  have hsh : selHead so = some hd := by rw [selHead, hhd]; rfl
  show some ((HeadFunction.leftSpine.head so).item.outerCat) = _
  rw [leftSpine_head so hd hsh, outerCatC, hsh, Option.map_some]

/-- Head-final mirror of `selLinearizeAux_initial_leftmost`: the **rightmost**
    leaf of the head-final embedding is the selector. -/
theorem selLinearizeAux_final_rightmost (fm : FreeMagma (LIToken ⊕ Nat)) :
    (selCheckAux fm).map (·.1)
        = some (rightmostLeafPlanar (selLinearizeAux .final fm))
      ∨ selCheckAux fm = none := by
  induction fm with
  | ih1 x => exact Or.inl (by cases x <;> rfl)
  | ih2 l r ihl ihr =>
    have hmul : selCheckAux (l * r) = selStep (selCheckAux l) (selCheckAux r) := rfl
    cases hstep : selStep (selCheckAux l) (selCheckAux r) with
    | none => exact Or.inr (by rw [hmul, hstep])
    | some p =>
      obtain ⟨hd, res⟩ := p
      refine Or.inl ?_
      rw [hmul, hstep, Option.map_some]
      obtain ⟨hsT, hxhd⟩ | ⟨hsF, hyhd⟩ := selStep_eq_some hstep
      · simp only [selLinearizeAux, hsT, placeHead, rightmostLeafPlanar]
        rcases ihl with hl | hl
        · rw [hxhd] at hl; exact hl
        · rw [hl] at hxhd; simp at hxhd
      · simp only [selLinearizeAux, hsF, placeHead, rightmostLeafPlanar]
        rcases ihr with hr | hr
        · rw [hyhd] at hr; exact hr
        · rw [hr] at hyhd; simp at hyhd

/-- Head-final dual of `leftSpine_outerCat_eq_outerCatC`: the head category of
    `rightSpine`'s head-final embedding equals the selector's. -/
theorem rightSpine_outerCat_eq_outerCatC (so : SyntacticObject)
    (hso : (selCheck so).isSome) :
    some (HeadFunction.rightSpine.outerCat so) = outerCatC so := by
  obtain ⟨⟨hd, res⟩, hhd⟩ := Option.isSome_iff_exists.mp hso
  have hsh : selHead so = some hd := by rw [selHead, hhd]; rfl
  have hrm : HeadFunction.rightSpine.head so = hd := by
    show rightmostLeafPlanar (selLinearize .final so) = hd
    induction so using Quot.inductionOn with
    | _ fm =>
      have hsel : selHead (FreeCommMagma.mk fm) = (selCheckAux fm).map (·.1) := rfl
      rw [hsel] at hsh
      rcases selLinearizeAux_final_rightmost fm with hl | hl
      · rw [hl] at hsh; exact Option.some.inj hsh
      · rw [hl] at hsh; simp at hsh
  show some ((HeadFunction.rightSpine.head so).item.outerCat) = _
  rw [hrm, outerCatC, hsh, Option.map_some]

/-- Apply a `Step` under c-selection ([adger-2003] eq. 134 Checking
    Requirement, eq. 106 Checking under Sisterhood). The projecting head
    is preserved across all step constructors — this matches M-C-B §1.15
    (the labeling algorithm assigns the same head to a node and its head
    daughter) and Adger eq. 137 ("Headedness").

    - `emR item` (complement Merge) requires (a) the head's `pending` to
      be non-empty and its head category to match `item.outerCat`, and
      (b) `item` to be saturated (`item.checkedSel? = some []`). The
      matched feature is consumed; head unchanged.
    - `emL item` (specifier Merge) does not consume selectional features;
      head unchanged.
    - `im` and `wlm` propagate without consumption; head unchanged.

    Returns `none` when checking fails (no pending feature, category
    mismatch, or unsaturated complement). -/
def Step.applyChecked : Step → SelectionalState → Option SelectionalState
  | .emR item, ⟨so, head, c :: rest⟩ =>
    match selCheck item with
    | some (ihead, []) =>
      if ihead.item.outerCat = c then some ⟨.node so item, head, rest⟩ else none
    | _ => none
  | .emR _, ⟨_, _, []⟩ => none
  | .emL item, ⟨so, head, sel⟩ => some ⟨.node item so, head, sel⟩
  | .im mover traceId, ⟨so, head, sel⟩ =>
    some ⟨(Step.im mover traceId).apply so, head, sel⟩

/-- Run a derivation through `applyChecked`. Seeds the head from the
    initial leaf (M-C-B §1.13.3: leaves are always in `Dom(h)`); for
    node-initial derivations falls back to `HeadFunction.leftSpine.head`.
    Returns `none` if the initial is ill-built or any step violates
    c-selection. -/
def Derivation.checkedFinal? (d : Derivation) : Option SelectionalState := do
  let (h0, pending) ← selCheck d.initial
  d.steps.foldl
    (fun st? step => st?.bind (Step.applyChecked step))
    (some ⟨d.initial, h0, pending⟩)

/-- A derivation is **well-formed** (Adger's Full Interpretation,
    [adger-2003] eq. 104+161) iff it completes with no unchecked
    selectional features remaining on the projecting head. -/
def Derivation.WellFormed (d : Derivation) : Prop :=
  d.checkedFinal?.map (·.pending) = some []

instance (d : Derivation) : Decidable d.WellFormed := by
  unfold Derivation.WellFormed; infer_instance

/-! ## M-C-B-aligned head accessors

For derivation-based code, head info is **tracked** through the derivation
rather than recovered via heuristics. These accessors implement M-C-B
§1.13.3's head function for the leaf-initial case (which covers all
canonical Minimalist derivations). -/

/-- The projecting head's lexical item, computed by tracking through the
    derivation. Returns `some tok` for derivations whose initial seed is
    `.leaf tok` and whose step sequence is well-formed under
    `applyChecked`; `none` otherwise.

    This is the M-C-B §1.13.3 head function specialized to derivation
    history — **total** for leaf-initial well-formed derivations, with no
    leftmost-leaf heuristic. -/
def Derivation.headLI? (d : Derivation) : Option LIToken :=
  d.checkedFinal?.map (·.head)

/-- The projecting head's outer categorial feature (Adger eq. 110 [F]),
    derived from the tracked head. Total for leaf-initial well-formed
    derivations. -/
def Derivation.outerCat? (d : Derivation) : Option Cat :=
  d.headLI?.map (·.item.outerCat)

/-! ## Adger ch. 7: silent D for bare nominal arguments

[adger-2003] ch. 7 (Functional Categories II — the DP) treats every
argumental nominal as a DP. Bare common nouns (mass nouns, generic plurals)
are headed by a phonologically silent D that projects DP and consumes the
noun's [N] feature.

`nullD id` builds a silent D leaf with selectional feature [N] (so that it
checks against an N complement); `nullDWrap n id` is the canonical
"null-D-wraps-a-bare-N" construction, returning `(nullD, n)` whose
`outerCat` is .D and whose `checkedSel?` is `some []` (saturated). -/

/-- A silent D head bearing the c-selectional feature [N], used by
    `nullDWrap` to project a DP from a bare common noun (Adger ch. 7).
    The `id` argument should be unique within the derivation. -/
def nullD (id : Nat) : SyntacticObject :=
  mkLeafPhon .D [.N] "" id

/-- Wrap a bare N (or any N-projecting SO) under a silent D, yielding a
    saturated DP suitable for use as a verb's [uD] complement.
    [adger-2003] ch. 7. -/
def nullDWrap (n : SyntacticObject) (id : Nat) : SyntacticObject :=
  .node (nullD id) n

/-! ## Angelopoulos 2026: silent light noun for [n]-feature checking

[angelopoulos-2026] §3.1 (following [arsenijevic-2009],
[moltmann-2019]) analyses Greek *oti*/*pu* as bearing an
uninterpretable [n]-feature checked by a silent light noun in their
specifier. The light noun is then licensed by incorporation
([hale-keyser-1993]) into a higher *lexical* head (`v_State` or
`v_Event`); incorporation into a *functional* head (`T`) is impossible.

`nullN id` builds a saturated silent little-n leaf, parallel to
`nullD`. It carries no further selectional features — its role is to
be Merged into Spec,CP, where it checks the C head's [n]-feature, and
subsequently to head-move into a hosting v. Uses the existing `Cat.n`
constructor (Marantz 2001 / Distributed Morphology nominal categorizer);
no new `Cat` constructor required. -/

/-- A silent light noun (n head) with no selectional features, used for
    checking a complementizer's [n]-feature in its specifier per
    [angelopoulos-2026] §3.1. The `id` argument should be unique
    within the derivation. Mirrors `nullD`. -/
def nullN (id : Nat) : SyntacticObject :=
  mkLeafPhon .n [] "" id

@[simp] theorem nullN_outerCatC (id : Nat) :
    outerCatC (nullN id) = some .n := by
  simp [nullN, mkLeafPhon, outerCatC, LexicalItem.outerCat, LexicalItem.simple]

@[simp] theorem nullN_checkedSel (id : Nat) :
    checkedSel (nullN id) = some [] := by
  simp [nullN, mkLeafPhon, checkedSel, LexicalItem.outerSel, LexicalItem.simple]

/-! ## Step-level lemmas

Destructor lemmas describing how `applyChecked` interacts with each `Step`
constructor. Front-loaded so consumers (paper-replication study files) can
reason about specific derivations without unfolding `foldl`. -/

/-- `emR` with a saturated, category-matching item consumes the first
    selectional feature; head is preserved. The category match is computed by
    the section-free `selCheck` (the head function `Step.applyChecked` uses). -/
@[simp] theorem applyChecked_emR_match
    (so item : SyntacticObject) (head ihead : LIToken) (c : Cat) (rest : List Cat)
    (hsel : selCheck item = some (ihead, []))
    (hcat : ihead.item.outerCat = c) :
    Step.applyChecked (.emR item) ⟨so, head, c :: rest⟩
      = some ⟨.node so item, head, rest⟩ := by
  simp [Step.applyChecked, hsel, hcat]

/-- `emR` on an empty pending stack fails (no feature to check). -/
theorem applyChecked_emR_empty (so item : SyntacticObject) (head : LIToken) :
    Step.applyChecked (.emR item) ⟨so, head, []⟩ = none := rfl

/-- `emL` (specifier Merge) preserves both pending stack and head. -/
theorem applyChecked_emL
    (so item : SyntacticObject) (head : LIToken) (sel : List Cat) :
    Step.applyChecked (.emL item) ⟨so, head, sel⟩
      = some ⟨.node item so, head, sel⟩ := rfl

/-- A leaf-initial derivation with empty `outerSel` and no steps is
    well-formed (Adger eq. 104: vacuously satisfies Full Interpretation). -/
theorem wellFormed_initial_no_sel (tok : LIToken)
    (h : tok.item.outerSel = []) :
    Derivation.WellFormed ⟨.leaf tok, []⟩ := by
  unfold Derivation.WellFormed Derivation.checkedFinal?
  rw [selCheck_leaf, h]
  rfl

/-- `nullDWrap` of any `selCheck`-saturated SO whose projecting head is category
    N is itself saturated under the computable `checkedSel` (Adger ch. 7: silent
    D wraps a saturated N to yield a saturated DP). Discharges the former
    `checkedSelWith?`/`Quot.out`-bound `sorry` — the selection-driven `selCheck`
    reduces structurally through the binary node. -/
theorem checkedSel_nullDWrap (n : SyntacticObject) (id : Nat) (nhead : LIToken)
    (hsel : selCheck n = some (nhead, [])) (hcat : nhead.item.outerCat = .N) :
    checkedSel (nullDWrap n id) = some [] := by
  show (selCheck (nullD id * n)).map (·.2) = some []
  rw [selCheck_mul, hsel,
      show selCheck (nullD id) = some (⟨.simple .D [.N] "", id⟩, [.N]) from rfl]
  simp [selStep, hcat]

end Minimalist
