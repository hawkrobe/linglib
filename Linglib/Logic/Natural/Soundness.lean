import Linglib.Logic.Natural.Basic
import Linglib.Core.Order.AntiAdditive
import Linglib.Logic.Natural.World

/-!
# Soundness of the projectivity calculus

Semantic grounding for [icard-2012]'s projectivity machinery: `Relation`
gets its lattice content (`Holds`, his Definition 1.2 — non-exclusive
equations, so `⊑` is plain `≤`), and a signature is *sound* for a function
(`Signature.SoundFor`) when the function projects every relation as the
signature's `project` row says (his Lemma 2.5). The characterization
theorems discharge each row from the property family in
`Entailment` — the additive-family rows need the
`IsCompletely*` unit conditions, exactly as Icard's tables assume; the
soundness proofs go through over bounded lattices, not just his Boolean
lattices.

`SoundFor.comp` and `soundFor_contextProjectivity` certify
`Signature.compose` and path projection against function composition
(his Lemma 2.7 and Proposition 2.10): study-file locality computations over
the enum become corollaries of facts about actual context functions.

## Main declarations

- `Relation.Holds`: lattice content of the seven relations;
- `Signature.SoundFor`: σ's projection row is sound for `f`;
- `soundFor_mono_iff`, `soundFor_anti_iff`: the monotone rows, as iffs;
- `soundFor_additive` … `soundFor_antiAddMult`: the algebraic rows, from
  `IsCompletely*` hypotheses (sound direction; the converses fail —
  projection rows are class-maximal, not function-characterizing);
- `SoundFor.comp`: soundness composes along `Signature.compose`;
- `soundFor_contextProjectivity`: soundness folds along a signature path.

## Order soundness

With the implication orders carrying their [icard-2012] readings (`.all` =
•, the no-property top; `≡` not below the exclusion relations), both
orders are certified here: `Relation.Holds.of_le` (relation-level
implication) and `Signature.SoundFor.of_le` (a more specific
signature's soundness implies a less specific one's), via the projection
monotonicity `Signature.project_mono`. `soundFor_all` holds
unconditionally — every function realizes the no-property row.
-/

namespace NaturalLogic

open Entailment

/-! ### Lattice content of the relations -/

/-- The lattice content of a natural-logic relation ([icard-2012]
Definition 1.2), in mathlib's complementation vocabulary: `negation` is
`IsCompl`, `alternation` is `Disjoint`, `cover` is `Codisjoint`; `forward`
is non-strict `≤` (the enum comments' `⊂` follows MacCartney's exclusive
reading, which the projectivity tables do not need). -/
def Relation.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    Relation → α → α → Prop
  | .equiv => (· = ·)
  | .forward => (· ≤ ·)
  | .reverse => (· ≥ ·)
  | .negation => IsCompl
  | .alternation => Disjoint
  | .cover => Codisjoint
  | .independent => fun _ _ => True

/-! ### Join soundness -/

/-- The join table is sound: chained relations compose as `join` says.
Distributivity is needed for the cells that reason through a complement
(`negation ⋈ negation = equiv` is uniqueness of complements). -/
theorem Relation.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {R S : Relation} {x y z : β} (hR : R.Holds x y) (hS : S.Holds y z) :
    (R.join S).Holds x z := by
  cases R <;> cases S <;>
    first
      | trivial
      | exact hR.symm ▸ hS
      | exact hS ▸ hR
      | exact hR.trans hS
      | exact hS.trans hR
      | exact hS.disjoint.mono_left hR
      | exact hS.mono_left hR
      | exact hS.codisjoint.mono_left hR
      | exact hR.codisjoint.mono_right hS
      | exact hR.disjoint.mono_right hS
      | exact hR.symm.right_unique hS
      | exact hS.symm.le_of_codisjoint hR.codisjoint.symm
      | exact hR.disjoint.le_of_codisjoint hS
      | exact hR.le_of_codisjoint hS.codisjoint
      | exact hR.mono_right hS
      | exact hR.le_of_codisjoint hS
      | exact hS.symm.le_of_codisjoint hR.symm
      | exact hS.disjoint.symm.le_of_codisjoint hR.symm

/-! ### Soundness of a signature for a function -/

section SoundFor

variable {α β γ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A signature σ is **sound for** `f` when `f` projects every relation as
σ's row of the projection table says ([icard-2012] Lemma 2.5: every
φ-function projects `R` to `[R]^φ`). -/
def Signature.SoundFor (σ : Signature) (f : α → β) : Prop :=
  ∀ (R : Relation) (x y : α), R.Holds x y →
    (Signature.project R σ).Holds (f x) (f y)

/-- The `.mono` row is sound for exactly the monotone functions. -/
theorem soundFor_mono_iff {f : α → β} :
    Signature.SoundFor .mono f ↔ Monotone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

/-- The `.anti` row is sound for exactly the antitone functions. -/
theorem soundFor_anti_iff {f : α → β} :
    Signature.SoundFor .anti f ↔ Antitone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

/-- The `.additive` row is sound for completely additive functions. -/
theorem soundFor_additive {f : α → β} (h : IsCompletelyAdditive f) :
    Signature.SoundFor .additive f := by
  obtain ⟨hadd, htop⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hadd.monotone hR
  | reverse => exact hadd.monotone hR
  | negation => exact codisjoint_iff.mpr (by rw [← hadd x y, codisjoint_iff.mp hR.codisjoint]; exact htop)
  | alternation => trivial
  | cover => exact codisjoint_iff.mpr (by rw [← hadd x y, codisjoint_iff.mp hR]; exact htop)
  | independent => trivial

/-- The `.mult` row is sound for completely multiplicative functions. -/
theorem soundFor_mult {f : α → β} (h : IsCompletelyMultiplicative f) :
    Signature.SoundFor .mult f := by
  obtain ⟨hmult, hbot⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hmult.monotone hR
  | reverse => exact hmult.monotone hR
  | negation => exact disjoint_iff.mpr (by rw [← hmult x y, disjoint_iff.mp hR.disjoint]; exact hbot)
  | alternation => exact disjoint_iff.mpr (by rw [← hmult x y, disjoint_iff.mp hR]; exact hbot)
  | cover => trivial
  | independent => trivial

/-- The `.antiAdd` row is sound for completely anti-additive functions. -/
theorem soundFor_antiAdd {f : α → β} (h : IsCompletelyAntiAdditive f) :
    Signature.SoundFor .antiAdd f := by
  obtain ⟨haa, htop⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact haa.antitone hR
  | reverse => exact haa.antitone hR
  | negation => exact disjoint_iff.mpr (by rw [← haa x y, codisjoint_iff.mp hR.codisjoint]; exact htop)
  | alternation => trivial
  | cover => exact disjoint_iff.mpr (by rw [← haa x y, codisjoint_iff.mp hR]; exact htop)
  | independent => trivial

/-- The `.antiMult` row is sound for completely anti-multiplicative
functions. -/
theorem soundFor_antiMult {f : α → β} (h : IsCompletelyAntiMultiplicative f) :
    Signature.SoundFor .antiMult f := by
  obtain ⟨ham, hbot⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact ham.antitone hR
  | reverse => exact ham.antitone hR
  | negation => exact codisjoint_iff.mpr (by rw [← ham x y, disjoint_iff.mp hR.disjoint]; exact hbot)
  | alternation => exact codisjoint_iff.mpr (by rw [← ham x y, disjoint_iff.mp hR]; exact hbot)
  | cover => trivial
  | independent => trivial

/-- The `.addMult` row (preserve everything) is sound for morphisms:
completely additive and completely multiplicative functions. -/
theorem soundFor_addMult {f : α → β} (hadd : IsCompletelyAdditive f)
    (hmult : IsCompletelyMultiplicative f) :
    Signature.SoundFor .addMult f := by
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hadd.1.monotone hR
  | reverse => exact hadd.1.monotone hR
  | negation =>
      exact ⟨disjoint_iff.mpr (by rw [← hmult.1 x y, disjoint_iff.mp hR.disjoint]; exact hmult.2),
             codisjoint_iff.mpr (by rw [← hadd.1 x y, codisjoint_iff.mp hR.codisjoint]; exact hadd.2)⟩
  | alternation => exact disjoint_iff.mpr (by rw [← hmult.1 x y, disjoint_iff.mp hR]; exact hmult.2)
  | cover => exact codisjoint_iff.mpr (by rw [← hadd.1 x y, codisjoint_iff.mp hR]; exact hadd.2)
  | independent => trivial

/-- The `.antiAddMult` row is sound for anti-morphisms: completely
anti-additive and completely anti-multiplicative functions. This is the
sentential-negation row — the semantic content of "double negation is a
morphism". -/
theorem soundFor_antiAddMult {f : α → β} (haa : IsCompletelyAntiAdditive f)
    (ham : IsCompletelyAntiMultiplicative f) :
    Signature.SoundFor .antiAddMult f := by
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact haa.1.antitone hR
  | reverse => exact haa.1.antitone hR
  | negation =>
      exact ⟨disjoint_iff.mpr (by rw [← haa.1 x y, codisjoint_iff.mp hR.codisjoint]; exact haa.2),
             codisjoint_iff.mpr (by rw [← ham.1 x y, disjoint_iff.mp hR.disjoint]; exact ham.2)⟩
  | alternation => exact codisjoint_iff.mpr (by rw [← ham.1 x y, disjoint_iff.mp hR]; exact ham.2)
  | cover => exact disjoint_iff.mpr (by rw [← haa.1 x y, codisjoint_iff.mp hR]; exact haa.2)
  | independent => trivial

/-- Every function realizes the • row: `.all` is the no-property
signature, projecting every relation to `#`. -/
theorem soundFor_all (f : α → β) : Signature.SoundFor .all f :=
  fun _ _ _ _ => trivial

/-- Relation-level order soundness: `≤` is the implication order on
the lattice content ([icard-2012] §1). -/
theorem _root_.NaturalLogic.Relation.Holds.of_le
    {R R' : Relation} {u v : β} (h : R.Holds u v) (href : R ≤ R') :
    R'.Holds u v := by
  cases R <;> cases R' <;>
    first
    | exact h
    | trivial
    | exact h.1
    | exact h.2
    | exact le_of_eq h
    | exact le_of_eq (Eq.symm h)

/-- Projection is monotone in the signature order: a more specific
signature projects every relation at least as informatively. -/
theorem Signature.project_mono (R : Relation) :
    Monotone (Signature.project R) := by
  intro σ τ h
  revert h; cases σ <;> cases τ <;> cases R <;> decide

/-- Signature-order soundness: if σ refines τ (every σ-function is a
τ-function), σ-soundness implies τ-soundness. This is the theorem that
makes the refinement order mean class inclusion. -/
theorem Signature.SoundFor.of_le {σ τ : Signature} {f : α → β}
    (h : σ.SoundFor f) (hστ : σ ≤ τ) : τ.SoundFor f :=
  fun R x y hR => (h R x y hR).of_le (Signature.project_mono R hστ)

/-! ### Composition and paths -/

/-- **Soundness composes along `Signature.compose`** ([icard-2012]
Lemma 2.7 + Proposition 2.10): if ψ is sound for the outer function and φ
for the inner one, `ψ * φ` is sound for the composite. This is the theorem
that certifies the enum-level `compose` table against actual context
functions. -/
theorem Signature.SoundFor.comp {ψ φ : Signature} {f : β → γ}
    {g : α → β} (hf : ψ.SoundFor f) (hg : φ.SoundFor g) :
    (ψ * φ).SoundFor (f ∘ g) := by
  intro R x y hR
  have h := hf (Signature.project R φ) (g x) (g y) (hg R x y hR)
  rwa [projection_composition] at h

/-- The identity context is sound for the identity signature `.addMult`. -/
theorem soundFor_addMult_id : Signature.SoundFor .addMult (id : α → α) :=
  soundFor_addMult ⟨fun _ _ => rfl, rfl⟩ ⟨fun _ _ => rfl, rfl⟩

/-- **Path soundness**: a path of (signature, context) pairs, each sound,
yields a context sound for `contextProjectivity` of the signature path —
the semantic counterpart of [icard-2012] Definition 2.9's marking
algorithm. Signatures are listed outermost-first, matching
`contextProjectivity`. -/
theorem soundFor_contextProjectivity :
    ∀ (l : List (Signature × (α → α))),
      (∀ p ∈ l, p.1.SoundFor p.2) →
      (Signature.contextProjectivity (l.map Prod.fst)).SoundFor
        ((l.map Prod.snd).foldr (· ∘ ·) id)
  | [], _ => soundFor_addMult_id
  | p :: l, h => by
      have hhead : p.1.SoundFor p.2 := h p (List.mem_cons_self ..)
      have htail := soundFor_contextProjectivity l
        (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simpa [Signature.contextProjectivity, List.prod_cons, List.map_cons,
        List.foldr_cons] using
        hhead.comp htail

end SoundFor

/-! ### Worked instance: double negation is a morphism, semantically

`pnot` is completely anti-additive and completely anti-multiplicative, so
the `.antiAddMult` row is sound for it; composing it with itself certifies
the enum fact `◇⊟ ∘ ◇⊟ = ⊕⊞` against the actual function `pnot ∘ pnot`. -/

section PnotInstance

open Entailment

theorem pnot_isCompletelyAntiAdditive : IsCompletelyAntiAdditive pnot :=
  ⟨pnot_isAntiAdditive, by show (Set.univ : Set World)ᶜ = ∅; exact Set.compl_univ⟩

theorem pnot_isCompletelyAntiMultiplicative :
    IsCompletelyAntiMultiplicative pnot :=
  ⟨pnot_isAntiMultiplicative, by show (∅ : Set World)ᶜ = Set.univ; exact Set.compl_empty⟩

/-- Negation realizes the anti-morphism row. -/
theorem pnot_soundFor_antiAddMult :
    Signature.SoundFor .antiAddMult pnot :=
  soundFor_antiAddMult pnot_isCompletelyAntiAdditive
    pnot_isCompletelyAntiMultiplicative

/-- Double negation realizes the morphism row — the composed-signature
fact `◇⊟ ∘ ◇⊟ = ⊕⊞`, certified semantically rather than by enum table
lookup. -/
example : Signature.SoundFor .addMult (pnot ∘ pnot) :=
  pnot_soundFor_antiAddMult.comp pnot_soundFor_antiAddMult

/-- Propositional negation realizes the anti-morphism row at the `Prop`
instance. -/
theorem not_soundFor_antiAddMult : Signature.SoundFor .antiAddMult Not :=
  soundFor_antiAddMult
    ⟨fun p q => propext not_or, by show (¬True) = False; simp⟩
    ⟨fun p q => propext not_and_or, by show (¬False) = True; simp⟩

end PnotInstance

/-! ### Per-position profiles

Two-place operators carry one signature per argument position — a
determiner is one signature in its restrictor and another in its scope.
`Signature₂` records the pair, `Signature₂.SoundFor` says each component is sound
for the corresponding section (the other argument held constant), and
`Signature.SoundFor.comp₂` composes an outer context into both
positions at once. Certified instances for generalized quantifiers live
in `Semantics/Quantification/Signatures.lean`. -/

/-- A per-position signature profile for a two-place operator. For
determiners the positions are restrictor and scope; under the restrictor
analysis of conditionals, antecedent and consequent. -/
structure Signature₂ where
  restrictor : Signature
  scope : Signature
  deriving DecidableEq, Repr

section Signature₂

variable {α β γ δ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ] [Lattice δ] [BoundedOrder δ]

/-- A profile is sound for a two-place operator when each component
signature is sound for the corresponding section (the other argument held
constant). -/
def Signature₂.SoundFor (σ : Signature₂) (f : α → β → γ) : Prop :=
  (∀ y, σ.restrictor.SoundFor (fun x => f x y)) ∧
  (∀ x, σ.scope.SoundFor (f x))

/-- Composing a sound outer context into a sound two-place operator
composes the profile componentwise — the two-place form of
`Signature.SoundFor.comp`. -/
theorem Signature.SoundFor.comp₂ {ψ : Signature} {g : γ → δ}
    {σ : Signature₂} {f : α → β → γ} (hg : ψ.SoundFor g) (hf : σ.SoundFor f) :
    Signature₂.SoundFor ⟨ψ * σ.restrictor, ψ * σ.scope⟩ (fun x y => g (f x y)) :=
  ⟨fun y => hg.comp (hf.1 y), fun x => hg.comp (hf.2 x)⟩

end Signature₂

end NaturalLogic
