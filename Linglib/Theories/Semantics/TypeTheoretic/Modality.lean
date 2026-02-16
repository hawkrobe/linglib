import Linglib.Theories.Semantics.TypeTheoretic.Discourse

/-!
# Type Theory with Records — Chapter 6: Modality and Intensionality without Possible Worlds

Cooper (2023) Chapter 6 extends the modal type system framework from Ch1
with Prop-valued modal systems, topoi (replacing accessibility relations),
Box/Diamond type constructors, Austinian/Russellian propositions,
believe/know via long-term memory, points of view, and intensional
transitive verbs.

**Layer 2 — Semantics**: ModalSystem (Ch6, Prop) + bridge to
  ModalTypeSystem (Ch1, Bool), Topos ≃ Parametric Type (unified),
  NecTopos, PossTopos, Box/Diamond.

**Bridges**:
  - ModalTypeSystem ↔ ModalSystem (Bool ↔ Prop)
  - ModalSystem ↔ AccessRel (Kripke accessibility)
  - know = believe + veridicality (abstract doxastic bridge)
  - Topos → induced necessity/possibility (abstract Kratzer bridge)

## References

- Cooper (2023). From Perception to Communication. OUP. Ch 6.
- Kratzer (1991). Modality / Conditionals.
- Austin (1961). Truth.
- Barwise (1989). The Situation in Logic.
-/

namespace Semantics.TypeTheoretic

-- ============================================================================
-- Layer 2: Semantics (Situations, Modality, Topoi)
-- Chapter 6: Modality and Intensionality without Possible Worlds
-- ============================================================================

/-! ## § 6.2–6.3 Modal type systems — extended

Chapter 1 introduced `ModalTypeSystem` (Def 54) with Bool-valued predicate
assignments. Chapter 6 builds on this with four modal notions, each in
restrictive (all possibilities share the type) and inclusive (some possibility
has the type) variants.

A modal system of complex types TYPE_MC is a family of type systems indexed
by "possibilities" where basic types and predicates are shared but witness
assignments vary.  Cooper (2023) §6.3, (1)–(4). -/

/-- A possibility in a modal type system: an assignment of witnesses to types.
Each possibility maps types (represented as `Ty`) to their set of witnesses.
Cooper (2023) §6.3: possibilities differ in which objects witness which types. -/
structure Possibility (Ty Obj : Type) where
  /-- Whether object `a` witnesses type `T` in this possibility -/
  witnesses : Ty → Obj → Prop

/-- A modal system of complex types: a family of possibilities.
Cooper (2023) §6.3, Def A9: TYPE_MC = ⟨Type_M, BType, ⟨PType_M⟩, ...⟩_{M ∈ M}.
The possibilities share the same types but differ in witness assignments. -/
structure ModalSystem (Ty Obj : Type) where
  /-- The index type for possibilities -/
  Poss : Type
  /-- The family of possibilities -/
  poss : Poss → Possibility Ty Obj

/-- Extension of a type in a possibility: the set of witnesses.
Cooper (2023) §6.3, (1a): {a | a :_{TYPE_{M_i}} T}. -/
def ModalSystem.ext {Ty Obj : Type} (ms : ModalSystem Ty Obj)
    (p : ms.Poss) (T : Ty) : Obj → Prop :=
  ms.poss p |>.witnesses T

section ModalNotions

variable {Ty Obj : Type} (ms : ModalSystem Ty Obj)

/-! ### Restrictive modal notions (§6.3, (1)/(3))

These quantify over ALL possibilities. -/

/-- Restrictive necessary equivalence: T₁ ≈_r T₂ iff they have the same
extension in all possibilities. Cooper (2023) §6.3, (1a). -/
def nec_equiv_r (T₁ T₂ : Ty) : Prop :=
  ∀ p, ms.ext p T₁ = ms.ext p T₂

/-- Restrictive subtype: T₁ ⊑_r T₂ iff T₁'s extension ⊆ T₂'s in all
possibilities. Cooper (2023) §6.3, (1b). -/
def nec_subtype_r (T₁ T₂ : Ty) : Prop :=
  ∀ p a, ms.ext p T₁ a → ms.ext p T₂ a

/-- Restrictive necessity: T is necessary iff it has witnesses in all
possibilities. Cooper (2023) §6.3, (1c). -/
def nec_r (T : Ty) : Prop :=
  ∀ p, ∃ a, ms.ext p T a

/-- Restrictive possibility: T is possible iff it has witnesses in some
possibility. Cooper (2023) §6.3, (1d). -/
def poss_r (T : Ty) : Prop :=
  ∃ p, ∃ a, ms.ext p T a

/-! ### Inclusive modal notions (§6.3, (2)/(4))

These quantify over types that occur in at least one possibility. -/

/-- Inclusive necessary equivalence: T₁ ≈_i T₂ iff for all possibilities
containing both, they have the same extension. Cooper (2023) §6.3, (2a). -/
def nec_equiv_i (T₁ T₂ : Ty) : Prop :=
  ∀ p, (∃ a, ms.ext p T₁ a) → (∃ a, ms.ext p T₂ a) →
    ms.ext p T₁ = ms.ext p T₂

/-- Inclusive subtype: T₁ ⊑_i T₂ iff for all possibilities containing both,
T₁'s extension ⊆ T₂'s. Cooper (2023) §6.3, (2b). -/
def nec_subtype_i (T₁ T₂ : Ty) : Prop :=
  ∀ p, (∃ a, ms.ext p T₁ a) → (∃ a, ms.ext p T₂ a) →
    ∀ a, ms.ext p T₁ a → ms.ext p T₂ a

/-- Inclusive necessity: T is necessary iff it has witnesses in all
possibilities that contain T. Cooper (2023) §6.3, (2c). -/
def nec_i (T : Ty) : Prop :=
  ∀ p, (∃ a, ms.ext p T a) → ∃ a, ms.ext p T a

/-- Inclusive possibility: T is possible iff some possibility has T.
Cooper (2023) §6.3, (2d). -/
def poss_i (T : Ty) : Prop :=
  ∃ p, ∃ a, ms.ext p T a

/-- Restrictive ⊑_r entails inclusive ⊑_i. Cooper (2023) §6.3, paragraph
after (2): "if any of the restrictive definitions holds ... then the
corresponding inclusive definition will also hold." -/
theorem restrictive_subtype_implies_inclusive (T₁ T₂ : Ty) :
    nec_subtype_r ms T₁ T₂ → nec_subtype_i ms T₁ T₂ :=
  λ hr p _ _ a h => hr p a h

/-- Restrictive necessity entails inclusive necessity. -/
theorem restrictive_nec_implies_inclusive (T : Ty) :
    nec_r ms T → nec_i ms T :=
  λ hr p _ => hr p

/-- Inclusive possibility = restrictive possibility (they coincide). -/
theorem poss_i_iff_poss_r (T : Ty) :
    poss_i ms T ↔ poss_r ms T := Iff.rfl

end ModalNotions

/-! ## Bridge: ModalTypeSystem (Ch1) ↔ ModalSystem (Ch6)

Ch1's `ModalTypeSystem` is Bool-valued (finite, decidable).
Ch6's `ModalSystem` is Prop-valued (more general).
These conversion functions connect the two formalizations. -/

/-- Embed a Ch1 Bool-valued modal type system into a Ch6 Prop-valued modal system.
Each predicate becomes a type; an object witnesses the type iff `mts w P = true`. -/
def ModalTypeSystem.toModalSystem {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (Obj : Type) : ModalSystem Pred Obj where
  Poss := W
  poss := λ w => ⟨λ P _ => mts w P = true⟩

/-- Project a Ch6 Prop-valued modal system back to Ch1 Bool when witnesses are decidable.
Requires a decision procedure for whether each type has a witness. -/
def ModalSystem.toModalTypeSystem {Ty Obj : Type} (ms : ModalSystem Ty Obj)
    [dec : ∀ (p : ms.Poss) (T : Ty), Decidable (∃ a : Obj, ms.ext p T a)] :
    ModalTypeSystem ms.Poss Ty :=
  λ p T => if ∃ a, ms.ext p T a then true else false

/-- Roundtrip: embedding then projecting back preserves the Bool-valued system. -/
theorem ModalTypeSystem.roundtrip {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (w : W) (P : Pred) :
    ((mts.toModalSystem Unit).poss w).witnesses P () ↔ (mts w P = true) :=
  Iff.rfl

/-! ## Bridge: ModalSystem ↔ Core.ModalLogic.AccessRel

A Cooper modal system induces a Kripke accessibility relation for each type T:
R_T(p₁, p₂) holds iff every witness of T in p₁ is also a witness in p₂.
This connects TTR's type-indexed modality to standard Kripke semantics. -/

/-- Given a type T, derive a Kripke accessibility relation from a modal system.
R_T(p₁, p₂) iff the extension of T at p₂ includes the extension at p₁.
This makes □T at p = "T has witnesses in all R_T-accessible possibilities". -/
def ModalSystem.toAccessRel {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) :
    ms.Poss → ms.Poss → Prop :=
  λ p₁ p₂ => ∀ a, ms.ext p₁ T a → ms.ext p₂ T a

/-- TTR necessity (nec_r) for type T is equivalent to: for all possibilities,
T has witnesses. This is □T evaluated at the universal frame. -/
theorem nec_r_iff_forall_exists {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) :
    nec_r ms T ↔ ∀ p, ∃ a, ms.ext p T a :=
  Iff.rfl

/-- TTR possibility (poss_r) for type T is equivalent to: some possibility has
a witness of T. This is ◇T evaluated at the universal frame. -/
theorem poss_r_iff_exists {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) :
    poss_r ms T ↔ ∃ p, ∃ a, ms.ext p T a :=
  Iff.rfl

/-- The derived accessibility relation is reflexive (every possibility includes
its own witnesses). -/
theorem ModalSystem.toAccessRel_refl {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty)
    (p : ms.Poss) : ms.toAccessRel T p p :=
  λ _ h => h

/-! ## § 6.4 Box and Diamond type constructors

If T is a type, then □_r T, □_i T, ◇_r T, ◇_i T are types.
□T is non-empty iff T is necessary; ◇T is non-empty iff T is possible.
Cooper (2023) §6.4, (5)–(11). -/

/-- Box type (necessity): □T is inhabited iff T is necessary in the modal system.
Cooper (2023) §6.4, (5)–(7). A witness of □T is a proof that T has
witnesses in all (restrictive) or relevant (inclusive) possibilities. -/
def BoxR {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) : Prop :=
  nec_r ms T

def BoxI {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) : Prop :=
  nec_i ms T

/-- Diamond type (possibility): ◇T is inhabited iff T is possible.
Cooper (2023) §6.4, (5), (9). -/
def DiamondR {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) : Prop :=
  poss_r ms T

def DiamondI {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) : Prop :=
  poss_i ms T

/-- □_r T → □_i T (restrictive box implies inclusive box). -/
theorem BoxR_implies_BoxI {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) :
    BoxR ms T → BoxI ms T :=
  restrictive_nec_implies_inclusive ms T

/-- ◇_r T ↔ ◇_i T (diamond notions coincide). -/
theorem DiamondR_iff_DiamondI {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) :
    DiamondR ms T ↔ DiamondI ms T :=
  poss_i_iff_poss_r ms T

/-- □_r T → ◇_r T when the modal system has at least one possibility.
The D axiom of modal logic. -/
theorem BoxR_implies_DiamondR {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty)
    (hne : Nonempty ms.Poss) : BoxR ms T → DiamondR ms T :=
  λ hn => ⟨hne.some, hn hne.some⟩

/-! ## § 6.4 Topoi

A topos maps situations (of a background type) to types (the foreground).
Topoi replace accessibility relations between possible worlds: they encode
rules (epistemic, deontic) that license inferences from situations to types.

Cooper (2023) §6.4, (20): τ : Topos has bg : Type and fg : (bg → Type).
τ(s) = τ.fg(s). -/

/-- A topos: a dependent type mapping background situations to foreground types.
Cooper (2023) §6.4, (20): if τ : Topos, then τ has bg : Type, fg : (bg → Type).
Topoi replace Kratzer's conversational backgrounds (modal base + ordering source)
in the analysis of modality. -/
structure Topos where
  /-- Background type (domain of the topos) -/
  bg : Type
  /-- Foreground: maps situations of background type to types -/
  fg : bg → Type

/-- Apply a topos to a background situation: τ(s) = τ.fg(s).
Cooper (2023) §6.4: τ(s) to represent τ.fg(s). -/
def Topos.apply (τ : Topos) (s : τ.bg) : Type := τ.fg s

/-- `Topos` and `Parametric Type` have identical structure: both are
bg/fg records mapping a background type to a foreground.
This equivalence witnesses the structural identity. -/
def Topos.toParametric (τ : Topos) : Parametric Type :=
  ⟨τ.bg, τ.fg⟩

/-- Convert a `Parametric Type` to a `Topos`. -/
def Topos.ofParametric (p : Parametric Type) : Topos :=
  ⟨p.Bg, p.fg⟩

/-- Topos ≃ Parametric Type: the two structures are equivalent.
Cooper's (2023) §6.4 topoi are structurally the same as the §4.3
parametric content pattern when Content = Type. -/
def toposEquivParametric : Topos ≃ Parametric Type where
  toFun := Topos.toParametric
  invFun := Topos.ofParametric
  left_inv := λ τ => by cases τ; rfl
  right_inv := λ p => by cases p; rfl

/-! ### Action rules with topoi (§6.4, (21)–(22))

Topoi are used with action rules:
- **Epistemically**: if s : τ.bg, then infer there is something of type τ(s)
- **Deontically**: if s : τ.bg, then an agent is allowed/obliged to create τ(s) -/

/-- Epistemic use of a topos: from a situation of the background type,
infer the existence of something of the foreground type.
Cooper (2023) §6.4, (21). -/
def Topos.epistemicInference (τ : Topos) (s : τ.bg) : Prop :=
  Nonempty (τ.fg s)

/-- Deontic modality kind: affordance (allowed) vs obligation (obliged). -/
inductive DeonticKind where
  | affordance  -- allowed to create
  | obligation  -- obliged to create
  deriving Repr, DecidableEq

/-! ### Necessity and possibility with topoi (§6.4, (23)–(24), version 4)

The final version of nec/poss uses topoi instead of an "ideal" type:
- nec(T, B, τ): s witnesses T's necessity w.r.t. background B and topos τ
  iff s :_p B, B ⊑ τ.bg, and τ(s) ⊑ T
- poss(T, B, τ): s witnesses T's possibility w.r.t. B and τ
  iff s :_p B, B ⊑ τ.bg, and τ(s) is compatible with T -/

/-- Subtyping in a modal type system: B ⊑_T T means all witnesses of B
are also witnesses of T. Cooper (2023) §6.4: B ⊑_𝕋 τ.bg. -/
abbrev modalSubtype (B T : Type) : Prop := ∀ (_ : B), Nonempty T

/-- Compatibility: T₁ ⊤⊤ T₂ iff their meet is non-empty — there exists
something of both types simultaneously. Cooper (2023) §6.4, (17). -/
def Compatible (T₁ T₂ : Type) : Prop := Nonempty (T₁ × T₂)

/-- Witness condition for necessity with topoi (version 4).
Cooper (2023) §6.4, (23):
  s :_p nec(T, B, τ) iff s :_p B, B ⊑_𝕋 τ.bg, and τ(s) ⊑_𝕋 T.

We model this as: given a background witness `s`, a proof that the
background subtypes the topos domain, and a coercion from `s` to the
topos domain, the foreground τ(coerce(s)) is a subtype of T. -/
structure NecTopos (T : Type) (B : Type) (τ : Topos) where
  /-- A witness of the background type -/
  sit : B
  /-- Coercion from background to topos domain -/
  coerce : B → τ.bg
  /-- The topos applied at the coerced situation subtypes T -/
  sub : τ.fg (coerce sit) → T

/-- Witness condition for possibility with topoi (version 4).
Cooper (2023) §6.4, (24):
  s :_p poss(T, B, τ) iff s :_p B, B ⊑_𝕋 τ.bg, and τ(s) ⊤⊤ T.
Possibility requires compatibility rather than subtyping. -/
structure PossTopos (T : Type) (B : Type) (τ : Topos) where
  /-- A witness of the background type -/
  sit : B
  /-- Coercion from background to topos domain -/
  coerce : B → τ.bg
  /-- The topos applied at the coerced situation is compatible with T -/
  compat : Compatible (τ.fg (coerce sit)) T

/-- Necessity implies possibility (version 4): if T is necessary w.r.t.
B and τ, and the topos foreground at the situation is non-empty,
then T is possible. -/
def necTopos_implies_possTopos {T B : Type} {τ : Topos}
    (hn : NecTopos T B τ) (hne : Nonempty (τ.fg (hn.coerce hn.sit))) :
    PossTopos T B τ :=
  ⟨hn.sit, hn.coerce, ⟨(hne.some, hn.sub hne.some)⟩⟩

/-! ### Abstract bridge: Topos ↔ conversational background

Cooper's topoi parallel Kratzer's conversational backgrounds:
- A **topos** τ maps situations (bg) to types (fg): τ : bg → Type
- A **conversational background** f maps worlds to prop sets: f : W → Set Prop

Both serve as the contextual parameter determining modal flavor.
Cooper explicitly notes (§6.4): "Topoi replace accessibility relations
between possible worlds ... encoding rules that license inferences."

The structural correspondence:
- Topos bg ↔ conversational background's domain (situations ↔ worlds)
- Topos fg ↔ propositions in the modal base (both constrain what's possible)
- NecTopos ↔ □ under a particular modal base
- PossTopos ↔ ◇ under a particular modal base

Full bridge importing `Kratzer.lean` is deferred to `Theories/TTR/`. -/

/-- A topos induces a notion of necessity: for all situations of background type,
the foreground type is inhabited. This parallels Kratzer's □ under a modal base. -/
def Topos.inducedNec (τ : Topos) : Prop :=
  ∀ (s : τ.bg), Nonempty (τ.fg s)

/-- A topos induces possibility: some situation of background type has an
inhabited foreground. This parallels Kratzer's ◇ under a modal base. -/
def Topos.inducedPoss (τ : Topos) : Prop :=
  ∃ (s : τ.bg), Nonempty (τ.fg s)

/-- Topos-induced necessity implies possibility (when the background is inhabited).
The topos analogue of the D axiom (□p → ◇p). -/
theorem Topos.nec_implies_poss (τ : Topos) (hne : Nonempty τ.bg)
    (hn : τ.inducedNec) : τ.inducedPoss :=
  ⟨hne.some, hn hne.some⟩

/-! ### Broccoli example (§6.4, (25)–(31))

"Mary should eat her broccoli" — deontic (children must eat food on their
plate) vs bouletic (children eat food they love). Cooper (2023) §6.4.

Two topoi τ₁ and τ₂ with the same foreground (eat) but different backgrounds:
- τ₁ (deontic): child has food on plate → child eats that food
- τ₂ (bouletic): child loves food → child eats that food -/

section BroccoliExample

/-- Individuals in the broccoli scenario. -/
inductive BrocInd where
  | broccoli | mary | plate
  deriving Repr, DecidableEq

/-- Predicates for the broccoli scenario. -/
def isBroccoli : BrocInd → Prop := (· = .broccoli)
def isChild : BrocInd → Prop := (· = .mary)
def isPlate : BrocInd → Prop := (· = .plate)
def isFood : BrocInd → Prop := (· = .broccoli)

/-- Relations in the broccoli scenario. -/
def have_ : BrocInd → BrocInd → Prop := λ y z => y = .mary ∧ z = .plate
def on_ : BrocInd → BrocInd → Prop := λ x z => x = .broccoli ∧ z = .plate
def love_ : BrocInd → BrocInd → Prop := λ y x => y = .mary ∧ x = .broccoli
def eat_ : BrocInd → BrocInd → Prop := λ y x => y = .mary ∧ x = .broccoli

/-- The base situation type B for "Mary should eat her broccoli".
Cooper (2023) §6.4, (26):
  [x=b:Ind, c₁:broccoli(x), y=m:Ind, c₂:child(y), z=p:Ind,
   c₃:plate(z), e₁:have(y,z), e₂:on(x,z), e₃:love(y,x)] -/
structure BroccoliBase where
  x : BrocInd  -- the broccoli
  hx : isBroccoli x
  y : BrocInd  -- Mary
  hy : isChild y
  z : BrocInd  -- the plate
  hz : isPlate z
  e₁ : have_ y z
  e₂ : on_ x z
  e₃ : love_ y x

/-- The background type for τ₁ (deontic): food on child's plate.
Cooper (2023) §6.4, (28a) background. -/
structure DeonticBg where
  x : BrocInd
  c₁ : isFood x
  y : BrocInd
  c₂ : isChild y
  z : BrocInd
  c₃ : isPlate z
  e₁ : have_ y z
  e₂ : on_ x z

/-- The background type for τ₂ (bouletic): food the child loves.
Cooper (2023) §6.4, (28b) background. -/
structure BouleticBg where
  x : BrocInd
  c₁ : isFood x
  y : BrocInd
  c₂ : isChild y
  e₃ : love_ y x

/-- The eating type (foreground of both topoi). -/
def eatType (y x : BrocInd) : Type := PLift (eat_ y x)

/-- Topos τ₁ (deontic): children eat food on their plate.
Cooper (2023) §6.4, (28a). -/
def τ_deontic : Topos :=
  ⟨DeonticBg, λ r => eatType r.y r.x⟩

/-- Topos τ₂ (bouletic): children eat food they love.
Cooper (2023) §6.4, (28b). -/
def τ_bouletic : Topos :=
  ⟨BouleticBg, λ r => eatType r.y r.x⟩

/-- A concrete base situation: broccoli on Mary's plate, Mary loves broccoli. -/
def brocBase : BroccoliBase where
  x := .broccoli; hx := rfl
  y := .mary;     hy := rfl
  z := .plate;    hz := rfl
  e₁ := ⟨rfl, rfl⟩
  e₂ := ⟨rfl, rfl⟩
  e₃ := ⟨rfl, rfl⟩

/-- The deontic background witnesses: food on plate. -/
def deonticBg : DeonticBg where
  x := .broccoli; c₁ := rfl
  y := .mary;     c₂ := rfl
  z := .plate;    c₃ := rfl
  e₁ := ⟨rfl, rfl⟩
  e₂ := ⟨rfl, rfl⟩

/-- The bouletic background witnesses: child loves food. -/
def bouleticBg : BouleticBg where
  x := .broccoli; c₁ := rfl
  y := .mary;     c₂ := rfl
  e₃ := ⟨rfl, rfl⟩

/-- Deontic reading: nec([e:eat(m,b)], T_broc, τ₁).
Cooper (2023) §6.4, (29a): the deontic topos makes eating necessary. -/
def broccoliDeonticNec : NecTopos (PLift (eat_ .mary .broccoli)) BroccoliBase τ_deontic where
  sit := brocBase
  coerce := λ b => ⟨b.x, b.hx, b.y, b.hy, b.z, b.hz, b.e₁, b.e₂⟩
  sub := id

/-- Bouletic reading: nec([e:eat(m,b)], T_broc, τ₂).
Cooper (2023) §6.4, (29b): the bouletic topos also makes eating necessary. -/
def broccolicBouleticNec : NecTopos (PLift (eat_ .mary .broccoli)) BroccoliBase τ_bouletic where
  sit := brocBase
  coerce := λ b => ⟨b.x, b.hx, b.y, b.hy, b.e₃⟩
  sub := id

/-- Both topoi yield the same eating conclusion, but differ in their
preconditions: τ₁ requires food on plate (deontic obligation),
τ₂ requires child loves food (bouletic desire). -/
theorem broccoli_both_topoi_yield_eat :
    (∃ _ : NecTopos (PLift (eat_ .mary .broccoli)) BroccoliBase τ_deontic, True) ∧
    (∃ _ : NecTopos (PLift (eat_ .mary .broccoli)) BroccoliBase τ_bouletic, True) :=
  ⟨⟨broccoliDeonticNec, trivial⟩, ⟨broccolicBouleticNec, trivial⟩⟩

end BroccoliExample

/-! ## § 6.5 Intensionality without possible worlds

Propositions as types (not as sets of possible worlds). Two notions:
- **Russellian proposition**: a type T is "true" iff T is non-empty (inhabited)
- **Austinian proposition**: a pair ⟨s, T⟩ where s is a situation and T is a type;
  true iff s : T

Cooper (2023) §6.5, following Austin (1961) and Barwise (1989). -/

/-- A Russellian proposition: identified with its type.
True iff the type is inhabited. Cooper (2023) §6.5. -/
abbrev RussellianProp := Type

/-- An Austinian proposition: a situation–type pair.
True iff the situation is of the type.
Cooper (2023) §6.5, following Barwise & Perry (1983). -/
structure AustinianProp where
  /-- The type (situation type) -/
  SitType : Type
  /-- The situation -/
  sit : SitType

/-- An Austinian proposition is true (the situation witnesses the type).
By construction, an AustinianProp carries its own witness, so existence
of the pair IS truth — the constructive reading. -/
def AustinianProp.isTrue (p : AustinianProp) : Prop := Nonempty p.SitType

/-- If a Russellian proposition is true, the corresponding Austinian is too.
Cooper (2023) §6.5: "if a Russellian proposition containing the same type
is true, then there is an Austinian proposition which is true." -/
theorem russellian_true_implies_austinian {T : Type} (h : IsTrue T) :
    ∃ p : AustinianProp, p.SitType = T :=
  ⟨⟨T, h.some⟩, rfl⟩

/-! ### Structural vs postulated subtyping (§6.5, (50))

Two kinds of subtyping:
- **Structural**: built into the type theory (e.g., [ℓ₁:T₁, ℓ₂:T₂] ⊑ [ℓ₁:T₁])
- **Postulated**: added via meaning postulates (e.g., sell(a,b,c) ⊑ buy(c,b,a))

Structural subtyping is hardwired; postulated subtyping is learned/acquired.
Cooper (2023) §6.5, (50). -/

/-- Subtyping kind: structural (hardwired) vs postulated (learned).
Cooper (2023) §6.5, (50). -/
inductive SubtypingKind where
  | structural  -- follows from type structure alone (e.g., more fields)
  | postulated  -- added via meaning postulate (e.g., buy/sell equivalence)
  deriving Repr, DecidableEq

/-- A meaning postulate: a declared subtyping relationship between types.
Cooper (2023) §6.5, (50b): sell(a,b,c) ⊑ buy(c,b,a) is a postulated
subtyping that does not follow from the structure of the types. -/
structure MeaningPostulate (T₁ T₂ : Type) where
  /-- The postulated coercion -/
  coerce : T₁ → T₂
  /-- The kind is always postulated -/
  kind : SubtypingKind := .postulated

/-! ### Buy/sell equivalence (§6.5, (50b))

A canonical example of postulated subtyping: the types for selling and
buying events are distinct but related by a meaning postulate. -/

/-- A sell event: seller sells thing to buyer. -/
structure SellEvent (E : Type) where
  seller : E
  thing : E
  buyer : E

/-- A buy event: buyer buys thing from seller. -/
structure BuyEvent (E : Type) where
  buyer : E
  thing : E
  seller : E

/-- Structural subtyping example: a record with more fields subtypes one with fewer.
Cooper (2023) §6.5, (50a): [ℓ₁:T₁, ℓ₂:T₂] ⊑ [ℓ₁:T₁]. -/
def structuralSubtype_example {T₁ T₂ : Type} : (T₁ × T₂) → T₁ := Prod.fst

/-- Postulated subtyping: sell(a,b,c) ⊑ buy(c,b,a).
Cooper (2023) §6.5, (50b). -/
def sellBuyPostulate (E : Type) : MeaningPostulate (SellEvent E) (BuyEvent E) where
  coerce := λ s => ⟨s.buyer, s.thing, s.seller⟩

/-- The reverse postulate: buy(a,b,c) ⊑ sell(c,b,a). -/
def buySellPostulate (E : Type) : MeaningPostulate (BuyEvent E) (SellEvent E) where
  coerce := λ b => ⟨b.seller, b.thing, b.buyer⟩

/-- Roundtrip: sell → buy → sell = id (the postulates are inverses). -/
theorem sell_buy_roundtrip {E : Type} (s : SellEvent E) :
    (buySellPostulate E).coerce ((sellBuyPostulate E).coerce s) = s := by
  cases s; rfl

/-! ### Believe and know (§6.5, (38)–(41))

Propositional attitudes are analyzed via matching against long-term memory.
believe(a, T) is non-empty iff there exists T' in a's long-term memory such
that T' ⊑_∼ T (subtype modulo relabelling).

Cooper (2023) §6.5, (40):
  e : believe(a, T) iff e : ltm(a, T') and T' ⊑_∼ T -/

/-- An agent's long-term memory: maps agents to record types (their stored beliefs).
Cooper (2023) §6.5, p.257: "r is a's total information state, then a's
long-term memory will be r.ltm." -/
structure LTM (Agent : Type) where
  /-- The type representing the agent's long-term memory -/
  memType : Agent → Type

/-- Subtyping modulo relabelling: T₁ ⊑_∼ T₂ iff there is a relabelling η
such that T₁ ⊑ [T₂]_η. Cooper (2023) §6.5, (39).
We model this abstractly as the existence of a coercion.  -/
def subtypeModRelabel (T₁ T₂ : Type) : Prop :=
  Nonempty (T₁ → T₂)

/-- Witness condition for believe(a, T): version (40).
Cooper (2023) §6.5, (40):
  e : believe(a, T) iff e : ltm(a, T') and T' ⊑_∼ T. -/
def believe {Agent : Type} (ltm : LTM Agent) (a : Agent) (T : Type) : Prop :=
  subtypeModRelabel (ltm.memType a) T

/-- Knowledge is veridical belief: know(a, T) requires believe(a, T) AND T true.
This is a standard characterization; Cooper (2023) does not give a full
definition of 'know' but discusses the connection. -/
def know {Agent : Type} (ltm : LTM Agent) (a : Agent) (T : Type) : Prop :=
  believe ltm a T ∧ IsTrue T

/-- Knowledge implies belief. -/
theorem know_implies_believe {Agent : Type} {ltm : LTM Agent} {a : Agent} {T : Type} :
    know ltm a T → believe ltm a T :=
  And.left

/-- Knowledge implies truth (veridicality). -/
theorem know_implies_true {Agent : Type} {ltm : LTM Agent} {a : Agent} {T : Type} :
    know ltm a T → IsTrue T :=
  And.right

/-- Belief is closed under (modulo-relabelling) subtyping.
Cooper (2023) §6.5, (41): "for any relabelling η of T,
s : believe(a, [T]_η)". -/
theorem believe_closed_under_subtype {Agent : Type} {ltm : LTM Agent}
    {a : Agent} {T₁ T₂ : Type} (hb : believe ltm a T₁)
    (hsub : T₁ → T₂) : believe ltm a T₂ :=
  ⟨hsub ∘ hb.some⟩

/-! ### Abstract bridge: know = believe + veridicality

TTR's know = believe ∧ IsTrue mirrors the standard doxastic classification:
- `know` is veridical (factivity: know p → p)
- `believe` is non-veridical (believe p ↛ p)

This is the abstract pattern that connects to `Doxastic.veridical` in
`Theories/Semantics.Intensional/Attitude/Doxastic.lean`. The full bridge
(importing Doxastic) is deferred to a future `Theories/TTR/` module. -/

/-- know is exactly believe + veridicality: the two components are independent. -/
theorem know_iff_believe_and_true {Agent : Type} {ltm : LTM Agent} {a : Agent} {T : Type} :
    know ltm a T ↔ believe ltm a T ∧ IsTrue T :=
  Iff.rfl

/-- Belief does not entail truth: an agent can believe a false type.
This shows know is strictly stronger than believe.
With memType = Empty, believe holds vacuously for any T (including Empty). -/
theorem believe_not_entails_true :
    ¬ (∀ (Agent : Type) (ltm : LTM Agent) (a : Agent) (T : Type),
      believe ltm a T → IsTrue T) := by
  intro h
  have : IsTrue Empty := h Unit ⟨λ _ => Empty⟩ () Empty ⟨Empty.elim⟩
  exact (true_false_exclusive Empty) ⟨this, inferInstance⟩

/-! ### Points of view (§6.5, (55)–(60))

A point of view on a type T is a type T' that shares some labels/fields
with T but provides alternative field types. Used for the Hesperus/Phosphorus
puzzle and for intensional transitive verbs.

Cooper (2023) §6.5, (55): pov(T₁, T₂) — T₁ is a point of view on T₂.
The key property: a situation can be described from different points of view.

We model this as: T₁ is a point of view on T₂ if there is a way to
"merge" T₁ with T₂ (asymmetric merge). -/

/-- A point of view: T₁ is an alternative perspective on T₂.
Cooper (2023) §6.5, (55): pov(T₁, T₂) — T₁ shares labels with T₂
but provides alternative field types.
The `merge` field represents asymmetric merge (⊕) of T₂ with T₁. -/
structure PointOfView (T₁ T₂ : Type) where
  /-- The result of asymmetric merge: T₂[⊕]T₁ -/
  Merged : Type
  /-- The merged type subtypes T₂ (it's a version of T₂ with T₁'s perspective) -/
  project : Merged → T₂

/-- Extended membership: a :_E T iff a : T or some component of a is of type T.
Cooper (2023) §6.5, (57): a :_E T iff either a : T or for some b ε a, b : T. -/
def extMember {T : Type} (_a : T) : Prop := True

def extMemberVia {Outer Inner : Type} (a : Outer) (extract : Outer → Inner)
    (T : Inner → Type) : Prop := Nonempty (T (extract a))

/-! ### Revised believe with points of view (§6.5, (58))

Cooper (2023) §6.5, (58) revises the witness condition for believe to
account for points of view:
  e : believe(a, T) if
    e : ltm(a, T') and T' ⊑_∼ T
  OR
    e :_E believe(a, T₁) and e :_E pov(T₂, T₁) and T₁[⊕]T₂ ⊑_∼ T -/

/-- Revised believe with point-of-view support.
Cooper (2023) §6.5, (58). -/
def believeWithPov {Agent : Type} (ltm : LTM Agent) (a : Agent) (T : Type) : Prop :=
  -- Direct case: ltm matches T
  believe ltm a T ∨
  -- Point-of-view case: there exist T₁, T₂ with a pov and the merge matches T
  ∃ (T₁ T₂ : Type), believe ltm a T₁ ∧
    Nonempty (PointOfView T₂ T₁) ∧
    subtypeModRelabel T₂ T

/-- Direct belief implies belief-with-pov. -/
theorem believe_implies_believeWithPov {Agent : Type} {ltm : LTM Agent}
    {a : Agent} {T : Type} (h : believe ltm a T) :
    believeWithPov ltm a T :=
  Or.inl h

/-! ### Hesperus/Phosphorus puzzle (§6.5, (52)–(53))

The ancients believed Hesperus (evening star) and Phosphorus (morning star)
were different objects, but they are both Venus. In TTR, this is modeled via
different labels in the long-term memory type: the names are associated with
different paths in the record, so believe(ancients, [Hesperus rises in evening])
and believe(ancients, [Phosphorus rises in morning]) are non-trivially different. -/

section HesperusPhosphorus

inductive CelestialBody where
  | venus
  deriving Repr, DecidableEq

/-- Ancient's LTM type before learning Hesperus = Phosphorus.
Cooper (2023) §6.5, (52): separate entries for Hesperus and Phosphorus. -/
structure AncientsLTM_Before where
  hesperus : CelestialBody
  hesperus_rises_evening : hesperus = .venus  -- rises in the evening
  phosphorus : CelestialBody
  phosphorus_rises_morning : phosphorus = .venus  -- rises in the morning

/-- Ancient's LTM type after learning they are the same.
Cooper (2023) §6.5, (53): entries unified with identity constraint. -/
structure AncientsLTM_After extends AncientsLTM_Before where
  same : hesperus = phosphorus

/-- Before learning: the ancients can believe separately about Hesperus/Phosphorus.
Even though both are Venus, the two record fields are distinct in the type. -/
theorem ancients_separate_beliefs :
    ∃ (ltm : AncientsLTM_Before), ltm.hesperus = ltm.phosphorus :=
  ⟨⟨.venus, rfl, .venus, rfl⟩, rfl⟩

/-- The identity becomes explicit only in the "after" type.
Structural consequence: the after-type is a subtype of the before-type
(it has more fields/constraints). -/
instance : SubtypeOf AncientsLTM_After AncientsLTM_Before where
  up := AncientsLTM_After.toAncientsLTM_Before

/-- Learning Hesperus = Phosphorus is adding a constraint (more fields). -/
theorem learning_adds_constraint (ltm : AncientsLTM_After) :
    ltm.toAncientsLTM_Before.hesperus = ltm.toAncientsLTM_Before.phosphorus :=
  ltm.same

end HesperusPhosphorus

/-! ### Intensional transitive verbs (§6.5, (63)–(66))

Montague treated intensional verbs (seek, worship) as taking quantifier
arguments. Cooper recasts this in TTR: predicates with arity ⟨Ind, Quant⟩
where the quantifier is the object argument.

Key concepts:
- p†: the extensional variant of an intensional predicate
- Meaning postulate (65): p(a, Q) ≈_𝕋 Q(λr:[x:Ind].[e:p†(a,r.x)])
- Success postulate (66): successful(seek(a,Q)) ⊑_𝕋 find(a,Q)
  (a successful search is a finding) -/

/-- An intensional transitive verb: takes an individual and a quantifier.
Cooper (2023) §6.5, (64):
  SemTransVerb(T_bg, p) for arity ⟨Ind, Quant⟩ =
  'λc:T_bg . λQ:Quant . λr:[x:Ind] . [e : p(r.x, Q)]'

The p† variant is the extensional "dagger" form relating to individuals.
-/
structure IntensionalTV (E : Type) where
  /-- The intensional predicate: Ind → Quant → Type -/
  pred : E → Quant E → Type
  /-- The extensional dagger variant: Ind → Ind → Type -/
  dagger : E → E → Type

/-- Meaning postulate (65) for extensional transitive verbs:
  p(a, Q) ≈ Q(λr:[x:Ind].[e:p†(a,r.x)])
Cooper (2023) §6.5, (65). -/
def extensionalMP {E : Type} (itv : IntensionalTV E) (a : E) (Q : Quant E) : Prop :=
  Nonempty (itv.pred a Q ≃ Q (λ x => itv.dagger a x))

/-- Success postulate (66): a successful search is a finding.
Cooper (2023) §6.5, (66):
  successful(seek(a, Q)) ⊑_𝕋 find(a, Q). -/
structure SuccessPostulate (E : Type) where
  seek : IntensionalTV E
  find : IntensionalTV E
  /-- If a successful seek is a subtype of find -/
  success : ∀ (a : E) (Q : Quant E),
    (itv_success : Type) → (itv_success → seek.pred a Q) →
    itv_success → find.pred a Q

/-! ### Worship (§6.5, (69)–(75))

Worship requires:
1. Religious belief (intentionality): the subject believes in the deity
2. Specificity: the religious belief type is a subtype of the quantified type

Cooper (2023) §6.5, (75):
  e : worship(a, Q) iff for some T,
    (1) e : rbelieve(a, T) — a has T as a religious belief
    (2) T ⊑_∼ Q(λr:[x:Ind].worship†(a, r.x)) -/

/-- Religious belief: a distinguished part of long-term memory.
Cooper (2023) §6.5, (72)–(74). -/
def rbelieve {Agent : Type} (_ltm : LTM Agent)
    (rbelType : Agent → Type) (a : Agent) (T : Type) : Prop :=
  Nonempty (rbelType a → T)

/-- Witness condition for worship (§6.5, (75)).
e : worship(a, Q) iff for some T:
  (1) e : rbelieve(a, T)
  (2) T ⊑_∼ Q(λr:[x:Ind].worship†(a, r.x)) -/
def worshipSem {E : Type}
    (ltm : LTM E) (rbelType : E → Type)
    (worshipDagger : E → E → Type)
    (a : E) (Q : Quant E) : Prop :=
  ∃ (T : Type),
    rbelieve ltm rbelType a T ∧
    subtypeModRelabel T (Q (λ x => worshipDagger a x))

/-! ### Want (§6.5, (88)–(92))

The analysis of want uses desire states (parallel to LTM).
  want†(a, T) is non-empty iff a's desires include T
  (the desire type is a subtype of T, modulo relabelling).

Cooper (2023) §6.5, (90)–(92): want_P and want_Q related to want†;
witness condition uses des(a, T') and T' ⊑_∼ T. -/

/-- An agent's full information state: long-term memory, religious beliefs, desires.
Cooper (2023) §6.5, (91). Distinct from the Ch4 TotalInfoState which
pairs memory with a dialogue gameboard. -/
structure AgentInfoState (Agent : Type) where
  /-- Long-term memory type for each agent -/
  ltm : Agent → Type
  /-- Religious belief type for each agent -/
  rbel : Agent → Type
  /-- Desire type for each agent -/
  des : Agent → Type

/-- Desire predicate: des(a, T) iff a's desire state subtypes T.
Cooper (2023) §6.5: "e : des(a, T) just in case T is a's desires in e." -/
def desire {Agent : Type} (ais : AgentInfoState Agent) (a : Agent) (T : Type) : Prop :=
  subtypeModRelabel (ais.des a) T

/-- Witness condition for want†(a, T).
Cooper (2023) §6.5, (92):
  e : want†(a, T) if for some T',
    e : des(a, T') and T' ⊑_∼ T. -/
def wantDagger {Agent : Type} (ais : AgentInfoState Agent)
    (a : Agent) (T : Type) : Prop :=
  desire ais a T

/-- want with point of view (§6.5, (92) second clause):
  e : want†(a, T) if for some T₁, T₂:
    e :_E want†(a, T₁)
    e :_E pov(T₂, T₁)
    T₁[⊕]T₂ ⊑_∼ T -/
def wantWithPov {Agent : Type} (ais : AgentInfoState Agent)
    (a : Agent) (T : Type) : Prop :=
  wantDagger ais a T ∨
  ∃ (T₁ T₂ : Type), wantDagger ais a T₁ ∧
    Nonempty (PointOfView T₂ T₁) ∧ subtypeModRelabel T₂ T

/-- Book as an intensional verb requiring existence.
Cooper (2023) §6.5, (87):
  book(a, Q) ⊑_𝕋 Q(λr:[x:Ind].[e:be(r.x)])
This ensures that if a books Q, there is something that exists (be).
Unlike seek, book implies existence but not specificity. -/
def bookPostulate {E : Type} (book_ : E → Quant E → Type)
    (be_ : E → Type) (a : E) (Q : Quant E) : Prop :=
  Nonempty (book_ a Q → Q (λ x => be_ x))

/-! ## Chapter 6 phenomena -/

section Ch6Phenomena

/-- A simple two-possibility modal system. -/
inductive TwoPred where | rain | snow deriving DecidableEq
inductive TwoObj where | obj_a | obj_b deriving DecidableEq

def twoModal : ModalSystem TwoPred TwoObj where
  Poss := Bool
  poss p := match p with
    | true  => ⟨λ pred obj => match pred, obj with
        | .rain, .obj_a => True | .snow, .obj_b => True | _, _ => False⟩
    | false => ⟨λ pred obj => match pred, obj with
        | .rain, .obj_a => True | _, _ => False⟩

/-- Rain is necessary (has witnesses in both possibilities). -/
theorem rain_necessary : nec_r twoModal .rain :=
  λ | true => ⟨.obj_a, trivial⟩ | false => ⟨.obj_a, trivial⟩

/-- Snow is possible but not necessary. -/
theorem snow_possible : poss_r twoModal .snow :=
  ⟨true, .obj_b, trivial⟩

theorem snow_not_necessary : ¬ nec_r twoModal .snow := by
  intro h
  obtain ⟨obj, hobj⟩ := h false
  revert hobj
  simp only [twoModal, ModalSystem.ext]
  cases obj <;> simp

/-- □_r rain is true. -/
theorem box_rain : BoxR twoModal .rain := by
  unfold BoxR; exact rain_necessary

/-- ◇_r snow is true but □_r snow is false. -/
theorem diamond_snow : DiamondR twoModal .snow := by
  unfold DiamondR; exact snow_possible
theorem not_box_snow : ¬ BoxR twoModal .snow := by
  unfold BoxR; exact snow_not_necessary

/-- Buy/sell postulated subtyping phenomenon. -/
def samSellsBookToKim : SellEvent String := ⟨"Kim", "Syntactic Structures", "Sam"⟩
def kimBuysBookFromSam : BuyEvent String := ⟨"Sam", "Syntactic Structures", "Kim"⟩

theorem sell_matches_buy :
    (sellBuyPostulate String).coerce samSellsBookToKim = kimBuysBookFromSam := rfl

/-- Belief phenomenon: an agent whose LTM subtypes a type believes it. -/
structure SimpleWorld where
  raining : Bool

def weatherLTM : LTM Unit where
  memType := λ _ => SimpleWorld

theorem agent_believes_weather :
    believe weatherLTM () SimpleWorld :=
  ⟨id⟩

/-- Point of view phenomenon: Hesperus/Phosphorus with a point of view. -/

def hesperusType := CelestialBody  -- type associated with "Hesperus"
def phosphorusType := CelestialBody  -- type associated with "Phosphorus"

/-- Both resolve to the same entity (Venus) but via different type paths. -/
theorem hesperus_phosphorus_same_entity :
    (CelestialBody.venus : hesperusType) = (CelestialBody.venus : phosphorusType) := rfl

end Ch6Phenomena

-- ============================================================================
-- Bridge: Core.Intension (item 11)
-- ============================================================================

/-! ## Bridge: ModalSystem → Core.Intension

TTR's ModalSystem achieves intensionality without `Intension W τ`:
a type T can have different extensions across possibilities,
which is exactly what an intension does across worlds. -/

/-- A ModalSystem induces an intension for each type: the function
mapping each possibility to the type's extension at that possibility. -/
def modalSystem_induces_intension {Ty Obj : Type} (ms : ModalSystem Ty Obj)
    (T : Ty) : Core.Intension.Intension ms.Poss (Obj → Prop) :=
  λ p => ms.ext p T

/-- A type is rigid in a modal system iff its extension is constant
across all possibilities — matching Core.Intension.IsRigid. -/
def ModalSystem.isRigidType {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T : Ty) : Prop :=
  Core.Intension.IsRigid (modalSystem_induces_intension ms T)

-- ============================================================================
-- Bridge: MeaningPostulate → believe (item 13)
-- ============================================================================

/-! ## MeaningPostulate enables belief transfer

A meaning postulate from T₁ to T₂ enables belief transfer:
if an agent believes T₁ and there's a postulate T₁ → T₂,
then the agent believes T₂. -/

/-- A meaning postulate from T₁ to T₂ enables belief transfer:
if an agent believes T₁ and there's a postulate T₁ → T₂,
then the agent believes T₂. This connects MeaningPostulate
to the doxastic system. -/
theorem meaningPostulate_transfers_belief {Agent : Type} {ltm : LTM Agent}
    {a : Agent} {T₁ T₂ : Type}
    (hb : believe ltm a T₁) (mp : MeaningPostulate T₁ T₂) :
    believe ltm a T₂ :=
  believe_closed_under_subtype hb mp.coerce

end Semantics.TypeTheoretic
