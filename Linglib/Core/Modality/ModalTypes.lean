import Linglib.Core.Register

/-!
# Modal Typological Types

Theory-neutral vocabulary for cross-linguistic modal typology: `ModalForce`,
`ModalFlavor`, `ForceFlavor`, `ModalItem`, `ConcordType`, `ModalDecomposition`.

These types classify modal meanings along two independent dimensions — force
(quantificational strength) and flavor (contextual source) — following
@cite{kratzer-1981} and @cite{imel-guo-steinert-threlkeld-2026}.

**Separated from `Core.Logic.ModalLogic`** because Kripke frames and frame
correspondence are pure mathematical logic, while force/flavor classification
is linguistic typology. The two are connected (Kripke semantics *interprets*
force-flavor pairs) but conceptually independent.

## What belongs here vs. `Core.Logic.ModalLogic`

- **Here** (`Core.Modality`): `ModalForce`, `ModalFlavor`, `ForceFlavor`,
  `ModalItem`, `ConcordType`, `ModalDecomposition` — linguistic classification
  of modal meanings.
- **There** (`Core.ModalLogic`): `AccessRel`, `kripkeEval`, frame conditions
  (`Refl`, `Serial`, `Trans`, `Symm`, `Eucl`), correspondence theorems,
  the lattice of normal modal logics — mathematical semantics.
-/

namespace Core.Modality

-- ============================================================================
-- §1. Modal Force
-- ============================================================================

/-- Modal force: necessity (□), weak necessity (□w), or possibility (◇).
    @cite{von-fintel-iatridou-2008}, @cite{agha-jeretic-2026}.

    Weak necessity ("ought", "should") sits between □ and ◇ in strength:
    □φ → □wφ → ◇φ. The nature of this intermediate force is debated:

    - @cite{von-fintel-iatridou-2008}: same ∀ quantifier as strong necessity
      but over a refined (smaller) set of best worlds (domain restriction).
    - Rubinstein (2014): fundamentally comparative meaning.
    - @cite{agha-jeretic-2022}: non-quantificational (plural predication).

    Weak necessity has no clean dual in this 3-point space: domain refinement
    weakens ∀ but strengthens ∃ (@cite{agha-jeretic-2026} §2.4). -/
inductive ModalForce where
  | necessity
  | weakNecessity
  | possibility
  deriving DecidableEq, Repr, Inhabited

instance : LawfulBEq ModalForce where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString ModalForce where
  toString | .necessity => "□" | .weakNecessity => "□w" | .possibility => "◇"

/-- Classical dual: □ ↔ ◇. Weak necessity maps to possibility as a
    stipulated default — no theoretically motivated dual for □w exists
    in this 3-point space (@cite{agha-jeretic-2026} §2.4: "the notion
    of a possibility counterpart to weak necessity has not received
    much attention"). -/
def ModalForce.dual : ModalForce → ModalForce
  | .necessity => .possibility
  | .weakNecessity => .possibility
  | .possibility => .necessity

@[simp] theorem ModalForce.dual_dual_necessity : ModalForce.necessity.dual.dual = .necessity := rfl
@[simp] theorem ModalForce.dual_dual_possibility : ModalForce.possibility.dual.dual = .possibility := rfl

/-- All modal forces. -/
def ModalForce.all : List ModalForce := [.necessity, .weakNecessity, .possibility]

/-- Strength ordering on modal force: □ ≥ □w ≥ ◇.
    `f₁.atLeastAsStrong f₂` iff an f₁-claim is at least as strong as an f₂-claim.
    @cite{von-fintel-iatridou-2008}: must φ → ought φ → can φ. -/
def ModalForce.atLeastAsStrong : ModalForce → ModalForce → Bool
  | .necessity, _ => true
  | .weakNecessity, .weakNecessity | .weakNecessity, .possibility => true
  | .possibility, .possibility => true
  | _, _ => false

theorem ModalForce.atLeastAsStrong_refl (f : ModalForce) :
    f.atLeastAsStrong f = true := by cases f <;> rfl

theorem ModalForce.atLeastAsStrong_trans (f₁ f₂ f₃ : ModalForce)
    (h₁ : f₁.atLeastAsStrong f₂ = true) (h₂ : f₂.atLeastAsStrong f₃ = true) :
    f₁.atLeastAsStrong f₃ = true := by
  cases f₁ <;> cases f₂ <;> cases f₃ <;> simp_all [atLeastAsStrong]

theorem ModalForce.necessity_strongest (f : ModalForce) :
    ModalForce.necessity.atLeastAsStrong f = true := by cases f <;> rfl

theorem ModalForce.possibility_weakest (f : ModalForce) :
    f.atLeastAsStrong .possibility = true := by cases f <;> rfl

-- ============================================================================
-- §2. Modal Flavor
-- ============================================================================

/-- Modal flavor: the contextual source of modality.
    Theory-neutral: avoids commitment to how flavor is semantically encoded.
    Teleological is subsumed under circumstantial (both concern facts/abilities).
    Bouletic (desires/wishes) is distinguished from deontic (norms/rules),
    following @cite{kratzer-1981}'s four-way classification. -/
inductive ModalFlavor where
  | epistemic       -- Evidence/knowledge
  | deontic         -- Norms/rules
  | bouletic        -- Desires/wishes
  | circumstantial  -- Facts/abilities (subsumes teleological)
  deriving DecidableEq, Repr, Inhabited

instance : LawfulBEq ModalFlavor where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString ModalFlavor where
  toString | .epistemic => "e" | .deontic => "d" | .bouletic => "b" | .circumstantial => "c"

/-- All modal flavors. -/
def ModalFlavor.all : List ModalFlavor := [.epistemic, .deontic, .bouletic, .circumstantial]

-- ============================================================================
-- §3. Force-Flavor Pairs
-- ============================================================================

/-- A force-flavor pair: one point in the modal semantic space P.
    |P| = |Force| × |Flavor| = 3 × 4 = 12.

    Imel, Guo, & @cite{imel-guo-steinert-threlkeld-2026}: modal meanings are subsets of P.
    Their original database uses a 2×3 space (necessity/possibility × 3 flavors);
    we extend to 3×4 by adding weak necessity as a distinct force value
    (following @cite{agha-jeretic-2026}) and bouletic as a distinct flavor
    (following @cite{kratzer-1981}). -/
structure ForceFlavor where
  force : ModalForce
  flavor : ModalFlavor
  deriving DecidableEq, Repr, Inhabited

instance : LawfulBEq ForceFlavor where
  eq_of_beq {a b} h := by
    cases a with | mk f1 fl1 => cases b with | mk f2 fl2 =>
    cases f1 <;> cases f2 <;> cases fl1 <;> cases fl2 <;>
      first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a with | mk f fl => cases f <;> cases fl <;> decide

instance : ToString ForceFlavor where
  toString ff := s!"({ff.force},{ff.flavor})"

/-- All nine points in the modal semantic space. -/
def ForceFlavor.universe : List ForceFlavor :=
  ModalForce.all.flatMap fun fo => ModalFlavor.all.map fun fl => ⟨fo, fl⟩

theorem ForceFlavor.universe_length : ForceFlavor.universe.length = 12 := by native_decide

/-- The Cartesian product of forces and flavors. Infrastructure for constructing
    modal meanings; no theoretical commitment (just list operations). -/
def ForceFlavor.cartesianProduct (fos : List ModalForce) (fls : List ModalFlavor) :
    List ForceFlavor :=
  fos.flatMap fun fo => fls.map fun fl => ⟨fo, fl⟩

-- ============================================================================
-- §4. Modal Item
-- ============================================================================

/-- A modal item: the shared core of any expression carrying modal meaning.

    Unifies `AuxEntry.{form, modalMeaning, register}`,
    `ModalAdvEntry.{form, modalMeaning, register}`, and
    `ModalExpression.{form, meaning}` under a common type.

    This enables generic operations (e.g., `sharesForce`, concord checks)
    that work across syntactic categories. -/
structure ModalItem where
  form : String
  meaning : List ForceFlavor
  register : Core.Register.Level := .neutral
  deriving Repr, BEq

/-- Two modal items share force if at least one ForceFlavor pair in each
    has the same force (exact match). -/
def ModalItem.sharesForce (a b : ModalItem) : Bool :=
  a.meaning.any fun ff1 => b.meaning.any fun ff2 => ff1.force == ff2.force

/-- Two modal items share flavor if at least one ForceFlavor pair in each
    has the same flavor. -/
def ModalItem.sharesFlavor (a b : ModalItem) : Bool :=
  a.meaning.any fun ff1 => b.meaning.any fun ff2 => ff1.flavor == ff2.flavor

/-- Two modal items are register variants if they differ in register. -/
def ModalItem.areRegisterVariants (a b : ModalItem) : Bool :=
  Core.Register.areVariants a.register b.register

-- ============================================================================
-- §5. Concord Types
-- ============================================================================

/-- Classification of concord phenomena by what logical type is doubled. -/
inductive ConcordType where
  | negation           -- ¬¬ → ¬ (negative concord)
  | modalNecessity     -- □□ → □ (necessity modal concord)
  | modalPossibility   -- ◇◇ → ◇ (possibility modal concord)
  deriving DecidableEq, Repr

/-- Map modal force to the corresponding concord type.
    Weak necessity patterns with necessity for concord purposes (both are ∀ quantifiers). -/
def ConcordType.fromModalForce : ModalForce → ConcordType
  | .necessity     => .modalNecessity
  | .weakNecessity => .modalNecessity
  | .possibility   => .modalPossibility

/-- Two modal items share concord-compatible force: both necessity and weak
    necessity map to the same concord class (necessity-type). This is the
    structural precondition for modal concord. -/
def ModalItem.sharesConcordForce (a b : ModalItem) : Bool :=
  a.meaning.any fun ff1 => b.meaning.any fun ff2 =>
    ConcordType.fromModalForce ff1.force == ConcordType.fromModalForce ff2.force

-- ============================================================================
-- §6. Modal Features (Zeijlstra 2007)
-- ============================================================================

/-- Interpretability of a modal feature (@cite{zeijlstra-2007}).

    Modal elements carry features specifying modal force (∃/∀).
    Features are either **interpretable** (semantically active — the element
    contributes a modal operator at LF) or **uninterpretable** (semantically
    vacuous — the element is checked by a c-commanding interpretable feature
    and does not contribute its own operator).

    @cite{ciardelli-guerrini-2026} use this distinction to derive narrow-scope
    readings for "MOD A COORD MOD B" sentences: when both auxiliaries carry
    uninterpretable features, a single silent interpretable operator scopes
    over the coordination, yielding Δ(A ∘ B) rather than ΔA ∘ ΔB. -/
inductive ModalInterpretability where
  | interpretable    -- i-MOD: semantically active (allow, demand, silent OP)
  | uninterpretable  -- u-MOD: semantically vacuous (may, must as auxiliaries)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A modal feature: force (∃/∀) paired with interpretability (i/u).

    @cite{zeijlstra-2007}: every modal element carries a feature from this
    four-cell space: [i∃-MOD], [u∃-MOD], [i∀-MOD], [u∀-MOD]. -/
structure ModalFeature where
  force : ModalForce
  interp : ModalInterpretability
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Feature checking: an interpretable feature checks a c-commanded
    uninterpretable feature of matching concord class.

    @cite{zeijlstra-2007}: u-features must be c-commanded by a matching
    i-feature to be licensed. The match is by concord class (necessity and
    weak necessity both count as ∀-type). -/
def ModalFeature.checks (checker checked : ModalFeature) : Bool :=
  checker.interp == .interpretable &&
  checked.interp == .uninterpretable &&
  ConcordType.fromModalForce checker.force == ConcordType.fromModalForce checked.force

/-- Negation flips the relevant modal force for concord purposes.

    @cite{ciardelli-guerrini-2026} §4.2: modal concord across negation
    requires opposite forces — ALLOW[i∃](¬NEED[u∀]) is well-formed because
    ¬∀ = ∃, but *DEMAND[i∀](¬NEED[u∀]) is ill-formed (same force).

    Derived from `ModalForce.dual` — negation over a modal operator yields
    its dual force (¬□ = ◇, ¬◇ = □). -/
abbrev ModalForce.negatedConcordForce := ModalForce.dual

/-- Feature checking across negation: an interpretable feature checks a
    negated uninterpretable feature when their forces are duals.

    ALLOW[i∃](¬NEED[u∀]): ∃ checks negated ∀ (= ∃) ✓
    *DEMAND[i∀](¬NEED[u∀]): ∀ checks negated ∀ (= ∃) ✗ -/
def ModalFeature.checksAcrossNegation (checker checked : ModalFeature) : Bool :=
  checker.interp == .interpretable &&
  checked.interp == .uninterpretable &&
  ConcordType.fromModalForce checker.force ==
    ConcordType.fromModalForce checked.force.dual

-- ============================================================================
-- §7. Modal Decomposability
-- ============================================================================

/-- Whether a modal meaning decomposes into independent force and flavor
    dimensions or is a unitary, non-decomposable operator.

    @cite{werner-2006}, @cite{condoravdi-2002}: some modals resist the standard
    force × flavor decomposition. "Will" and other temporal-modal elements
    do not factor cleanly into a modal force and a conversational background
    flavor. -/
inductive ModalDecomposition where
  | decomposable  -- ⟦m⟧ = fo(m) × fl(m)
  | unitary       -- ⟦m⟧ ≠ fo(m) × fl(m)
  deriving DecidableEq, Repr

/-- Classify a modal item by whether its meaning set equals the Cartesian
    product of its force and flavor projections. A modal is decomposable
    iff every combination of its attested forces and flavors is also
    attested — the two dimensions are independent. -/
def ModalItem.decomposition (m : ModalItem) : ModalDecomposition :=
  let forces := (m.meaning.map (·.force)).eraseDups
  let flavors := (m.meaning.map (·.flavor)).eraseDups
  if (ForceFlavor.cartesianProduct forces flavors).all (m.meaning.contains ·) then
    .decomposable
  else
    .unitary

/-- A modal item is unitary (non-decomposable into force × flavor). -/
def ModalItem.isUnitary (m : ModalItem) : Bool :=
  m.decomposition == .unitary

/-- Singleton meanings are trivially decomposable: a modal with exactly
    one force-flavor pair always satisfies IFF. -/
theorem singleton_decomposable (ff : ForceFlavor) :
    (({ form := "m", meaning := [ff] } : ModalItem)).isUnitary = false := by
  cases ff with | mk f fl => cases f <;> cases fl <;> native_decide

/-- A non-IFF meaning is unitary: necessity-epistemic + possibility-deontic
    without the cross-product pairs. -/
theorem cross_cutting_is_unitary :
    (({ form := "m", meaning := [⟨.necessity, .epistemic⟩, ⟨.possibility, .deontic⟩] } : ModalItem)).isUnitary = true := by
  native_decide

end Core.Modality
