import Linglib.Core.Register

/-!
# Modal Typological Types

Theory-neutral vocabulary for cross-linguistic modal typology: `ModalForce`,
`ModalFlavor`, `ForceFlavor`, `ModalItem`, `ConcordType`, `ModalDecomposition`.

These types classify modal meanings along two independent dimensions — force
(quantificational strength) and flavor (contextual source) — following
@cite{kratzer-1981} and @cite{imel-guo-steinert-threlkeld-2026}.

**Separated from `Core.IntensionalLogic`** because Kripke frames and frame
correspondence are pure mathematical logic, while force/flavor classification
is linguistic typology. The two are connected (Kripke semantics *interprets*
force-flavor pairs) but conceptually independent.

## What belongs here vs. `Core.IntensionalLogic`

- **Here** (`Core.Modality`): `ModalForce`, `ModalFlavor`, `ForceFlavor`,
  `ModalItem`, `ConcordType`, `ModalDecomposition` — linguistic classification
  of modal meanings.
- **There** (`Core.IntensionalLogic`): `AccessRel`, `kripkeEval`, frame conditions
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
    `ModalExpression.{form, meaning}` under a common type. -/
structure ModalItem where
  form : String
  meaning : List ForceFlavor
  register : Core.Register.Level := .neutral
  deriving Repr, BEq

/-- Two modal items are register variants if they differ in register. -/
def ModalItem.areRegisterVariants (a b : ModalItem) : Prop :=
  Core.Register.areVariants a.register b.register

instance (a b : ModalItem) : Decidable (a.areRegisterVariants b) :=
  inferInstanceAs (Decidable (Core.Register.areVariants _ _))

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

-- ============================================================================
-- §8. Projection Modes (Kratzer 2012)
-- ============================================================================

/-- Mode of projecting conversational backgrounds.
    @cite{kratzer-2012} replaces the traditional epistemic/circumstantial
    dichotomy with a distinction between **factual** and **content** modes:

    - **Factual**: the modal quantifies over worlds containing a counterpart
      of some actual-world situation or body of evidence. The actual world
      is always among the accessible worlds (`w ∈ ∩f(w)`).
    - **Content**: the modal quantifies over worlds compatible with the
      propositional content of some information source (rumour, report,
      sensory evidence). The actual world need not be accessible — the
      speaker can disbelieve the content.

    @cite{matthewson-2016}: Table 18.2.

    The old circumstantial class is entirely factual. The old epistemic
    class splits: factual epistemics (inferential, based on situation
    counterparts) vs. content epistemics (reportative, based on
    propositional content). -/
inductive ProjectionMode where
  | factual   -- Counterparts of actual-world situation/evidence
  | content   -- Propositional content of information source
  deriving DecidableEq, Repr, BEq, Inhabited

instance : ToString ProjectionMode where
  toString | .factual => "factual" | .content => "content"

/-- Three-way classification of conversational backgrounds.
    @cite{matthewson-2016}: Table 18.3. Refines the traditional
    epistemic/circumstantial binary into a three-way split based on
    projection mode and whether information source is encoded.

    - **factualCircumstantial**: factual mode, no information source encoded.
      Covers deontic, bouletic, teleological, ability, pure circumstantial.
      English: *can* (circumstantial), German: *können*.
    - **factualEvidential**: factual mode, information source encoded.
      The speaker cannot disbelieve the prejacent.
      St'át'imcets: *k'a* (inferential), English: *must* (indirect evidence).
    - **contentEvidential**: content mode, information source encoded.
      The speaker can disbelieve the prejacent.
      St'át'imcets: *lákw7a* (sensory non-visual), German: *sollen*. -/
inductive BackgroundClass where
  | factualCircumstantial  -- Factual, no info source (deontic, ability, circ)
  | factualEvidential      -- Factual, info source encoded (inferential)
  | contentEvidential      -- Content, info source encoded (reportative, sensory)
  deriving DecidableEq, Repr, BEq, Inhabited

instance : ToString BackgroundClass where
  toString
    | .factualCircumstantial => "fact-circ"
    | .factualEvidential => "fact-evid"
    | .contentEvidential => "cont-evid"

/-- The projection mode of each background class. -/
def BackgroundClass.projectionMode : BackgroundClass → ProjectionMode
  | .factualCircumstantial => .factual
  | .factualEvidential => .factual
  | .contentEvidential => .content

/-- Whether the background class encodes an information source. -/
def BackgroundClass.EncodesInfoSource (b : BackgroundClass) : Prop :=
  b = .factualEvidential ∨ b = .contentEvidential

instance : DecidablePred BackgroundClass.EncodesInfoSource :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Whether the speaker can disbelieve the prejacent under this class.
    Only content-mode backgrounds allow speaker disbelief —
    factual modes commit the speaker to the prejacent being compatible
    with reality. -/
def BackgroundClass.AllowsSpeakerDisbelief (b : BackgroundClass) : Prop :=
  b = .contentEvidential

instance : DecidablePred BackgroundClass.AllowsSpeakerDisbelief :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- The traditional epistemic/circumstantial classification that the
    three-way split refines. -/
def BackgroundClass.traditionalFlavor : BackgroundClass → ModalFlavor
  | .factualCircumstantial => .circumstantial
  | .factualEvidential => .epistemic
  | .contentEvidential => .epistemic

/-- Traditional circumstantial modals are always factual. -/
theorem circumstantial_always_factual :
    BackgroundClass.factualCircumstantial.projectionMode = .factual := rfl

/-- Content-mode backgrounds always encode an information source. -/
theorem content_encodes_info :
    BackgroundClass.contentEvidential.EncodesInfoSource := by decide

/-- Speaker disbelief distinguishes the two epistemic subtypes. -/
theorem factual_epistemic_no_disbelief :
    ¬ BackgroundClass.factualEvidential.AllowsSpeakerDisbelief := by decide

theorem content_epistemic_allows_disbelief :
    BackgroundClass.contentEvidential.AllowsSpeakerDisbelief := by decide

-- ============================================================================
-- §9. Force Analysis (how modal force arises)
-- ============================================================================

/-- How a modal's quantificational force is determined.
    Distinguishes three mechanisms that the `List ForceFlavor` encoding conflates:

    - **fixed**: The modal lexically specifies a single force value.
      English *must* (necessity), *can* (possibility).
    - **variableForce**: The modal is semantically compatible with both
      necessity and possibility contexts without being ambiguous.
      Gitksan *ima('a)*, *gat* (@cite{matthewson-2013}).
    - **strengthened**: The modal has a fixed base force (typically
      possibility) but can receive strengthened readings in the absence
      of a contrasting dual. Nez Perce *o'qa* (@cite{deal-2011}):
      a possibility modal acceptable in necessity contexts because no
      contrasting necessity modal triggers scalar implicature. -/
inductive ForceAnalysis where
  | fixed         : ModalForce → ForceAnalysis
  | variableForce : ForceAnalysis
  | strengthened  : ModalForce → ForceAnalysis  -- base force
  deriving DecidableEq, Repr

/-- Whether the modal has a necessity reading (semantically or pragmatically). -/
def ForceAnalysis.AdmitsNecessity (a : ForceAnalysis) : Prop :=
  a ≠ .fixed .possibility

instance : DecidablePred ForceAnalysis.AdmitsNecessity :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Whether the modal has a possibility reading. -/
def ForceAnalysis.AdmitsPossibility (a : ForceAnalysis) : Prop :=
  a = .fixed .possibility ∨ a = .variableForce ∨ a = .strengthened .possibility

instance : DecidablePred ForceAnalysis.AdmitsPossibility :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Whether the modal has a lexical dual (contrasting force partner).
    @cite{matthewson-2016} §18.3.2: modals without duals do not come
    in necessity–possibility pairs. -/
def ForceAnalysis.HasDual : ForceAnalysis → Prop
  | .fixed _ => True        -- presumes a dual exists in the language
  | .variableForce => False -- variable-force modals lack duals by definition
  | .strengthened _ => False -- strengthened precisely because no dual exists

instance : DecidablePred ForceAnalysis.HasDual := fun a => by
  cases a <;> unfold ForceAnalysis.HasDual <;> infer_instance

end Core.Modality
