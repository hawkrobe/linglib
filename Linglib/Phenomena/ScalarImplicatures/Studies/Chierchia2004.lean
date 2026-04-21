/-
# Parallel Recursive Strengthening: @cite{chierchia-2004}

Formalizes the core architecture of @cite{chierchia-2004} "Scalar Implicatures,
Polarity Phenomena, and the Syntax/Pragmatics Interface" (§3).

Every expression gets both a plain meaning ‖α‖ and a strengthened meaning ‖α‖^S,
computed in tandem at every compositional step.

## Core mechanism

1. **Krifka's Rule** (cf. (81)): At scope sites, ‖α‖^S = ‖α‖ ∧ ¬(‖alt‖)
2. **Strength Condition** (82): ‖α‖^S must entail ‖α‖; otherwise fallback
3. **Strong Application** (84): DE-sensitive function application
   - If f is not DE: ‖[f g]‖^S = f^S(g^S)
   - If f is DE: ‖[f g]‖^S = f^S(g) ∧ indirect implicatures
4. **Scale Axioms** (99): Context selects ≥2 scale members; uttered ≠ strongest

## Key results

- **SI-NPI Generalization** (53): SIs are suspended in exactly NPI-licensing (DE)
  contexts — direct implicatures are blocked, indirect implicatures may arise
- **Direct vs indirect implicatures**: Direct from Krifka's Rule at scope sites;
  indirect from Strong Application in DE contexts
- **Intervention effects**: Strong scalar terms (every, and) generate indirect
  implicatures that can block NPI strengthening; weak terms (some, or) don't
- **Bridge**: At root level in UE contexts, Chierchia's ‖S‖^S ⊆ exhIE(ALT, S)

-/

import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Mathlib.Data.Set.Basic

namespace Chierchia2004

open Exhaustification

-- ============================================================================
-- A. Strengthened Meanings
-- ============================================================================

variable {World : Type*}

/-- A strengthened meaning pairs a plain denotation with its strengthened version
    and the alternatives used to compute the strengthening.

    This is the central data structure: every propositional node in a derivation
    carries both ‖α‖ (plain) and ‖α‖^S (strong). -/
structure StrengthenedMeaning (World : Type*) where
  /-- ‖α‖ — the plain semantic value -/
  plain : Set World
  /-- ‖α‖^S — the strengthened semantic value -/
  strong : Set World
  /-- The scalar alternatives considered -/
  alternatives : Set (Set World)

/-- Lift a plain meaning to a trivially strengthened one (‖α‖^S = ‖α‖). -/
def StrengthenedMeaning.trivial (φ : Set World) : StrengthenedMeaning World :=
  { plain := φ, strong := φ, alternatives := ∅ }

-- ============================================================================
-- B. Scale Axioms (99)
-- ============================================================================

/-- Chierchia's scale axioms (99a–c) as a predicate:
    (a) Context activates at least 2 members of the scale
    (b) The uttered term is a member of the activated scale
    (c) The uttered term is not the strongest activated member

    "Strictly stronger" means: a ⊆ utt (a entails utt, true in fewer worlds)
    but not utt ⊆ a (utt does not entail a). -/
def scaleAxiomsSatisfied (activated : Set (Set World)) (utt : Set World) : Prop :=
  -- (99a): at least 2 alternatives
  (∃ a b, a ∈ activated ∧ b ∈ activated ∧ a ≠ b) ∧
  -- (99b): uttered is in the scale
  utt ∈ activated ∧
  -- (99c): uttered is not the strongest — some alt is strictly stronger
  (∃ a ∈ activated, (a ⊆ utt) ∧ ¬(utt ⊆ a))

-- ============================================================================
-- C. Strength Condition (82)
-- ============================================================================

/-- The Strength Condition (82): ‖α‖^S must entail ‖α‖.

    If this fails, the strengthened meaning is discarded and we fall back
    to the plain meaning. This prevents over-generation of implicatures. -/
def strengthCondition (sm : StrengthenedMeaning World) : Prop :=
  sm.strong ⊆ sm.plain

/-- Apply the strength condition: keep strengthened meaning if it entails plain;
    otherwise fall back to plain. Uses a Boolean flag for decidability. -/
def applyStrengthCondition (sm : StrengthenedMeaning World)
    (holds : Bool) : StrengthenedMeaning World :=
  if holds then sm
  else { sm with strong := sm.plain }

-- ============================================================================
-- D. Krifka's Rule — Direct Implicatures (81)
-- ============================================================================

/-- Krifka's Rule (cf. (81)):
    At a scope site, introduce a direct implicature by conjoining the plain
    meaning with the negation of each strictly stronger alternative.

    ‖S‖^S = ‖S‖ ∧ ⋂₀ {¬‖alt‖ : alt ∈ ALT, alt strictly stronger than ‖S‖}

    "Strictly stronger" = a ⊆ φ ∧ ¬(φ ⊆ a): the alternative entails the
    uttered meaning but not vice versa (true in strictly fewer worlds).

    This is the source of DIRECT implicatures. -/
def krifkaRule (φ : Set World) (ALT : Set (Set World)) : StrengthenedMeaning World :=
  { plain := φ
  , strong := φ ∩ (⋂₀ { ψ | ∃ a ∈ ALT, ψ = aᶜ ∧ (a ⊆ φ) ∧ ¬(φ ⊆ a) })
  , alternatives := ALT }

/-- Direct implicatures satisfy the strength condition:
    ‖S‖ ∧ ¬(stronger alts) entails ‖S‖. -/
theorem krifkaRule_satisfies_strength (φ : Set World) (ALT : Set (Set World)) :
    strengthCondition (krifkaRule φ ALT) := by
  intro w ⟨hφ, _⟩
  exact hφ

-- ============================================================================
-- E. DE-Sensitivity — Strong Application (84)
-- ============================================================================

/-- A context function is downward-entailing (DE) over `Set World`.

    f is DE iff: φ ⊆ ψ → f(ψ) ⊆ f(φ).

    This reverses entailment: strengthening the argument weakens the result.

    Note: This is the `World → Prop` version, paralleling `IsDownwardEntailing`
    (`Antitone`) from `Semantics.Entailment.Polarity` which uses `World → Bool`. -/
def IsDE (f : Set World → Set World) : Prop :=
  ∀ φ ψ : Set World, (φ ⊆ ψ) → (f ψ ⊆ f φ)

/-- Negation is DE. -/
theorem compl_isDE : IsDE (World := World) Compl.compl := by
  intro φ ψ hφψ w hnψ hφ
  exact hnψ (hφψ hφ)

/-- Strong Application (84): DE-sensitive function application.

    This is the formal heart of @cite{chierchia-2004}.

    **Non-DE case** (UE contexts): Pass strengthened meanings through.
      ‖[f g]‖^S = f^S(g^S)

    **DE case**: Strip implicatures from the argument (use plain meaning),
      then add INDIRECT implicatures from the alternatives.
      ‖[f g]‖^S = f^S(g) ∩ ⋂₀ {∼(f(alt)) : alt ∈ g.alternatives, f(alt) not entailed}

    The key insight: in DE contexts, direct SIs of the argument are blocked
    because strengthening the argument would WEAKEN the result.
    But indirect implicatures arise at the matrix level from the alternatives. -/
def strongApply (f fS : Set World → Set World) (g : StrengthenedMeaning World)
    (fIsDE : Bool) : StrengthenedMeaning World :=
  if fIsDE then
    -- DE case: use PLAIN meaning of argument (strip its implicatures)
    -- Then add indirect implicatures from alternatives
    let indirectImplicatures : Set World :=
      ⋂₀ { ψ | ∃ alt ∈ g.alternatives,
            ψ = (f alt)ᶜ ∧
            -- Only negate alternatives where f(alt) is not entailed by f(g.plain)
            ¬(f alt ⊆ f g.plain) }
    { plain := f g.plain
    , strong := fS g.plain ∩ indirectImplicatures
    , alternatives := g.alternatives }
  else
    -- UE case: pass strengthened meanings through
    { plain := f g.plain
    , strong := fS g.strong
    , alternatives := g.alternatives }

-- ============================================================================
-- F. Direct vs Indirect Implicatures
-- ============================================================================

/-- Classification of implicatures by their source. -/
inductive ImplicatureType where
  /-- Direct: from Krifka's Rule at a scope site (UE contexts) -/
  | direct
  /-- Indirect: from Strong Application through a DE function -/
  | indirect
  deriving DecidableEq, Repr

/-- In UE contexts, scalar items generate DIRECT implicatures.
    In DE contexts, the direct implicature is blocked, but the DE operator
    may generate INDIRECT implicatures at the matrix level.

    Example:
    - UE: "John ate some cookies" → direct: ¬all (from Krifka's Rule)
    - DE: "John didn't eat some cookies" → direct ¬all blocked;
      indirect: ¬(¬all) = all may arise at matrix -/
def implicatureSource (fIsDE : Bool) : ImplicatureType :=
  if fIsDE then .indirect else .direct

-- ============================================================================
-- G. The SI-NPI Generalization (53)
-- ============================================================================

/-- The SI-NPI Generalization (@cite{chierchia-2004}, (53)):

    Scalar implicatures are systematically SUSPENDED in the same environments
    that LICENSE negative polarity items (NPIs).

    Formally: If f is DE, then direct scalar implicatures of its argument are
    blocked. The strengthened argument g^S entails g (by the strength condition),
    so DE reverses this: f(g) ⊆ f(g^S). Using the strengthened argument would
    WEAKEN the matrix meaning, violating the strength condition at that level.

    This is exactly the DE property that licenses NPIs: DE contexts are
    precisely where scalar strengthening is blocked. -/
theorem si_npi_generalization
    (f : Set World → Set World) (hDE : IsDE f)
    (g : StrengthenedMeaning World) (hStrength : g.strong ⊆ g.plain) :
    f g.plain ⊆ f g.strong := by
  exact hDE g.strong g.plain hStrength

/-- Corollary: Under a DE function, applying f to the Krifka-strengthened
    argument is WEAKER than applying f to the plain argument. -/
theorem de_blocks_direct_si
    (f : Set World → Set World) (hDE : IsDE f)
    (φ : Set World) (ALT : Set (Set World)) :
    let strengthened := (krifkaRule φ ALT).strong
    f φ ⊆ f strengthened := by
  simp only
  apply hDE
  exact krifkaRule_satisfies_strength φ ALT

-- ============================================================================
-- H. NPI Licensing as Domain Widening + Strengthening
-- ============================================================================

/-- Chierchia's O operator (cf. (127)): exhaustification over domain alternatives.

    For an indefinite with domain D, the O operator provides universal closure
    over the domain — the NPI "widens" the domain to the maximal set,
    and O yields the strengthened meaning.

    O_D(∃x∈D. P(x)) = ∃x∈D. P(x) ∧ ∀D'⊂D. ¬(∃x∈D'. P(x) ∧ ∀y∈D\D'. ¬P(y))

    Simplified: the assertion holds AND no subdomain alternative holds. -/
def domainExhaustify (assertion : Set World) (subdomainAlts : Set (Set World))
    : Set World :=
  assertion ∩ (⋂₀ { ψ | ∃ alt ∈ subdomainAlts, ψ = altᶜ })

/-- NPI strengthening succeeds when the exhaustified meaning entails the
    plain meaning of the non-widened competitor.

    (127): ‖any NP‖^S = O_D(∃x∈D.P(x)) must be stronger than ∃x∈D₀.P(x)
    where D₀ is the default (non-widened) domain. -/
def npiStrengtheningSucceeds (exhaustified competitor : Set World) : Prop :=
  exhaustified ⊆ competitor

/-- NPI strengthening is BLOCKED when embedding under a DE function,
    because the DE function reverses the strengthening relationship.

    This connects NPIs to scalar implicatures: both involve DE-ness,
    but for NPIs, the blocking is what makes them grammatical in DE contexts
    (they don't need to strengthen, so domain widening is "free"). -/
theorem npi_blocked_under_de
    (f : Set World → Set World) (hDE : IsDE f)
    (widened competitor : Set World) (hStronger : widened ⊆ competitor) :
    f competitor ⊆ f widened := by
  exact hDE widened competitor hStronger

-- ============================================================================
-- I. Intervention Effects (§4.3)
-- ============================================================================

/-- Intervention occurs when a strong scalar item (every, and, numerals)
    sits between an NPI licensor and the NPI.

    The strong item generates an INDIRECT implicature that conflicts with
    the NPI's domain-widening requirement.

    Weak items (some, or) do not intervene because they don't generate
    indirect implicatures that conflict. -/
inductive ScalarStrength where
  /-- Strong: top of scale (every, and, all numerals > 1). Generates indirect
      implicatures that can interfere with NPI licensing. -/
  | strong
  /-- Weak: bottom of scale (some, or). No interfering indirect implicatures. -/
  | weak
  deriving DecidableEq, Repr

/-- Whether a scalar item of given strength intervenes in NPI licensing.

    Strong scalars generate indirect implicatures under DE operators;
    these indirect implicatures can block NPI strengthening.
    Weak scalars don't generate interfering implicatures. -/
def intervenes (strength : ScalarStrength) : Bool :=
  match strength with
  | .strong => true
  | .weak => false

-- Verify: "every" intervenes, "some" doesn't
-- "*No one who read every book understood any theorem" (every intervenes)
-- "No one who read some book understood any theorem" (some doesn't)
#guard intervenes .strong == true
#guard intervenes .weak == false

-- ============================================================================
-- J. Bridge to exhIE (@cite{fox-2007} / @cite{spector-2016})
-- ============================================================================

/-- At a root-level scope site in a UE context, Chierchia's parallel
    strengthening entails Fox's exhIE.

    Krifka's Rule produces: φ ∧ ⋂₀ {¬alt : alt strictly stronger than φ}
    exhIE produces: φ ∧ ⋂₀ {¬alt : alt innocently excludable}

    On "flat" (linearly ordered) scales, every innocently excludable alternative
    is strictly stronger, so Krifka's output negates a superset and thus entails
    exhIE. The hypothesis `hFlat` captures this: every IE alt is strictly stronger.

    Requires MC-set existence to decompose IE members into φ or aᶜ forms. -/
theorem root_ue_bridge (φ : Set World) (ALT : Set (Set World))
    (hMC : ∃ E, IsMCSet ALT φ E)
    (hFlat : ∀ a ∈ ALT, IsInnocentlyExcludable ALT φ a →
      (a ⊆ φ) ∧ ¬(φ ⊆ a)) :
    ∀ w, (krifkaRule φ ALT).strong w → exhIE ALT φ w := by
  intro w ⟨hφ, hnegs⟩
  -- hnegs : ∀ ψ ∈ {ψ | ∃ a ∈ ALT, ψ = aᶜ ∧ (a ⊆ φ) ∧ ¬(φ ⊆ a)}, ψ w
  -- Goal: ∀ ψ ∈ IE ALT φ, ψ w
  intro ψ hψ_IE
  -- Use MC-set existence to determine the form of ψ
  obtain ⟨E, hE_mc⟩ := hMC
  have hψ_E : ψ ∈ E := hψ_IE E hE_mc
  -- From compatibility: every member of E is φ or aᶜ for some a ∈ ALT
  rcases hE_mc.1.2.1 ψ hψ_E with rfl | ⟨a, ha_ALT, rfl⟩
  · -- Case ψ = φ: immediate from Krifka's hypothesis
    exact hφ
  · -- Case ψ = aᶜ for some a ∈ ALT: need ¬(a w)
    -- Since aᶜ ∈ IE (it's in every MC-set), a is innocently excludable
    have h_ie : IsInnocentlyExcludable ALT φ a := ⟨ha_ALT, hψ_IE⟩
    -- By the flat-scale hypothesis: a is strictly stronger than φ
    obtain ⟨ha_str, ha_strict⟩ := hFlat a ha_ALT h_ie
    -- Krifka's Rule negated all strictly stronger alternatives, including a
    exact hnegs (aᶜ) ⟨a, ha_ALT, rfl, ha_str, ha_strict⟩

-- ============================================================================
-- K. Scalar Licensing Parametrized by Direction (@cite{schwab-2022})
-- ============================================================================

/-- Strength relation for scalar licensing.

    @cite{krifka-1995a} and @cite{chierchia-2004} treat all NPIs as STRENGTHENING:
    the NPI makes the assertion stronger than its scalar alternatives,
    so under negation the negated NPI statement is informationally weaker
    (= more conservative), which is the hallmark of DE environments.

    @cite{schwab-2022} observes that ATTENUATING NPIs (like German "so recht")
    work in the opposite direction: they make the assertion WEAKER than
    alternatives. Under negation, the negated attenuating statement is
    actually STRONGER — which means attenuating NPIs should NOT produce
    illusion effects in non-DE environments (and empirically, they don't). -/
inductive StrengthRelation where
  | strongerThan  -- for strengthening NPIs / Krifka's ScalAssert
  | weakerThan    -- for attenuating NPIs / Schwab's condition
  deriving DecidableEq, Repr

/-- Unified scalar licensing parametrized by direction.

    For **strengthening** (= Krifka's ScalAssert):
    Assert φ and deny all strictly stronger alternatives.
    φ ∧ ⋂₀ {¬alt : alt ∈ ALT, alt ⊂ φ}

    For **attenuating** (Schwab & Liu's condition):
    Assert φ and affirm the existence of a strictly stronger alternative.
    φ ∧ ⋃₀ {alt : alt ∈ ALT, alt ⊂ φ}
    (Simplified: we record the required relationship, not the full licensing.) -/
def scalarLicensing (rel : StrengthRelation) (φ : Set World)
    (ALT : Set (Set World)) : StrengthenedMeaning World :=
  match rel with
  | .strongerThan =>
    -- Krifka's Rule: deny stronger alternatives
    krifkaRule φ ALT
  | .weakerThan =>
    -- Attenuating: assert φ and require a stronger alternative exists
    { plain := φ
    , strong := φ ∩ (⋃₀ { ψ | ∃ a ∈ ALT, ψ = a ∧ (a ⊆ φ) ∧ ¬(φ ⊆ a) })
    , alternatives := ALT }

/-- Bridge: `scalarLicensing.strongerThan` is exactly `krifkaRule`. -/
theorem scalarLicensing_strongerThan_eq_krifkaRule (φ : Set World)
    (ALT : Set (Set World)) :
    scalarLicensing .strongerThan φ ALT = krifkaRule φ ALT := rfl

/-- Strengthening licensing satisfies the strength condition (inherits from krifkaRule). -/
theorem scalarLicensing_strongerThan_strength (φ : Set World)
    (ALT : Set (Set World)) :
    strengthCondition (scalarLicensing .strongerThan φ ALT) :=
  krifkaRule_satisfies_strength φ ALT

end Chierchia2004
