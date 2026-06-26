import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Semantics.Verb.Root.Template
import Linglib.Syntax.Anaphora.Basic

/-!
# Ellipsis: [E] Features and Deletion Domains
[merchant-2001] [merchant-2013] [benz-salzmann-2025]

The [E] feature on a functional head triggers PF-deletion of the head's
complement and presupposes e-GIVENness ([merchant-2001]). Different
ellipsis types correspond to different [E] positions in a functional spine.

## Generic Framework (`DeletionSpine`)

The deletion-domain mechanism is domain-general: the same theory governs
clausal ellipsis (VP-ellipsis, sluicing) and nominal ellipsis (NP-ellipsis,
N-stranding). The `DeletionSpine` class captures the shared structure:

- A set of spine positions with a complement-of relation (`isBelow`)
- [E] on position p → everything strictly below p is deleted
- Monotonicity: lower [E] → smaller domain → more external positions
- X-stranding ([liptak-saab-2014]): head movement out of the
  deletion domain lets the moved head survive ellipsis

Two instances:
- **Clausal** (`SpinePos`): V, VP_adj, v, Voice, T, C
- **Nominal** (`NomSpinePos`): N, NP_adj, n, Num, D

## Clausal Ellipsis ([merchant-2013])

Voice mismatch tolerance tracks the *height* of ellipsis:
- **VPE** ([E] on Voice): Voice is *external* → voice mismatch OK
- **Sluicing** ([E] on C): Voice is *internal* → voice mismatch blocked
- **vVPE** ([E] on v): both v and Voice are *external* →
  voice *and* transitivity mismatches OK ([kalyakin-2026])

## Nominal Ellipsis ([benz-salzmann-2025])

Variable [E] placement in the nominal spine:
- **N-stranding NP-ellipsis** ([E] on n): N survives via N-to-n movement;
  postnominal material (PPs, relatives) deleted; prenominal adjectives survive
- **nP-ellipsis** ([E] on Num): N, n, and adjectives all deleted
- **NumP-ellipsis** ([E] on D): everything below D deleted

## Monotonicity ([sailor-2014]'s Generalization)

Lower [E] position → smaller deletion domain → more features external
→ more mismatches tolerated. This is a strict monotonicity proved
generically for all `DeletionSpine` instances.
-/

namespace Minimalist.Ellipsis

open Verb

-- ════════════════════════════════════════════════════
-- § 0. Generic Deletion Spine
-- ════════════════════════════════════════════════════

/-- A deletion spine: a finite set of positions in a functional spine
    equipped with a deletion-domain relation and structural ordering.

    Both clausal spines (V, v, Voice, T, C) and nominal spines (N, n, Num, D)
    are instances. The class captures the domain-general logic of
    [merchant-2001]'s [E]-feature theory:

    - [E] on head H → complement of H (everything `isBelow` H) is deleted
    - Monotonicity: lower [E] → smaller deletion domain
    - Irreflexivity: H itself is never in its own deletion domain -/
class DeletionSpine (α : Type*) where
  /-- `isBelow p₁ p₂` = true iff p₁ is in the deletion domain when [E]
      is at p₂. Encodes the complement-of relation, NOT simple structural
      ordering — adjunction sites may be structurally between two heads
      without being in the lower head's complement. A `Bool` decision
      procedure; the `Prop` predicate layer (`inDomain`/`canMismatch`)
      is built on top. -/
  isBelow : α → α → Bool
  /-- `isAtOrBelow p₁ p₂` = true iff p₁ is structurally at or below p₂.
      A simple linear ordering used for monotonicity reasoning.
      (A mathlib `LinearOrder` upgrade of this is a planned follow-up.) -/
  isAtOrBelow : α → α → Bool
  /-- No position is in its own deletion domain. -/
  isBelow_irrefl : ∀ (p : α), isBelow p p = false
  /-- If d is external (not below) at p₁, it is external at any lower p₂.
      This is [sailor-2014]'s monotonicity generalization. -/
  isBelow_mono : ∀ (d p₁ p₂ : α),
    isBelow d p₁ = false → isAtOrBelow p₂ p₁ = true → isBelow d p₂ = false

/-- Generic: is position c in the deletion domain of [E] at ePos?
    A `Prop` predicate; the underlying `isBelow` stays a `Bool` decision
    procedure (the `Nat.ble`-style computational core). -/
def inDomain {α : Type*} [DeletionSpine α] (c ePos : α) : Prop :=
  DeletionSpine.isBelow c ePos = true

instance {α : Type*} [DeletionSpine α] (c ePos : α) : Decidable (inDomain c ePos) := by
  unfold inDomain; infer_instance

/-- X-stranding ([liptak-saab-2014]): if X has moved from `base` to
    the [E]-bearing head at `ePos`, X is external (survives ellipsis)
    while its base position is deleted.

    This is the abstract core of the X-stranding diagnostic for head
    movement: X-stranding XP-ellipsis exists in a language iff both
    X-movement and XP-ellipsis exist independently.

    Instances:
    - V-stranding VPE: V moves to v, [E] on v → V survives, VP deleted
    - N-stranding NP-ellipsis: N moves to n, [E] on n → N survives, NP deleted -/
theorem xStranding {α : Type*} [DeletionSpine α] (ePos base : α)
    (h_base_in_domain : inDomain base ePos) :
    ¬ inDomain ePos ePos ∧ inDomain base ePos :=
  ⟨by simp [inDomain, DeletionSpine.isBelow_irrefl ePos], h_base_in_domain⟩

-- ════════════════════════════════════════════════════
-- § 1. Clausal Spine
-- ════════════════════════════════════════════════════

/-- Positions in the clausal spine, ordered from lowest to highest.
    This is a deliberately coarse-grained linear order sufficient for
    ellipsis domain computation. It does not replace `Cat` or
    `ExtendedProjection`; it captures the relative height relevant
    to Merchant's deletion-domain theory.

    `VP_adj` encodes VP-adjunction — the attachment site of restitutive
    *again* and result-state modifiers. Structurally below v but NOT in
    v's complement: adjuncts to XP are part of the XP projection but
    not selected by the head that takes XP as complement. This matters
    for vVPE ([kalyakin-2026]): VP-adjuncts survive when [E] is on
    v (complement of v = bare VP, excluding adjuncts) but are deleted
    when [E] is on Voice (complement of Voice = full vP, including
    VP-adjuncts). -/
inductive SpinePos where
  | V      -- Lexical verb
  | VP_adj -- VP-adjunction (restitutive *again*, result-state modifiers)
  | v      -- Little v (transitivity, event structure)
  | Voice  -- Voice head (active/passive/anticausative)
  | T      -- Tense
  | C      -- Complementizer
  deriving DecidableEq, Repr

/-- Strict "in deletion domain of" relation on spine positions.

    `isBelow p₁ p₂` means "p₁ is inside the deletion domain when [E]
    is at p₂." This is NOT a simple structural ordering — it encodes
    the complement-vs-adjunction distinction:

    - `V.isBelow .v = true`: V is in v's complement (VP)
    - `VP_adj.isBelow .v = false`: VP-adjuncts are NOT in v's complement
    - `VP_adj.isBelow .Voice = true`: VP-adjuncts ARE inside Voice's
      complement (vP contains the full VP projection including adjuncts)

    This distinction is what makes vVPE ([kalyakin-2026]) predict
    both *again* readings survive: restitutive *again* (VP-adjoined) is
    outside the complement of v but inside vP. -/
def SpinePos.isBelow : SpinePos → SpinePos → Bool
  | .V, .VP_adj | .V, .v | .V, .Voice | .V, .T | .V, .C => true
  | .VP_adj, .Voice | .VP_adj, .T | .VP_adj, .C => true
  | .v, .Voice | .v, .T | .v, .C => true
  | .Voice, .T | .Voice, .C => true
  | .T, .C => true
  | _, _ => false

/-- Structural height comparison (non-strict).
    Used for monotonicity: `p₁.isAtOrBelow p₂` means p₁ is structurally
    at or below p₂. Unlike `isBelow`, this IS a simple linear ordering
    with VP_adj between V and v.
    Fully pattern-matched to avoid BEq reduction issues in proofs. -/
def SpinePos.isAtOrBelow : SpinePos → SpinePos → Bool
  | .V, _ => true
  | .VP_adj, .VP_adj | .VP_adj, .v | .VP_adj, .Voice
  | .VP_adj, .T | .VP_adj, .C => true
  | .v, .v | .v, .Voice | .v, .T | .v, .C => true
  | .Voice, .Voice | .Voice, .T | .Voice, .C => true
  | .T, .T | .T, .C => true
  | .C, .C => true
  | _, _ => false

instance : DeletionSpine SpinePos where
  isBelow := SpinePos.isBelow
  isAtOrBelow := SpinePos.isAtOrBelow
  isBelow_irrefl := by intro p; cases p <;> decide
  isBelow_mono := by
    intro d p₁ p₂
    cases d <;> cases p₁ <;> cases p₂ <;>
      simp_all [SpinePos.isBelow, SpinePos.isAtOrBelow]

-- ════════════════════════════════════════════════════
-- § 2. Ellipsis Types
-- ════════════════════════════════════════════════════

/-- An ellipsis type is defined by the spine position of the [E]-bearing
    head. The deletion domain is the complement of that head —
    everything strictly below it in the spine. -/
structure EllipsisType where
  /-- The head carrying [E] -/
  ePosition : SpinePos
  /-- Label for display -/
  name : String := ""
  deriving Repr

/-- Every ellipsis type is a Hankamer–Sag **surface** anaphor ([hankamer-sag-1976]):
    PF-deletion under identity leaves full internal structure in place. So
    `EllipsisType` is an `Anaphor.HasDepth` carrier (depth `.surface` throughout) —
    the depth-axis analogue of a `Bound` pronoun. -/
instance : Anaphor.HasDepth EllipsisType := ⟨fun _ => .surface⟩

/-- Witness: every ellipsis type is surface. -/
theorem isSurface (e : EllipsisType) : Anaphor.HasDepth.IsSurface e := rfl

/-- Is a spine position inside the deletion domain of an ellipsis type?
    A position is in the deletion domain iff it is strictly below the
    [E]-bearing head. -/
def isInDeletionDomain (c : SpinePos) (e : EllipsisType) : Prop :=
  inDomain c e.ePosition

instance (c : SpinePos) (e : EllipsisType) : Decidable (isInDeletionDomain c e) := by
  unfold isInDeletionDomain; infer_instance

/-- Sluicing: [E] on C, deletes TP. Contains Voice → voice mismatch blocked. -/
def sluicing : EllipsisType := ⟨.C, "sluicing"⟩

/-- TP ellipsis: [E] on T, deletes VoiceP. -/
def tpEllipsis : EllipsisType := ⟨.T, "TP ellipsis"⟩

/-- English VPE: [E] on Voice, deletes vP.
    Voice is external → voice mismatch tolerated.
    v is internal → transitivity mismatch blocked. -/
def englishVPE : EllipsisType := ⟨.Voice, "English VPE"⟩

/-- v-stranding VPE: [E] on v, deletes VP.
    Both Voice and v are external → voice and transitivity mismatches OK.
    Attested in Muira Dargwa complex predicates ([kalyakin-2026]). -/
def vVPE : EllipsisType := ⟨.v, "v-stranding VPE"⟩

-- ════════════════════════════════════════════════════
-- § 3. Mismatch Dimensions
-- ════════════════════════════════════════════════════

/-- A mismatch dimension: a syntactic feature whose head position
    determines whether mismatches in that feature are tolerated. -/
structure MismatchDimension where
  /-- Label for the dimension -/
  name : String
  /-- The spine position of the head bearing this feature -/
  headPosition : SpinePos
  deriving Repr

/-- Voice mismatch: active vs. passive, determined by Voice head. -/
def voiceMismatch : MismatchDimension := ⟨"voice", .Voice⟩

/-- Transitivity mismatch: transitive v vs. unaccusative v. -/
def transitivityMismatch : MismatchDimension := ⟨"transitivity", .v⟩

/-- Lexical verb mismatch: different V heads. -/
def lexicalMismatch : MismatchDimension := ⟨"lexical verb", .V⟩

/-- Dative alternation: double-object vs prepositional dative.
    Regulated by distinct v heads below Voice ([merchant-2013] §3.3). -/
def dativeAlternation : MismatchDimension := ⟨"dative alternation", .v⟩

/-- Applicative/prepositional alternation: embroider X with Y vs embroider Y on X.
    Regulated by applicative v heads below Voice ([merchant-2013] §3.3). -/
def prepAlternation : MismatchDimension := ⟨"prepositional alternation", .v⟩

/-- Transitive/middle alternation: they market ethanol vs ethanol markets well.
    Regulated by v heads determining external argument realization
    ([merchant-2013] §3.3). -/
def middleAlternation : MismatchDimension := ⟨"middle alternation", .v⟩

/-- A mismatch in dimension d is tolerated by ellipsis type e iff the
    head bearing the feature is NOT in the deletion domain — i.e., it
    is at or above the [E]-bearing head. -/
def canMismatch (e : EllipsisType) (d : MismatchDimension) : Prop :=
  ¬ isInDeletionDomain d.headPosition e

instance (e : EllipsisType) (d : MismatchDimension) : Decidable (canMismatch e d) := by
  unfold canMismatch; infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Core Predictions
-- ════════════════════════════════════════════════════

-- English VPE: [E] on Voice

/-- English VPE tolerates voice mismatches: Voice is external to vP. -/
theorem englishVPE_voice_ok :
    canMismatch englishVPE voiceMismatch := by decide

/-- English VPE blocks transitivity mismatches: v is inside vP. -/
theorem englishVPE_transitivity_blocked :
    ¬ canMismatch englishVPE transitivityMismatch := by decide

/-- English VPE blocks lexical verb mismatches: V is inside vP. -/
theorem englishVPE_lexical_blocked :
    ¬ canMismatch englishVPE lexicalMismatch := by decide

-- Sluicing: [E] on C

/-- Sluicing blocks voice mismatches: Voice is inside TP. -/
theorem sluicing_voice_blocked :
    ¬ canMismatch sluicing voiceMismatch := by decide

/-- Sluicing blocks transitivity mismatches: v is inside TP. -/
theorem sluicing_transitivity_blocked :
    ¬ canMismatch sluicing transitivityMismatch := by decide

-- v-stranding VPE: [E] on v

/-- vVPE tolerates voice mismatches: Voice is external to VP. -/
theorem vVPE_voice_ok :
    canMismatch vVPE voiceMismatch := by decide

/-- vVPE tolerates transitivity mismatches: v is external to VP. -/
theorem vVPE_transitivity_ok :
    canMismatch vVPE transitivityMismatch := by decide

/-- vVPE blocks lexical verb mismatches: V is inside VP. -/
theorem vVPE_lexical_blocked :
    ¬ canMismatch vVPE lexicalMismatch := by decide

-- ════════════════════════════════════════════════════
-- § 5. Monotonicity
-- ════════════════════════════════════════════════════

/-- Monotonicity of mismatch tolerance: if ellipsis type e₁ tolerates
    a mismatch dimension d, then any ellipsis type e₂ whose [E] position
    is at or below e₁'s also tolerates d. [sailor-2014]'s monotonicity:
    lower [E] → smaller domain → more mismatches tolerated. Routed through
    the generic class law `DeletionSpine.isBelow_mono`. -/
theorem mismatch_monotone (d : MismatchDimension) (e₁ e₂ : EllipsisType)
    (h₁ : canMismatch e₁ d)
    (h₂ : e₂.ePosition.isAtOrBelow e₁.ePosition = true) :
    canMismatch e₂ d := by
  simp only [canMismatch, isInDeletionDomain, inDomain, Bool.not_eq_true] at h₁ ⊢
  exact DeletionSpine.isBelow_mono d.headPosition e₁.ePosition e₂.ePosition h₁ h₂

-- ════════════════════════════════════════════════════
-- § 6. Root Attachment Position
-- ════════════════════════════════════════════════════

/-- Spine position of a root by its attachment (`Root.Position`,
    `Semantics/Lexical/Roots/Template.lean`; Marantz, [beavers-koontz-garboden-2020]):
    change-of-state `.complement` roots sit at `V` (in v's complement),
    manner/activity `.adjoined` roots at `VP_adj` (outside it). -/
def rootSpinePos : Root.Position → SpinePos
  | .complement => .V
  | .adjoined => .VP_adj

/-- Is a root inside the vVPE deletion domain (= complement of v)?
    Derived from the spine, not stipulated: a root is deleted under vVPE
    iff its attachment position is below `v`. -/
def rootInVVPEDomain (p : Root.Position) : Prop :=
  isInDeletionDomain (rootSpinePos p) vVPE

instance (p : Root.Position) : Decidable (rootInVVPEDomain p) := by
  unfold rootInVVPEDomain; infer_instance

/-- Complement roots (change-of-state) are deleted under vVPE: `V` is in
    v's complement (follows from the spine, not stipulated). -/
theorem complementRoot_in_vVPE : rootInVVPEDomain .complement := by decide

/-- Adjoined roots (manner/activity) survive vVPE — `VP_adj` is outside
    v's complement. This is why antipassive roots block vVPE in Muira
    Dargwa: antipassive coerces adjunction ([kalyakin-2026]). -/
theorem adjoinedRoot_outside_vVPE : ¬ rootInVVPEDomain .adjoined := by decide

-- ════════════════════════════════════════════════════
-- § 7. Again Ambiguity
-- ════════════════════════════════════════════════════

/-- Adjunction position of *again*, following [merchant-2013]
    (building on Johnson 2004, von Stechow 1996). -/
inductive AgainPosition where
  | vP_adjunction  -- Repetitive: event-level *again* (high)
  | VP_adjunction  -- Restitutive: result-state *again* (low)
  deriving DecidableEq, Repr

/-- Is an *again* reading available under a given ellipsis type?

    Repetitive *again* adjoins high (vP or VoiceP): modeled at `Voice`
    level — outside the deletion domain of both VPE and vVPE.

    Restitutive *again* adjoins to VP — modeled at `VP_adj`. This is
    inside vP (deleted under English VPE, [E] on Voice) but NOT inside
    v's complement (survives vVPE, [E] on v). The distinction between
    `VP_adj` and `V` is crucial: V (the head) is in v's complement,
    but VP-adjunction is at the complement boundary, outside it. -/
def againSurvives (pos : AgainPosition) (e : EllipsisType) : Prop :=
  match pos with
  | .vP_adjunction => ¬ isInDeletionDomain .Voice e   -- VoiceP-level adjunction
  | .VP_adjunction => ¬ isInDeletionDomain .VP_adj e   -- VP-adjunction level

instance (pos : AgainPosition) (e : EllipsisType) : Decidable (againSurvives pos e) := by
  unfold againSurvives; split <;> infer_instance

/-- Under English VPE, restitutive *again* is inside the deletion domain
    (deleted), while repetitive *again* survives.
    [merchant-2013]: only repetitive reading available (Johnson 2004
    exx. 49a–b). -/
theorem englishVPE_again :
    againSurvives .vP_adjunction englishVPE ∧
    ¬ againSurvives .VP_adjunction englishVPE := by decide

/-- Under vVPE, BOTH readings survive: restitutive *again* (VP-adjoined)
    is outside v's complement, so it is not deleted.
    [kalyakin-2026] §4.1 (exx. 52a–b): both repetitive and
    restitutive ʔibrra 'again' are available under vVPE in Muira Dargwa.
    This is the key diagnostic proving the deletion domain is VP (smaller
    than English VPE's vP). -/
theorem vVPE_again :
    againSurvives .vP_adjunction vVPE ∧
    againSurvives .VP_adjunction vVPE := by decide

-- ════════════════════════════════════════════════════
-- § 8. Cross-Linguistic Comparison
-- ════════════════════════════════════════════════════

/-- English VPE and vVPE agree on voice: both tolerate voice mismatches. -/
theorem voice_agreement :
    canMismatch englishVPE voiceMismatch ∧
    canMismatch vVPE voiceMismatch := by decide

/-- English VPE and vVPE diverge on transitivity: English blocks it,
    vVPE allows it. This is the key prediction that distinguishes the
    two ellipsis types. -/
theorem transitivity_divergence :
    ¬ canMismatch englishVPE transitivityMismatch ∧
    canMismatch vVPE transitivityMismatch := by decide

/-- Both block lexical verb mismatches: V is inside the deletion domain
    of both English VPE and vVPE. -/
theorem lexical_blocked_both :
    ¬ canMismatch englishVPE lexicalMismatch ∧
    ¬ canMismatch vVPE lexicalMismatch := by decide

-- ════════════════════════════════════════════════════
-- § 9. Cross-Linguistic vVPE Typology
-- ════════════════════════════════════════════════════

/-- Extended ellipsis type with cross-linguistic variation parameters.
    Languages with verb-stranding ellipsis vary in:
    - deletion domain size (*again* test: VP vs vP)
    - whether the Verbal Identity Requirement holds (LV must match)
    - whether argument-structure alternations are tolerated -/
structure VPEProfile where
  /-- The core ellipsis type (spine position of [E]) -/
  ellipsisType : EllipsisType
  /-- Verbal Identity Requirement ([goldberg-2005]): antecedent and
      target light verbs must be identical in root and derivational
      morphology. Active in Persian and Bangla; inactive in Muira Dargwa. -/
  virRequired : Bool
  /-- Language label -/
  language : String
  deriving Repr

/-- Muira Dargwa vVPE: [E] on v, deletion domain = VP.
    Both *again* readings survive; arg-structure alternations tolerated;
    LV mismatches tolerated ([kalyakin-2026] ex. 78). -/
def muiraDargwaVVPE : VPEProfile :=
  { ellipsisType := vVPE, virRequired := false, language := "Muira Dargwa" }

/-- Persian vVPE: [E] on v, deletion domain = VP.
    Both *again* readings survive ([toosarvandani-2009] ex. 90).
    But arg-structure alternations blocked (ex. 91) and LV identity
    required — VIR is active. -/
def persianVVPE : VPEProfile :=
  { ellipsisType := vVPE, virRequired := true, language := "Persian" }

/-- Bangla verb-stranding: deletion domain = vP (NOT VP).
    Only repetitive *again* survives (Haldar 2021 ex. 94a–b);
    adjuncts CAN be interpreted in the ellipsis site (ex. 95).
    This means the [E] position is Voice (same as English VPE),
    with the LV evacuating via head movement. -/
def banglaVVPE : VPEProfile :=
  { ellipsisType := englishVPE, virRequired := true, language := "Bangla" }

/-- British *do* ellipsis: [E] on v, deletion domain = VP.
    Tolerates voice mismatches (Silk 2025 ex. 97) and arg-structure
    alternations (ex. 98), matching Muira Dargwa vVPE. -/
def britishDoVVPE : VPEProfile :=
  { ellipsisType := vVPE, virRequired := false, language := "British English" }

/-- Muira Dargwa and Persian share the same [E] position but differ on VIR. -/
theorem dargwa_persian_same_domain :
    muiraDargwaVVPE.ellipsisType.ePosition = persianVVPE.ellipsisType.ePosition ∧
    muiraDargwaVVPE.virRequired ≠ persianVVPE.virRequired := ⟨rfl, by decide⟩

/-- Bangla has a LARGER deletion domain than Muira Dargwa: [E] on Voice
    (= English VPE) vs [E] on v. The *again* test diagnoses this: Bangla
    deletes restitutive *again* (Haldar 2021), Muira Dargwa does not. -/
theorem bangla_larger_domain :
    banglaVVPE.ellipsisType.ePosition = SpinePos.Voice ∧
    muiraDargwaVVPE.ellipsisType.ePosition = SpinePos.v ∧
    inDomain SpinePos.v SpinePos.Voice := by decide

/-- The *again* test correctly differentiates Bangla (vP domain) from
    Muira Dargwa (VP domain): restitutive *again* is deleted under
    Bangla's ellipsis but survives Muira Dargwa's. -/
theorem again_differentiates_bangla_dargwa :
    ¬ againSurvives .VP_adjunction banglaVVPE.ellipsisType ∧
    againSurvives .VP_adjunction muiraDargwaVVPE.ellipsisType := by
  decide

-- ════════════════════════════════════════════════════
-- § 10. Nominal Spine
-- ════════════════════════════════════════════════════

/-- Positions in the nominal spine, ordered from lowest to highest.
    Parallels the clausal `SpinePos` for the nominal extended projection
    N(F0) → n(F1) → Num(F3) → D(F4).

    `NP_adj` parallels clausal `VP_adj`: the site of prenominal modifiers
    (adjectives in Spec of functional heads within nP) that are inside
    nP but NOT in n's complement (NP). This distinction matters for
    N-stranding NP-ellipsis ([benz-salzmann-2025]): prenominal
    adjectives survive n[E] (outside NP) but are deleted under Num[E]
    (inside nP). -/
inductive NomSpinePos where
  | N      -- Lexical noun (content)
  | NP_adj -- nP-internal modifier position (prenominal adjectives): inside nP, outside NP
  | n      -- Categorizer (gender/class, nominalizer; [marantz-2001])
  | Num    -- Number ([ritter-1991])
  | D      -- Determiner
  deriving DecidableEq, Repr

/-- Strict "in deletion domain of" relation on nominal spine positions.

    Parallels `SpinePos.isBelow` with the same complement-vs-adjunction
    distinction:

    - `N.isBelow .n = true`: N is in n's complement (NP)
    - `NP_adj.isBelow .n = false`: prenominal modifiers NOT in n's complement
    - `NP_adj.isBelow .Num = true`: prenominal modifiers ARE in Num's
      complement (nP) -/
def NomSpinePos.isBelow : NomSpinePos → NomSpinePos → Bool
  | .N, .NP_adj | .N, .n | .N, .Num | .N, .D => true
  | .NP_adj, .Num | .NP_adj, .D => true
  | .n, .Num | .n, .D => true
  | .Num, .D => true
  | _, _ => false

/-- Structural height comparison (non-strict) for nominal spine.
    Simple linear order: N ≤ NP_adj ≤ n ≤ Num ≤ D. -/
def NomSpinePos.isAtOrBelow : NomSpinePos → NomSpinePos → Bool
  | .N, _ => true
  | .NP_adj, .NP_adj | .NP_adj, .n | .NP_adj, .Num | .NP_adj, .D => true
  | .n, .n | .n, .Num | .n, .D => true
  | .Num, .Num | .Num, .D => true
  | .D, .D => true
  | _, _ => false

instance : DeletionSpine NomSpinePos where
  isBelow := NomSpinePos.isBelow
  isAtOrBelow := NomSpinePos.isAtOrBelow
  isBelow_irrefl := by intro p; cases p <;> decide
  isBelow_mono := by
    intro d p₁ p₂
    cases d <;> cases p₁ <;> cases p₂ <;>
      simp_all [NomSpinePos.isBelow, NomSpinePos.isAtOrBelow]

-- ════════════════════════════════════════════════════
-- § 11. Nominal Ellipsis Types and Predictions
-- ════════════════════════════════════════════════════

/-- A nominal ellipsis type: [E] on a head in the nominal spine.
    The deletion domain is the complement of the [E]-bearing head. -/
structure NomEllipsisType where
  ePosition : NomSpinePos
  name : String := ""
  deriving Repr

/-- Is a nominal position in the deletion domain? -/
def nomInDeletionDomain (c : NomSpinePos) (e : NomEllipsisType) : Prop :=
  inDomain c e.ePosition

instance (c : NomSpinePos) (e : NomEllipsisType) : Decidable (nomInDeletionDomain c e) := by
  unfold nomInDeletionDomain; infer_instance

/-- Does a nominal position survive ellipsis? -/
def nomSurvives (c : NomSpinePos) (e : NomEllipsisType) : Prop :=
  ¬ nomInDeletionDomain c e

instance (c : NomSpinePos) (e : NomEllipsisType) : Decidable (nomSurvives c e) := by
  unfold nomSurvives; infer_instance

/-- NumP-ellipsis: [E] on D, deletes everything below D.
    Determiner/demonstrative survives; N, adjectives, numerals deleted. -/
def numPEllipsis : NomEllipsisType := ⟨.D, "NumP-ellipsis"⟩

/-- nP-ellipsis: [E] on Num, deletes nP (complement of Num).
    Numeral and determiner survive; N, n, and prenominal adjectives deleted.
    [saab-2026]: Num[E] in Spanish pseudo-partitive/quantificational
    binominals. -/
def nPEllipsis : NomEllipsisType := ⟨.Num, "nP-ellipsis"⟩

/-- N-stranding NP-ellipsis: [E] on n, deletes only NP (complement of n).
    N survives via N-to-n head movement; prenominal adjectives survive
    (in nP, not NP). Postnominal dependents of N (PPs, relative clauses,
    genitive arguments) are in NP and are deleted.
    [benz-salzmann-2025]: German N-stranding NP-ellipsis. -/
def nStrandingNPE : NomEllipsisType := ⟨.n, "N-stranding NP-ellipsis"⟩

-- N-stranding NP-ellipsis: [E] on n

/-- Under N-stranding, NP-internal material (postnominal PPs, relatives,
    genitive arguments) is in the deletion domain. -/
theorem nStranding_deletes_NP :
    nomInDeletionDomain .N nStrandingNPE := by decide

/-- Under N-stranding, prenominal adjectives survive: they are inside nP
    but NOT in n's complement (NP).
    [benz-salzmann-2025] ex. (25): *Ich habe das schönste Auto und du
    das schönste Motorrad — adjective cannot be deleted. -/
theorem nStranding_adj_survives :
    nomSurvives .NP_adj nStrandingNPE := by decide

/-- Under N-stranding, the n head is external (it bears [E]). N moves
    here via N-to-n head movement and survives. -/
theorem nStranding_n_external :
    nomSurvives .n nStrandingNPE := by decide

/-- Under N-stranding, Num is external (numerals survive).
    [benz-salzmann-2025] ex. (25b): numeral *zwei* cannot be deleted
    under N-stranding. -/
theorem nStranding_num_survives :
    nomSurvives .Num nStrandingNPE := by decide

-- nP-ellipsis: [E] on Num

/-- Under nP-ellipsis, N is in the deletion domain (N does not survive). -/
theorem nPE_deletes_N :
    nomInDeletionDomain .N nPEllipsis := by decide

/-- Under nP-ellipsis, prenominal adjectives are deleted (inside nP). -/
theorem nPE_deletes_adj :
    nomInDeletionDomain .NP_adj nPEllipsis := by decide

/-- Under nP-ellipsis, n is deleted. -/
theorem nPE_deletes_n :
    nomInDeletionDomain .n nPEllipsis := by decide

/-- Under nP-ellipsis, Num is external (numerals survive).
    [saab-2026]: the numeral/determiner remnant in Spanish
    pseudo-partitive ellipsis. -/
theorem nPE_num_survives :
    nomSurvives .Num nPEllipsis := by decide

-- NumP-ellipsis: [E] on D

/-- Under NumP-ellipsis, everything below D is deleted. -/
theorem numPE_deletes_all :
    nomInDeletionDomain .N numPEllipsis ∧
    nomInDeletionDomain .NP_adj numPEllipsis ∧
    nomInDeletionDomain .n numPEllipsis ∧
    nomInDeletionDomain .Num numPEllipsis := by decide

-- Monotonicity across nominal ellipsis types

/-- Nominal monotonicity: N-stranding (n[E]) → nP-ellipsis (Num[E]) →
    NumP-ellipsis (D[E]) form a chain where lower [E] → smaller domain.
    Anything deleted under n[E] is also deleted under Num[E] and D[E]. -/
theorem nom_deletion_monotone :
    -- N is deleted under all three
    nomInDeletionDomain .N nStrandingNPE ∧
    nomInDeletionDomain .N nPEllipsis ∧
    nomInDeletionDomain .N numPEllipsis ∧
    -- NP_adj: NOT deleted under N-stranding, IS deleted under nP-ellipsis
    nomSurvives .NP_adj nStrandingNPE ∧
    nomInDeletionDomain .NP_adj nPEllipsis ∧
    -- n: NOT deleted under N-stranding, IS deleted under nP-ellipsis
    nomSurvives .n nStrandingNPE ∧
    nomInDeletionDomain .n nPEllipsis := by decide

-- ════════════════════════════════════════════════════
-- § 12. X-Stranding Instantiations
-- ════════════════════════════════════════════════════

/-- N-to-n movement instantiates generic X-stranding: N (base) is below
    n (landing), so when [E] is on n, N's base position is in the deletion
    domain but the n head (where N has moved) is external.
    [benz-salzmann-2025]: German N-stranding NP-ellipsis. -/
theorem n_stranding_is_xStranding :
    ¬ inDomain NomSpinePos.n NomSpinePos.n ∧
    inDomain NomSpinePos.N NomSpinePos.n :=
  xStranding NomSpinePos.n NomSpinePos.N (by decide)

/-- V-to-v movement is the clausal analogue: V (base) is below v (landing),
    so when [E] is on v, V's base position is deleted but v survives.
    This is exactly v-stranding VPE ([kalyakin-2026]). -/
theorem v_stranding_is_xStranding :
    ¬ inDomain SpinePos.v SpinePos.v ∧
    inDomain SpinePos.V SpinePos.v :=
  xStranding SpinePos.v SpinePos.V (by decide)

/-- The clausal and nominal X-stranding patterns are structurally
    identical: both are instances of the generic `xStranding` theorem
    at the F1 (categorizer) level of their respective extended projections.
    V:v :: N:n — the same abstract relationship. -/
theorem clausal_nominal_xStranding_parallel :
    -- Clausal: V below v
    inDomain SpinePos.V SpinePos.v ∧
    -- Nominal: N below n
    inDomain NomSpinePos.N NomSpinePos.n := by decide

end Minimalist.Ellipsis
