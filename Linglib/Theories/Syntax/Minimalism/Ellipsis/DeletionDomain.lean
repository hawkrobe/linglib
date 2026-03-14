import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Core.RootDimensions

/-!
# Merchant's Theory of Ellipsis: [E] Features and Deletion Domains
@cite{merchant-2001} @cite{merchant-2013}

The [E] feature on a functional head triggers PF-deletion of the head's
complement and presupposes e-GIVENness (@cite{merchant-2001}). Different
ellipsis types correspond to different [E] positions in the clausal spine.

## Key Insight (@cite{merchant-2013}, Figure 1)

Voice mismatch tolerance tracks the *height* of ellipsis:
- **VPE** ([E] on Voice; @cite{merchant-2013} adopts Voice[E],
  eliding vP): Voice is *external* → voice mismatch OK
- **Sluicing** ([E] on C): elides TP, Voice is *internal* → voice mismatch blocked
- **vVPE** ([E] on v): elides VP, both v and Voice are *external* →
  voice *and* transitivity mismatches OK (@cite{kalyakin-2026})

The generalization: a mismatch in feature F is tolerated iff the head
bearing F is *outside* the deletion domain (i.e., at or above the [E]-
bearing head in the clausal spine).

## Monotonicity (@cite{sailor-2014}'s Generalization)

Lower [E] position → smaller deletion domain → more features external
→ more mismatches tolerated. This is a strict monotonicity: if ellipsis
type A tolerates a mismatch, every type with a lower [E] position does too.
-/

namespace Minimalism.Ellipsis

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
    for vVPE (@cite{kalyakin-2026}): VP-adjuncts survive when [E] is on
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
  deriving DecidableEq, BEq, Repr

/-- Strict "in deletion domain of" relation on spine positions.

    `isBelow p₁ p₂` means "p₁ is inside the deletion domain when [E]
    is at p₂." This is NOT a simple structural ordering — it encodes
    the complement-vs-adjunction distinction:

    - `V.isBelow .v = true`: V is in v's complement (VP)
    - `VP_adj.isBelow .v = false`: VP-adjuncts are NOT in v's complement
    - `VP_adj.isBelow .Voice = true`: VP-adjuncts ARE inside Voice's
      complement (vP contains the full VP projection including adjuncts)

    This distinction is what makes vVPE (@cite{kalyakin-2026}) predict
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

/-- Is a spine position inside the deletion domain of an ellipsis type?
    A position is in the deletion domain iff it is strictly below the
    [E]-bearing head. -/
def isInDeletionDomain (c : SpinePos) (e : EllipsisType) : Bool :=
  c.isBelow e.ePosition

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
    Attested in Muira Dargwa complex predicates (@cite{kalyakin-2026}). -/
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
    Regulated by distinct v heads below Voice (@cite{merchant-2013} §3.3). -/
def dativeAlternation : MismatchDimension := ⟨"dative alternation", .v⟩

/-- Applicative/prepositional alternation: embroider X with Y vs embroider Y on X.
    Regulated by applicative v heads below Voice (@cite{merchant-2013} §3.3). -/
def prepAlternation : MismatchDimension := ⟨"prepositional alternation", .v⟩

/-- Transitive/middle alternation: they market ethanol vs ethanol markets well.
    Regulated by v heads determining external argument realization
    (@cite{merchant-2013} §3.3). -/
def middleAlternation : MismatchDimension := ⟨"middle alternation", .v⟩

/-- A mismatch in dimension d is tolerated by ellipsis type e iff the
    head bearing the feature is NOT in the deletion domain — i.e., it
    is at or above the [E]-bearing head. -/
def canMismatch (e : EllipsisType) (d : MismatchDimension) : Bool :=
  !isInDeletionDomain d.headPosition e

-- ════════════════════════════════════════════════════
-- § 4. Core Predictions
-- ════════════════════════════════════════════════════

-- English VPE: [E] on Voice

/-- English VPE tolerates voice mismatches: Voice is external to vP. -/
theorem englishVPE_voice_ok :
    canMismatch englishVPE voiceMismatch = true := by native_decide

/-- English VPE blocks transitivity mismatches: v is inside vP. -/
theorem englishVPE_transitivity_blocked :
    canMismatch englishVPE transitivityMismatch = false := by native_decide

/-- English VPE blocks lexical verb mismatches: V is inside vP. -/
theorem englishVPE_lexical_blocked :
    canMismatch englishVPE lexicalMismatch = false := by native_decide

-- Sluicing: [E] on C

/-- Sluicing blocks voice mismatches: Voice is inside TP. -/
theorem sluicing_voice_blocked :
    canMismatch sluicing voiceMismatch = false := by native_decide

/-- Sluicing blocks transitivity mismatches: v is inside TP. -/
theorem sluicing_transitivity_blocked :
    canMismatch sluicing transitivityMismatch = false := by native_decide

-- v-stranding VPE: [E] on v

/-- vVPE tolerates voice mismatches: Voice is external to VP. -/
theorem vVPE_voice_ok :
    canMismatch vVPE voiceMismatch = true := by native_decide

/-- vVPE tolerates transitivity mismatches: v is external to VP. -/
theorem vVPE_transitivity_ok :
    canMismatch vVPE transitivityMismatch = true := by native_decide

/-- vVPE blocks lexical verb mismatches: V is inside VP. -/
theorem vVPE_lexical_blocked :
    canMismatch vVPE lexicalMismatch = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Monotonicity
-- ════════════════════════════════════════════════════

/-- If a head is outside the deletion domain at position p₁, then it
    is also outside the deletion domain at any lower position p₂.
    This is @cite{sailor-2014}'s monotonicity: lower [E] → smaller
    domain → more mismatches tolerated. -/
private theorem isBelow_monotone (d p₁ p₂ : SpinePos)
    (h₁ : d.isBelow p₁ = false) (h₂ : p₂.isAtOrBelow p₁ = true) :
    d.isBelow p₂ = false := by
  cases d <;> cases p₁ <;> cases p₂ <;>
    simp_all [SpinePos.isBelow, SpinePos.isAtOrBelow]

/-- Monotonicity of mismatch tolerance: if ellipsis type e₁ tolerates
    a mismatch dimension d, then any ellipsis type e₂ whose [E] position
    is at or below e₁'s also tolerates d. -/
theorem mismatch_monotone (d : MismatchDimension) (e₁ e₂ : EllipsisType)
    (h₁ : canMismatch e₁ d = true)
    (h₂ : e₂.ePosition.isAtOrBelow e₁.ePosition = true) :
    canMismatch e₂ d = true := by
  simp only [canMismatch, isInDeletionDomain, Bool.not_eq_true'] at *
  exact isBelow_monotone d.headPosition e₁.ePosition e₂.ePosition h₁ h₂

-- ════════════════════════════════════════════════════
-- § 6. Root Attachment Position
-- ════════════════════════════════════════════════════

/-- Is a root inside the vVPE deletion domain (= VP)?
    Uses `RootPosition` from `Core.RootDimensions` (Marantz 2013,
    @cite{beavers-koontz-garboden-2020}):
    - `.complement` roots (change-of-state) are inside VP → deleted
    - `.adjoined` roots (manner/activity) are outside VP → survive -/
def rootInVVPEDomain : RootPosition → Bool
  | .complement => true
  | .adjoined => false

/-- Complement roots (change-of-state) are deleted under vVPE. -/
theorem complementRoot_in_vVPE : rootInVVPEDomain .complement = true := rfl

/-- Adjoined roots (manner/activity) survive vVPE — they are outside
    the deletion domain. This is why antipassive roots block vVPE in
    Muira Dargwa: antipassive coerces adjunction (@cite{kalyakin-2026}). -/
theorem adjoinedRoot_outside_vVPE : rootInVVPEDomain .adjoined = false := rfl

-- ════════════════════════════════════════════════════
-- § 7. Again Ambiguity
-- ════════════════════════════════════════════════════

/-- Adjunction position of *again*, following @cite{merchant-2013}
    (building on Johnson 2004, von Stechow 1996). -/
inductive AgainPosition where
  | vP_adjunction  -- Repetitive: event-level *again* (high)
  | VP_adjunction  -- Restitutive: result-state *again* (low)
  deriving DecidableEq, BEq, Repr

/-- Is an *again* reading available under a given ellipsis type?

    Repetitive *again* adjoins high (vP or VoiceP): modeled at `Voice`
    level — outside the deletion domain of both VPE and vVPE.

    Restitutive *again* adjoins to VP — modeled at `VP_adj`. This is
    inside vP (deleted under English VPE, [E] on Voice) but NOT inside
    v's complement (survives vVPE, [E] on v). The distinction between
    `VP_adj` and `V` is crucial: V (the head) is in v's complement,
    but VP-adjunction is at the complement boundary, outside it. -/
def againSurvives (pos : AgainPosition) (e : EllipsisType) : Bool :=
  match pos with
  | .vP_adjunction => !isInDeletionDomain .Voice e   -- VoiceP-level adjunction
  | .VP_adjunction => !isInDeletionDomain .VP_adj e   -- VP-adjunction level

/-- Under English VPE, restitutive *again* is inside the deletion domain
    (deleted), while repetitive *again* survives.
    @cite{merchant-2013}: only repetitive reading available (Johnson 2004
    exx. 49a–b). -/
theorem englishVPE_again :
    againSurvives .vP_adjunction englishVPE = true ∧
    againSurvives .VP_adjunction englishVPE = false := by native_decide

/-- Under vVPE, BOTH readings survive: restitutive *again* (VP-adjoined)
    is outside v's complement, so it is not deleted.
    @cite{kalyakin-2026} §4.1 (exx. 52a–b): both repetitive and
    restitutive ʔibrra 'again' are available under vVPE in Muira Dargwa.
    This is the key diagnostic proving the deletion domain is VP (smaller
    than English VPE's vP). -/
theorem vVPE_again :
    againSurvives .vP_adjunction vVPE = true ∧
    againSurvives .VP_adjunction vVPE = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Cross-Linguistic Comparison
-- ════════════════════════════════════════════════════

/-- English VPE and vVPE agree on voice: both tolerate voice mismatches. -/
theorem voice_agreement :
    canMismatch englishVPE voiceMismatch = true ∧
    canMismatch vVPE voiceMismatch = true := ⟨rfl, rfl⟩

/-- English VPE and vVPE diverge on transitivity: English blocks it,
    vVPE allows it. This is the key prediction that distinguishes the
    two ellipsis types. -/
theorem transitivity_divergence :
    canMismatch englishVPE transitivityMismatch = false ∧
    canMismatch vVPE transitivityMismatch = true := ⟨rfl, rfl⟩

/-- Both block lexical verb mismatches: V is inside the deletion domain
    of both English VPE and vVPE. -/
theorem lexical_blocked_both :
    canMismatch englishVPE lexicalMismatch = false ∧
    canMismatch vVPE lexicalMismatch = false := ⟨rfl, rfl⟩

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
  /-- Verbal Identity Requirement (@cite{goldberg-2005}): antecedent and
      target light verbs must be identical in root and derivational
      morphology. Active in Persian and Bangla; inactive in Muira Dargwa. -/
  virRequired : Bool
  /-- Language label -/
  language : String
  deriving Repr

/-- Muira Dargwa vVPE: [E] on v, deletion domain = VP.
    Both *again* readings survive; arg-structure alternations tolerated;
    LV mismatches tolerated (@cite{kalyakin-2026} ex. 78). -/
def muiraDargwaVVPE : VPEProfile :=
  { ellipsisType := vVPE, virRequired := false, language := "Muira Dargwa" }

/-- Persian vVPE: [E] on v, deletion domain = VP.
    Both *again* readings survive (@cite{toosarvandani-2009} ex. 90).
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
    SpinePos.v.isBelow SpinePos.Voice = true := ⟨rfl, rfl, rfl⟩

/-- The *again* test correctly differentiates Bangla (vP domain) from
    Muira Dargwa (VP domain): restitutive *again* is deleted under
    Bangla's ellipsis but survives Muira Dargwa's. -/
theorem again_differentiates_bangla_dargwa :
    againSurvives .VP_adjunction banglaVVPE.ellipsisType = false ∧
    againSurvives .VP_adjunction muiraDargwaVVPE.ellipsisType = true := by
  native_decide

end Minimalism.Ellipsis
