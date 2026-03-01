import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Categorizing Heads (Distributed Morphology) @cite{harley-2014}
@cite{acquaviva-2008} @cite{embick-2004} @cite{marantz-1997} @cite{pfau-2000}

Harley (2014) "On the identity of roots" addresses three questions about
roots in DM:

1. **What are roots?** (§2) Root terminal nodes are individuated by arbitrary
   indices (Pfau 2000, Acquaviva 2008), not by phonological or semantic content.
   The **Categorization Assumption** holds: roots must merge with a categorizing
   head (n, v, a) to enter the syntax.

2. **Can roots take complements?** (§3) Yes — roots can Merge directly with
   internal arguments without mediation by a functional head. Evidence:
   *one*-replacement in argument structure nominals, verb-object idioms,
   Hiaki suppletive verbs conditioned by the root's complement.

3. **What delimits the domain of special interpretation?** (§4) VoiceP, not
   the first categorizing head. Idiosyncratic interpretation can extend past
   the first categorizer (evidence: multiply derived words like *editorial*,
   *classifieds*, *nationalize*). Voice is the phase head.

## DM Three-Lists Architecture (Marantz 1997, Harley 2014 §5)

- **List 1**: Root terminal nodes — syntactic atoms with opaque indices
- **List 2**: Vocabulary Items — phonological realizations competing for insertion
- **List 3**: Encyclopedia entries — interpretations conditioned by context

This module formalizes the categorization layer and its relationship to Voice.
List 2/3 architecture is left for future work.

-/

namespace Morphology.DM

open Minimalism

-- ============================================================================
-- § 1: Categorizer Type
-- ============================================================================

/-- A categorizing head that merges with an acategorial root to project
    syntactic structure. The three options correspond to the functional
    heads n, v, a in Distributed Morphology (Marantz 1997, Harley 2014 §2). -/
inductive Categorizer where
  | n  -- nominal categorizer
  | v  -- verbal categorizer
  | a  -- adjectival categorizer
  deriving DecidableEq, BEq, Repr

/-- Map a categorizer to its syntactic category. -/
def Categorizer.toCategory : Categorizer → Cat
  | .n => .N
  | .v => .V
  | .a => .A

-- ============================================================================
-- § 2: CategorizedRoot
-- ============================================================================

/-- A root that has been merged with a categorizing head, yielding a
    syntactically projectable unit (Harley 2014 §2). -/
structure CategorizedRoot where
  /-- The acategorial root (arity, change-type, etc.) -/
  root : Root
  /-- The categorizing head that gives it syntactic category -/
  categorizer : Categorizer
  deriving BEq, Repr

/-- The syntactic category of a categorized root, derived from its categorizer. -/
def CategorizedRoot.category (cr : CategorizedRoot) : Cat :=
  cr.categorizer.toCategory

-- ============================================================================
-- § 3: Cross-Categorial Identity and Root Complement Selection
-- ============================================================================

/-- Same root + different categorizer → different syntactic category.
    This is the formal content of the claim that √HAMMER can surface as
    either a noun (hammer) or a verb (to hammer) — same root, different
    category, determined entirely by the categorizer (Harley 2014 §2). -/
theorem same_root_different_category (r : Root) (c1 c2 : Categorizer)
    (h : c1 ≠ c2) :
    (CategorizedRoot.mk r c1).category ≠ (CategorizedRoot.mk r c2).category := by
  simp only [CategorizedRoot.category, Categorizer.toCategory]
  cases c1 <;> cases c2 <;> simp_all

/-- Complement selection is a root-level property, not contributed by the
    categorizer (Harley 2014 §3). Evidence:

    1. *one*-replacement in argument structure nominals: "the proud owner
       of a large dog" → "the proud one" — *one* replaces nP including
       √OWN + complement, showing the root took its complement directly.
    2. Verb-object idioms: *kick the bucket* — √KICK selects *the bucket*
       directly under vP, not via mediation by v.
    3. Hiaki suppletive verbs: suppletive forms are conditioned by the
       root's complement (singular vs. plural object), showing locality
       between root and argument below the categorizer.

    In our formalization, `RootArity.selectsTheme` captures this: the
    root obligatorily selects an internal argument at the root level,
    and this persists regardless of which categorizer it merges with. -/
theorem complement_selection_at_root_level (r : Root) (c1 c2 : Categorizer) :
    (CategorizedRoot.mk r c1).root.arity = (CategorizedRoot.mk r c2).root.arity := rfl

/-- A theme-selecting root maintains its complement requirement regardless
    of whether it surfaces as a noun, verb, or adjective (Harley 2014 §3). -/
theorem theme_selecting_root_always_selects (r : Root) (c : Categorizer)
    (h : r.arity = .selectsTheme) :
    (CategorizedRoot.mk r c).root.arity.hasInternalArg = true := by
  simp [h, RootArity.hasInternalArg]

-- ============================================================================
-- § 4: Layered Derivation (Denominal, Deadjectival, Deverbal)
-- ============================================================================

/-- Layered derivational morphology: a root categorized by one head can be
    further categorized by another, yielding derived forms. For example,
    √SHELF + n → shelf, then + v → to shelve (denominal verb).

    Harley (2014 §4) uses multiply derived words (*editor-ial*,
    *class-ifi-eds*, *national-ize*) to argue that idiosyncratic
    interpretation can extend past the first categorizer — the phase
    boundary is at Voice, not at the inner categorizer. -/
inductive Recategorization where
  | denominal    -- n → v (to hammer, to shelve)
  | deadjectival -- a → v (to flatten, to widen)
  | deverbal_n   -- v → n (a build, a throw)
  | deverbal_a   -- v → a (broken, flattened)
  deriving DecidableEq, BEq, Repr

/-- The source categorizer of a re-categorization. -/
def Recategorization.source : Recategorization → Categorizer
  | .denominal    => .n
  | .deadjectival => .a
  | .deverbal_n   => .v
  | .deverbal_a   => .v

/-- The target categorizer of a re-categorization. -/
def Recategorization.target : Recategorization → Categorizer
  | .denominal    => .v
  | .deadjectival => .v
  | .deverbal_n   => .n
  | .deverbal_a   => .a

/-- Apply a re-categorization to a categorized root. Returns `none` if the
    root's current categorizer doesn't match the expected source. -/
def CategorizedRoot.recategorize (cr : CategorizedRoot)
    (rc : Recategorization) : Option CategorizedRoot :=
  if cr.categorizer = rc.source then
    some { root := cr.root, categorizer := rc.target }
  else
    none

/-- Denominal verbs start from n-categorized roots. -/
theorem denominal_requires_n (cr : CategorizedRoot) (cr' : CategorizedRoot)
    (h : cr.recategorize .denominal = some cr') :
    cr.categorizer = .n := by
  unfold CategorizedRoot.recategorize at h
  simp only [Recategorization.source] at h
  split at h <;> simp_all

/-- Re-categorization yields the target categorizer. -/
theorem recategorization_changes_category (cr : CategorizedRoot)
    (rc : Recategorization) (cr' : CategorizedRoot)
    (h : cr.recategorize rc = some cr') :
    cr'.categorizer = rc.target := by
  unfold CategorizedRoot.recategorize at h
  split at h
  case isTrue => simp only [Option.some.injEq] at h; rw [← h]
  case isFalse => simp at h

/-- A denominal verb and a directly verbal root yield the same syntactic
    category (V), but have different internal structure. √HAMMER + v gives
    V directly; √HAMMER + n + v also gives V but via layered derivation.
    This structural ambiguity is invisible at the category level
    (Harley 2014 §2, p. 253). -/
theorem denominal_yields_verbal (r : Root) :
    ∃ cr, (CategorizedRoot.mk r .n).recategorize .denominal = some cr ∧
          cr.category = Cat.V :=
  ⟨⟨r, .v⟩, rfl, rfl⟩

/-- Deadjectival derivation (a → v) connects to Embick's (2004)
    resultStative structure: what RootTypology calls
    `AdjectivalStructure.resultStative` is, in DM terms, a root
    first categorized by a, then further categorized by v. -/
theorem deadjectival_source_target :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: VoiceP as Phase Boundary
-- ============================================================================

/- Harley (2014 §4) argues that the first phase head above the root is
   **Voice**, not the categorizer. Evidence:

   1. Multiply derived words can have idiosyncratic interpretations even
      above the first categorizer (*editorial* = related to editing,
      *classifieds* = classified ads, *nationalize* = make state-owned).
   2. Phrasal idioms (*kick the bucket*) involve idiosyncratic interpretation
      up to VoiceP but the external argument is always compositional
      (Kratzer 1996, Marantz 1997).
   3. Agentive Voice introduces the external argument and closes off the
      domain of idiosyncratic interpretation.

   Formal consequence: categorizers are never phase heads,
   while `VoiceHead.phaseHead` can be `true`. -/

/-- Categorizers are never phase heads (Harley 2014 §4). -/
def Categorizer.isPhaseHead : Categorizer → Bool
  | _ => false

/-- No categorizer is a phase head (Harley 2014 §4). -/
theorem categorizer_never_phase (c : Categorizer) :
    c.isPhaseHead = false := by cases c <;> rfl

/-- Agentive Voice IS a phase head — it demarcates the boundary above which
    interpretation must be compositional (Harley 2014 §4). -/
theorem agentive_voice_is_phase : voiceAgent.phaseHead = true := rfl

/-- The phase-boundary asymmetry: Voice can be a phase head while
    categorizers never are. This is why idiosyncratic interpretation
    extends past categorizers but not past Voice (Harley 2014 §4). -/
theorem phase_boundary_at_voice_not_categorizer (c : Categorizer) :
    c.isPhaseHead = false ∧ voiceAgent.phaseHead = true :=
  ⟨by cases c <;> rfl, rfl⟩

/-- Voice introduces the external argument (Harley 2014 §4, following
    Kratzer 1996). The categorizer does NOT introduce arguments —
    complement selection is a root property (§3). -/
theorem voice_introduces_external_arg :
    voiceAgent.hasD = true ∧ voiceAgent.assignsTheta = true :=
  ⟨rfl, rfl⟩

end Morphology.DM
