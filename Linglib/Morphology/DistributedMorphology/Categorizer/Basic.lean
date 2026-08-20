import Linglib.Morphology.DistributedMorphology.Root
import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Categorization

The categorizing heads n, v, a of Distributed Morphology merge with an
acategorial root to give it a syntactic category — the categorization
assumption. The same root index survives categorization and
re-categorization, which is what makes √HAMMER one root across *hammer*
and *to hammer*. Complement selection is a property of the root, and the
domain of idiosyncratic interpretation is bounded by Voice, not by the
categorizer.

## Main definitions

* `Categorizer` — the closed inventory n, v, a
* `Categorizer.toCategory` — the syntactic category of n, v, a
* `CategorizedRoot`, `Recategorization` — roots under a categorizer and
  layered derivation

## Main statements

* `same_root_different_category`, `recategorize_preserves_root` — one
  root index across categories, threaded unchanged through derivation
* `agentive_voice_is_phase` — Voice, not the categorizer, bounds special
  interpretation

## References

* [A. Marantz, *No escape from syntax*][marantz-1997]
* [H. Harley, *On the identity of roots*][harley-2014]
* [D. Embick and A. Marantz, *Architecture and blocking*][embick-marantz-2008]
-/

namespace DistributedMorphology

open Minimalist Minimalist.Voice
open Verb Verb.Root

/-! ### The categorizer inventory -/

/-- A categorizing head that merges with an acategorial root to project
    syntactic structure. The three options correspond to the functional
    heads n, v, a in Distributed Morphology ([marantz-1997], [harley-2014] §2). -/
inductive Categorizer where
  | n  -- nominal categorizer
  | v  -- verbal categorizer
  | a  -- adjectival categorizer
  deriving DecidableEq, Repr, Fintype

/-- The categorizer inventory is closed: unlike the open class of roots
(`Infinite Root`), the functional heads are exactly n, v, a. -/
theorem card_categorizer : Fintype.card Categorizer = 3 := rfl

/-- The syntactic category of a categorizer. -/
def Categorizer.toCategory : Categorizer → Cat
  | .n => .N
  | .v => .V
  | .a => .A

/-! ### CategorizedRoot -/

/-- A root merged with a categorizing head, yielding a syntactically
    projectable unit ([harley-2014] §2). The `root` atom is what survives
    (re)categorization (`recategorize_preserves_root`) and so what makes
    √HAMMER one root across *hammer* and *to hammer*; the `classification`
    is c-selection content ([harley-2014] §3) that unrelated roots may
    share, so it cannot individuate. -/
structure CategorizedRoot where
  /-- The acategorial root. -/
  root : DistributedMorphology.Root
  /-- The root's c-selection content (arity, change-type). -/
  classification : Classification
  /-- The categorizing head that gives it syntactic category. -/
  categorizer : Categorizer
  deriving DecidableEq, Repr

/-- The syntactic category of a categorized root, derived from its categorizer. -/
def CategorizedRoot.category (cr : CategorizedRoot) : Cat :=
  cr.categorizer.toCategory

/-! ### Cross-categorial identity and root complement selection

[harley-2014] §3's evidence that roots select their complements directly:
*one*-replacement (§3.1 — *this student of chemistry* rejects *that one of
physics* because the root selects the PP and projects √P, which *one*
targets), verb-object idioms (§3.2, after [kratzer-1996] — special
meanings arise for verb-object pairs while the agentive subject composes
freely), and morphological ergative splits (§3.3). Hiaki suppletion
conditioned by the object's number is the §2.1 sisterhood evidence. -/

/-- Same root + different categorizer → different syntactic category.
    This is the formal content of the claim that √HAMMER can surface as
    either a noun (hammer) or a verb (to hammer) — same root, different
    category, determined entirely by the categorizer ([harley-2014] §2). -/
theorem same_root_different_category (i : DistributedMorphology.Root) (r : Classification)
    (c1 c2 : Categorizer) (h : c1 ≠ c2) :
    (CategorizedRoot.mk i r c1).category ≠ (CategorizedRoot.mk i r c2).category := by
  simp only [CategorizedRoot.category, Categorizer.toCategory]
  cases c1 <;> cases c2 <;> simp_all

/-- Complement valency is a root-level property, unaltered by the
categorizer ([harley-2014] §3). This covers c-selection, not l-selection,
which [hewett-2026] shows can vary by verbal template (`Hewett2026`). -/
theorem complement_selection_at_root_level (i : DistributedMorphology.Root) (r : Classification)
    (c1 c2 : Categorizer) :
    (CategorizedRoot.mk i r c1).classification.valency
      = (CategorizedRoot.mk i r c2).classification.valency := rfl

/-! ### Layered Derivation (Denominal, Deadjectival, Deverbal) -/

/-- A re-categorization further categorizes an already categorized root,
as in √SHELF + n (*shelf*) + v (*to shelve*). Idiosyncratic
interpretation can survive the inner categorizer ([harley-2014] §4). -/
inductive Recategorization where
  | denominal    -- n → v (to hammer, to shelve)
  | deadjectival -- a → v (to flatten, to widen)
  | deverbal_n   -- v → n (a build, a throw)
  | deverbal_a   -- v → a (broken, flattened)
  deriving DecidableEq, Repr

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
    some { root := cr.root, classification := cr.classification, categorizer := rc.target }
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

/-- The acategorial root survives (re)categorization, so *shelf* (n) and
    *to shelve* (v) share one List-1 root ([harley-2014] §2, §4). -/
theorem recategorize_preserves_root (cr cr' : CategorizedRoot)
    (rc : Recategorization) (h : cr.recategorize rc = some cr') :
    cr'.root = cr.root := by
  unfold CategorizedRoot.recategorize at h
  split at h
  case isTrue => simp only [Option.some.injEq] at h; rw [← h]
  case isFalse => simp at h

/-- A denominal verb and a directly verbal root yield the same syntactic
    category (V), but have different internal structure. √HAMMER + v gives
    V directly; √HAMMER + n + v also gives V but via layered derivation.
    This structural ambiguity is invisible at the category level
    ([harley-2014] §2). -/
theorem denominal_yields_verbal (i : DistributedMorphology.Root) (r : Classification) :
    ∃ cr, (CategorizedRoot.mk i r .n).recategorize .denominal = some cr ∧
          cr.category = Cat.V :=
  ⟨⟨i, r, .v⟩, rfl, rfl⟩

/-- Deadjectival derivation (a → v) connects to [embick-2004]'s result-stative
    structure ([AspP AspR [vP DP v_become √ROOT]]): in DM terms, a root first
    categorized by a, then further categorized by v. -/
theorem deadjectival_source_target :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

/-! ### VoiceP as phase boundary

[harley-2014] §4: the phase head above the root is Voice, not the
categorizer. Multiply derived words carry idiosyncratic senses above the
first categorizer ((36) *editor-ial*, *classifi-eds*, *national-ize*),
while the external argument that Voice introduces stays compositional. -/

/-- Agentive Voice is a phase head — the boundary above which
    interpretation must be compositional. [harley-2014] §4: "Voice is the
    phase head, not v"; the categorizer inventory here accordingly carries
    no phasal structure at all, so the special-interpretation domain
    extends past n, v, a and closes only at Voice. -/
theorem agentive_voice_is_phase : agentive.IsPhasal := by decide

/-- Voice introduces the external argument ([harley-2014] §4, following
    [kratzer-1996]). The categorizer does NOT introduce arguments —
    complement selection is a root property ([harley-2014] §3). -/
theorem voice_introduces_external_arg :
    agentive.HasD ∧ agentive.AssignsTheta := by
  refine ⟨?_, ?_⟩ <;> decide

end DistributedMorphology
