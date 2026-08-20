import Linglib.Core.Data.RoseTree.Leaves
import Linglib.Morphology.DistributedMorphology.Root
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Categorization

Word formation is syntactic: a categorizing head n, v, or a merges with
an acategorial root — the categorization assumption — and layered
derivation is more of the same merger, [v [n √SHELF]] for *to shelve*
beside [n √SHELF] for *shelf*. Word-internal structure is a nonplanar
tree over root and head leaves, the same carrier shape as syntactic and
morphological objects elsewhere in the library, so the root's survival
across (re)categorization and the structural difference between direct
and layered derivation are facts about leaves rather than stipulations.

## Main definitions

* `Categorizer` — the closed inventory n, v, a
* `WordStructure` — word-internal structure over a head alphabet:
  `Categorizer` for the bare theory, `CatHead`
  (`Categorizer/Gender.lean`) when heads carry φ-content
* `categorize`, `roots`, `heads`, `Headed` — head merger, the two leaf
  projections, and outermost headedness

## Main statements

* `roots_categorize` — categorization does not touch root leaves: one
  root index across categories and layers
* `categorize_ne_of_ne`, `categorize_categorize_ne` — distinct heads
  build distinct structures, and layered derivation differs from direct
  derivation even when the outermost head agrees
* `agentive_voice_is_phase` — Voice, not the categorizer, bounds special
  interpretation

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [A. Marantz, *No escape from syntax*][marantz-1997]
* [H. Harley, *On the identity of roots*][harley-2014]
* [D. Embick and A. Marantz, *Architecture and blocking*][embick-marantz-2008]
-/

namespace DistributedMorphology

open Minimalist Minimalist.Voice RoseTree

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

/-! ### Word-internal structure

Distributed Morphology builds words with the same binary structure
building as sentences ([halle-marantz-1993]): a categorized root is the
configuration [x √], not a kind of object, and re-categorization is
merger of a further head. The carrier is a nonplanar tree whose leaves
are acategorial roots or categorizing heads and whose internal vertices
are bare. -/

/-- Word-internal syntactic structure over head labels `H`: a nonplanar
tree whose leaves are acategorial roots or heads and whose internal
vertices are bare. -/
abbrev WordStructure (H : Type*) :=
  Nonplanar ((Root ⊕ H) ⊕ Unit)

variable {H : Type*}

/-- The structure consisting of a bare root. -/
def ofRoot (r : Root) : WordStructure H :=
  Nonplanar.leaf (.inl (.inl r))

/-- The structure consisting of a bare head. -/
def ofHead (h : H) : WordStructure H := Nonplanar.leaf (.inl (.inr h))

/-- Merge a categorizing head with a structure: the configuration [h T].
Categorization is `categorize h (ofRoot r)`; re-categorization is
another `categorize` on top — *to shelve* is
`categorize .v (categorize .n (ofRoot shelf))` — and every further
derivation (*happi-ness* a → n, *boy-ish* n → a) is simply another
instance, with no inventory of re-categorization types to extend. -/
noncomputable def categorize (h : H) (T : WordStructure H) : WordStructure H :=
  Nonplanar.node (.inr ()) (ofHead h ::ₘ {T})

/-- The root leaves: the List-1 content of a word structure. -/
def roots (T : WordStructure H) : Multiset Root :=
  T.leaves.filterMap fun x => x.getLeft?.bind Sum.getLeft?

/-- The head leaves: the functional content of a word structure. -/
def heads (T : WordStructure H) : Multiset H :=
  T.leaves.filterMap fun x => x.getLeft?.bind Sum.getRight?

@[simp] theorem roots_ofRoot (r : Root) :
    roots (ofRoot r : WordStructure H) = {r} := rfl

@[simp] theorem roots_ofHead (h : H) :
    roots (ofHead h : WordStructure H) = 0 := rfl

@[simp] theorem heads_ofHead (h : H) :
    heads (ofHead h : WordStructure H) = {h} := rfl

@[simp] theorem heads_ofRoot (r : Root) :
    heads (ofRoot r : WordStructure H) = 0 := rfl

/-- Categorization does not touch root leaves: the same root index
survives categorization and re-categorization — √HAMMER is one root
across *hammer* and *to hammer* ([harley-2014] §2, §4) — and with it
every piece of root-level lexical content. C-selection is therefore
untouched by the categorizer ([harley-2014] §3: *one*-replacement,
verb-object idioms, ergative splits), in contrast with l-selection,
which varies with the functional structure (`Hewett2026`). -/
theorem roots_categorize (h : H) (T : WordStructure H) :
    roots (categorize h T) = roots T := by
  rw [categorize, roots, Nonplanar.leaves_node_cons, Multiset.filterMap_add,
    show Multiset.filterMap (fun x => x.getLeft?.bind Sum.getLeft?)
      (ofHead h : WordStructure H).leaves
      = (0 : Multiset Root) from rfl]
  simp [roots]

/-- Each categorization contributes exactly its head. -/
theorem heads_categorize (h : H) (T : WordStructure H) :
    heads (categorize h T) = h ::ₘ heads T := by
  rw [categorize, heads, Nonplanar.leaves_node_cons, Multiset.filterMap_add]
  rw [show Multiset.filterMap (fun x => x.getLeft?.bind Sum.getRight?)
      (ofHead h : WordStructure H).leaves = {h} from rfl]
  simp [heads, Multiset.singleton_add]

/-- Each categorization adds one leaf. -/
theorem numLeaves_categorize (h : H) (T : WordStructure H) :
    (categorize h T).numLeaves = T.numLeaves + 1 := by
  rw [← Nonplanar.card_leaves, categorize, Nonplanar.leaves_node_cons,
    Multiset.card_add]
  simp [ofHead, Nonplanar.card_leaves, Nat.add_comm]

/-- Outermost headedness: the structure is the head itself, or was built
by merging it last. -/
inductive Headed : WordStructure H → H → Prop
  | ofHead (h : H) : Headed (ofHead h) h
  | categorize (h : H) (T : WordStructure H) : Headed (categorize h T) h

/-- Same base, different categorizer, different structure: √HAMMER under
n (*hammer*) and under v (*to hammer*) are distinct objects
([marantz-1997], [harley-2014] §2). -/
theorem categorize_ne_of_ne {h h' : H} (hne : h ≠ h') (T : WordStructure H) :
    categorize h T ≠ categorize h' T := fun he => by
  have hh := congrArg heads he
  rw [heads_categorize, heads_categorize] at hh
  exact hne ((Multiset.cons_inj_left _).mp hh)

/-- Layered derivation is structurally distinct from direct derivation
even when the outermost head agrees: [v [n √SHELF]] (*to shelve*) is not
[v √SHELF], though both are `Headed` by v — the ambiguity a bare
category label hides ([harley-2014] §2, §4). -/
theorem categorize_categorize_ne (h₁ h₂ h₃ : H) (T : WordStructure H) :
    categorize h₁ (categorize h₂ T) ≠ categorize h₃ T := fun he => by
  have := congrArg Nonplanar.numLeaves he
  rw [numLeaves_categorize, numLeaves_categorize, numLeaves_categorize] at this
  omega

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
