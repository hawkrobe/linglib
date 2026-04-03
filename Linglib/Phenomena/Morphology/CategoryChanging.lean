/-!
# Category-Changing Morphology: English Root Families
@cite{marantz-1997}

Theory-neutral empirical data on English roots that surface across multiple
lexical categories via different morphological processes.

## Data Source

Standard examples from the Distributed Morphology literature.

## Empirical Generalization

Many English roots can appear as nouns, verbs, and adjectives. The
category of the resulting word is determined by the morphological
environment (suffixation, zero-derivation, syntactic context), not
by inherent properties of the root itself.
-/

namespace Phenomena.Morphology.CategoryChanging

-- ============================================================================
-- § 1: Lexical Category
-- ============================================================================

/-- The lexical category of a word form (theory-neutral). -/
inductive LexCat where
  | noun
  | verb
  | adjective
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2: Root Families
-- ============================================================================

/-- A root family: a set of word forms derived from a common root,
    each appearing in a different lexical category. -/
structure RootFamily where
  /-- Label for the root (approximate; roots are sub-morphemic) -/
  rootLabel : String
  /-- Word forms and their categories -/
  forms : List (String × LexCat)
  deriving Repr

/-- Does this root family have a form in the given category? -/
def RootFamily.hasCategory (rf : RootFamily) (c : LexCat) : Bool :=
  rf.forms.any (·.2 == c)

/-- How many distinct categories does this root family span? -/
def RootFamily.categoryCount (rf : RootFamily) : Nat :=
  let cats := rf.forms.map (·.2) |>.eraseDups
  cats.length

-- ============================================================================
-- § 3: English Root Families (@cite{panagiotidis-2015} §5.2, @cite{marantz-1997})
-- ============================================================================

/-- √DESTROY: destroy (V), destruction (N), destructive (A) -/
def destroy : RootFamily := ⟨"DESTROY",
  [("destroy", .verb), ("destruction", .noun), ("destructive", .adjective)]⟩

/-- √BEAUTY: beautify (V), beauty (N), beautiful (A) -/
def beauty : RootFamily := ⟨"BEAUTY",
  [("beautify", .verb), ("beauty", .noun), ("beautiful", .adjective)]⟩

/-- √CLEAR: clear (V), clarity (N), clear (A) -/
def clear : RootFamily := ⟨"CLEAR",
  [("clear", .verb), ("clarity", .noun), ("clear", .adjective)]⟩

/-- √PRODUCE: produce (V), product/production (N), productive (A) -/
def produce : RootFamily := ⟨"PRODUCE",
  [("produce", .verb), ("production", .noun), ("productive", .adjective)]⟩

/-- √CREATE: create (V), creation (N), creative (A) -/
def create : RootFamily := ⟨"CREATE",
  [("create", .verb), ("creation", .noun), ("creative", .adjective)]⟩

/-- √ACT: act (V), action (N), active (A) -/
def act : RootFamily := ⟨"ACT",
  [("act", .verb), ("action", .noun), ("active", .adjective)]⟩

/-- All sample root families. -/
def allFamilies : List RootFamily :=
  [destroy, beauty, clear, produce, create, act]

-- ============================================================================
-- § 4: Empirical Generalizations
-- ============================================================================

/-- Every root in our sample spans all three categories. -/
theorem all_families_tricategorial :
    allFamilies.all (·.hasCategory .noun) = true ∧
    allFamilies.all (·.hasCategory .verb) = true ∧
    allFamilies.all (·.hasCategory .adjective) = true := by
  native_decide

/-- Every root in our sample has exactly 3 forms. -/
theorem all_families_three_forms :
    allFamilies.all (fun rf => rf.forms.length == 3) = true := by
  native_decide

end Phenomena.Morphology.CategoryChanging
