import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Process.RuleBased.Defs

/-!
# Tagalog Phonological Inventory and Nasal Substitution
@cite{hayes-2009} @cite{zuraw-2010}

Segment inventory and the nasal substitution process for Tagalog,
defined using the SPE formalism from `Phonology.RuleBased.Defs`.

## Nasal substitution

Tagalog has a productive process whereby a nasal-final prefix
(e.g. maŋ-, paŋ-) combines with an obstruent-initial stem and the
cluster optionally coalesces into a single nasal homorganic with the
underlying obstruent (@cite{zuraw-2010}):

- `maŋ + bigáj` → `mamigáj` 'to distribute' (substitution applies)
- `paŋ + tabój` → `pantabój` 'to goad'      (faithful cluster preserved)

The coalescence pattern is homorganic and voicing-neutralizing:
p,b → m; t,d → n; k,g → ŋ.

## SPE encoding

The `PhonRule` formalism in `Theories/Phonology/Process/RuleBased/Defs.lean`
supports `changeFeatures` and `delete` effects, and segment / wordBoundary
contexts. It does not support α-spreading (assimilatory rules where the
target inherits a feature value from the context). Tagalog nasal
substitution is therefore approximated here as **post-nasal obstruent
deletion**; the homorganic place of the resulting nasal is supplied by
the independent rule of homorganic-nasal-place assimilation, which
@cite{hayes-2009} treats as a separate process.

## Cross-cutting paper analyses

- @cite{zuraw-2010} factorial typology of NS over six obstruents with
  the constraint set DEP-C / \*NC / \*ASSOC / \*[ŋ / \*[n / \*[m
  → see `Phenomena/Phonology/Studies/Zuraw2010.lean`.
- @cite{zuraw-hayes-2017} 2×2 sub-square analysis (maŋ-other × paŋ-res
  prefixes, /b/ × /k/ stems) with prefix-indexed UNIFORMITY constraints
  → see `Phenomena/Phonology/Studies/ZurawHayes2017.lean`.
- @cite{magri-2025} MaxEnt-on-square deduction from the Hayes-Zuraw
  shifted-sigmoids generalization
  → see `Phenomena/Phonology/Studies/Magri2025.lean`.
-/

open Phonology
open Phonology.RuleBased

namespace Fragments.Tagalog.Phonology

/-! ## § 1: Stem-initial obstruents (NS targets) -/

/-- /p/: voiceless bilabial stop -/
def p : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.labial, true)]

/-- /t/: voiceless alveolar stop -/
def t : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true)]

/-- /k/: voiceless velar stop -/
def k : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.dorsal, true)]

/-- /b/: voiced bilabial stop -/
def b : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.labial, true)]

/-- /d/: voiced alveolar stop -/
def d : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /g/: voiced velar stop -/
def g : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.dorsal, true)]

/-! ## § 2: Homorganic nasals (NS outputs) -/

/-- /m/: bilabial nasal -/
def m : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.labial, true)]

/-- /n/: alveolar nasal -/
def n : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /ŋ/: velar nasal -/
def ŋ : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.dorsal, true)]

/-! ## § 3: Nasal Substitution Rule -/

/-- **Tagalog Nasal Substitution** (@cite{zuraw-2010}).

    Post-nasal obstruent deletion: an obstruent (`[+cons, −son]`) deletes
    when preceded by a nasal (`[+nasal]`). The homorganic place of the
    surviving nasal is supplied by general homorganic-nasal-place
    assimilation, treated as a separate rule (@cite{hayes-2009} Ch 6).

    The variable application of this process — from ~96% for /p/ to
    ~52% for /g/ in @cite{zuraw-2010}'s dictionary count — is a
    paper-specific empirical claim and lives in the relevant study
    files, not here. -/
def nasalSubstitution : PhonRule where
  name := "Tagalog Nasal Substitution"
  target := Segment.ofSpecs
    [(Feature.consonantal, true), (Feature.sonorant, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]

/-! ## § 4: Verification -/

/-- /p/ is a voiceless obstruent — matches the NS target. -/
theorem p_is_voiceless_obstruent :
    p.HasValue Feature.consonantal true = true ∧
    p.HasValue Feature.sonorant false = true ∧
    p.HasValue Feature.voice false = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- /b/ is a voiced obstruent — matches the NS target despite being voiced. -/
theorem b_is_voiced_obstruent :
    b.HasValue Feature.consonantal true = true ∧
    b.HasValue Feature.sonorant false = true ∧
    b.HasValue Feature.voice true = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- /m/, /n/, /ŋ/ are nasals — match the NS left-context. -/
theorem nasals_are_nasal :
    m.HasValue Feature.nasal true = true ∧
    n.HasValue Feature.nasal true = true ∧
    ŋ.HasValue Feature.nasal true = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- All six stem-initial obstruents match the nasal-substitution target. -/
theorem ns_target_matches_obstruents :
    p.matchesPattern nasalSubstitution.target = true ∧
    t.matchesPattern nasalSubstitution.target = true ∧
    k.matchesPattern nasalSubstitution.target = true ∧
    b.matchesPattern nasalSubstitution.target = true ∧
    d.matchesPattern nasalSubstitution.target = true ∧
    g.matchesPattern nasalSubstitution.target = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The three homorganic nasals do NOT match the obstruent target
    (sanity check: NS doesn't target nasals themselves). -/
theorem ns_target_excludes_nasals :
    m.matchesPattern nasalSubstitution.target = false ∧
    n.matchesPattern nasalSubstitution.target = false ∧
    ŋ.matchesPattern nasalSubstitution.target = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Fragments.Tagalog.Phonology
