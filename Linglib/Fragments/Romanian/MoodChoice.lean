import Linglib.Semantics.Verb.Basic

/-!
# Romanian Mood-Choice Verb Entries [grano-2024]

Minimal verb entries for Romanian attitude and causative predicates
relevant to cross-linguistic mood choice ([grano-2024], Table 1).

In Romanian, mood is reflected in both complementizer choice (*să* = SBJV
vs *că* = IND) and verb morphology. 'want' and 'intend' take *să* (SBJV);
'hope' allows both *să* and *că* (IND/SBJV). Causatives take *să* (SBJV).

## Key examples (from [grano-2024])

- (6a) Ion vrea [**să** meargă în parc]. ('want': SBJV)
- (6b) \*Ion vrea [**că** va merge în parc]. ('want': \*IND)
- (14a) Ion speră [**să** meargă în parc]. ('hope': SBJV)
- (14b) Ion speră [**că** va merge în parc]. ('hope': IND)
- (23a) Ion intenționează [**să** meargă în parc]. ('intend': SBJV)
- (23b) \*Ion intenționează [**că** va merge în parc]. ('intend': \*IND)
- (46a) L-am făcut pe Ion **să** meargă în parc. ('make': SBJV)
-/

namespace Romanian.MoodChoice

open ArgumentStructure

/-- *a vrea* 'want' — robustly subjunctive-selecting via *să*.
    [grano-2024], (6): *să* (SBJV) required, *că* (IND) rejected. -/
def a_vrea : Verb where
  form := "a vrea"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *a spera* 'hope' — cross-linguistically variable (IND/SBJV).
    [grano-2024], (14): both *să* (SBJV) and *că* (IND) accepted. -/
def a_spera : Verb where
  form := "a spera"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *a intenționa* 'intend' — robustly rejects indicative.
    [grano-2024], (23): *să* (SBJV) required, *că* (IND) rejected. -/
def a_intentiona : Verb where
  form := "a intenționa"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *a face* 'make' — causative, subjunctive-selecting via *să*.
    [grano-2024], (46): *să* (SBJV) required, *că* (IND) rejected. -/
def a_face : Verb where
  form := "a face"
  frames := [Frame.finiteClause]
  readings := [{ frame := Frame.finiteClause, control := some .objectControl }]
  causative := some .make

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem a_vrea_is_want_class :
    a_vrea.levinClass = some .want := rfl

theorem a_spera_not_want_class :
    a_spera.levinClass ≠ some .want := by decide

theorem a_intentiona_is_want_class :
    a_intentiona.levinClass = some .want := rfl

theorem a_face_is_causative :
    a_face.causative.isSome = true := rfl

end Romanian.MoodChoice
