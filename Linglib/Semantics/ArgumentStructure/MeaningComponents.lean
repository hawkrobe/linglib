/-!
# ArgumentStructure.MeaningComponents
[levin-1993] [beavers-koontz-garboden-2020]

Binary meaning-component features that define [levin-1993] verb classes
diagnostically (via diathesis alternation participation), with the `fuse`
operator for componentwise composition.

## Provenance

Moved from `Core/Lexical/VerbClass.lean` in the cleanup that dissolved
`Core/Lexical/`. Lives at `Semantics/Lexical/` (sibling of
`LevinTheory.lean`, `LevinClassProfiles.lean`, `LevinClass.lean`,
`DiathesisAlternation.lean`) because it encodes Levin's specific
diagnostic apparatus (CoS / contact / motion / causation as the 4
canonical features) — paper-anchored framework content, not consensus
substrate.

## Framework commitment

The 4-feature decomposition is [levin-1993]'s diagnostic apparatus.
[beavers-koontz-garboden-2020] argue these are SURFACE behaviors,
not root-level entailments — root-level structural features live in
`Semantics/Lexical/Roots/Signature.lean::Root.Kinds`
(state/manner/result/cause). The two carve-ups are NOT equivalent:
e.g., `causation` here is what diathesis alternations diagnose, while
B&KG's `cause` is a root entailment.

The `instrumentSpec` and `mannerSpec` features supplement the 4-feature
core for finer-grained subclass distinctions in Part II.

## Note on `fuse`

`fuse a b` is componentwise OR — the formaliser's design choice for
modeling how a construction augments a verb's inherent semantics.
Originally attributed to [goldberg-1995] in source comments, but
Goldberg's actual constructional unification is *not* componentwise
boolean OR (it involves semantic frame unification with role-fusion
constraints, far more structured than disjunctive feature OR). The
substrate's `fuse` is a useful approximation but should not be cited
as Goldberg's operation directly.

## Alternative frameworks not formalized at parallel substrate granularity

The Levin-style alternation-diagnosed feature decomposition competes
with other lexical-semantic frameworks worth formalizing as siblings:
- **Generative Lexicon** ([pustejovsky-1995]): qualia structure
  (formal/constitutive/telic/agentive) as the primitive decomposition.
- **Frame semantics** ([fillmore-1982],
  [fillmore-kay-oconnor-1988]): semantic frames as primitive,
  alternations as surface reflexes.
- **Lexical Conceptual Structure** ([jackendoff-1996]): primitive
  predicates GO/STAY/CAUSE compose into LCS templates.
- **Configurational lexical semantics** ([hale-keyser-1987]):
  verb meaning derives from syntactic configuration, not feature
  decomposition.
-/

namespace ArgumentStructure

/-- Binary meaning components that define [levin-1993] verb classes.

    These describe **surface** verb behavior, not root-level entailments.
    [beavers-koontz-garboden-2020] argue that surface CoS and causation
    can come from either the template or the root; see `Root.Kinds`
    in `Semantics/Lexical/Roots/Signature.lean` for the
    root-level decomposition.

    Diagnosed by participation in diathesis alternations:
    - `changeOfState`: middle alternation, causative/inchoative alternation
    - `contact`: body-part possessor ascension alternation
    - `motion`: conative alternation (with contact)
    - `causation`: causative/inchoative alternation (with changeOfState)

    The four canonical classes from Levin's Introduction:
    - *break* = [+CoS, −contact, −motion, +causation]
    - *cut* = [+CoS, +contact, +motion, +causation]
    - *hit* = [−CoS, +contact, +motion, −causation]
    - *touch* = [−CoS, +contact, −motion, −causation]

    Additional binary features (from class descriptions in Part II):
    - `instrumentSpec`: verb specifies instrument/means (cut vs. break)
    - `mannerSpec`: verb specifies manner of action

    UNVERIFIED: Levin Part II page references for instrumentSpec/mannerSpec
    cited from memory. -/
structure MeaningComponents where
  changeOfState : Bool
  contact : Bool
  motion : Bool
  causation : Bool
  instrumentSpec : Bool := false
  mannerSpec : Bool := false
  deriving DecidableEq, Repr

namespace MeaningComponents

def break_ : MeaningComponents := ⟨true, false, false, true, false, false⟩
def cut : MeaningComponents := ⟨true, true, true, true, true, false⟩
def hit : MeaningComponents := ⟨false, true, true, false, false, false⟩
def touch : MeaningComponents := ⟨false, true, false, false, false, false⟩
def destroy : MeaningComponents := ⟨true, false, false, true, false, false⟩
def bend : MeaningComponents := ⟨true, false, false, true, false, false⟩
def none : MeaningComponents := ⟨false, false, false, false, false, false⟩

/-- Componentwise OR. The formaliser's chosen approximation of
    construction-on-verb composition; not equivalent to Goldberg's
    actual constructional unification (see file docstring). -/
def fuse (a b : MeaningComponents) : MeaningComponents :=
  { changeOfState := a.changeOfState || b.changeOfState
  , contact := a.contact || b.contact
  , motion := a.motion || b.motion
  , causation := a.causation || b.causation
  , instrumentSpec := a.instrumentSpec || b.instrumentSpec
  , mannerSpec := a.mannerSpec || b.mannerSpec }

instance : Append MeaningComponents where
  append := fuse

theorem fuse_none_left (mc : MeaningComponents) : none.fuse mc = mc := by
  cases mc; simp [fuse, none]

theorem fuse_none_right (mc : MeaningComponents) : mc.fuse none = mc := by
  cases mc; simp [fuse, none, Bool.or_false]

theorem fuse_comm (a b : MeaningComponents) : a.fuse b = b.fuse a := by
  cases a; cases b; simp [fuse, Bool.or_comm]

end MeaningComponents

end ArgumentStructure
