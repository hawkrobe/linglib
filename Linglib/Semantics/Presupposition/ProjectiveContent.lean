/-!
# The taxonomy of projective content

[tonhauser-beaver-roberts-simons-2013]'s classification of projective
contents by two diagnostics: **Strong Contextual Felicity** (does the
trigger require its projective content to be established in the
utterance context?) and **Obligatory Local Effect** (when embedded
under a belief predicate, must the content be part of the attitude
holder's beliefs?). The two binary diagnostics yield four classes A–D.

Consumed as classification vocabulary by the projective-content study
files ([tonhauser-beaver-roberts-simons-2013], [solstad-bott-2024],
[roberts-simons-2024], and the Nez Perce study of attitude embedding).

## Main declarations

* `StrongContextualFelicity`, `ObligatoryLocalEffect` — the two
  diagnostics.
* `ProjectiveClass` — classes A–D, with `scf`/`ole` projections and
  the `classFromProperties` reconstruction
  (`class_properties_roundtrip`).
* `ProjectiveTrigger` — the framework's per-trigger table, with
  `toClass`. The `occasion_verb` case follows [solstad-bott-2024].
-/

namespace Semantics.Presupposition.ProjectiveContent

/--
Strong Contextual Felicity (SCF): whether a trigger requires its
projective content to be established in the utterance context prior
to use. Pronouns, demonstratives, and salience-*too* require it;
expressives, appositives, and factives can be informative.
-/
inductive StrongContextualFelicity where
  /-- SCF = yes: requires prior establishment. -/
  | requires
  /-- SCF = no: the content can be informative. -/
  | noRequires
  deriving DecidableEq, Repr

/--
Obligatory Local Effect (OLE): whether, under a belief predicate, the
projective content must be part of the attitude holder's beliefs.
*Stop* and *know* contents are attributed to the attitude holder;
appositive and expressive contents remain speaker commitments.
-/
inductive ObligatoryLocalEffect where
  /-- OLE = yes: attributed to the attitude holder. -/
  | obligatory
  /-- OLE = no: attributed to the speaker. -/
  | notObligatory
  deriving DecidableEq, Repr

/--
The four classes of projective content, each a combination of SCF and
OLE values.
-/
inductive ProjectiveClass where
  /-- Class A (SCF=yes, OLE=yes): pronouns (existence), *too*
      (existence). -/
  | classA
  /-- Class B (SCF=no, OLE=no): expressives, appositives, NRRCs,
      possessive NPs. -/
  | classB
  /-- Class C (SCF=no, OLE=yes): *stop*, *know*, *only*, *almost*. -/
  | classC
  /-- Class D (SCF=yes, OLE=no): *too* (salience), demonstratives,
      focus (salience). -/
  | classD
  deriving DecidableEq, Repr

/-- The SCF value of a projective class. -/
def ProjectiveClass.scf : ProjectiveClass → StrongContextualFelicity
  | .classA => .requires
  | .classB => .noRequires
  | .classC => .noRequires
  | .classD => .requires

/-- The OLE value of a projective class. -/
def ProjectiveClass.ole : ProjectiveClass → ObligatoryLocalEffect
  | .classA => .obligatory
  | .classB => .notObligatory
  | .classC => .obligatory
  | .classD => .notObligatory

/-- Reconstruct the class from its SCF and OLE values. -/
def classFromProperties :
    StrongContextualFelicity → ObligatoryLocalEffect → ProjectiveClass
  | .requires,   .obligatory    => .classA
  | .noRequires, .notObligatory => .classB
  | .noRequires, .obligatory    => .classC
  | .requires,   .notObligatory => .classD

/-- The two diagnostics jointly determine the class. -/
theorem class_properties_roundtrip (c : ProjectiveClass) :
    classFromProperties c.scf c.ole = c := by
  cases c <;> rfl

/--
Projective-content triggers, following
[tonhauser-beaver-roberts-simons-2013]'s per-trigger table.
-/
inductive ProjectiveTrigger where
  -- Class A triggers (SCF=yes, OLE=yes)
  /-- Personal pronouns: existence of referent. -/
  | pronoun_existence
  /-- *too*: existence of an alternative satisfying the predicate. -/
  | too_existence
  -- Class B triggers (SCF=no, OLE=no)
  /-- Expressives like *damn*: speaker attitude. -/
  | expressive
  /-- Appositives: supplementary content. -/
  | appositive
  /-- Non-restrictive relative clauses. -/
  | nrrc
  /-- Possessive NPs: existence of possessor. -/
  | possessive_np
  -- Class C triggers (SCF=no, OLE=yes)
  /-- Change-of-state predicates: prior state. -/
  | stop_prestate
  /-- Factive verbs: complement truth. -/
  | know_complement
  /-- Focus-sensitive *only*: prejacent. -/
  | only_prejacent
  /-- *almost*: polar content. -/
  | almost_polar
  /-- Definite descriptions: existence and uniqueness. -/
  | definite_description
  /-- Occasion verbs: prior occasioning eventuality
      ([solstad-bott-2024]). *Punish* presupposes a prior offense;
      *manage* presupposes a prior difficulty. SCF=no (can be
      informative), OLE=yes (attributed to attitude holder). -/
  | occasion_verb
  -- Class D triggers (SCF=yes, OLE=no)
  /-- *too*: salience of alternative. -/
  | too_salience
  /-- Demonstratives: indication established. -/
  | demonstrative_indication
  /-- Focus: salience of alternatives. -/
  | focus_salience
  deriving DecidableEq, Repr

/-- The projective class of each trigger. -/
def ProjectiveTrigger.toClass : ProjectiveTrigger → ProjectiveClass
  | .pronoun_existence => .classA
  | .too_existence => .classA
  | .expressive => .classB
  | .appositive => .classB
  | .nrrc => .classB
  | .possessive_np => .classB
  | .stop_prestate => .classC
  | .know_complement => .classC
  | .only_prejacent => .classC
  | .almost_polar => .classC
  | .definite_description => .classC
  | .occasion_verb => .classC
  | .too_salience => .classD
  | .demonstrative_indication => .classD
  | .focus_salience => .classD

end Semantics.Presupposition.ProjectiveContent
