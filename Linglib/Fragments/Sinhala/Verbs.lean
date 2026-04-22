import Linglib.Theories.Semantics.Causation.CauserSort

/-!
# Colloquial Sinhala verb fragment

@cite{beavers-zubair-2013} @cite{gair-paolillo-1997} @cite{inman-1993}

A minimal fragment of the Sinhala (Sinhalese) verb system as
formalized in @cite{beavers-zubair-2013}. The data here is the
verb inventory needed to drive the empirical predictions of B&Z
2013 about anticausativization, the volitive/involitive stem
contrast, and the typology of causer sorts.

## Volitive/involitive stem alternation

Every Sinhala verb root has a volitive stem and (most have) an
involitive stem. The stems are distinguished by a thematic-vowel
alternation: front vowel + *-e-* in the present for involitive,
*-a-* or *-i-* otherwise. The volitive defaults to a volitional /
intentional reading; the involitive defaults to non-volitional /
accidental. Crucially, this is *not* truth-conditional — what the
volitive grammaticalizes is sortal (causer ∈ U_E, the event sort);
what the involitive does is fail to grammaticalize anything (no
sortal restriction).

## Causer-sort typology

Verbs are classified by the sort their causer must satisfy
(@cite{beavers-zubair-2013} ex. (81), p. 40):

- *kadann* / *kædenn* 'break': causer ∈ U (any) — anticausativizes
- *minimarann* 'murder': causer ∈ U_E (event) — does not anticausativize
- *kapann* 'cut': causer ∈ U_E (event) — does not anticausativize

Roots without involitive stems (*minimarann*, *kapann*) precisely
correspond to roots whose causer sort excludes individuals — the
predictive engine of B&Z's analysis.
-/

namespace Fragments.Sinhala.Verbs

open Semantics.Causation

/-- A Colloquial Sinhala verb root.

    `involitiveForm` is `none` for verbs whose causer sort excludes
    individuals (e.g., *minimarann* 'murder' has no involitive form
    because its U_E causer can never resolve to an individual, which
    is what the involitive operator would require). -/
structure SinhalaVerb where
  gloss : String
  volitiveForm : String
  involitiveForm : Option String
  causerSort : CauserSort
  deriving Repr, BEq

/-- *kadann* (vol) / *kædenn* (invol) 'break'.
    @cite{beavers-zubair-2013} ex. (76): `[[kada-]] = λyλv∈U λe[...]`. -/
def kadann : SinhalaVerb :=
  { gloss := "break",
    volitiveForm := "kadann",
    involitiveForm := some "kædenn",
    causerSort := .any }

/-- *gilann* (vol) / *gilenn* (invol) 'drown'.
    The canonical example: vol+nominative = intentional drowning;
    invol+postposition *atiŋ* = accidental drowning; intransitive
    *gilenn* = anticausative 'drown' (paper's exx. (2)-(3)). -/
def gilann : SinhalaVerb :=
  { gloss := "drown",
    volitiveForm := "gilann",
    involitiveForm := some "gilenn",
    causerSort := .any }

/-- *marann* (vol) / *mærenn* (invol) 'kill/die'.

    TODO: B&Z 2013 do not directly classify *marann* on the U/U_E
    axis; it is included here by analogy with the other alternating
    roots. Cross-linguistically *kill* often patterns with U_V
    (effector OK, individual subject pragmatically marked) — see
    @cite{levin-hovav-1995} ch. 3 on *kill* vs. *murder*. -/
def marann : SinhalaVerb :=
  { gloss := "kill",
    volitiveForm := "marann",
    involitiveForm := some "mærenn",
    causerSort := .any }

/-- *minimarann* 'murder' — no involitive form.
    @cite{beavers-zubair-2013} ex. (65b): `[[minimara-]] = λyλv∈U_E λe[...]`.
    The U_E sortal restriction is incompatible with U_I, blocking
    both involitive inflection and anticausativization. -/
def minimarann : SinhalaVerb :=
  { gloss := "murder",
    volitiveForm := "minimarann",
    involitiveForm := none,
    causerSort := .event }

/-- *kapann* 'cut' — no involitive form.
    Patterns with *minimarann* (event-sort causer) because cutting
    requires a sharp instrument and intentional manipulation. -/
def kapann : SinhalaVerb :=
  { gloss := "cut",
    volitiveForm := "kapann",
    involitiveForm := none,
    causerSort := .event }

/-- *vinaash-karann* (vol) / *vinaash-kerenn* (invol) 'destroy'.

    **Cross-linguistic note** (@cite{beavers-zubair-2013} §7.4, p. 40):
    the *destroy*-class is the wedge B&Z use to motivate the U_V
    constructor in their lattice — but the wedge is typological, not
    Sinhala-internal. B&Z 2013 explicitly note that "[the] equivalent
    [of *destroy*] does alternate in Sinhala (as do equivalents in
    Spanish, French, Hebrew, and Greek)", citing Härtl 2003 for German
    *destroy*-class verbs that do *not* alternate. B&Z's ex. (80)
    `[[destroy]] = λyλv∈U_V λe[…]` is the analysis of *English* /
    German destroy (which does not anticausativize), not of the Sinhala
    cognate. Sinhala *vinaash-karann* gets the unrestricted `.any`
    sort, consistent with its observed alternation behavior.

    The non-trivial empirical content of the lattice is therefore
    *cross*-linguistic: `destroy_no_anticausative` is verified for
    English/German *destroy* but not for Sinhala. See the planned
    English/German fragment for the contrastive instantiation. -/
def vinaashKarann : SinhalaVerb :=
  { gloss := "destroy",
    volitiveForm := "vinaash-karann",
    involitiveForm := some "vinaash-kerenn",
    causerSort := .any }

/-- The canonical inventory used in B&Z 2013's empirical arguments. -/
def allVerbs : List SinhalaVerb :=
  [kadann, gilann, marann, minimarann, kapann, vinaashKarann]

/-- Whether a verb has an involitive stem form. -/
def hasInvolitive (v : SinhalaVerb) : Bool := v.involitiveForm.isSome

/-- **Fragment-internal correlation, not a B&Z prediction.**

    Within this fragment, the verbs lacking an involitive form
    happen to be exactly those whose causer sort excludes individuals
    (*minimarann*, *kapann*; both U_E). This is a stipulated
    correlation in the data, not a derivation: B&Z 2013 (p. 38) are
    explicit that the involitive is the *elsewhere* form — it does
    not encode anything semantically and is "forced" only because the
    volitive (which requires U_E) cannot apply. Counterexamples to a
    naïve sort↔morphology biconditional include experiencer-subject
    verbs *dænenn*/*ridenn* 'feel'/'ache' (p. 36 around (74)) which
    take individual subjects but lack volitive forms — i.e., they are
    involitive-only, not absent-of-involitive.

    This theorem is therefore a *test of the fragment data*, not a
    test of B&Z's theory. -/
theorem fragment_involitive_correlates_with_causer_sort :
    allVerbs.all (fun v =>
      hasInvolitive v == decide (v.causerSort = .any ∨
                                  v.causerSort = .individual)) = true := by
  decide

end Fragments.Sinhala.Verbs
