import Linglib.Semantics.Attitudes.Anchor

/-!
# Content individuals

A content individual is a first-class mental state carrying propositional
content — [kratzer-2006]'s denotation for content DPs like *John's belief
that p*, *the claim*, *every rumor*, *her wish*. Content individuals are
the shared ontological sort underlying beliefs, desires, and percepts
([liefke-2024]); what distinguishes a belief from a desire or a percept
is not the sort but the attitude relation that embeds it. In Bayesian
theory-of-mind models ([baker-jara-ettinger-saxe-tenenbaum-2017],
`Pragmatics/BToM.lean`) they correspond to the type parameters over which
the observer's posterior is defined.

Content individuals are the content-mode instance of the `Anchor` class:
the projection is CONT, so `Anchor.comp` is the *that*-complementizer of
[kratzer-2006] and [moulton-2015] and `Anchor.existsClosure` composes
attitude reports. `cont_surjective` — every proposition is the content
of some individual — makes `Anchor.existsClosure_ofAccessibility`
applicable, recovering the classical doxastic semantics of
[hintikka-1962].

Two ways to relate a content individual x_c to a proposition p:
*identity*, CONT(x_c) = p, the notion of [kratzer-2006] and
[moulton-2015] (p **is** the content, `Anchor.comp`); and *entailment*,
CONT(x_c) ⊆ p, the notion of [hintikka-1962] (p **follows from** the
content, `entails`). Identity is strictly stronger:
`eq_implies_entails` and the counterexample `entails_not_implies_eq`.
-/

/-- A content individual: a first-class mental state carrying propositional
    content. The `cont` field is [kratzer-2006]'s CONT function.

    Caveat: because `cont` is the only field, this formalization identifies
    individuals with their contents — the intuition "my belief that p ≠ your
    belief that p" is NOT captured. A Kratzerian atom-plus-model shape
    (`cont : E → W → (W → Prop)`) would capture it, deferred until a study
    states an identity-vs-content theorem. -/
structure ContentIndividual (W : Type*) where
  /-- Propositional content: CONT(c) -/
  cont : W → Prop

/-- A content-selecting verb (*say*, *believe*) relates an agent to a
    content individual at a world — the content-sort sibling of
    `SituationVerb`. -/
abbrev ContentVerb (W E : Type*) := E → ContentIndividual W → W → Prop

namespace ContentIndividual

variable {W : Type*}

instance : Anchor (ContentIndividual W) W :=
  ⟨cont⟩

/-- Every proposition is the content of some individual — the belief that
    `p` — so the content-mode projection is surjective. -/
theorem cont_surjective :
    Function.Surjective (cont : ContentIndividual W → W → Prop) :=
  fun p => ⟨⟨p⟩, rfl⟩

/-- Content entailment: `xc.entails p` iff every content world of `xc` is a
    `p`-world (CONT ⊆ p) — the reading of attitude reports in
    [hintikka-1962], where [kratzer-2006] and [moulton-2015] use content
    *identity*. -/
def entails (xc : ContentIndividual W) (p : W → Prop) : Prop :=
  ∀ w, xc.cont w → p w

/-- Content identity implies content entailment. -/
theorem eq_implies_entails (xc : ContentIndividual W) (p : W → Prop) :
    xc.cont = p → xc.entails p :=
  fun h _w hw => h ▸ hw

/-- Content entailment does not imply content identity: empty content
    entails every proposition. -/
theorem entails_not_implies_eq :
    ¬ ∀ (p : Bool → Prop) (xc : ContentIndividual Bool),
      xc.entails p → xc.cont = p := fun h =>
  (iff_of_eq (congrFun (h (fun _ => True) ⟨fun _ => False⟩ fun _ hw => hw.elim)
    true)).mpr trivial

end ContentIndividual

