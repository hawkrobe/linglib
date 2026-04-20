import Linglib.Theories.Semantics.Polarity.Operator

/-!
# Turkish Question Particles
@cite{atlamaz-2023} @cite{turk-hirsch-2026}

Lexical entries for Turkish polar question particles. The fragment commits
only to *lexical primitives* — citation form, vowel-harmony allomorphs, and
semantic contribution (a bare operator on propositions). It does not commit
to a syntactic theory: there is no UPOS tag, no head-position label, no
left-periphery layer here. Those decisions are theory-laden and belong in
study files that actually adopt the relevant theory (e.g.,
@cite{fox-katzir-2011}-style category match needs a UPOS tagging;
@cite{laka-1990}-style PolP needs a head label).

The semantic operator is `Semantics.Polarity.affirm` (identity), reflecting
the consensus that *mI* is propositionally vacuous and contributes only
question force / focus marking — a claim that is theory-neutral up to the
choice of denotation type for propositions.
-/

namespace Fragments.Turkish.QuestionParticles

open Semantics.Polarity

/-- A Turkish question particle: form, vowel-harmony allomorphs, and the
    bare semantic operator it contributes. No syntactic categorization. -/
structure TurkishQParticle where
  /-- Citation form (cover symbol). -/
  form : String
  /-- Surface allomorphs after vowel harmony. -/
  allomorphs : List String
  /-- Semantic contribution: a polynomial transformation of propositions.
      Polymorphic in the world type so the entry is reusable across
      theory-specific world models. -/
  denotation : ∀ {W : Type}, (W → Prop) → (W → Prop)

/-- Turkish *mI* — the polar question particle (mı/mi/mu/mü under vowel
    harmony). Semantically the identity (no propositional contribution
    beyond marking question force). -/
def mi : TurkishQParticle where
  form := "mI"
  allomorphs := ["mı", "mi", "mu", "mü"]
  denotation := affirm _

/-- *mI*'s denotation is the identity, for any world model. -/
theorem mi_denotation_id (W : Type) :
    (mi.denotation : (W → Prop) → (W → Prop)) = id := rfl

end Fragments.Turkish.QuestionParticles
