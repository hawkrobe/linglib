import Linglib.Syntax.Particle.Basic

/-!
# Bulgarian Question Particles
[simik-2024]

Lexical entries for Bulgarian interrogative particles as `Particle`
values. Bias classifications (nima's evidential requirement) and the
left-peripheral layer assignments live in `Simik2024`.

## Cross-Module Connections

- `Simik2024.bulgarian` (`Studies/Simik2024`): PQ strategy profile
  (verb-attached li) and the neutral/evidential contrast
- Cross-Slavic RAZVE family: nima is the Bulgarian member
- Dukova-Zheleva: nima expresses incredulity/surprise
-/

namespace Bulgarian.QuestionParticles

/-- ли li — verb-attached neutral PQ particle ([simik-2024] ex. 33).
Second-position (Wackernagel): encliticizes onto the focused
constituent. -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .secondPosition
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

/-- нима nima — mirative/dubitative particle (RAZVE family, [simik-2024]
§4.2.4). Expresses incredulity: speaker encounters evidence conflicting
with prior expectations (Dukova-Zheleva). Evidential classification in
`Simik2024`. -/
def nima : Particle where
  form := "nima"
  script := some "нима"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [li, nima]

end Bulgarian.QuestionParticles
