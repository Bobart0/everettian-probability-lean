import EverettianProbability.Rivals.Nonvacuity

/-!
**FR.** # Audit de l'accord Born--puissance quatrième

Ce module d'audit vérifie la surface publique de l'incrément E1 et imprime
les dépendances axiomatiques des résultats correspondants. Il ne contient
aucune preuve supplémentaire.

**EN.** # Born--fourth-power agreement audit

This audit module checks the public surface of increment E1 and prints the
axiomatic dependencies of the corresponding results. It contains no further
proofs.
-/

namespace EverettianProbability.Audit

open EverettianProbability.Rivals

#check @fourthPowerDenominator_pos
#check @renormalizedFourthPower_axPos
#check @renormalizedFourthPower_axNorm
#check @renormalizedFourthPower_agrees_iff
#check @renormalizedFourthPower_not_axGrain
#check @renormalizedFourthPower_agreement_witness
#check @renormalizedFourthPower_disagreement_witness

#print axioms EverettianProbability.Rivals.fourthPowerDenominator_pos
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_axPos
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_axNorm
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_agrees_iff
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_not_axGrain
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_agreement_witness
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_disagreement_witness

end EverettianProbability.Audit
