import EverettianProbability.Confirmation.DiscriminationRate

/-!
**FR.** # Audit E3 — taux de discrimination

Ce module expose les résultats publics de l'égalité des supports, de
l'invariance d'échelle et du taux de discrimination. Il imprime leurs
dépendances axiomatiques sans ajouter de preuve. Les résultats restent
conditionnels au principe CW de Greaves--Myrvold.

**EN.** # E3 audit — discrimination rate

This module exposes the public support-equality, scale-invariance, and
discrimination-rate results. It prints their axiomatic dependencies without
adding proofs. The results remain conditional on Greaves--Myrvold's CW
principle.
-/

namespace EverettianProbability.Audit

open EverettianProbability.Rivals
open EverettianProbability.Confirmation

#check @renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero
#check @renormalizedFourthPower_smul
#check @bornWeight_smul
#check @bornDiscriminationRate
#check @rivalDiscriminationRate
#check @bornDiscriminationRate_nonneg
#check @rivalDiscriminationRate_nonneg
#check @bornDiscriminationRate_eq_zero_iff
#check @rivalDiscriminationRate_eq_zero_iff
#check @bornDiscriminationRate_eq_zero_iff_bornAgreement
#check @coarse_bornDiscriminationRate_eq
#check @coarse_bornDiscriminationRate_pos

#print axioms EverettianProbability.Rivals.renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero
#print axioms EverettianProbability.Rivals.renormalizedFourthPower_smul
#print axioms EverettianProbability.Rivals.bornWeight_smul
#print axioms EverettianProbability.Confirmation.bornDiscriminationRate_nonneg
#print axioms EverettianProbability.Confirmation.rivalDiscriminationRate_nonneg
#print axioms EverettianProbability.Confirmation.bornDiscriminationRate_eq_zero_iff
#print axioms EverettianProbability.Confirmation.rivalDiscriminationRate_eq_zero_iff
#print axioms EverettianProbability.Confirmation.bornDiscriminationRate_eq_zero_iff_bornAgreement
#print axioms EverettianProbability.Confirmation.coarse_bornDiscriminationRate_eq
#print axioms EverettianProbability.Confirmation.coarse_bornDiscriminationRate_pos

end EverettianProbability.Audit
