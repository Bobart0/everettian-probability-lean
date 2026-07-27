import EverettianProbability.Frequency.HammingCells

/-!
**FR.** # Vecteur d'amplitudes de répétition — noyau P10

Pour deux amplitudes complexes `α` et `β`, l'amplitude d'une configuration
binaire de `R` sites est définie par

`α ^ (R - k) * β ^ k`,

où `k` est son poids de Hamming. Le vecteur obtenu est d'abord défini dans
la représentation par sites, puis transporté vers `H (2 ^ R)`.

Ce module établit uniquement que les amplitudes sont constantes sur chaque
cellule de fréquence. Il ne formalise pas encore la normalisation du vecteur,
la formule binomiale des poids, une loi des grands nombres ou la typicalité.
Aucune factorisation tensorielle explicite ni notion autonome d'indépendance
probabiliste n'est introduite.

**EN.** # Repetition-amplitude vector — P10 kernel

For two complex amplitudes `α` and `β`, the amplitude of a binary
configuration on `R` sites is defined as

`α ^ (R - k) * β ^ k`,

where `k` is its Hamming weight. The resulting vector is first defined in
the site representation and then transported to `H (2 ^ R)`.

This module proves only that amplitudes are constant on each frequency
cell. It does not yet formalize vector normalization, the binomial weight
formula, a law of large numbers, or typicality. No explicit tensor
factorization or autonomous notion of probabilistic independence is
introduced.
-/

namespace EverettianProbability.Frequency

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.Repetition
open scoped Classical InnerProductSpace

noncomputable section

/-- **FR.** Amplitude associée à une configuration de `R` répétitions :
`α` pour chaque zéro et `β` pour chaque un.

**EN.** Amplitude associated with a configuration of `R` repetitions:
`α` for each zero and `β` for each one. -/
def repetitionAmplitude
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) : ℂ :=
  α ^ (R - hammingWeight g) * β ^ hammingWeight g

/-- **FR.** Vecteur d'amplitudes dans la représentation par sites.

**EN.** Amplitude vector in the site representation. -/
def repetitionSitesVector
    (R : ℕ) (α β : ℂ) : Sites R 2 :=
  (WithLp.equiv 2 ((Fin R → Fin 2) → ℂ)).symm
    (fun g => repetitionAmplitude R α β g)

/-- **FR.** Transport du vecteur de répétition vers l'espace standard
`H (2 ^ R)`.

**EN.** Transport of the repetition vector to the standard space
`H (2 ^ R)`. -/
def repetitionVector
    (R : ℕ) (α β : ℂ) : H (2 ^ R) :=
  (sitesEquivR R).symm (repetitionSitesVector R α β)

/-- **FR.** Formule de coordonnée du vecteur dans la représentation par
sites.

**EN.** Coordinate formula for the vector in the site representation. -/
@[simp] theorem repetitionSitesVector_apply
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) :
    repetitionSitesVector R α β g =
      repetitionAmplitude R α β g := by
  simp [repetitionSitesVector]

/-- **FR.** Le transport inverse restitue exactement le vecteur défini par
ses amplitudes sur les configurations.

**EN.** Transporting back recovers exactly the vector defined by its
configuration amplitudes. -/
@[simp] theorem sitesEquivR_repetitionVector
    (R : ℕ) (α β : ℂ) :
    sitesEquivR R (repetitionVector R α β) =
      repetitionSitesVector R α β := by
  simp [repetitionVector]

/-- **FR.** Deux configurations de même poids de Hamming reçoivent la même
amplitude.

**EN.** Two configurations with the same Hamming weight receive the same
amplitude. -/
theorem repetitionAmplitude_eq_of_hammingWeight_eq
    {R : ℕ} {α β : ℂ} {g h : Fin R → Fin 2}
    (hweight : hammingWeight g = hammingWeight h) :
    repetitionAmplitude R α β g =
      repetitionAmplitude R α β h := by
  simp [repetitionAmplitude, hweight]

/-- **FR.** Le vecteur par sites est constant sur chaque classe de
configurations de même poids de Hamming.

**EN.** The site vector is constant on every class of configurations with
the same Hamming weight. -/
theorem repetitionSitesVector_eq_of_hammingWeight_eq
    {R : ℕ} {α β : ℂ} {g h : Fin R → Fin 2}
    (hweight : hammingWeight g = hammingWeight h) :
    repetitionSitesVector R α β g =
      repetitionSitesVector R α β h := by
  simp only [repetitionSitesVector_apply]
  exact repetitionAmplitude_eq_of_hammingWeight_eq hweight

/-- **FR.** Sur la configuration canonique de poids `k`, l'amplitude vaut
exactement `α ^ (R - k) * β ^ k`.

**EN.** On the canonical configuration of weight `k`, the amplitude is
exactly `α ^ (R - k) * β ^ k`. -/
theorem repetitionAmplitude_prefixConfiguration
    (R : ℕ) (k : Fin (R + 1)) (α β : ℂ) :
    repetitionAmplitude R α β
        (prefixConfiguration R k) =
      α ^ (R - k.val) * β ^ k.val := by
  simp [repetitionAmplitude,
    hammingWeight_prefixConfiguration]

end
end EverettianProbability.Frequency
