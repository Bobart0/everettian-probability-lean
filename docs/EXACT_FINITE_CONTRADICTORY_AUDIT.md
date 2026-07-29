# Audit contradictoire de la couche exacte finie
# Contradictory Audit of the Exact-Finite Layer

## Français

### Affirmation exacte auditée

« Tout profil futur positif dont les sommes par fibre coïncident avec le
record bornien présent possède une réalisation unitaire exacte, commutant avec
les projecteurs présents. Sous les prémisses P4 explicites, les crédences
envers les continuateurs coïncident avec les ratios conditionnels prescrits
sur les fibres de poids non nul. »

### Compatibilité et risque de circularité

`CompatibleFineWeights` contient déjà les poids borniens présents. Le
résultat ne dérive donc pas Born à partir de la seule dynamique : il
caractérise les profils physiquement réalisables à record présent fixé.
L'équivalence compatibilité/réalisabilité est un résultat géométrique et
physique exact, non une justification normative autonome de Born.

**Verdict : VALID WITH EXPLICIT SCOPE / VALIDE SOUS PORTÉE EXPLICITE.**

### Séparation CORE/CALIBRATED

`ExactFiniteCoreResults` ne dépend que de `CompatibleFineWeights`.
`ExactFiniteCalibratedResults` ajoute une famille d'espérance rationnelle,
`3 ≤ n`, l'invariance locale, un état source normalisé, `AxNul` sur l'état
cible, et un poids parent non nul. Les conclusions calibrées ne sont jamais
présentées comme dérivées du seul unitaire.

**Verdict : SEPARATION VERIFIED / SÉPARATION VÉRIFIÉE.**

### `AxNul` sur l'état cible

`target_null_support` est une prémisse explicite : elle n'est pas dérivée de
la conservation du record présent, concerne le poids canonique de la famille
d'espérance et l'état cible, et demeure visible dans chaque théorème calibré.

**Verdict : EXPLICIT BRIDGE PREMISE / PRÉMISSE-PONT EXPLICITE.**

### Cellule parente de poids nul

Les théorèmes
`compatibleFineWeight_eq_zero_of_parentWeight_eq_zero`,
`prescribedRatio_eq_zero_of_parentWeight_eq_zero`,
`ExactFiniteNullParentResults` et `exactFiniteNullParentResults` établissent
que les poids fins compatibles de cette fibre sont tous nuls et que les ratios
totalisés valent zéro. Cette valeur zéro ne constitue pas une distribution
normalisée ; aucun théorème de crédence normalisée n'est énoncé pour cette
fibre.

**Verdict : BOUNDARY CASE EXPLICITLY HANDLED / CAS LIMITE TRAITÉ EXPLICITEMENT.**

### Non-unicité et choix canonique

`canonicalPhysicalRealization` est un choix mathématique fixé par les
définitions : « canonical » signifie seulement canonique relativement à ce
choix formel. Aucune unicité physique de l'unitaire ou de ses phases n'est
démontrée, et aucun principe dynamique ne sélectionne ce choix.

**Verdict : EXISTENCE ONLY / EXISTENCE UNIQUEMENT.**

### Portée du terme `PhysicalAdequacy`

Il signifie une réalisation exacte dans un espace de Hilbert complexe fini,
la commutation avec une perspective projective présente, ainsi que la
conservation du record et des conséquences présentes. Il ne signifie ni
localité, ni faible complexité, ni Hamiltonien naturel, ni dynamique réaliste
d'interaction, ni décohérence, ni robustesse, ni réalisabilité expérimentale.

### Sémantique des continuateurs

`ContinuationStep` organise formellement les fibres futures. L'interprétation
de ces cellules comme continuateurs pertinents reste sémantique : Lean vérifie
les conséquences de cette indexation, non une théorie métaphysique de
l'identité personnelle.

### Verdict final EF9

**EF9 AUDITED.** Le résultat exact fini est cohérent dans sa portée déclarée ;
aucun défaut logique interne n'a été identifié dans les frontières auditées.
Ses prémisses physiques, normatives et sémantiques restent explicitement
séparées. Aucune conclusion réaliste ou approximative supplémentaire n'est
licenciée, et EF10 n'est pas encore ouvert.

## English

### Exact claim audited

“Every positive future profile whose fibre sums coincide with the present Born
record has an exact unitary realization commuting with the present projectors.
Under explicit P4 premises, continuator credences coincide with the prescribed
conditional ratios on nonzero-weight fibres.”

### Compatibility and circularity risk

`CompatibleFineWeights` already contains present Born weights. The result
therefore does not derive Born from dynamics alone: it characterizes physically
realizable profiles at a fixed present record. The
compatibility/realizability equivalence is an exact geometric and physical
result, not an autonomous normative justification of Born.

**Verdict: VALID WITH EXPLICIT SCOPE.**

### CORE/CALIBRATED separation

`ExactFiniteCoreResults` depends only on `CompatibleFineWeights`.
`ExactFiniteCalibratedResults` adds a rational expectation family, `3 ≤ n`,
local invariance, a normalized source state, `AxNul` at the target, and a
nonzero parent weight. Calibrated conclusions are never presented as following
from the unitary alone.

**Verdict: SEPARATION VERIFIED.**

### `AxNul` at the target state

`target_null_support` is an explicit premise. It is not derived from
preservation of the present record, concerns the canonical weight of the
expectation family and the target state, and remains visible in every
calibrated theorem.

**Verdict: EXPLICIT BRIDGE PREMISE.**

### Zero-weight parent cell

The theorems `compatibleFineWeight_eq_zero_of_parentWeight_eq_zero`,
`prescribedRatio_eq_zero_of_parentWeight_eq_zero`,
`ExactFiniteNullParentResults`, and `exactFiniteNullParentResults` show that
all compatible fine weights in that fibre are zero and that totalized ratios
are zero. That value is not a normalized distribution; no normalized credence
theorem is stated for this fibre.

**Verdict: BOUNDARY CASE EXPLICITLY HANDLED.**

### Non-uniqueness and canonical choice

`canonicalPhysicalRealization` is a mathematical choice fixed by the
definitions: “canonical” means only canonical relative to that formal choice.
No physical uniqueness of the unitary or its phases is proved, and no dynamic
principle selects that choice.

**Verdict: EXISTENCE ONLY.**

### Scope of `PhysicalAdequacy`

It means exact realization in a finite complex Hilbert space, commutation with
a present projective perspective, and preservation of the present record and
consequences. It does not mean locality, low complexity, a natural Hamiltonian,
a realistic interaction dynamics, decoherence, robustness, or experimental
realizability.

### Continuator semantics

`ContinuationStep` formally organizes future fibres. Interpreting those cells
as relevant continuators remains semantic: Lean checks the consequences of
this indexing, not a metaphysical theory of personal identity.

### Final EF9 verdict

**EF9 AUDITED.** The exact-finite result is coherent in its stated scope; no
internal logical flaw was identified in the audited boundaries. Its physical,
normative, and semantic premises remain explicitly separated. No additional
realistic or approximate conclusion is licensed, and EF10 is not yet open.
