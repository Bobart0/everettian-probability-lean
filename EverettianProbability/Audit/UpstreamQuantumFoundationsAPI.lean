import EverettianProbability.API.UpstreamQuantumFoundations

/-!
**FR.** Contrat de compilation de la frontiere amont stable. Les controles
nomment les declarations par leurs namespaces amont : la frontiere ne cree pas
d'API plate et ne confond ni `NSNC1`, ni neutralite d'ancilla, ni neutralite
residuelle.

**EN.** Compilation contract for the stable upstream boundary. The checks name
declarations through their upstream namespaces: the boundary creates no flat
API and conflates neither `NSNC1`, ancilla neutrality, nor residual neutrality.
-/

#check QuantumFoundations.ProbabilityAPI.Perspective
#check QuantumFoundations.BornRule.Perspective.eq_of_cells
#check QuantumFoundations.BornRule.lemma4_noncontextual_grain_only
#check QuantumFoundations.BornRule.lemma4_noncontextual
#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization
#check QuantumFoundations.FiniteTensorAPI.SystemEnvironmentFactorization
#check QuantumFoundations.SelectorBridgeAPI.AncillaNeutralUnder
#check QuantumFoundations.SelectorBridgeAPI.tSelectors_tensorMultiplicative_iff
#check QuantumFoundations.NaimarkImplementationAPI.ResidualExtensionNeutral
#check QuantumFoundations.NaimarkImplementationAPI.implementationIndependent_of_residualNeutral

#print axioms QuantumFoundations.ProbabilityAPI.grainCoherenceTheorem_projector
#print axioms QuantumFoundations.BornRule.Perspective.eq_of_cells
#print axioms QuantumFoundations.BornRule.lemma4_noncontextual_grain_only
#print axioms QuantumFoundations.BornRule.lemma4_noncontextual
#print axioms QuantumFoundations.SelectorBridgeAPI.tSelectors_tensorMultiplicative_iff
#print axioms QuantumFoundations.NaimarkImplementationAPI.implementationIndependent_of_residualNeutral
