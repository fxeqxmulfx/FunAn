-- Functional Analysis - Formal Proofs in Lean 4
-- Based on: Bashmakov & Galimov, "Functional Analysis", BashGU, 2007
-- Co-authored with Claude

-- Section 1: Set Algebra
import FunAn.Section01_SetAlgebra.Task05  -- closed under ∪∩ ≠> ring
import FunAn.Section01_SetAlgebra.Task06  -- product of semirings
import FunAn.Section01_SetAlgebra.Task08  -- [a,b] connected
import FunAn.Section01_SetAlgebra.Task12  -- Cantor set cardinality

-- Section 2: Measure
import FunAn.Section02_Measure.Task01     -- μ* ≥ μ_*
import FunAn.Section02_Measure.Task03     -- Borel ⊆ Lebesgue

-- Section 3: Measurable Functions
import FunAn.Section03_MeasurableFunctions.Task01  -- restriction measurable
import FunAn.Section03_MeasurableFunctions.Task02  -- continuous/sum measurable
import FunAn.Section03_MeasurableFunctions.Task06  -- a.e. → in measure

-- Section 5: BV Functions & Riemann-Stieltjes
import FunAn.Section05_BVandRS.Task01     -- Jordan decomposition

-- Section 6: Topological Spaces
import FunAn.Section06_TopologicalSpaces.Task02  -- weakest (initial) topology
import FunAn.Section06_TopologicalSpaces.Task03  -- strongest (final) topology

-- Section 7: Metric Spaces
import FunAn.Section07_MetricSpaces.Task04  -- quadrilateral inequality
import FunAn.Section07_MetricSpaces.Task05  -- ρ(x,A)=0 ↔ x ∈ cl(A)
import FunAn.Section07_MetricSpaces.Task06  -- continuity of ρ(·,A)
import FunAn.Section07_MetricSpaces.Task07  -- {ρ<ε} open, {ρ≤ε} closed

-- Section 9: Separable Metric Spaces
import FunAn.Section09_Separable.Task01  -- countable finite ℚ-sequences
import FunAn.Section09_Separable.Task02  -- countable ℚ-polynomials
import FunAn.Section09_Separable.Task06  -- ℓ∞ not separable
import FunAn.Section09_Separable.Task08  -- subsequences uncountable

-- Section 10: Contraction Mapping Principle
import FunAn.Section10_Contraction.Task03  -- (x²+2)/2x contraction

-- Section 11: Normed Spaces
import FunAn.Section11_NormedSpaces.Task01  -- triangle ↔ convex ball
import FunAn.Section11_NormedSpaces.Task03  -- Banach ↔ abs convergent
import FunAn.Section11_NormedSpaces.Task04  -- ℓp ⊂ ℓq
import FunAn.Section11_NormedSpaces.Task07  -- sup ≠ L¹ norm
import FunAn.Section11_NormedSpaces.Task09  -- product norms equivalent
import FunAn.Section11_NormedSpaces.Task10  -- fin-dim subspace closed

-- Section 12: Hilbert Spaces
import FunAn.Section12_HilbertSpaces.Task02  -- parallelogram law
import FunAn.Section12_HilbertSpaces.Task03  -- Hilbert ↔ p=2
import FunAn.Section12_HilbertSpaces.Task05  -- polarization identity
import FunAn.Section12_HilbertSpaces.Task06  -- M⊥ closed
import FunAn.Section12_HilbertSpaces.Task07  -- M+N closed if M⊥N
import FunAn.Section12_HilbertSpaces.Task17  -- dense M ⟹ M⊥={0}

-- Section 14: Linear Continuous Operators
import FunAn.Section14_LinearOperators.Task06  -- equiv norms preserve continuity

-- Section 15: Inverse Operators
import FunAn.Section15_InverseOperators.Task09  -- (AB)⁻¹ = B⁻¹A⁻¹
import FunAn.Section15_InverseOperators.Task11  -- (I-AB)⁻¹ ⟹ (I-BA)⁻¹

-- Section 18: Adjoint Operators
import FunAn.Section18_AdjointOperators.Task05  -- (A*)⁻¹ = (A⁻¹)*

-- Section 19: Operator Convergence
import FunAn.Section19_OperatorConvergence.Task01  -- weak→uniform in fin-dim

-- Section 20: Compact Sets
import FunAn.Section20_CompactSets.Task07  -- compact ⟹ nowhere dense
import FunAn.Section20_CompactSets.Task08  -- parallelepiped in ℓ² compact

-- Section 21: Compact Operators
import FunAn.Section21_CompactOperators.Task01  -- fin-dim ⟹ compact
import FunAn.Section21_CompactOperators.Task04  -- diagonal compact ↔ aₙ→0
import FunAn.Section21_CompactOperators.Task09  -- compact range separable
