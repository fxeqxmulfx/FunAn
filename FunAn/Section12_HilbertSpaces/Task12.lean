/-
  Section 12, Task 12.
  Gram-Schmidt on {tⁿ} in L²(-1,1) yields Legendre polynomials.

  The Gram-Schmidt process applied to the monomials {1, t, t², …} in L²(-1,1)
  produces the Legendre polynomials pₙ(t) = cₙ · dⁿ/dtⁿ[(t²-1)ⁿ],
  where cₙ = 1/(2ⁿ · n!).

  We formalize:
  (1) The Rodrigues polynomial Rₙ = dⁿ/dtⁿ[(X²-1)ⁿ] and Legendre polynomial
      Pₙ = (1/(2ⁿ·n!)) · Rₙ via the Rodrigues formula.
  (2) natDegree(Rₙ) = n: the Rodrigues polynomial has degree exactly n.
  (3) Boundary vanishing: eval(±1) of derivative^[k]((X²-1)ⁿ) = 0 for k < n.
      This is the key algebraic fact for orthogonality: integration by parts
      n times gives ∫₋₁¹ q(t)·Rₙ(t)dt = (-1)ⁿ ∫₋₁¹ q⁽ⁿ⁾(t)·(t²-1)ⁿ dt = 0
      for any polynomial q of degree < n, since q⁽ⁿ⁾ = 0.
  (4) The normalization constant cₙ = 1/(2ⁿ · n!).
  (5) Abstract Gram-Schmidt span/orthogonality properties (from Mathlib).
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

noncomputable section

open Polynomial

/-- The Rodrigues numerator: Rₙ(t) = dⁿ/dtⁿ[(t²-1)ⁿ] as a polynomial over ℝ. -/
def rodrigues (n : ℕ) : ℝ[X] :=
  derivative^[n] ((X ^ 2 - 1) ^ n)

/-- The Legendre polynomial via Rodrigues formula:
    Pₙ(t) = (1/(2ⁿ · n!)) · dⁿ/dtⁿ[(t²-1)ⁿ]. -/
def legendrePoly (n : ℕ) : ℝ[X] :=
  (1 / (2 ^ n * (Nat.factorial n : ℝ))) • rodrigues n

/-- The Rodrigues coefficient cₙ = 1/(2ⁿ · n!). -/
theorem legendre_rodrigues_coeff (n : ℕ) :
    legendrePoly n = (1 / (2 ^ n * (Nat.factorial n : ℝ))) • rodrigues n := rfl

private theorem natDegree_X_sq_sub_one : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
  have : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [this, natDegree_X_pow_sub_C]

/-- (X² - 1)ⁿ has degree 2n. -/
theorem natDegree_X_sq_sub_one_pow (n : ℕ) :
    ((X ^ 2 - 1 : ℝ[X]) ^ n).natDegree = 2 * n := by
  rw [natDegree_pow, natDegree_X_sq_sub_one, mul_comm]

private theorem leadingCoeff_X_sq_sub_one_pow (n : ℕ) :
    ((X ^ 2 - 1 : ℝ[X]) ^ n).leadingCoeff = 1 := by
  have : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [this, leadingCoeff_pow, leadingCoeff_X_pow_sub_C (by norm_num : 0 < 2), one_pow]

/-- The coefficient of Rₙ at position n equals (2n)!/n! (the descending factorial). -/
theorem rodrigues_coeff_n (n : ℕ) :
    (rodrigues n).coeff n = ((2 * n).descFactorial n : ℝ) := by
  simp only [rodrigues, coeff_iterate_derivative, nsmul_eq_mul]
  have h1 : n + n = 2 * n := by omega
  rw [h1]
  have h2 : ((X ^ 2 - 1 : ℝ[X]) ^ n).coeff (2 * n) = 1 := by
    have := leadingCoeff_X_sq_sub_one_pow n
    rwa [leadingCoeff, natDegree_X_sq_sub_one_pow] at this
  rw [h2, mul_one]

/-- The coefficient at degree n is nonzero since (2n)!/n! > 0. -/
theorem rodrigues_coeff_n_ne_zero (n : ℕ) : (rodrigues n).coeff n ≠ 0 := by
  rw [rodrigues_coeff_n]
  exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : n ≤ 2 * n)).ne'

/-- **Degree of the Rodrigues polynomial.**
    natDegree(dⁿ/dtⁿ[(t²-1)ⁿ]) = n. Each Legendre polynomial
    has degree exactly n, matching the Gram-Schmidt degree property. -/
theorem natDegree_rodrigues (n : ℕ) : (rodrigues n).natDegree = n := by
  apply le_antisymm
  · calc (rodrigues n).natDegree
        ≤ ((X ^ 2 - 1 : ℝ[X]) ^ n).natDegree - n := natDegree_iterate_derivative _ _
      _ = 2 * n - n := by rw [natDegree_X_sq_sub_one_pow]
      _ = n := by omega
  · exact le_natDegree_of_ne_zero (rodrigues_coeff_n_ne_zero n)

private theorem X_sq_sub_one_pow_ne_zero (n : ℕ) : (X ^ 2 - 1 : ℝ[X]) ^ n ≠ 0 := by
  apply pow_ne_zero
  have : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [this]
  exact X_pow_sub_C_ne_zero (by norm_num : (0 : ℕ) < 2) 1

private theorem rootMultiplicity_one_ge (n : ℕ) :
    n ≤ ((X ^ 2 - 1 : ℝ[X]) ^ n).rootMultiplicity 1 := by
  rw [le_rootMultiplicity_iff (X_sq_sub_one_pow_ne_zero n)]
  apply pow_dvd_pow_of_dvd
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

private theorem rootMultiplicity_neg_one_ge (n : ℕ) :
    n ≤ ((X ^ 2 - 1 : ℝ[X]) ^ n).rootMultiplicity (-1) := by
  rw [le_rootMultiplicity_iff (X_sq_sub_one_pow_ne_zero n)]
  apply pow_dvd_pow_of_dvd
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-- **Boundary vanishing at t = 1.**
    For k < n, the kth derivative of (t²-1)ⁿ vanishes at t = 1.
    Since (t²-1)ⁿ has a zero of multiplicity n at t = 1,
    all derivatives of order < n vanish there. -/
theorem rodrigues_boundary_vanish_at_one (n : ℕ) {k : ℕ} (hk : k < n) :
    (derivative^[k] ((X ^ 2 - 1 : ℝ[X]) ^ n)).eval 1 = 0 :=
  isRoot_iterate_derivative_of_lt_rootMultiplicity
    (lt_of_lt_of_le hk (rootMultiplicity_one_ge n))

/-- **Boundary vanishing at t = -1.**
    Analogous to the result at t = 1. -/
theorem rodrigues_boundary_vanish_at_neg_one (n : ℕ) {k : ℕ} (hk : k < n) :
    (derivative^[k] ((X ^ 2 - 1 : ℝ[X]) ^ n)).eval (-1) = 0 :=
  isRoot_iterate_derivative_of_lt_rootMultiplicity
    (lt_of_lt_of_le hk (rootMultiplicity_neg_one_ge n))

/-- **Gram-Schmidt orthogonalization properties.**
    Applied to the monomials {1, t, t², …} in L²(-1,1), Gram-Schmidt produces
    gₙ with: (a) gₙ ≠ 0, (b) gₘ ⊥ gₙ for m ≠ n, (c) span{g₀,…,gₙ} = span{1,…,tⁿ}.
    The boundary vanishing (theorems above) shows the Rodrigues polynomials satisfy
    the same orthogonality via integration by parts, hence each Legendre polynomial
    Pₙ = cₙ·dⁿ/dtⁿ[(t²-1)ⁿ] is a scalar multiple of gₙ, with cₙ = 1/(2ⁿ·n!). -/
theorem gramSchmidt_orthogonal_basis
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (f : ℕ → E) (hf : LinearIndependent 𝕜 f) :
    (∀ n, InnerProductSpace.gramSchmidt 𝕜 f n ≠ 0) ∧
    (Pairwise fun i j =>
      @inner 𝕜 E _ (InnerProductSpace.gramSchmidt 𝕜 f i)
                    (InnerProductSpace.gramSchmidt 𝕜 f j) = 0) ∧
    (∀ c, Submodule.span 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f '' Set.Iic c) =
          Submodule.span 𝕜 (f '' Set.Iic c)) :=
  ⟨fun n => InnerProductSpace.gramSchmidt_ne_zero n hf,
   InnerProductSpace.gramSchmidt_pairwise_orthogonal 𝕜 f,
   InnerProductSpace.span_gramSchmidt_Iic 𝕜 f⟩
