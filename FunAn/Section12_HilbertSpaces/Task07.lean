/-
  Section 12, Task 7.
  If M, N are closed orthogonal subspaces, then M + N is closed.

  Proof strategy: The addition map φ : M × N → H, (m,n) ↦ m+n is
  antilipschitz (with constant 1) by the Pythagorean theorem:
  ‖m+n‖² = ‖m‖² + ‖n‖² ≥ max(‖m‖,‖n‖)² = ‖(m,n)‖².
  Since M × N is complete (product of complete), the range M+N is closed.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If M and N are closed orthogonal subspaces, then M + N is closed. -/
theorem sum_orthogonal_closed_is_closed
    (M N : Submodule ℝ H) [CompleteSpace M] [CompleteSpace N]
    (horth : ∀ m ∈ M, ∀ n ∈ N, @inner ℝ H _ m n = 0) :
    IsClosed ((M ⊔ N : Submodule ℝ H) : Set H) := by
  -- The addition map φ : M × N →L[ℝ] H, (m, n) ↦ m + n
  set φ : ↥M × ↥N →L[ℝ] H := M.subtypeL.coprod N.subtypeL with hφ_def
  -- Key lemma: orthogonal elements satisfy ‖(m,n)‖ ≤ ‖m+n‖
  have hbound : ∀ (p : ↥M × ↥N), ‖p‖ ≤ ‖φ p‖ := by
    intro ⟨m, n⟩
    have hφmn : φ (m, n) = (↑m : H) + (↑n : H) := by
      simp [hφ_def, ContinuousLinearMap.coprod_apply]
    rw [hφmn, Prod.norm_def]
    have hm : ‖m‖ = ‖(↑m : H)‖ := rfl
    have hn : ‖n‖ = ‖(↑n : H)‖ := rfl
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (↑m : H) (↑n : H) (horth _ m.property _ n.property)
    rw [hm, hn]
    apply max_le <;> nlinarith [norm_nonneg (↑m : H), norm_nonneg (↑n : H),
      norm_nonneg ((↑m : H) + (↑n : H))]
  -- φ is antilipschitz with constant 1
  have hanti : AntilipschitzWith 1 φ :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      simp only [NNReal.coe_one, one_mul]
      calc dist x y = ‖x - y‖ := dist_eq_norm x y
        _ ≤ ‖φ (x - y)‖ := hbound (x - y)
        _ = ‖φ x - φ y‖ := by rw [map_sub]
        _ = dist (φ x) (φ y) := (dist_eq_norm _ _).symm
  -- The range of φ equals M ⊔ N as a set
  suffices IsClosed (Set.range φ) by
    convert this using 1
    ext x; simp only [SetLike.mem_coe, Submodule.mem_sup, Set.mem_range, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [hφ_def, ContinuousLinearMap.coprod_apply]⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨↑m, m.property, ↑n, n.property,
        by simp [hφ_def, ContinuousLinearMap.coprod_apply]⟩
  exact hanti.isClosed_range φ.lipschitz.uniformContinuous
