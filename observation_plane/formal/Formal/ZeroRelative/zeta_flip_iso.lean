import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# T6: 翻转计数的连续基础 — 零点离散/有限 (相位对齐前件)

翻转计数 (u → -u 的跳变次数 = N₀(T)) 需要: 零点在带内孤立且有限。
全部 0pat (mathlib 基础), 直接复用 ZetaZeros.lean 的现成定理:
- `isDiscrete_riemannZetaZeros` / `isClosed_riemannZetaZeros`: 零点集离散闭 (mathlib 官方);
- `IsCompact.inter_riemannZetaZeros_finite`: 紧集 ∩ 零点集有限;
- 带内零点 ⊆ 闭球 (‖z‖ ≤ sqrt(1+T²)+1) ⟹ 带内有限。

隔离文件 (mathlib-only)。 
English: discreteness/finiteness of the zero set and finiteness in strips: the topological base of the flip chain (T6) -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- ζ 的零点集 = mathlib 的 `riemannZetaZeros`。 
English: The zero set of ζ = mathlib's `riemannZetaZeros`. -/
def zetaZeroSet : Set ℂ := riemannZetaZeros

/-- 零点集闭。 
English: The zero set is closed. -/
lemma isClosed_zetaZeroSet : IsClosed zetaZeroSet := by
  simpa [zetaZeroSet] using isClosed_riemannZetaZeros

/-- 零点集离散: 每个零点孤立。 
English: The zero set is discrete: every zero is isolated. -/
lemma isDiscrete_zetaZeroSet : IsDiscrete zetaZeroSet := by
  simpa [zetaZeroSet] using isDiscrete_riemannZetaZeros

/-- 紧致集 ∩ 零点集有限。 
English: Compact set ∩ zero set is finite. -/
lemma IsCompact.inter_zetaZeroSet_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ zetaZeroSet).Finite := by
  simpa [zetaZeroSet] using hS.inter_riemannZetaZeros_finite

/-- 带内零点有限: [0,1]×[-T,T] 内仅有限多个零点。
带是紧致的 (含于闭球 ‖z‖ ≤ sqrt(1+T²)+1, 离散零点在紧集内有限)。 
English: Finitely many zeros in a strip: only finitely many zeros in [0,1]×[-T,T]; the strip is compact (contained in the closed ball ‖z‖ ≤ sqrt(1+T²)+1, discrete zeros finite in a compact set). -/
theorem zeta_zeros_finite_in_strip (T : ℝ) :
    ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}).Finite := by
  let R : ℝ := Real.sqrt (1 + T ^ 2) + 1
  have hsub : {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
      ⊆ Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet := by
    intro z hz
    rcases hz with ⟨hz0, hre0, hre1, him⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hnormSq : Complex.normSq z ≤ 1 + T ^ 2 := by
        rw [Complex.normSq_apply]
        have h1 : z.re ^ 2 ≤ 1 := by
          have hmul : z.re * z.re ≤ 1 * 1 := mul_le_mul hre1 hre1 hre0 zero_le_one
          simpa [pow_two] using hmul
        have h2 : z.im ^ 2 ≤ T ^ 2 := by
          have hT : 0 ≤ T := le_trans (abs_nonneg z.im) him
          have hmul : |z.im| * |z.im| ≤ T * T := mul_le_mul him him (abs_nonneg z.im) hT
          have h2' : |z.im| ^ 2 ≤ T ^ 2 := by simpa [pow_two] using hmul
          nlinarith [h2', sq_abs (z.im)]
        nlinarith
      calc
        ‖z‖ = Real.sqrt (‖z‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
        _ = Real.sqrt (Complex.normSq z) := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ Real.sqrt (1 + T ^ 2) := Real.sqrt_le_sqrt hnormSq
        _ ≤ R := by
          dsimp [R]
          linarith
    · simpa [zetaZeroSet, mem_riemannZetaZeros] using hz0
  have hfin : (Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet).Finite :=
    IsCompact.inter_zetaZeroSet_finite (isCompact_closedBall (x := (0 : ℂ)) R)
  exact hfin.subset hsub

end RiemannUnifiedObservation
