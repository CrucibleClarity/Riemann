import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# T6b: u 分段连续 + χ 沿临界线连续 (相位对齐的连续基础)

翻转计数 (u → -u 的跳变次数 = N₀(T)) 的连续前件:
- u(s) = ζ(s)/‖ζ(s)‖: 单位圆投影 (相位), 在 ζ ≠ 0 且 s ≠ 1 处连续
  (ζ 在 {1}ᶜ 可微 (differentiableOn_riemannZeta), 除法分母非零);
- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子, 沿临界线连续
  (幂/Γ/sin 显式连续; Γ 在 1-s 无极点: re (1-s) = 1/2 > 0)。

"连续 = 无数不同相位离散点的投影": u(t) 是每个 t 的 ζ 值投影到单位圆,
轨迹连续 ⟸ 相位场逐点连续。全部 0pat (mathlib 基础)。

隔离文件 (mathlib-only)。 
English: continuity of u = ζ/|ζ| and of chi on the line -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- u(s) = ζ(s)/|ζ(s)|: 单位圆投影 (相位)。 
English: u(s) = ζ(s)/|ζ(s)|: unit-circle projection (phase). -/
def zetaUnit (s : ℂ) : ℂ := riemannZeta s / ‖riemannZeta s‖

/-- u 在 ζ ≠ 0 且 s ≠ 1 处连续: ζ 在 {1}ᶜ 可微, 除法分母非零。 
English: u continuous where ζ ≠ 0 and s ≠ 1: ζ differentiable on {1}ᶜ, division denominator nonzero. -/
lemma continuousOn_zetaUnit :
    ContinuousOn zetaUnit ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
  have hzeta : ContinuousOn riemannZeta ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) :=
    differentiableOn_riemannZeta.continuousOn.mono (by intro s hs; exact hs.1)
  have hnorm : ContinuousOn (fun s : ℂ => (‖riemannZeta s‖ : ℂ))
      ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
    intro x hx
    exact ContinuousWithinAt.comp (t := Set.univ) continuous_ofReal.continuousWithinAt
      (hzeta x hx).norm (by intro y hy; simp)
  refine hzeta.div hnorm ?_
  intro s hs
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hs.2)

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 
English: χ(s) = 2·(2π)^{s−1}·Γ(1−s)·sin(πs/2): functional equation multiplier (explicit phase). -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

/-- χ 沿临界线连续: 幂 (底 2π ∈ slitPlane) / Γ (1-s 非负整数) / sin 逐项连续。 
English: χ continuous on the critical line: power (base 2π ∈ slitPlane) / Γ (1−s not a nonpositive integer) / sin, each continuous. -/
lemma continuousOn_chi_line : ContinuousOn chi {s : ℂ | s.re = 1 / 2} := by
  have hpow : ContinuousOn (fun s : ℂ => (2 * ↑Real.pi : ℂ) ^ (s - 1))
      {s | s.re = 1 / 2} := by
    refine ContinuousOn.cpow continuousOn_const ?hg ?h0
    · have hg : ContinuousOn (fun s : ℂ => s - 1) {s | s.re = 1 / 2} := by
        intro s hs
        exact (continuousAt_id.sub continuousAt_const).continuousWithinAt
      exact hg
    · intro s hs
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
        rw [Complex.mul_re]
        simp
        nlinarith [Real.pi_pos]))
  have hΓ : ContinuousOn (fun s : ℂ => Complex.Gamma (1 - s))
      {s | s.re = 1 / 2} := by
    intro s hs
    have h1ms : ContinuousAt (fun s : ℂ => 1 - s) s := by
      change ContinuousAt ((fun _ : ℂ => (1 : ℂ)) - id) s
      exact continuousAt_const.sub continuousAt_id
    exact (ContinuousAt.comp (continuousAt_Gamma (1 - s) (by
      intro m hm
      have hsr : s.re = 1 / 2 := by simpa using hs
      have hre' : 1 - s.re = -↑(m : ℝ) := by
        simpa using congrArg Complex.re hm
      have hneg : -↑(m : ℝ) = 1 / 2 := by linarith [hsr, hre']
      have hnonneg : (0 : ℝ) ≤ ↑(m : ℝ) := Nat.cast_nonneg m
      nlinarith)) h1ms).continuousWithinAt
  have hsin : ContinuousOn (fun s : ℂ => Complex.sin (↑Real.pi * s / 2))
      {s | s.re = 1 / 2} := by
    have hlin : Continuous (fun s : ℂ => (↑Real.pi / 2 : ℂ) * s) :=
      continuous_const.mul continuous_id
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Function.comp_def] using
      (continuous_sin.comp hlin).continuousOn
  change ContinuousOn
    (fun s : ℂ =>
      2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2))
    {s | s.re = 1 / 2}
  exact ((continuousOn_const.mul hpow).mul hΓ).mul hsin

end RiemannUnifiedObservation
