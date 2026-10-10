import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# T6c: χ 沿临界线的连续幅角提升 (翻转计数 = 提升差/2π 的前件)

翻转 (u → -u) ⟺ χ 转一整圈: u² = χ (T5), u 翻转 ⟹ u² 相位跳 2π。
χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) 是显式函数, 沿临界线非零连续,
故 χ 沿临界线本身是基空间 ℂ\{0} 中的路径, 经覆盖映射 exp : ℂ → ℂ\{0}
提升为连续幅角 θ (IsCoveringMap.liftPath):
    exp(θ(s)) = χ(1/2 + T·s·i),  θ 0 = y₀ = log χ(1/2)
翻转次数 = (θ(1) - θ(0)) 的虚部差 / 2π (圈数)。

"连续 = 无数离散相位点的投影": χ 的相位场 (连续) 的整数圈数 = 离散
翻转计数。π 的超越性 (sin 零点恰在 πℤ, Lindemann) 保证相位跳变是
精确的 π 量子, 计数无漂移。

隔离文件 (mathlib-only)。 
English: χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): functional-equation multiplier (explicit phase). -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 
English: χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): functional-equation multiplier (explicit phase). -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

/-- χ 沿临界线连续: 幂 (底 2π ∈ slitPlane) / Γ (1-s 非负整数) / sin 逐项连续。 
English: χ continuous on the critical line: power (base 2π ∈ slitPlane) / Γ (1-s not a nonnegative integer) / sin each continuous. -/
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

/-- χ 沿临界线非零: 2 非零 / (2π)^{s-1} 底非零 / Γ(1-s) 在 re>0 / sin 零点在 πℤ 之外。 
English: χ nonzero on the critical line: 2 ≠ 0 / base (2π)^{s-1} ≠ 0 / Γ(1-s) at re > 0 / sin zeros outside πℤ. -/
lemma chi_ne_zero_on_line (t : ℝ) :
    chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0 := by
  dsimp [chi]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · norm_num
      · have h2pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
          mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
        exact (cpow_ne_zero_iff.mpr (Or.inl h2pi))
    · exact Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.add_re, Complex.mul_re]
        simp
        norm_num)
  · rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hπ0 : (↑Real.pi : ℂ) *
        (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ)) = 0 := by
      rw [mul_sub]
      have hπhalf : (↑Real.pi : ℂ) * (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) =
          (↑Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 := by
        ring
      rw [hπhalf, hk]
      ring
    have hsub : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ) = 0 :=
      (mul_eq_zero.mp hπ0).resolve_left hπ
    have hs2 : (1 / 2 : ℂ) + (t : ℝ) * Complex.I = (2 : ℂ) * (k : ℂ) := by
      calc
        (1 / 2 : ℂ) + (t : ℝ) * Complex.I =
            (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) * 2 := by ring
        _ = (k : ℂ) * 2 := by
          rw [show ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 = (k : ℂ)
            by simpa [sub_eq_zero] using hsub]
        _ = 2 * (k : ℂ) := by ring
    have hre0 : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by
      rw [Complex.add_re, Complex.mul_re]
      simp
    have hre1 : ((2 : ℂ) * (k : ℂ)).re = 2 * (k : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = 2 * (k : ℝ) := by
      have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re =
          ((2 : ℂ) * (k : ℂ)).re := by
        rw [hs2]
      rw [hre0, hre1] at hre
      exact hre
    have hEq' : (4 * (k : ℤ) : ℤ) = 1 := by
      have h4 : (4 * (k : ℝ) : ℝ) = 1 := by nlinarith [hEq]
      exact_mod_cast h4
    omega

/-- χ 沿临界线在 [0,1] 上的路径: 基空间 ℂ\{0} 值, 连续 (线上连续 + 参数连续)。 
English: χ path on [0,1] along the critical line: values in base space ℂ\{0}, continuous (continuity on the line + continuity in parameter). -/
def chiPath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I),
    chi_ne_zero_on_line (T * s.1)⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hpath : Continuous (fun s : ℝ => chi ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact continuousOn_chi_line.comp hsfun.continuousOn (by intro s hs; simp)
    exact Continuous.subtype_mk (hpath.comp continuous_subtype_val)
      (fun s => chi_ne_zero_on_line (T * s.1))

/-- 提升起点 y₀ = log χ(1/2): exp y₀ = χ(1/2) (exp_log)。 
English: Lift basepoint y₀ = log χ(1/2): exp y₀ = χ(1/2) (exp_log). -/
noncomputable def theta0 (_T : ℝ) : ℂ :=
  Complex.log (chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I))

lemma exp_theta0 (T : ℝ) :
    Complex.exp (theta0 T) = chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I) := by
  dsimp [theta0]
  exact Complex.exp_log (chi_ne_zero_on_line 0)

/-- liftPath 的起点条件: γ 0 = p y₀ (χ(1/2) = exp y₀)。 
English: Starting-point condition for liftPath: γ 0 = p y₀ (χ(1/2) = exp y₀). -/
private lemma liftPath_γ0 (T : ℝ) :
    chiPath T 0 = (⟨Complex.exp (theta0 T), Complex.exp_ne_zero (theta0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  dsimp [chiPath]
  have hzero : ((T * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by
    simp
  rw [hzero]
  simpa using (exp_theta0 T).symm

/-- χ 的连续幅角提升: exp(θ(s)) = χ(1/2 + T·s·i), θ 0 = y₀。
    翻转计数 = (θ(1) - θ(0)) 的虚部差 / 2π。 
English: Continuous argument lift of χ: exp(θ(s)) = χ(1/2 + T·s·i), θ 0 = y₀. Flip count = (θ(1) - θ(0)).im / 2π (winding number). -/
noncomputable def thetaLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (chiPath T) (theta0 T) (liftPath_γ0 T)

/-- 提升性质: exp(θ(s)) = χ(1/2 + T·s·i)。 
English: Lifting property: exp(θ(s)) = χ(1/2 + T·s·i). -/
lemma thetaLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (thetaLift T s) = chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I) := by
  have h := (isCoveringMap_exp.liftPath_lifts (chiPath T) (theta0 T) (liftPath_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [thetaLift]
  simpa [chiPath] using hs

/-- 提升起点: θ(0) = y₀。 
English: Lift basepoint: θ(0) = y₀. -/
lemma thetaLift_zero (T : ℝ) :
    thetaLift T 0 = theta0 T := by
  exact isCoveringMap_exp.liftPath_zero (chiPath T) (theta0 T) (liftPath_γ0 T)

end RiemannUnifiedObservation
