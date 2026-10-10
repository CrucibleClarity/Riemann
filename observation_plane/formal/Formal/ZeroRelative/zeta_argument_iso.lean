import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Ring

/-!
# T6j: 参数原理 — 矩形闭合 (对消法的积分形式)

**参数原理 = 对消法的积分形式** (pat 本质, 2026-08-19):
绕闭合路径一圈, 连续相位对消干净, 剩下的整数 = 内部零点数:
    (1/2πi)∮_∂R f'/f = N(内部零点数) ∈ ℤ
单零点情形 (本文件): f 在圆盘内唯一简单零点 z₀ ⟹
    ∮_{C(c,R)} f'/f = 2πi   (f'/f 的对数导数 = 相位变化率)
证明: f = (z-z₀)·g, g(z₀) ≠ 0 ⟹ f'/f = 1/(z-z₀) + g'/g;
    ∮ 1/(z-z₀) = 2πi (柯西积分公式), ∮ g'/g = 0 (Cauchy-Goursat);
    环域上两积分相等 (挖洞同伦不变)。

矩形闭合 (Riemann-von Mangoldt, 后续拼装):
    N(T) = (1/2πi)∮_{∂R} ξ'/ξ = (1/π)θ_χ(T) + S(T) + 1
    竖直边 (临界线) = ζ 相位变化 (θ_ζ), 实轴边 = 0 (ξ 实值),
    对消: 连续相位全消 ⟹ 整数零点计数。

隔离文件 (mathlib-only)。 
English: Logarithmic-derivative decomposition: f = (z-z₀)·g ⟹ f'/f = 1/(z-z₀) + g'/g -/

noncomputable section

open Complex Function FormalMultilinearSeries Set circleIntegral
open Metric
open scoped Topology

namespace RiemannUnifiedObservation

/-- **对数导数分解**: f = (z-z₀)·g ⟹ f'/f = 1/(z-z₀) + g'/g
    (乘积求导: f' = g + (z-z₀)·g' ⟹ f'/f = g/f + (z-z₀)g'/f
    = 1/(z-z₀) + g'/g, 在 z ≠ z₀ 且 g ≠ 0 处)。 
English: Logarithmic-derivative decomposition: f = (z-z₀)·g ⟹ f'/f = 1/(z-z₀) + g'/g -/
theorem logDeriv_decomposition {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ z, f z = (z - z₀) * g z) (hg : DifferentiableAt ℂ g z)
    (hz : z ≠ z₀) (hgz : g z ≠ 0) :
    deriv f z / f z = (z - z₀)⁻¹ + deriv g z / g z := by
  -- f' = g + (z-z₀)·g' (乘积求导)
  have hderiv : deriv f z = g z + (z - z₀) * deriv g z := by
    have hfg : f = fun w => (w - z₀) * g w := by
      funext w
      exact hf w
    rw [hfg]
    have hd : deriv (fun w : ℂ => w - z₀) z = 1 := by
      simp
    have hdm : deriv (fun w : ℂ => (w - z₀) * g w) z =
        deriv (fun w : ℂ => w - z₀) z * g z + (z - z₀) * deriv g z := by
      have hc : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z := by fun_prop
      have hdm0 := deriv_mul (𝕜 := ℂ) hc hg
      -- hdm0 : deriv ((fun w => w - z₀) * g) z = deriv (fun w => w-z₀) z * g z + ...
      calc
        deriv (fun w : ℂ => (w - z₀) * g w) z = deriv ((fun w : ℂ => w - z₀) * g) z := by
          congr 1
        _ = deriv (fun w : ℂ => w - z₀) z * g z + (z - z₀) * deriv g z := hdm0
    rw [hdm, hd]
    ring
  -- f = (z-z₀)·g, 除:
  rw [hderiv, hf z]
  -- (g + (z-z₀)g') / ((z-z₀)·g) = 1/(z-z₀) + g'/g
  field_simp [hz, hgz]

/-- **参数原理 (单简单零点, 圆路径)**: f 在闭圆盘解析, 唯一简单零点
    z₀ 在内部, 边界无零点 ⟹ ∮_{C(c,R)} f'/f = 2πi。
    证明: 局部 f = (z-z₀)g (g(z₀) ≠ 0); 环域上 ∮_{C(c,R)} = ∮_{C(z₀,r)};
    ∮_{C(z₀,r)} f'/f = ∮ 1/(z-z₀) + ∮ g'/g = 2πi + 0。 
English: The argument principle (single simple zero, circular path): f analytic on the closed disk with a unique simple zero -/
theorem circle_argument_principle_simple_zero {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R))
    (hfz₀ : f z₀ = 0) (hf' : deriv f z₀ ≠ 0)
    (hfne : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z ≠ 0) :
    (∮ z in C(z₀, R / 2), deriv f z / f z) = 2 * ↑Real.pi * I := by
  let g : ℂ → ℂ := dslope f z₀
  -- f = (z-z₀)·g 处处 (f(z₀) = 0: (z-z₀)·dslope = f z - f z₀)
  have hfg : ∀ z, f z = (z - z₀) * g z := by
    intro z
    have hd := sub_smul_dslope f z₀ z
    have : f z = (z - z₀) * dslope f z₀ z := by
      simpa [smul_eq_mul, hfz₀] using hd.symm
    simpa [g] using this
  -- g(z₀) = deriv f z₀ ≠ 0
  have hgz₀ : g z₀ ≠ 0 := by
    simpa [g, dslope_same] using hf'
  -- g ≠ 0 于开球 (去心由 f ≠ 0, 圆心由 hgz₀)
  have hgne : ∀ z ∈ ball z₀ R, g z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = z₀
    · subst z
      exact hgz₀
    · have hg : g z = f z / (z - z₀) := by
        dsimp [g]
        have hd0 := dslope_of_ne f hz0
        rw [hd0]
        simp [slope, hfz₀, div_eq_mul_inv, mul_comm]
      rw [hg]
      exact div_ne_zero (hfne z hz hz0) (sub_ne_zero.mpr hz0)
  -- f 解析于开球 ⟹ g 解析于开球
  have hf_ana : AnalyticOn ℂ f (ball z₀ R) := hf.analyticOn isOpen_ball
  have hg_ana : AnalyticOn ℂ g (ball z₀ R) := by
    intro z hz
    by_cases hz0 : z = z₀
    · subst z
      rcases (hf_ana.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))) with ⟨p, hp⟩
      -- dslope 保持解析 (has_fpower_series_iterate_dslope_fslope)
      have hds : HasFPowerSeriesAt (dslope f z₀) (fslope^[1] p) z₀ := by
        -- swap dslope z₀ f = dslope f z₀ (swap 交换 dslope 的第 2/3 参数)
        simpa [g, swap] using (hp.has_fpower_series_iterate_dslope_fslope 1)
      exact hds.analyticAt.analyticWithinAt
    · -- z ≠ z₀: g 与 f/(·-z₀) 邻域相等, 后者解析 (f 解析 / 非零线性)
      have hg_eq : g =ᶠ[𝓝 z] fun w => f w / (w - z₀) := by
        filter_upwards [eventually_ne_nhds hz0] with w hw
        dsimp [g]
        have hd0 := dslope_of_ne f hw
        rw [hd0]
        simp [slope, hfz₀, div_eq_mul_inv, mul_comm]
      have hid : AnalyticAt ℂ (fun w : ℂ => w - z₀) z := by
        -- id - const: 多项式解析 (恒等与常数)
        simpa [show (fun w : ℂ => w - z₀) = _root_.id - fun _ : ℂ => z₀ by funext w; rfl]
          using ((analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := z)).sub
            (analyticAt_const (𝕜 := ℂ) (F := ℂ) (x := z) (v := z₀)))
      have hquot : AnalyticAt ℂ (fun w : ℂ => f w / (w - z₀)) z :=
        (hf_ana.analyticAt (isOpen_ball.mem_nhds hz)).div hid (sub_ne_zero.mpr hz0)
      exact ((analyticAt_congr hg_eq).mpr hquot).analyticWithinAt
  -- g 可导于开球 (解析 ⟹ 可导)
  have hg_diff : DifferentiableOn ℂ g (ball z₀ R) := hg_ana.differentiableOn
  -- 圆周上分解: f'/f = (z-z₀)⁻¹ + g'/g
  have hfun : EqOn (fun z => deriv f z / f z)
      (fun z => (z - z₀)⁻¹ + deriv g z / g z) (sphere z₀ (R / 2)) := by
    intro z hz
    have hzball : z ∈ ball z₀ R := by
      -- dist z z₀ = R/2 < R
      exact mem_ball.mpr (by
        have hd : dist z z₀ = R / 2 := by simpa [sphere] using hz
        linarith)
    have hz0 : z ≠ z₀ := by
      -- dist z z₀ = R/2 > 0
      intro h
      have : dist z z₀ = 0 := by rw [h]; simp
      linarith [show dist z z₀ = R / 2 by simpa [sphere] using hz, hR]
    exact logDeriv_decomposition hfg
      ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).differentiableAt) hz0 (hgne z hzball)
  -- ∮ f'/f = ∮ 1/(z-z₀) + ∮ g'/g (积分线性)
  have hsplit : (∮ z in C(z₀, R / 2), deriv f z / f z) =
      (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) + (∮ z in C(z₀, R / 2), deriv g z / g z) := by
    calc
      (∮ z in C(z₀, R / 2), deriv f z / f z) =
          ∮ z in C(z₀, R / 2), ((z - z₀)⁻¹ + deriv g z / g z) := by
        rw [circleIntegral.integral_congr (by positivity : (0 : ℝ) ≤ R / 2) hfun]
      _ = (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) +
          (∮ z in C(z₀, R / 2), deriv g z / g z) := by
        rw [circleIntegral.integral_add]
        · -- (z-z₀)⁻¹ 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          -- (fun z => (z - z₀)⁻¹) 连续于 z (z ≠ z₀)
          have hz_ne : (fun w : ℂ => w - z₀) z ≠ 0 := by
            change z - z₀ ≠ 0
            intro hz_eq  -- hz_eq : z - z₀ = 0
            have hz0 : z = z₀ := sub_eq_zero.mp hz_eq
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            rw [hz0] at hd
            simp at hd
            linarith
          exact ((continuousAt_id.sub continuousAt_const).inv₀ hz_ne).continuousWithinAt
        · -- g'/g 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          -- g 解析 ⟹ g'/g 解析 ⟹ 连续
          have hzball : z ∈ ball z₀ R := by
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            exact mem_ball.mpr (by linarith)
          have hd_ana : AnalyticAt ℂ (fun w => deriv g w / g w) z :=
            ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
              (hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
          exact hd_ana.continuousAt.continuousWithinAt
  -- ∮ 1/(z-z₀) = 2πi
  have hmain : (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) = 2 * ↑Real.pi * I := by
    -- integral_sub_inv_of_mem_ball: z₀ ∈ ball z₀ (R/2)
    exact integral_sub_inv_of_mem_ball (c := z₀) (w := z₀) (R := R / 2)
      (mem_ball_self (div_pos hR (by norm_num)))
  -- ∮ g'/g = 0 (g'/g 解析于小闭圆盘, Goursat)
  have hzero : (∮ z in C(z₀, R / 2), deriv g z / g z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable (c := z₀) (R := R / 2)
      (s := ∅) (f := fun z => deriv g z / g z)
    · -- 0 ≤ R/2
      positivity
    · -- s 可数
      simp
    · -- ContinuousOn (fun z => deriv g z / g z) (closedBall z₀ (R/2))
      have hdg_ana : AnalyticOn ℂ (deriv g) (ball z₀ R) := fun z hz =>
        (hg_ana.analyticAt (isOpen_ball.mem_nhds hz)).deriv.analyticWithinAt
      have hsub : closedBall z₀ (R / 2) ⊆ ball z₀ R := by
        intro z hz
        exact mem_ball.mpr (by
          have hd : dist z z₀ ≤ R / 2 := (mem_closedBall.mp hz)
          linarith)
      have hdg_cont : ContinuousOn (deriv g) (closedBall z₀ (R / 2)) :=
        hdg_ana.continuousOn.mono hsub
      have hg_cont : ContinuousOn g (closedBall z₀ (R / 2)) :=
        hg_ana.continuousOn.mono hsub
      have hg_inv : ContinuousOn (fun z => (g z)⁻¹) (closedBall z₀ (R / 2)) :=
        hg_cont.inv₀ (fun z hz => hgne z (hsub hz))
      have hmul : ContinuousOn (deriv g * fun z => (g z)⁻¹) (closedBall z₀ (R / 2)) :=
        hdg_cont.mul hg_inv
      have hfun_eq : (deriv g * fun z => (g z)⁻¹) = fun z => deriv g z * (g z)⁻¹ := by
        funext z
        rfl
      simpa [div_eq_mul_inv, hfun_eq] using hmul
    · -- hd: 开球内 (去心) g'/g 可导
      intro z hz
      have hzball : z ∈ ball z₀ R := by
        have hd : dist z z₀ < R / 2 := (mem_ball.mp hz.1)
        exact mem_ball.mpr (by linarith)
      have hd_ana : AnalyticAt ℂ (fun w => deriv g w / g w) z :=
        ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
          (hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
      exact hd_ana.differentiableAt
  -- 组合: 2·↑π·I + 0
  rw [hsplit, hmain, hzero]
  ring

/-- **相位-计数恒等式**: 参数原理的积分形式 — 绕闭合路径的相位变化
    = 2πi·(内部零点数)。单零点: ∮ f'/f = 2πi ⟺ 一个零点。 
English: Phase-count identity: the integral form of the argument principle —— the phase change around a closed path -/
theorem zero_count_formula {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R))
    (hfz₀ : f z₀ = 0) (hf' : deriv f z₀ ≠ 0)
    (hfne : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z ≠ 0) :
    (∮ z in C(z₀, R / 2), deriv f z / f z) / (2 * ↑Real.pi * I) = 1 := by
  rw [circle_argument_principle_simple_zero hR hf hfz₀ hf' hfne]
  -- (2πi)/(2πi) = 1
  have hne : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp h)
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hπ)
      (by norm_num : (I : ℂ) ≠ 0)
  exact div_self hne

end RiemannUnifiedObservation
