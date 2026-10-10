import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Ring

/-!
# T6j-m: 参数原理 m 阶版 — 围道-计数桥的分析实例 (Part II KNOWN 首块机证)

**m 阶幅角原理**: f 在闭圆盘解析, 唯一 m 阶零点 z₀ 在内部, 边界无零点
⟹ ∮_{C(z₀,R/2)} f'/f = 2πi·m。
证明: 局部 f = (z-z₀)^m·g (g(z₀) ≠ 0) ⟹ f'/f = m/(z-z₀) + g'/g
(logDeriv_pow_decomposition); ∮ m/(z-z₀) = m·2πi (积分常数线性 +
柯西积分公式), ∮ g'/g = 0 (Cauchy-Goursat)。

**净元链 (ArgumentPrincipleMultiplicity 拼装)**: ①分解件 (幂版对数导数)
× ②线性件 (integral_add + integral_const_mul) × ③配对件 (重数 m × 圈长
2π) × ④消零件 (Goursat) — 本文件是生产区自动化直证 (步骤 2)。

**落点**: Part II KNOWN 首块 (multiplicity-weighted summation 的
单零点版); hseg (每零点贡献 m·2π) 的实例化第一步。

隔离文件 (mathlib-only)。 
English: Argument principle, m-th order: f analytic on the closed disk with a unique zero of order m ⟹ ∮ f'/f = 2πi·m -/

noncomputable section

open Complex Function FormalMultilinearSeries Set circleIntegral
open Metric
open scoped Topology

namespace RiemannUnifiedObservation

/-- **对数导数分解 (m 阶)**: f = (z-z₀)^m·g ⟹ f'/f = m/(z-z₀) + g'/g
    (乘积求导 + 幂求导: f' = m·a^{m-1}·g + a^m·g' ⟹ 除法化简;
    在 z ≠ z₀ 且 g ≠ 0 处)。 
English: Logarithmic-derivative decomposition (m-th order): f = (z−z₀)^m·g ⟹ f'/f = m/(z−z₀) + g'/g -/
theorem logDeriv_pow_decomposition {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (m : ℕ)
    (hf : ∀ z ∈ ball z₀ R, f z = (z - z₀) ^ m * g z) (hzball : z ∈ ball z₀ R)
    (hg : DifferentiableAt ℂ g z)
    (hz : z ≠ z₀) (hgz : g z ≠ 0) :
    deriv f z / f z = (m : ℂ) * (z - z₀)⁻¹ + deriv g z / g z := by
  -- 球内逐点相等 ⟹ z 邻域内函数相等 (ball 开) ⟹ deriv 不变
  have hfg_nhds : f =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    exact hf w hw
  -- f' = m·a^{m-1}·g + a^m·g' (a = z-z₀, 乘积求导 + 幂求导)
  have hderiv : deriv f z = (m : ℂ) * (z - z₀) ^ (m - 1) * g z + (z - z₀) ^ m * deriv g z := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z := by fun_prop
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ m) z := by fun_prop
    have hm := deriv_mul (𝕜 := ℂ) hpow hg
    have hp : deriv (fun w : ℂ => (w - z₀) ^ m) z = (m : ℂ) * (z - z₀) ^ (m - 1) := by
      have hpd := deriv_pow (f := fun w : ℂ => w - z₀) (x := z) (n := m) hd
      have hd1 : deriv (fun w : ℂ => w - z₀) z = 1 := by simp
      simpa [hd1] using hpd
    calc
      deriv f z = deriv (fun w : ℂ => (w - z₀) ^ m * g w) z := by
        exact hfg_nhds.deriv_eq
      _ = deriv ((fun w : ℂ => (w - z₀) ^ m) * g) z := by congr 1
      _ = deriv (fun w : ℂ => (w - z₀) ^ m) z * g z + (z - z₀) ^ m * deriv g z := by
        simpa using hm
      _ = (m : ℂ) * (z - z₀) ^ (m - 1) * g z + (z - z₀) ^ m * deriv g z := by rw [hp]
  -- f'/f = [m·a^{m-1}·g + a^m·g'] / (a^m·g) = m·a⁻¹ + g'/g
  rw [hderiv, hf z hzball]
  by_cases hm : m = 0
  · -- m = 0: f = g, 平凡 (a^0 = 1, 0·a⁻¹ = 0)
    subst m
    simp [pow_zero]
  · -- m ≥ 1: a^m = a^{m-1}·a, 对消 a^{m-1}·g 与 a
    have hpow : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm))
      rw [← pow_succ]
      rw [hm1]
    rw [hpow]
    field_simp [hz, hgz]

/-- **参数原理 (m 阶零点, 圆路径)**: f 在闭圆盘解析, 唯一 m 阶零点
    z₀ 在内部, 边界无零点 ⟹ ∮_{C(z₀,R/2)} f'/f = 2πi·m。
    证明: 局部 f = (z-z₀)^m·g (g(z₀) ≠ 0); 圆周上 f'/f = m/(z-z₀) + g'/g;
    ∮ m/(z-z₀) = m·2πi (积分常数线性 + 柯西), ∮ g'/g = 0 (Goursat)。 
English: The argument principle (zero of order m, circular path): f analytic on the closed disk with a unique zero of order m -/
theorem circle_argument_principle_multiplicity {z₀ : ℂ} {R : ℝ} (m : ℕ)
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R))
    (hfg : ∀ z ∈ ball z₀ R, f z = (z - z₀) ^ m * g z)
    (hgz₀ : g z₀ ≠ 0) (hg_cont : ContinuousAt g z₀)
    (hg_diff : DifferentiableOn ℂ g (ball z₀ R))
    (hfne : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z ≠ 0) :
    (∮ z in C(z₀, R / 2), deriv f z / f z) =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  -- g ≠ 0 于开球 (去心由 f ≠ 0, 圆心由 hgz₀)
  have hgne : ∀ z ∈ ball z₀ R, g z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = z₀
    · subst z
      exact hgz₀
    · have hg : g z = f z / (z - z₀) ^ m := by
        have hfz := hfg z hz
        -- f = a^m·g ⟹ g = f/a^m (a ≠ 0)
        have hne : (z - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hz0)
        rw [hfz]
        field_simp [hne]
      rw [hg]
      exact div_ne_zero (hfne z hz hz0) (pow_ne_zero m (sub_ne_zero.mpr hz0))
  -- 圆周上分解: f'/f = m·(z-z₀)⁻¹ + g'/g
  have hfun : EqOn (fun z => deriv f z / f z)
      (fun z => (m : ℂ) * (z - z₀)⁻¹ + deriv g z / g z) (sphere z₀ (R / 2)) := by
    intro z hz
    have hzball : z ∈ ball z₀ R := by
      exact mem_ball.mpr (by
        have hd : dist z z₀ = R / 2 := by simpa [sphere] using hz
        linarith)
    have hz0 : z ≠ z₀ := by
      intro h
      have : dist z z₀ = 0 := by rw [h]; simp
      linarith [show dist z z₀ = R / 2 by simpa [sphere] using hz, hR]
    exact logDeriv_pow_decomposition (f := f) (g := g) (z₀ := z₀) (R := R) m
      hfg hzball
      (hg_diff.differentiableAt (isOpen_ball.mem_nhds hzball)) hz0 (hgne z hzball)
  -- ∮ f'/f = ∮ m·(z-z₀)⁻¹ + ∮ g'/g (积分线性)
  have hsplit : (∮ z in C(z₀, R / 2), deriv f z / f z) =
      (∮ z in C(z₀, R / 2), (m : ℂ) * (z - z₀)⁻¹) + (∮ z in C(z₀, R / 2), deriv g z / g z) := by
    calc
      (∮ z in C(z₀, R / 2), deriv f z / f z) =
          ∮ z in C(z₀, R / 2), ((m : ℂ) * (z - z₀)⁻¹ + deriv g z / g z) := by
        rw [circleIntegral.integral_congr (by positivity : (0 : ℝ) ≤ R / 2) hfun]
      _ = (∮ z in C(z₀, R / 2), (m : ℂ) * (z - z₀)⁻¹) +
          (∮ z in C(z₀, R / 2), deriv g z / g z) := by
        rw [circleIntegral.integral_add]
        · -- m·(z-z₀)⁻¹ 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          have hz_ne : (fun w : ℂ => w - z₀) z ≠ 0 := by
            change z - z₀ ≠ 0
            intro hz_eq
            have hz0 : z = z₀ := sub_eq_zero.mp hz_eq
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            rw [hz0] at hd
            simp at hd
            linarith
          exact (((continuousAt_id.sub continuousAt_const).inv₀ hz_ne).const_mul (m : ℂ)).continuousWithinAt
        · -- g'/g 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          have hzball : z ∈ ball z₀ R := by
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            exact mem_ball.mpr (by linarith)
          have hd_ana : AnalyticAt ℂ (fun w => deriv g w / g w) z :=
            ((hg_diff.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
              (hg_diff.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
          exact hd_ana.continuousAt.continuousWithinAt
  -- ∮ m·(z-z₀)⁻¹ = m·2πi (积分常数线性 + 柯西)
  have hmain : (∮ z in C(z₀, R / 2), (m : ℂ) * (z - z₀)⁻¹) =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    have hbase : (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) = 2 * ↑Real.pi * Complex.I :=
      integral_sub_inv_of_mem_ball (c := z₀) (w := z₀) (R := R / 2)
        (mem_ball_self (div_pos hR (by norm_num)))
    -- ∮ m·h = m·∮ h (circleIntegral.integral_const_mul)
    rw [circleIntegral.integral_const_mul (a := (m : ℂ)) (f := fun z => (z - z₀)⁻¹)
      (c := z₀) (R := R / 2)]
    rw [hbase]
  -- ∮ g'/g = 0 (g'/g 解析于小闭圆盘, Goursat)
  have hzero : (∮ z in C(z₀, R / 2), deriv g z / g z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable (c := z₀) (R := R / 2)
      (s := ∅) (f := fun z => deriv g z / g z)
    · positivity
    · simp
    · -- ContinuousOn (fun z => deriv g z / g z) (closedBall z₀ (R/2))
      have hdg_ana : AnalyticOn ℂ (deriv g) (ball z₀ R) := fun z hz =>
        (hg_diff.analyticAt (isOpen_ball.mem_nhds hz)).deriv.analyticWithinAt
      have hsub : closedBall z₀ (R / 2) ⊆ ball z₀ R := by
        intro z hz
        exact mem_ball.mpr (by
          have hd : dist z z₀ ≤ R / 2 := (mem_closedBall.mp hz)
          linarith)
      have hdg_cont : ContinuousOn (deriv g) (closedBall z₀ (R / 2)) :=
        hdg_ana.continuousOn.mono hsub
      have hg_cont : ContinuousOn g (closedBall z₀ (R / 2)) :=
        hg_diff.continuousOn.mono hsub
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
        ((hg_diff.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
          (hg_diff.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
      exact hd_ana.differentiableAt
  -- 组合: m·2πi + 0 = m·(2πi)
  rw [hsplit, hmain, hzero]
  ring

/-- **ζ 的 m 阶围道 (hseg 单零点实例)**: ζ 在 s₀ 零点 (重数 m), 小圆内
    ζ(s) = (s-s₀)^m·g (分解, g 解析非零) 且无其他零点 ⟹ ∮ ζ'/ζ = 2πi·m
    — 围道-计数桥输入 hseg 的 ζ 实例化 (Part II KNOWN 首块:
    multiplicity-weighted summation 的单零点版)。分解 (hExp) 由
    zeta_local_expansion 给出 (R 足够小), 此处为显式输入; m 为参数
    (与分解的重数一致)。 
English: Zeta m-th order contour: local expansion at zero s₀ (order m) with no other zeros in the small circle ⟹ ∮ ζ'/ζ = 2πi·m -/
theorem zeta_contour_multiplicity (s₀ : ℂ) (hs₀ : s₀ ≠ 1) (hz₀ : riemannZeta s₀ = 0)
    {R : ℝ} (m : ℕ) (hR : 0 < R)
    (hR1 : ball s₀ R ⊆ ({1}ᶜ : Set ℂ))
    (hExp : ∃ g : ℂ → ℂ,
      (∀ s ∈ ball s₀ R, riemannZeta s = (s - s₀) ^ m * g s) ∧
      g s₀ ≠ 0 ∧ AnalyticOn ℂ g (ball s₀ R))
    (hne : ∀ z ∈ ball s₀ R, z ≠ s₀ → riemannZeta z ≠ 0) :
    (∮ z in C(s₀, R / 2), deriv riemannZeta z / riemannZeta z) =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rcases hExp with ⟨g, hfg, hg0, hgana⟩
  exact circle_argument_principle_multiplicity (f := riemannZeta) (g := g)
    (z₀ := s₀) (R := R) m hR
    (analyticOn_riemannZeta.analyticOn.differentiableOn.mono hR1)
    hfg hg0
    (hgana.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR)))
    hgana.differentiableOn hne

/-- **ζ 多零点求和 (hseg 全局实例)**: K 个零点 (重数 m_k), 互不相交
    小圆内无他零 ⟹ Σ_k ∮_{C(s_k,R_k/2)} ζ'/ζ = 2πi·Σ m_k —
    multiplicity-weighted summation 的机证版 (Part II KNOWN 主体;
    每零点由 zeta_contour_multiplicity 给出, Finset 求和 + sum_mul)。 
English: Zeta multi-zero summation: K zeros with multiplicities m_k ⟹ Σ_k ∮ ζ'/ζ = 2πi·Σ m_k (machine-verified multiplicity-weighted summation) -/
theorem zeta_contour_multiplicity_sum {K : ℕ} (s : Fin K → ℂ) (m : Fin K → ℕ)
    (hs : ∀ k : Fin K, s k ≠ 1)
    (hz : ∀ k : Fin K, riemannZeta (s k) = 0)
    {R : Fin K → ℝ} (hR : ∀ k : Fin K, 0 < R k)
    (hR1 : ∀ k : Fin K, ball (s k) (R k) ⊆ ({1}ᶜ : Set ℂ))
    (hExp : ∀ k : Fin K, ∃ g : ℂ → ℂ,
      (∀ z ∈ ball (s k) (R k), riemannZeta z = (z - s k) ^ (m k) * g z) ∧
      g (s k) ≠ 0 ∧ AnalyticOn ℂ g (ball (s k) (R k)))
    (hne : ∀ k : Fin K, ∀ z ∈ ball (s k) (R k), z ≠ s k → riemannZeta z ≠ 0) :
    (∑ k : Fin K, (∮ z in C(s k, R k / 2), deriv riemannZeta z / riemannZeta z)) =
      (∑ k : Fin K, (m k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by
  -- 每零点: ∮_k = 2πi·m_k (单零点定理)
  have hk : ∀ k : Fin K,
      (∮ z in C(s k, R k / 2), deriv riemannZeta z / riemannZeta z) =
        (m k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    intro k
    exact zeta_contour_multiplicity (s k) (hs k) (hz k) (R := R k) (m k) (hR k)
      (hR1 k) (hExp k) (hne k)
  -- 求和: Σ (m_k·2πi) = (Σm_k)·2πi
  calc
    (∑ k : Fin K, (∮ z in C(s k, R k / 2), deriv riemannZeta z / riemannZeta z))
        = ∑ k : Fin K, ((m k : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact hk k
    _ = (∑ k : Fin K, (m k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by
          rw [← Finset.sum_mul]

/-- **全局围道桥 (连接段贡献 0 的组合落点)**: 总围道 ∮_Γ 分解为
    每零点小圈之和 (hΓ — 挖洞同伦/连接段消零的分析侧输入) ⟹
    ∮_Γ = 2πi·Σ m_k — 围道-计数桥输入 hseg 的全局 ζ 实例 (代数侧
    完整: 求和已机证; 分析侧 hΓ 显式输入, 由 Goursat 全局给出)。 
English: Global contour bridge: total contour = sum of per-zero small circles (punctured-homotopy input hΓ) ⟹ ∮_Γ = 2πi·Σ m_k -/
theorem contour_total_bridge {K : ℕ} (s : Fin K → ℂ) (m : Fin K → ℕ) {c : ℂ} {RΓ : ℝ}
    (hs : ∀ k : Fin K, s k ≠ 1)
    (hz : ∀ k : Fin K, riemannZeta (s k) = 0)
    {R : Fin K → ℝ} (hR : ∀ k : Fin K, 0 < R k)
    (hR1 : ∀ k : Fin K, ball (s k) (R k) ⊆ ({1}ᶜ : Set ℂ))
    (hExp : ∀ k : Fin K, ∃ g : ℂ → ℂ,
      (∀ z ∈ ball (s k) (R k), riemannZeta z = (z - s k) ^ (m k) * g z) ∧
      g (s k) ≠ 0 ∧ AnalyticOn ℂ g (ball (s k) (R k)))
    (hne : ∀ k : Fin K, ∀ z ∈ ball (s k) (R k), z ≠ s k → riemannZeta z ≠ 0)
    (hΓ : (∮ z in C(c, RΓ), deriv riemannZeta z / riemannZeta z) =
      ∑ k : Fin K, (∮ z in C(s k, R k / 2), deriv riemannZeta z / riemannZeta z)) :
    (∮ z in C(c, RΓ), deriv riemannZeta z / riemannZeta z) =
      (∑ k : Fin K, (m k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by
  rw [hΓ]
  exact zeta_contour_multiplicity_sum s m hs hz hR hR1 hExp hne


/-- **ζ 围道挖洞 (环域同伦)**: 环域 (closedBall R \ ball r) 内 ζ 无零点
    (且闭球避开 1) ⟹ 大圆 ∮_{C(z₀,R)} ζ'/ζ = 小圆 ∮_{C(z₀,r)} ζ'/ζ —
    Cauchy-Goursat 环域定理 (circleIntegral_eq_of_differentiable_on_annulus_off_countable)
    的 ζ 实例: 连接段贡献 0 的分析侧 (挖洞同伦, hΓ 的单零点版)。 
English: Zeta contour puncturing (annular homotopy): no zeros in the closed annulus ⟹ integrals over the large and small circles agree (Cauchy-Goursat for annuli, ζ instance) -/
theorem zeta_contour_ring_shrink (z₀ : ℂ) {r R : ℝ} (h0 : 0 < r) (hrR : r ≤ R)
    (hR1 : closedBall z₀ R ⊆ ({1}ᶜ : Set ℂ))
    (hne : ∀ z ∈ closedBall z₀ R \ ball z₀ r, riemannZeta z ≠ 0) :
    (∮ z in C(z₀, R), deriv riemannZeta z / riemannZeta z) =
      (∮ z in C(z₀, r), deriv riemannZeta z / riemannZeta z) := by
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := z₀) (r := r) (R := R)
    (s := ∅) h0 hrR
  · -- ∅ 可数
    simp
  · -- 连续 on closedBall R \ ball r: ζ'/ζ = ζ'·(ζ)⁻¹
    intro z hz
    have hz1 : z ≠ 1 := by
      rcases hz with ⟨hzcb, hzr⟩
      exact (Set.mem_compl_singleton_iff.mp (hR1 hzcb))
    have hzana : AnalyticAt ℂ riemannZeta z :=
      analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds
        (by simpa [Set.mem_compl_singleton_iff] using hz1))
    have hdcont : ContinuousAt (deriv riemannZeta) z := hzana.deriv.continuousAt
    have hz0 : riemannZeta z ≠ 0 := hne z hz
    have hzcont : ContinuousAt riemannZeta z := hzana.continuousAt
    exact (hdcont.div hzcont hz0).continuousWithinAt
  · -- 可导 on (ball R \ closedBall r) \ ∅: ζ'/ζ 解析 (ζ 解析非零)
    intro z hz
    rcases hz with ⟨hzr, hzr'⟩
    have hz1 : z ≠ 1 := by
      have hzball : z ∈ ball z₀ R := hzr.1
      have hzcb : z ∈ closedBall z₀ R := mem_closedBall.mpr (le_of_lt (mem_ball.mp hzball))
      exact (Set.mem_compl_singleton_iff.mp (hR1 hzcb))
    have hzana : AnalyticAt ℂ riemannZeta z :=
      analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds
        (by simpa [Set.mem_compl_singleton_iff] using hz1))
    have hz0 : riemannZeta z ≠ 0 := by
      -- z ∈ ball R \ closedBall r ⟹ z ∈ closedBall R \ ball r
      apply hne z
      constructor
      · exact mem_closedBall.mpr (le_of_lt (mem_ball.mp hzr.1))
      · intro hb
        -- z ∈ ball r ⟹ z ∈ closedBall r — 与 hzr.2 (z ∉ closedBall r) 矛盾
        exact hzr.2 (mem_closedBall.mpr (le_of_lt (mem_ball.mp hb)))
    exact ((hzana.deriv).div hzana hz0).differentiableAt

/-- **ζ 全局围道 (单零点, hΓ 闭合)**: 闭球内唯一零点 z₀ (重数 m), 环域无零
    ⟹ 大圆 ∮_{C(z₀,R)} ζ'/ζ = 2πi·m — 挖洞 (ring_shrink) + 单零点
    (zeta_contour_multiplicity) 合成: 连接段贡献 0 的全局落点
    (contour_total_bridge 的 hΓ 对单零点不再需要输入 — 环域定理直接给)。 
English: Zeta global contour (single zero): unique zero of order m in the closed ball ⟹ ∮ over the large circle = 2πi·m (puncturing + single-zero theorem) -/
theorem zeta_contour_global_single (z₀ : ℂ) (hz₀ : riemannZeta z₀ = 0)
    {R : ℝ} (hR : 0 < R) (hR1 : closedBall z₀ R ⊆ ({1}ᶜ : Set ℂ))
    (m : ℕ)
    (hExp : ∃ g : ℂ → ℂ,
      (∀ z ∈ ball z₀ R, riemannZeta z = (z - z₀) ^ m * g z) ∧
      g z₀ ≠ 0 ∧ AnalyticOn ℂ g (ball z₀ R))
    (hne : ∀ z ∈ closedBall z₀ R, z ≠ z₀ → riemannZeta z ≠ 0) :
    (∮ z in C(z₀, R), deriv riemannZeta z / riemannZeta z) =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  -- 大圈 = 小圈 (环域无零, 挖洞同伦)
  have hshrink := zeta_contour_ring_shrink z₀ (r := R / 2) (R := R)
    (div_pos hR (by norm_num)) (by linarith) hR1
    (by
      -- 环域无零: 由闭球无他零 (环域不含 z₀)
      intro z hz
      apply hne z
      · exact hz.1
      · intro hz0
        -- z = z₀ 但 z ∈ closedBall R \ ball (R/2): z₀ ∈ ball (R/2) — 矛盾
        have hzin : z₀ ∈ ball z₀ (R / 2) := mem_ball_self (div_pos hR (by norm_num))
        have : z ∉ ball z₀ (R / 2) := hz.2
        exact this (by simpa [hz0] using hzin))
  rw [hshrink]
  -- 小圆: 单零点定理 (r = R/2)
  exact zeta_contour_multiplicity z₀ (by
      -- z₀ ≠ 1: z₀ ∈ closedBall z₀ R (dist 0 ≤ R) ⊆ {1}ᶜ
      have hzcb : z₀ ∈ closedBall z₀ R := mem_closedBall.mpr (by simp [le_of_lt hR])
      exact (Set.mem_compl_singleton_iff.mp (hR1 hzcb)))
    hz₀ (R := R) m hR
    (by
      -- ball ⊆ closedBall: 从 hR1 (闭球版) 得球版
      intro z hz
      exact hR1 (mem_closedBall.mpr (le_of_lt (mem_ball.mp hz))))
    hExp
    (by
      -- 球版无他零: 闭球版 mono
      intro z hz hz0
      exact hne z (mem_closedBall.mpr (le_of_lt (mem_ball.mp hz))) hz0)


/-- **ζ 矩形 Goursat (连接段贡献 0 的矩形版)**: ζ'/ζ 在无零点闭矩形上
    连续、开矩形内可导 ⟹ 矩形边界积分 = 0 — 多孔挖洞 (断点 A) 的
    基础件: 无零点区域边界积分消零 (mathlib 矩形 Cauchy-Goursat 的
    ζ 实例; 圆版为 zeta_contour_ring_shrink, 矩形版供分割论证用)。 
English: Zeta rectangle Goursat: ζ'/ζ has zero boundary integral over a zero-free rectangle (rectangle version of the segment-cancellation basis for multi-zero puncturing) -/
theorem zeta_rect_goursat (z w : ℂ)
    (hR1 : ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) ⊆ ({1}ᶜ : Set ℂ))
    (hne : ∀ x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)), riemannZeta x ≠ 0) :
    (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + z.im * Complex.I) /
        riemannZeta (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + w.im * Complex.I) /
        riemannZeta (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re w + y * Complex.I) /
        riemannZeta (re w + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re z + y * Complex.I) /
        riemannZeta (re z + y * Complex.I)) = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (f := fun x => deriv riemannZeta x / riemannZeta x) (z := z) (w := w) (s := ∅)
  · simp
  · -- 连续 on closedRect: ζ 解析非零 ⟹ ζ'/ζ 连续 (ContinuousAt.div)
    intro x hx
    have hx1 : x ≠ 1 := by
      exact (Set.mem_compl_singleton_iff.mp (hR1 hx))
    have hxana : AnalyticAt ℂ riemannZeta x :=
      analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds
        (by simpa [Set.mem_compl_singleton_iff] using hx1))
    have hdcont : ContinuousAt (deriv riemannZeta) x := hxana.deriv.continuousAt
    have hz0 : riemannZeta x ≠ 0 := hne x hx
    have hzcont : ContinuousAt riemannZeta x := hxana.continuousAt
    exact (hdcont.div hzcont hz0).continuousWithinAt
  · -- 可导 on 开矩形 \ ∅: ζ 解析非零 ⟹ ζ'/ζ 解析可导
    intro x hx
    rcases hx with ⟨hxr, hxr'⟩
    -- 开矩形 ⊆ 闭矩形 (Ioo ⊆ Icc 逐分量) ⟹ x ∈ 闭矩形
    have hxcb : x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
      exact ⟨Set.Ioo_subset_Icc_self hxr.1, Set.Ioo_subset_Icc_self hxr.2⟩
    have hx1 : x ≠ 1 := by
      exact (Set.mem_compl_singleton_iff.mp (hR1 hxcb))
    have hxana : AnalyticAt ℂ riemannZeta x :=
      analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds
        (by simpa [Set.mem_compl_singleton_iff] using hx1))
    have hz0 : riemannZeta x ≠ 0 := hne x hxcb
    exact ((hxana.deriv).div hxana hz0).differentiableAt

end RiemannUnifiedObservation
