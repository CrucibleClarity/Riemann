import Formal.ZeroRelative.EtaPhaseSplit
import Formal.ZeroRelative.EtaFactorPhase
import Formal.ZeroRelative.zeta_chi_explicit_iso

noncomputable section

namespace EtaFactorWinding

open Complex

open EtaPhaseSplit

open RiemannUnifiedObservation

open PrimeCircle.RiemannUnifiedObservation.RiemannUnifiedObservation.RiemannUnifiedObservation

/-! ## 层 5d: 因子圈数 (周期 P = 2π/ln 2 的闭合与提升差)

5d-1 (EtaFactorPhase.factor_line_period): 因子沿临界线周期 P。
本文件(5d-2a/2b): 因子单位化路径闭合 ⟹ 因子提升差 ∈ expKernel (= 2πiℤ) —
圈数 = 整数层的代数骨架; 剩余核心: 钉值 (Δθ_因子 = −2π, 大圆绕一圈) —
需要分支常数 (半平面/象限 界 + 离散核常数), 下一层。
-/

/-- **因子沿临界线周期 P 的单位化路径闭合**: factorPath P 1 = factorPath P 0. -/
lemma factorPath_period_closed :
    (EtaPhaseSplit.factorPath (2 * Real.pi / Real.log 2) 1 : {z : ℂ // z ≠ 0}) =
      (EtaPhaseSplit.factorPath (2 * Real.pi / Real.log 2) 0 : {z : ℂ // z ≠ 0}) := by
  apply Subtype.ext
  change ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2 * 1 : ℝ) : ℂ) * Complex.I))) /
      ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2 * 1 : ℝ) : ℂ) * Complex.I)))‖ : ℂ) =
    ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2 * 0 : ℝ) : ℂ) * Complex.I))) /
      ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2 * 0 : ℝ) : ℂ) * Complex.I)))‖ : ℂ)
  simp only [mul_one, mul_zero]
  have hp := EtaFactorPhase.factor_line_period (0 : ℝ)
  have hp' : (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I))) =
      (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (0 : ℂ) * Complex.I))) := by
    simpa using hp
  exact congrArg (fun x : ℂ => x / ‖x‖) hp'

/-- **因子提升差 ∈ expKernel**: 周期闭合 ⟹ exp(Δθ_因子) = exp(L1)/exp(L0) = 1
    ⟹ Δθ_因子 = 2πi·ℤ (圈数 = 整数层). -/
lemma factorLift_period_diff_kernel :
    EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 -
      EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0 ∈ expKernel := by
  rw [expKernel]
  change Complex.exp (EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 -
      EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0) = 1
  rw [Complex.exp_sub]
  rw [EtaPhaseSplit.factorLift_lifts, EtaPhaseSplit.factorLift_lifts]
  rw [factorPath_period_closed]
  exact div_self (EtaPhaseSplit.factorPath (2 * Real.pi / Real.log 2) 0).2

/-! ## 层 5d-2c 核心 (钉值通用件): 右半平面无绕

分支常数: p 单位化路径 (值 ≠ 0, Re > 0), σ 连续提升 (exp σ = p), 路径闭合 ⟹
F(s) = σ(s) − log(p(s)): 连续 (log 在 slitPlane 连续 = Re>0 域) + ∈ expKernel
(exp 恒等 ⟹ exp 差 = 1) ⟹ IsPreconnected.constant ⟹ F(0) = F(1) ⟹
σ 差 = log 差 = 0 (闭合)。签名: 右半平面无绕 ⟹ 提升差 = 0 — 小圆圈数 = 0 的核心。
-/

/-- **右半平面无绕 (通用核心)**: 单位化路径 p (连续, 值 ≠ 0, 右半平面) 的连续提升 σ
    (exp σ = p) 且路径闭合 (p 1 = p 0) ⟹ σ 1 = σ 0. -/
theorem lift_diff_zero_of_re_pos_path (p : C(unitInterval, {z : ℂ // z ≠ 0}))
    (σ : C(unitInterval, ℂ))
    (hσ : ∀ s, Complex.exp (σ s) = (p s : {z : ℂ // z ≠ 0}).1)
    (hclosed : p 1 = p 0)
    (hre : ∀ s, 0 < ((p s : {z : ℂ // z ≠ 0}).1).re) :
    σ 1 - σ 0 = 0 := by
  let F : unitInterval → {z : ℂ // z ∈ expKernel} := fun s =>
    ⟨σ s - Complex.log ((p s : {z : ℂ // z ≠ 0}).1), by
      change Complex.exp (σ s - Complex.log ((p s : {z : ℂ // z ≠ 0}).1)) = 1
      rw [Complex.exp_sub]
      rw [hσ s]
      rw [Complex.exp_log (p s).2]
      exact div_self (p s).2⟩
  have hF : Continuous F := by
    have hc1 : Continuous (fun s : unitInterval => σ s) := σ.continuous
    have hc2 : Continuous (fun s : unitInterval => Complex.log ((p s : {z : ℂ // z ≠ 0}).1)) := by
      rw [continuous_iff_continuousAt]
      intro s
      have hpc : Continuous (fun s : unitInterval => ((p s : {z : ℂ // z ≠ 0}).1 : ℂ)) := by
        simpa using p.continuous.subtype_val
      exact (ContinuousAt.clog hpc.continuousAt
        (by
          rw [Complex.slitPlane]
          exact Or.inl (hre s)))
    exact Continuous.subtype_mk (hc1.sub hc2) (fun s => (F s).2)
  have hc : F 0 = F 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hF.continuousOn (by trivial) (by trivial)
  have hF01 : σ 1 - Complex.log ((p 1 : {z : ℂ // z ≠ 0}).1) =
      σ 0 - Complex.log ((p 0 : {z : ℂ // z ≠ 0}).1) := by
    have := congrArg Subtype.val hc
    simpa [F] using this.symm
  have hlg : Complex.log ((p 1 : {z : ℂ // z ≠ 0}).1) = Complex.log ((p 0 : {z : ℂ // z ≠ 0}).1) := by
    rw [hclosed]
  have heq : σ 1 = σ 0 := by
    rw [hlg] at hF01
    exact sub_left_inj.mp hF01
  rw [heq, sub_self]

/-- 小圆: g(φ) = 1 − e^{iφ}/√2 (φ = t·ln2). -/
def gFun (t : ℝ) : ℂ :=
  1 - Complex.exp (((t * Real.log 2 : ℝ) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

/-- 小圆非零: Re g > 0 (EtaFactorPhase.g_re_pos). -/
lemma gFun_ne_zero (t : ℝ) : gFun t ≠ 0 := by
  have h : 0 < (gFun t).re := by
    simpa [gFun] using EtaFactorPhase.g_re_pos t
  intro hz
  rw [hz] at h
  norm_num at h

/-- 小圆周期律: g(t + P) = g(t) (P = 2π/ln2). -/
lemma gFun_period (t : ℝ) :
    gFun (t + 2 * Real.pi / Real.log 2) = gFun t := by
  rw [gFun, gFun]
  have hln : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  have hstep : (t + 2 * Real.pi / Real.log 2) * Real.log 2 = t * Real.log 2 + 2 * Real.pi := by
    rw [add_mul, div_mul_cancel₀ (2 * Real.pi) hln]
  rw [hstep]
  have hargs : (((t * Real.log 2 + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (((t * Real.log 2 : ℝ) : ℂ) * Complex.I + (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.ofReal_add]
    ring
  rw [hargs, Complex.exp_add]
  have hon : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos]
    rw [← Complex.ofReal_sin]
    rw [Real.cos_two_pi, Real.sin_two_pi, Complex.ofReal_zero, zero_mul, add_zero,
      Complex.ofReal_one]
  rw [hon, mul_one]

/-- 小圆单位化路径: g/‖g‖ — 连续, 值 ≠ 0 (gFun_ne_zero). -/
def gPath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨(gFun (T * s.1) / ‖gFun (T * s.1)‖ : ℂ),
    div_ne_zero (gFun_ne_zero (T * s.1))
      (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (gFun_ne_zero (T * s.1))))⟩
  continuous_toFun := by
    have hgfun : Continuous (fun t : ℝ => gFun (T * t)) := by
      dsimp [gFun]
      fun_prop
    have hdiv : Continuous (fun t : ℝ => gFun (T * t) / ‖gFun (T * t)‖) :=
      hgfun.div (continuous_ofReal.comp hgfun.norm) (fun t =>
        ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (gFun_ne_zero (T * t))))
    exact Continuous.subtype_mk (hdiv.comp continuous_subtype_val)
      (fun s => div_ne_zero (gFun_ne_zero (T * s.1))
        (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (gFun_ne_zero (T * s.1)))))

/-- 小圆单位化值右半平面: Re(g/‖g‖) > 0 (gFun_re_pos + ‖g‖ > 0). -/
lemma gPath_re_pos (T : ℝ) (s : unitInterval) :
    0 < (((gPath T s : {z : ℂ // z ≠ 0}).1).re) := by
  have hg : 0 < (gFun (T * s.1)).re := by
    simpa [gFun] using EtaFactorPhase.g_re_pos (T * s.1)
  have hn : 0 < ‖gFun (T * s.1)‖ := norm_pos_iff.mpr (gFun_ne_zero (T * s.1))
  -- (a / ↑‖a‖).re = a.re·‖a‖⁻¹ (change 穿 C 结构 + mul_re + ofReal_inv + 0 消去):
  change 0 < (gFun (T * s.1) / ‖gFun (T * s.1)‖ : ℂ).re
  rw [div_eq_mul_inv]
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  -- 目标 0 < a.re·‖a‖⁻¹ − a.im·0:
  rw [mul_zero, sub_zero]
  exact div_pos hg hn

/-- 小圆单位化路径周期闭合: gPath P 1 = gPath P 0 (gFun_period). -/
lemma gPath_period_closed :
    (gPath (2 * Real.pi / Real.log 2) 1 : {z : ℂ // z ≠ 0}) =
      (gPath (2 * Real.pi / Real.log 2) 0 : {z : ℂ // z ≠ 0}) := by
  apply Subtype.ext
  change (gFun ((2 * Real.pi / Real.log 2) * 1) / ‖gFun ((2 * Real.pi / Real.log 2) * 1)‖ : ℂ) =
    (gFun ((2 * Real.pi / Real.log 2) * 0) / ‖gFun ((2 * Real.pi / Real.log 2) * 0)‖ : ℂ)
  simp only [mul_one, mul_zero]
  have hp := gFun_period (0 : ℝ)
  have hp' : gFun (2 * Real.pi / Real.log 2) = gFun 0 := by simpa using hp
  simpa using (congrArg (fun x : ℂ => x / ‖x‖) hp')

/-- 小圆单位化的提升起点. -/
noncomputable def gLift0 (T : ℝ) : ℂ :=
  Complex.log ((gPath T 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_gLift0 (T : ℝ) :
    Complex.exp (gLift0 T) = (gPath T 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [gLift0]
  exact Complex.exp_log (gPath T 0).2

private lemma gLift_γ0 (T : ℝ) :
    gPath T 0 = (⟨Complex.exp (gLift0 T), Complex.exp_ne_zero (gLift0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_gLift0 T).symm

/-- 小圆的连续幅角提升: exp(θ_g(s)) = g/‖g‖. -/
noncomputable def gLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (gPath T) (gLift0 T) (gLift_γ0 T)

lemma gLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (gLift T s) = (gPath T s : {z : ℂ // z ≠ 0}).1 := by
  have h := (isCoveringMap_exp.liftPath_lifts (gPath T) (gLift0 T) (gLift_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [gLift]
  simpa using hs

/-- **小圆提升差 = 0**: 右半平面 (gPath_re_pos) + 闭合 (gPath_period_closed) + 提升
    ⟹ lift_diff_zero_of_re_pos_path 应用 ⟹ 小圆圈数 = 0. -/
lemma gLift_diff_zero :
    gLift (2 * Real.pi / Real.log 2) 1 - gLift (2 * Real.pi / Real.log 2) 0 = 0 :=
  lift_diff_zero_of_re_pos_path (gPath (2 * Real.pi / Real.log 2))
    (gLift (2 * Real.pi / Real.log 2))
    (gLift_lifts (2 * Real.pi / Real.log 2)) gPath_period_closed
    (gPath_re_pos (2 * Real.pi / Real.log 2))


/-- 大圆 (归一化): circle(φ) = −e^{−iφ} (φ = t·ln2, 单位圆). -/
def circleFun (t : ℝ) : ℂ := -Complex.exp ((-(t * Real.log 2 : ℝ) : ℂ) * Complex.I)

/-- 大圆单位化路径 (值已是单位圆, ‖·‖ = 1 ≠ 0). -/
def circlePath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨circleFun (T * s.1), by
    have hnorm : ‖circleFun (T * s.1)‖ = 1 := by
      rw [circleFun]
      rw [norm_neg]
      rw [Complex.norm_exp]
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, neg_zero, zero_mul, sub_zero]
      rw [Real.exp_zero]
    exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)⟩
  continuous_toFun := by
    have hg : Continuous (fun t : ℝ => circleFun (T * t)) := by
      dsimp [circleFun]
      fun_prop
    have hi : ∀ s : unitInterval, circleFun (T * s.1) ≠ 0 := by
      intro s
      have hnorm : ‖circleFun (T * s.1)‖ = 1 := by
        rw [circleFun]
        rw [norm_neg]
        rw [Complex.norm_exp]
        rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, neg_zero, zero_mul, sub_zero]
        rw [Real.exp_zero]
      exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
    exact Continuous.subtype_mk (hg.comp continuous_subtype_val) (fun s => hi s)

/-- 大圆连续提升: λ(s) = i·(π − T·s·ln2) — exp λ = −e^{−iφ} = circle/|circle|. -/
noncomputable def circleLift (T : ℝ) : C(unitInterval, ℂ) where
  toFun s := (((Real.pi - (T * s.1 * Real.log 2 : ℝ) : ℝ) : ℂ) * Complex.I : ℂ)
  continuous_toFun := by
    have hc : Continuous (fun t : ℝ => (((Real.pi - (T * t * Real.log 2 : ℝ) : ℝ) : ℂ) * Complex.I : ℂ)) := by
      fun_prop
    exact hc.comp continuous_subtype_val

/-- 提升恒等: exp(i(π−φ)) = −e^{−iφ}. -/
lemma circleLift_exp (T : ℝ) (s : unitInterval) :
    Complex.exp (circleLift T s) = circleFun (T * s.1) := by
  dsimp [circleLift, circleFun]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_sin]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_neg]
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.zero_re,
      Complex.zero_im, Complex.neg_im, sub_zero, zero_sub, add_zero, zero_add, mul_zero,
      mul_one, neg_zero, sub_eq_add_neg]
    rw [← sub_eq_add_neg]
    rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]
    ring
  · simp only [Complex.mul_im, Complex.add_im, Complex.neg_im, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im, Complex.zero_re,
      Complex.zero_im, sub_zero, zero_sub, add_zero, zero_add, mul_zero, mul_one, neg_zero,
      sub_eq_add_neg]
    rw [← sub_eq_add_neg]
    rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]
    ring

/-- 大圆端点差: λ(1) − λ(0) = −2πi (P·ln2 = 2π). -/
lemma circleLift_diff :
    circleLift (2 * Real.pi / Real.log 2) 1 - circleLift (2 * Real.pi / Real.log 2) 0 =
      ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
  dsimp [circleLift]
  have hln : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  let P : ℝ := 2 * Real.pi / Real.log 2
  have hp : P * 1 * Real.log 2 = 2 * Real.pi := by
    rw [show P * 1 * Real.log 2 = P * Real.log 2 by ring]
    rw [show P * Real.log 2 = 2 * Real.pi by
      dsimp [P]
      exact div_mul_cancel₀ (2 * Real.pi) hln]
  rw [hp, mul_zero, zero_mul]
  rw [show Real.pi - 2 * Real.pi = -(Real.pi) by ring]
  rw [show Real.pi - 0 = Real.pi by ring]
  rw [Complex.ofReal_neg]
  rw [Complex.ofReal_mul]
  rw [sub_eq_add_neg, neg_mul, ← neg_add, ← two_mul, ← mul_assoc]
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  rw [neg_mul]


/-- 大圆归一化: (−√2·e^{−iφ})/‖·‖ = −e^{−iφ} (‖−√2·e‖ = √2). -/
lemma circle_ratio (φ : ℝ) :
    ((-(Real.sqrt 2 : ℂ) * Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I)) /
      ((‖(-(Real.sqrt 2 : ℂ) * Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I))‖ : ℂ))) =
      (-Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I)) := by
  have h1 : ‖(((Real.sqrt 2 : ℝ) : ℂ))‖ = Real.sqrt 2 := by
    have hs : Complex.normSq ((Real.sqrt 2 : ℝ) : ℂ) = Real.sqrt 2 * Real.sqrt 2 := by
      rw [Complex.normSq_ofReal]
    have hs2 : ‖(((Real.sqrt 2 : ℝ) : ℂ))‖ ^ 2 = (Real.sqrt 2 : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq] at hs
      simpa [pow_two] using hs
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs2 with h | h
    · exact h
    · have : ‖(((Real.sqrt 2 : ℝ) : ℂ))‖ < 0 := by
        rw [h]
        exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
      exact False.elim (not_lt_of_ge (norm_nonneg _) this)
  have hnorm : ‖(-(Real.sqrt 2 : ℂ)) * Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I)‖ = Real.sqrt 2 := by
    rw [norm_mul]
    rw [Complex.norm_exp]
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, neg_zero, zero_mul, sub_zero]
    rw [Real.exp_zero]
    rw [norm_neg]
    rw [h1]
    rw [mul_one]
  rw [hnorm]
  have hsq : (Real.sqrt 2 : ℝ) ≠ 0 := EtaFactorPhase.sqrt2_ne
  rw [← div_mul_eq_mul_div]
  rw [neg_div]
  rw [div_self (Complex.ofReal_ne_zero.mpr hsq)]
  rw [neg_one_mul]


/-- 点级乘积恒等: factorPath P s = circlePath P s · gPath P s (f = C·g 归一化). -/
lemma factorPath_circle_g_mul (s : unitInterval) :
    (EtaPhaseSplit.factorPath (2 * Real.pi / Real.log 2) s : {z : ℂ // z ≠ 0}).1 =
      (circlePath (2 * Real.pi / Real.log 2) s : {z : ℂ // z ≠ 0}).1 *
        (gPath (2 * Real.pi / Real.log 2) s : {z : ℂ // z ≠ 0}).1 := by
  let P : ℝ := 2 * Real.pi / Real.log 2
  let C : ℂ := -(Real.sqrt 2 : ℂ) * Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I)
  let gv : ℂ := 1 - Complex.exp (((P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr EtaFactorPhase.sqrt2_ne))
      (Complex.exp_ne_zero _)
  have hg : gv ≠ 0 := by
    dsimp [gv]
    exact gFun_ne_zero (P * s.1)
  have hunit := EtaPhaseSplit.unit_split_of_mul C gv hC hg
  calc
    (EtaPhaseSplit.factorPath P s : {z : ℂ // z ≠ 0}).1
        = (1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I)) /
            ‖1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I)‖ := by
          change (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((P * s.1 : ℝ) : ℂ) * Complex.I))) /
              ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((P * s.1 : ℝ) : ℂ) * Complex.I)))‖ =
            (1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I)) /
              ‖1 - (Real.sqrt 2 : ℂ) * Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I)‖
          exact congrArg (fun x : ℂ => x / ‖x‖) (EtaFactorPhase.factor_line_form (P * s.1))
    _ = (C * gv) / ‖C * gv‖ := by
      dsimp [C, gv]
      exact congrArg (fun x : ℂ => x / ‖x‖) (EtaFactorPhase.factor_line_g_split (P * s.1))
    _ = (C / (‖C‖ : ℂ)) * (gv / (‖gv‖ : ℂ)) := hunit
    _ = (circlePath P s : {z : ℂ // z ≠ 0}).1 * (gPath P s : {z : ℂ // z ≠ 0}).1 := by
      have hcval : (circlePath P s : {z : ℂ // z ≠ 0}).1 =
          -Complex.exp ((-(P * s.1 * Real.log 2 : ℝ) : ℂ) * Complex.I) := by
        dsimp [P, circlePath, circleFun]
      have hgval : (gv / (‖gv‖ : ℂ)) = (gPath P s : {z : ℂ // z ≠ 0}).1 := by
        dsimp [gv, P]
        change gFun ((2 * Real.pi / Real.log 2) * s.1) / (‖gFun ((2 * Real.pi / Real.log 2) * s.1)‖ : ℂ) =
          (gPath (2 * Real.pi / Real.log 2) s : {z : ℂ // z ≠ 0}).1
        rfl
      rw [hcval, ← circle_ratio, hgval]

/-- 提升差可加: Δθ_因子 = Δθ_大圆 + Δθ_小圆 (F = factorLift − circleLift − gLift 连续+expKernel). -/
theorem factorLift_endpoint_split :
    EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 -
      EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0 =
      (circleLift (2 * Real.pi / Real.log 2) 1 - circleLift (2 * Real.pi / Real.log 2) 0) +
        (gLift (2 * Real.pi / Real.log 2) 1 - gLift (2 * Real.pi / Real.log 2) 0) := by
  let P : ℝ := 2 * Real.pi / Real.log 2
  let F : unitInterval → {z : ℂ // z ∈ expKernel} := fun s =>
    ⟨EtaPhaseSplit.factorLift P s - (circleLift P s + gLift P s), by
      change Complex.exp (EtaPhaseSplit.factorLift P s - (circleLift P s + gLift P s)) = 1
      rw [Complex.exp_sub]
      rw [Complex.exp_add]
      rw [EtaPhaseSplit.factorLift_lifts]
      rw [circleLift_exp]
      rw [gLift_lifts]
      rw [factorPath_circle_g_mul s]
      exact div_self (mul_ne_zero (circlePath (2 * Real.pi / Real.log 2) s).2
        (gPath (2 * Real.pi / Real.log 2) s).2)⟩
  have hF : Continuous F := by
    have hc1 : Continuous (fun s : unitInterval => EtaPhaseSplit.factorLift P s) :=
      (EtaPhaseSplit.factorLift P).continuous
    have hc2 : Continuous (fun s : unitInterval => circleLift P s + gLift P s) :=
      (circleLift P).continuous.add (gLift P).continuous
    exact Continuous.subtype_mk (hc1.sub hc2) (fun s => (F s).2)
  have hc : F 0 = F 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hF.continuousOn (by trivial) (by trivial)
  have hF01 : EtaPhaseSplit.factorLift P 1 - (circleLift P 1 + gLift P 1) =
      EtaPhaseSplit.factorLift P 0 - (circleLift P 0 + gLift P 0) := by
    have := congrArg Subtype.val hc
    simpa [F] using this.symm
  calc
    EtaPhaseSplit.factorLift P 1 - EtaPhaseSplit.factorLift P 0
        = (EtaPhaseSplit.factorLift P 1 - (circleLift P 1 + gLift P 1)) +
            (circleLift P 1 + gLift P 1) - EtaPhaseSplit.factorLift P 0 := by ring
    _ = (EtaPhaseSplit.factorLift P 0 - (circleLift P 0 + gLift P 0)) +
            (circleLift P 1 + gLift P 1) - EtaPhaseSplit.factorLift P 0 := by
      rw [← hF01]
    _ = (circleLift P 1 - circleLift P 0) + (gLift P 1 - gLift P 0) := by ring

/-- **因子圈数 = −2π/周期**: Δθ_因子 = Δθ_大圆 + Δθ_小圆 = −2πi + 0. -/
theorem factorLift_period_diff :
    EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 -
      EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0 =
      ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
  rw [factorLift_endpoint_split]
  rw [circleLift_diff]
  rw [gLift_diff_zero]
  rw [add_zero]


/-- **层 6a: η 周期对账** — 一个因子周期 P 上: Δθ_η = −2πi + Δθ_ζ
    (端点差可加 (层 4) + 因子圈数 = −2π (层 5d)). -/
theorem eta_period_accounting (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2) * s.1 : ℝ) * Complex.I) ≠ 0) :
    etaLift (2 * Real.pi / Real.log 2) hz 1 - etaLift (2 * Real.pi / Real.log 2) hz 0 =
      ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) +
        (uLift (2 * Real.pi / Real.log 2) hz 1 - uLift (2 * Real.pi / Real.log 2) hz 0) := by
  rw [etaLift_endpoint_add]
  rw [factorLift_period_diff]


/-- 因子在 t = 0 的归一化值: f(0)/‖f(0)‖ = −1 (f(0) = 1−√2 < 0). -/
lemma factor_zero_value :
    (EtaPhaseSplit.factorPath (2 * Real.pi / Real.log 2) 0 : {z : ℂ // z ≠ 0}).1 = -1 := by
  have hf := EtaFactorPhase.factor_line_re_im (0 : ℝ)
  have hc : Real.cos (0 * Real.log 2) = 1 := by norm_num
  have hs : Real.sin (0 * Real.log 2) = 0 := by norm_num
  rw [hc, hs] at hf
  change (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (((2 * Real.pi / Real.log 2) * 0 : ℝ) : ℂ) * Complex.I))) /
      ‖(1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (((2 * Real.pi / Real.log 2) * 0 : ℝ) : ℂ) * Complex.I)))‖ = -1
  simp only [mul_zero]
  rw [hf]
  simp only [mul_one, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, sub_zero]
  have hnm : ‖((1 - Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 - 1 := by
    have hsq : ‖((1 - Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (Real.sqrt 2 - 1) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hnn : 0 ≤ ‖((1 - Real.sqrt 2 : ℝ) : ℂ)‖ := norm_nonneg _
    have hlt : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    have hpp : 0 ≤ Real.sqrt 2 - 1 := le_of_lt (sub_pos.mpr hlt)
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
    · exact h
    · have : ‖((1 - Real.sqrt 2 : ℝ) : ℂ)‖ < 0 := by
        rw [h]
        exact neg_lt_zero.mpr (sub_pos.mpr hlt)
      exact False.elim (not_lt_of_ge (norm_nonneg _) this)
  rw [hnm]
  rw [show (1 : ℝ) - Real.sqrt 2 = -(Real.sqrt 2 - 1) by ring]
  rw [Complex.ofReal_neg]
  rw [neg_div]
  rw [div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr
    (by rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]; norm_num))))]

/-- 因子提升起点显式: θ_因子(0) = log(−1) = πi. -/
lemma factorLift0_period :
    EtaPhaseSplit.factorLift0 (2 * Real.pi / Real.log 2) = Real.pi * Complex.I := by
  dsimp [EtaPhaseSplit.factorLift0]
  rw [factor_zero_value]
  exact Complex.log_neg_one

/-- **因子端点显式 (层 6b)**: θ_因子(0) = πi, θ_因子(P) = −πi (四角点两垂直端点). -/
theorem factorLift_period_endpoints :
    EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0 = Real.pi * Complex.I ∧
    EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 = -(Real.pi * Complex.I) := by
  constructor
  · rw [EtaPhaseSplit.factorLift_zero]
    exact factorLift0_period
  · have h0 : EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 0 = Real.pi * Complex.I := by
      rw [EtaPhaseSplit.factorLift_zero]
      exact factorLift0_period
    have hdiff := factorLift_period_diff
    rw [h0] at hdiff
    have heq : EtaPhaseSplit.factorLift (2 * Real.pi / Real.log 2) 1 =
        ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) + Real.pi * Complex.I := by
      exact (sub_eq_iff_eq_add).mp hdiff
    rw [heq]
    rw [Complex.ofReal_mul]
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
    ring


/-- **层 6c: 黑箱转移** — 一个因子周期 P 上: Δθ_ζ = Δθ_χ/2 (u² = χ ⟹ T6d 端点对齐),
    代入 η 对账 ⟹ Δθ_η = −2πi + Δθ_χ/2 (黑箱从 ζ 侧转移到显式 χ 侧). -/
theorem eta_period_accounting_chi (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi / Real.log 2) * s.1 : ℝ) * Complex.I) ≠ 0) :
    etaLift (2 * Real.pi / Real.log 2) hz 1 - etaLift (2 * Real.pi / Real.log 2) hz 0 =
      ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) +
        ((thetaLift (2 * Real.pi / Real.log 2) 1 - thetaLift (2 * Real.pi / Real.log 2) 0) / 2) := by
  let P : ℝ := 2 * Real.pi / Real.log 2
  have hdr : uLift P hz 1 - uLift P hz 0 =
      (thetaLift P 1 - thetaLift P 0) / 2 := by
    have h2 := phase_align_two_zeta_lift_eq_chi_lift P hz
    -- 2·a = b ⟹ a = b/2:
    have := congrArg (fun x : ℂ => x / 2) h2
    -- (2a)/2 = a:
    simpa using this
  rw [eta_period_accounting]
  rw [hdr]


/-- (2π)^(s-1) 沿临界线显式: (2π)^(-1/2+it) = exp(-ln(2π)/2)·(cos(t·ln(2π)) + i·sin(t·ln(2π)))。 -/
theorem cpow_two_pi_on_line_explicit (t : ℝ) :
    ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (-Real.log (2 * Real.pi) / 2) : ℂ) * (Real.cos (t * Real.log (2 * Real.pi)) : ℂ)
        + (Real.exp (-Real.log (2 * Real.pi) / 2) : ℂ) *
          (Real.sin (t * Real.log (2 * Real.pi)) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero
    (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))]
  have hlog : Complex.log (((2 * Real.pi : ℝ) : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
    exact (Complex.ofReal_log (by positivity)).symm
  rw [hlog]
  have hdecomp : (Real.log (2 * Real.pi) : ℂ) * (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((-Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + ((t * Real.log (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring


/-- **ⓑ sin(πs/2) 幅角 (arcsin 形)**: sin(π/4 + iπt/2) 实部恒正 ⟹
    arg = arcsin(sinh(πt/2)/√(cosh²+sinh²)) — 与 tanh 形等价 (待下件). -/
theorem sin_line_arg_arcsin (t : ℝ) :
    Complex.arg (Complex.sin (↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I)) =
      Real.arcsin (Real.sinh (Real.pi / 2 * t) /
        Real.sqrt (Real.cosh (Real.pi / 2 * t) ^ 2 + Real.sinh (Real.pi / 2 * t) ^ 2)) := by
  rw [sin_pi_quarter_add_mul_I]
  have hre : 0 ≤ (Complex.sin (↑Real.pi / 4) * Complex.cosh (↑(Real.pi / 2 * t)) +
      Complex.cos (↑Real.pi / 4) * Complex.sinh (↑(Real.pi / 2 * t)) * Complex.I).re := by
    -- re = sin(π/4)·cosh(πt/2) > 0 (实部恒正):
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_div]
    rw [← Complex.ofReal_sin]
    rw [← Complex.ofReal_cosh]
    rw [← Complex.ofReal_cos]
    rw [← Complex.ofReal_sinh]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one,
      sub_zero, neg_zero]
    have hsp : 0 ≤ Real.sin (Real.pi / 4) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
        (div_lt_self Real.pi_pos (by norm_num : (1 : ℝ) < 4)))
    have hcp : 0 ≤ Real.cosh (Real.pi / 2 * t) := le_of_lt (Real.cosh_pos (Real.pi / 2 * t))
    exact mul_nonneg hsp hcp
  rw [Complex.arg_of_re_nonneg hre]
  -- 目标: arcsin(z.im/‖z‖) = arcsin(sinh/√(cosh²+sinh²)) — im/‖z‖ 计算:
  congr 1
  -- z.im = sin(π/4)·sinh(πt/2):
  rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_div]
  rw [← Complex.ofReal_sin]
  rw [← Complex.ofReal_cosh]
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_sinh]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one,
    sub_zero, neg_zero]
  -- ‖·‖² = (sin(π/4)cosh)² + (sin(π/4)sinh)²;  |sin(π/4)| = √2/2 > 0:
  have hsq : (Real.sin (Real.pi / 4)) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.sin_pi_div_four]
    rw [show (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2) ^ 2 / 2 ^ 2 by ring]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  -- cos(π/4) = sin(π/4):
  have hcos : Real.cos (Real.pi / 4) = Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  -- 分母: ‖z‖ = √(normSq z):
  have hnorm : ‖↑(Real.sin (Real.pi / 4)) * ↑(Real.cosh (Real.pi / 2 * t)) +
      ↑(Real.cos (Real.pi / 4)) * ↑(Real.sinh (Real.pi / 2 * t)) * Complex.I‖ =
    Real.sqrt ((Real.sin (Real.pi / 4) * Real.cosh (Real.pi / 2 * t)) ^ 2 +
      (Real.sin (Real.pi / 4) * Real.sinh (Real.pi / 2 * t)) ^ 2) := by
    rw [← abs_of_nonneg (norm_nonneg _)]
    rw [← Real.sqrt_sq_eq_abs]
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      mul_zero, zero_mul, zero_add, add_zero, sub_zero]
    rw [hcos]
    ring_nf
  rw [hnorm]
  rw [hcos]
  rw [show (Real.sin (Real.pi / 4) * Real.cosh (Real.pi / 2 * t)) ^ 2 +
      (Real.sin (Real.pi / 4) * Real.sinh (Real.pi / 2 * t)) ^ 2
      = (Real.sin (Real.pi / 4)) ^ 2 *
        (Real.cosh (Real.pi / 2 * t) ^ 2 + Real.sinh (Real.pi / 2 * t) ^ 2) by ring]
  rw [hsq]
  -- 分子有 s, 分母 √(s²·b) = s·√b — 用 sqrt_mul:
  rw [Real.sqrt_mul]
  · rw [← div_mul_div_comm]
    have hfac : Real.sin (Real.pi / 4) / Real.sqrt (1 / 2) = 1 := by
      rw [Real.sin_pi_div_four]
      have hs : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
        rw [Real.sqrt_div]
        rw [Real.sqrt_one]
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [hs]
      exact div_self (div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
        (by norm_num : (2 : ℝ) ≠ 0))
    rw [hfac, one_mul]
  · norm_num


end EtaFactorWinding
