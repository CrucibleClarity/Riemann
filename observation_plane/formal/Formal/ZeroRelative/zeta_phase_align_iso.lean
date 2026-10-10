import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.Discrete

/-!
# T6d: 相位对齐 — 无零点区间上 2·Δθ_ζ = Δθ_χ (预言/召唤的对称映射)

相位调制存在映射相位关系: u² = χ (T5, 精确等式, u = ζ/|ζ|)。
在无零点区间 [0,T] 上 u 连续非零, 经覆盖映射 exp 提升为 θ_ζ (uLift);
χ 的连续提升为 θ_χ (thetaLift)。由 exp(2θ_ζ) = u² = χ = exp(θ_χ):
    f = 2θ_ζ - θ_χ 的像 ⊆ expKernel = exp⁻¹{1} (离散)
    f 连续 ⟹ f 常数 (IsPreconnected.constant) ⟹
    **2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0)** (端点差)
这是"召唤"的对称映射: 起点 (显式 χ 相位) 与终点 (θ_ζ 端点差) 之间
的映射相位关系直接锁定, 不需要迭代逼近。翻转 (跨零点) 是 2π 整数层
差, 见 T6c 的计数结构。

隔离文件 (mathlib-only, 自包含: T5 及其依赖一并复制)。 
English: χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): functional-equation multiplier (explicit phase). -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 
English: χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): functional-equation multiplier (explicit phase). -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

-- arg(2π) ≠ π (conj_cpow 的条件: 底数不在负实轴)
private lemma arg_two_pi_ne_pi : ((2 * ↑Real.pi : ℂ).arg) ≠ Real.pi := by
  have h0 : (2 * ↑Real.pi : ℂ).arg = 0 := by
    have h0' : ((2 * Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by positivity)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

-- conj 穿透 cpow (2π 底数, 正实数)
private lemma conj_two_pi_cpow (z : ℂ) :
    (starRingEnd ℂ) ((2 * ↑Real.pi : ℂ) ^ z) = (2 * ↑Real.pi : ℂ) ^ ((starRingEnd ℂ) z : ℂ) := by
  have h := Complex.conj_cpow (2 * ↑Real.pi : ℂ) z arg_two_pi_ne_pi
  have hc : (starRingEnd ℂ) (2 * ↑Real.pi : ℂ) = 2 * ↑Real.pi := by
    have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hcast]
    exact Complex.conj_ofReal (2 * Real.pi)
  rw [hc] at h
  have h' := congrArg (starRingEnd ℂ) h.symm
  simpa using h'.symm

/-- ζ(s) = χ(s)·conj ζ(s), s = 1/2+it (函数方程 + mathlib 全域共轭)。 
English: ζ(s) = χ(s)·conj ζ(s), s = 1/2+it (functional equation + mathlib global conjugation). -/
theorem zeta_eq_chi_mul_conj_on_line (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) *
          (starRingEnd ℂ) (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  have hs_int : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = (-(n : ℂ)).re := by rw [hn]
    rw [hre] at this
    have hnre : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [hnre] at this
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = 1 := by rw [h]; simp
    rw [hre] at this
    norm_num at this
  have hfe := riemannZeta_one_sub (s := s) hs_int hs1
  rw [h1s] at hfe
  rw [riemannZeta_conj s] at hfe
  have hfe' := congrArg (starRingEnd ℂ) hfe
  have hfe'' : riemannZeta s = 2 * (2 * ↑Real.pi) ^ (-(starRingEnd ℂ) s) *
      Complex.Gamma ((starRingEnd ℂ) s) * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) *
      riemannZeta ((starRingEnd ℂ) s) := by
    have h2c : (starRingEnd ℂ) 2 = 2 := by exact Complex.conj_ofReal 2
    simpa [h2c, ← Complex.Gamma_conj, ← Complex.cos_conj, ← riemannZeta_conj, conj_two_pi_cpow]
      using hfe'
  rw [← h1s] at hfe''
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe''
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [← Complex.cos_sub_pi_div_two]
    have harg : ↑Real.pi * (1 - s) / 2 = -((↑Real.pi * s / 2) - ↑Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  rw [hcos] at hfe''
  have hzeta_arg : riemannZeta (1 - s) = riemannZeta ((starRingEnd ℂ) s) := by rw [h1s]
  rw [hzeta_arg] at hfe''
  rw [riemannZeta_conj s] at hfe''
  dsimp [s] at hfe''
  exact hfe''

/-- u² = χ: u(t) = ζ(s)/|ζ(s)| 满足 u² = χ(s) (s = 1/2+it)。
    ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1)。
    u 是 χ 的连续平方根 — 相位调制的映射相位关系。 
English: u² = χ: u(t) = ζ(s)/|ζ(s)| satisfies u² = χ(s) (s = 1/2+it). ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1). u is a continuous square root of χ — the mapped-phase relation of phase modulation. -/
theorem zeta_unit_sq_eq_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) ^ 2
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := riemannZeta s / ‖riemannZeta s‖
  have hmain := zeta_eq_chi_mul_conj_on_line t
  have h2 : (‖riemannZeta s‖ : ℂ) ^ 2 =
      2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
        (starRingEnd ℂ) (riemannZeta s) := by
    calc
      (‖riemannZeta s‖ : ℂ) ^ 2 = (↑(‖riemannZeta s‖ ^ 2) : ℂ) := by
        exact (map_pow Complex.ofRealHom (‖riemannZeta s‖) 2).symm
      _ = (Complex.normSq (riemannZeta s) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ = riemannZeta s * (starRingEnd ℂ) (riemannZeta s) := by
        rw [← Complex.mul_conj]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s)) *
          (starRingEnd ℂ) (riemannZeta s) := by
        exact congrArg (fun x : ℂ => x * (starRingEnd ℂ) (riemannZeta s)) hmain
  have hz_norm : (‖riemannZeta s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have h1 : (1 : ℂ) = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
    calc
      1 = (‖riemannZeta s‖ : ℂ) ^ 2 / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        field_simp [hz_norm]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
            (starRingEnd ℂ) (riemannZeta s)) / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        rw [h2]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ)) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
        congr 1
        have hu : (starRingEnd ℂ) (riemannZeta s / (‖riemannZeta s‖ : ℂ)) =
            (starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ) := by
          rw [map_div₀]
          simp
        simpa [u] using hu
  have hu1 : u * (starRingEnd ℂ) u = 1 := by
    have hnorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div]
      have hn : ‖(‖riemannZeta s‖ : ℂ)‖ = ‖riemannZeta s‖ := by
        calc
          ‖(‖riemannZeta s‖ : ℂ)‖ = |‖riemannZeta s‖| :=
            RCLike.norm_ofReal (‖riemannZeta s‖)
          _ = ‖riemannZeta s‖ := abs_of_nonneg (norm_nonneg _)
      rw [hn]
      have hz_norm_r : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp [hz_norm_r]
    rw [Complex.mul_conj]
    have hnsq : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
    rw [hnsq, hnorm]
    norm_num
  have hu2 : u ^ 2 = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) := by
    have hu1' : (starRingEnd ℂ) u * u = 1 := by rw [← hu1]; ring
    calc
      u ^ 2 = u ^ 2 * ((starRingEnd ℂ) u * u) := by
        rw [hu1']
        ring
      _ = u ^ 2 * (u * (starRingEnd ℂ) u) := by
        ring
      _ = (u * (starRingEnd ℂ) u) * u ^ 2 := by
        ring
      _ = u ^ 2 := by
        rw [hu1]
        ring
      _ = (u ^ 2) * 1 := by ring
      _ = (u ^ 2) * (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2) := by
        rw [← h1]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (u * (starRingEnd ℂ) u) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * 1 := by
        rw [hu1]
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) := by
        ring
  dsimp [u, s] at hu2
  exact hu2

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
English: Continuous argument lift of χ: exp(θ(s)) = χ(1/2 + T·s·i), θ 0 = y₀. -/
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

/-- u 沿临界线的路径 (无零点区间 [0,T] 上 ζ ≠ 0): 基空间 ℂ\{0} 值, 连续。 
English: u path along the critical line (ζ ≠ 0 on zero-free interval [0,T]): values in base space ℂ\{0}, continuous. -/
def uPath (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
      ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖,
    by
      exact div_ne_zero (hz s)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s)))⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hzeta : Continuous (fun s : ℝ => riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact differentiableOn_riemannZeta.continuousOn.comp hsfun.continuousOn
        (by
          intro s hs h1
          have h1' : (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I = 1 := h1
          have hre : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 := by
            rw [h1']
            simp
          have hre' : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by
            simp
          rw [hre'] at hre
          norm_num at hre)
    have hnorm : Continuous (fun s : ℝ => (‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖ : ℂ)) := by
      have hc : Continuous (fun s : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) :=
        hzeta.norm
      exact continuous_ofReal.comp hc
    have hunitOn : ContinuousOn (fun s : ℝ =>
        riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) (Set.Icc 0 1) := by
      refine hzeta.continuousOn.div hnorm.continuousOn ?_
      intro s hs
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz ⟨s, hs⟩))
    have hunit : Continuous (fun s : unitInterval =>
        riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖) :=
      hunitOn.restrict
    exact Continuous.subtype_mk hunit
      (fun s => div_ne_zero (hz s) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s))))

/-- u 的提升起点: y₀ = log u(0)。 
English: u's lift basepoint: y₀ = log u(0). -/
noncomputable def uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : ℂ :=
  Complex.log ((uPath T hz 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    Complex.exp (uLift0 T hz) = (uPath T hz 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [uLift0]
  exact Complex.exp_log (uPath T hz 0).2

/-- liftPath 的起点条件: γ 0 = p y₀。 
English: Starting-point condition for liftPath: γ 0 = p y₀. -/
private lemma uLift_γ0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uPath T hz 0 = (⟨Complex.exp (uLift0 T hz), Complex.exp_ne_zero (uLift0 T hz)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_uLift0 T hz).symm

/-- u 的连续幅角提升: exp(θ_ζ(s)) = u(s)。 
English: Continuous argument lift of u: exp(θ_ζ(s)) = u(s). -/
noncomputable def uLift (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- 提升性质: exp(θ_ζ(s)) = ζ/‖ζ‖ (1/2 + T·s·i)。 
English: Lifting property: exp(θ_ζ(s)) = ζ/‖ζ‖ (1/2 + T·s·i). -/
lemma uLift_lifts (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (uLift T hz s) =
      riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖ := by
  have h := (isCoveringMap_exp.liftPath_lifts (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [uLift]
  simpa [uPath] using hs

/-- 提升起点: θ_ζ(0) = y₀。 
English: Lift basepoint: θ_ζ(0) = y₀. -/
lemma uLift_zero (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uLift T hz 0 = uLift0 T hz := by
  exact isCoveringMap_exp.liftPath_zero (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- exp 的核: exp z = 1 的点集 (离散, 2πiℤ)。 
English: Kernel of exp: the set of points with exp z = 1 (discrete, 2πiℤ). -/
def expKernel : Set ℂ := {z | Complex.exp z = 1}

/-- expKernel = 2πiℤ: exp z = 1 ⟺ ∃ n : ℤ, z = n·2πi。 
English: expKernel = 2πiℤ: exp z = 1 ⟺ ∃ n : ℤ, z = n·2πi. -/
lemma expKernel_mem_iff (z : ℂ) :
    z ∈ expKernel ↔ ∃ n : ℤ, z = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rw [expKernel]
  constructor
  · intro hz
    have he : Complex.exp z = Complex.exp 0 := by simpa using hz
    rcases (exp_eq_exp_iff_exists_int.mp he) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using hn
  · rintro ⟨n, rfl⟩
    change Complex.exp (n * (2 * ↑Real.pi * Complex.I)) = 1
    rw [← Complex.exp_zero, exp_eq_exp_iff_exists_int]
    exact ⟨n, by ring⟩

/-- expKernel 中不同点距离 ≥ 2π (2πiℤ 的网格间距)。 
English: Distinct points of expKernel have distance ≥ 2π (lattice spacing of 2πiℤ). -/
lemma expKernel_dist_ge_two_pi {z w : ℂ} (hz : z ∈ expKernel) (hw : w ∈ expKernel)
    (hzw : z ≠ w) : 2 * Real.pi ≤ ‖z - w‖ := by
  rcases (expKernel_mem_iff z).1 hz with ⟨n, rfl⟩
  rcases (expKernel_mem_iff w).1 hw with ⟨m, rfl⟩
  have hn0 : n ≠ m := by
    intro hnm
    apply hzw
    rw [hnm]
  have hnm1 : (1 : ℝ) ≤ |(n - m : ℤ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hn0))
  calc
    2 * Real.pi ≤ |((n - m : ℤ) : ℝ)| * (2 * Real.pi) := by
      have hnm1' : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
        simpa [Int.cast_abs] using hnm1
      nlinarith [hnm1', Real.pi_pos]
    _ = ‖((n - m : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      rw [Complex.norm_mul]
      have hnorm : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
        rw [show (2 * ↑Real.pi * Complex.I : ℂ) = (2 * ↑Real.pi : ℂ) * Complex.I by ring]
        rw [Complex.norm_mul]
        have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
        rw [hcast]
        have hn2 : ‖(↑(2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
          exact (RCLike.norm_ofReal (2 * Real.pi)).trans
            (abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)))
        rw [hn2, Complex.norm_I]
        ring
      rw [Complex.norm_intCast, hnorm]
    _ = ‖(n : ℂ) * (2 * ↑Real.pi * Complex.I) - (m : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      congr 1
      rw [← sub_mul]
      congr 1
      simp

/-- expKernel 的诱导拓扑离散 (每点孤立: 间距 2π > 半径 π 的开球)。 
English: Induced topology of expKernel is discrete (each point isolated: spacing 2π > open ball of radius π). -/
instance expKernel_discrete : DiscreteTopology {z : ℂ // z ∈ expKernel} := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  -- {z} = ball z.1 π ∩ expKernel (诱导拓扑的开集)
  refine ⟨Metric.ball (z : ℂ) Real.pi, Metric.isOpen_ball, ?_⟩
  apply Set.ext
  intro w
  change w ∈ Subtype.val ⁻¹' Metric.ball (z.1 : ℂ) Real.pi ↔ w = z
  constructor
  · intro hw
    apply Subtype.ext
    by_contra hne
    have hd : 2 * Real.pi ≤ ‖w.1 - z.1‖ :=
      expKernel_dist_ge_two_pi w.2 z.2 hne
    have hlt : ‖w.1 - z.1‖ < Real.pi := by
      rw [← dist_eq_norm]
      exact hw
    nlinarith [hd, hlt, Real.pi_pos]
  · intro hw
    rw [hw]
    have hself : z.1 ∈ Metric.ball (z.1 : ℂ) Real.pi :=
      Metric.mem_ball_self Real.pi_pos
    simpa [dist_eq_norm] using hself

/-- **相位对齐 (预言/召唤的对称映射)**: 无零点区间 [0,T] 上,
    u² = χ (T5) ⟹ exp(2θ_ζ) = exp(θ_χ) ⟹ 2θ_ζ - θ_χ ∈ expKernel 常数 ⟹
    2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0)。
    起点 (显式 χ 相位) 与终点 (θ_ζ 端点差) 之间的映射相位关系直接锁定,
    不需要迭代逼近。 
English: **Phase alignment (symmetric map of prophecy/summoning)**: on a zero-free interval [0,T], u² = χ (T5) ⟹ exp(2θ_ζ) = exp(θ_χ) ⟹ 2θ_ζ - θ_χ ∈ expKernel constant ⟹ 2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0). The mapped-phase relation between basepoint (explicit χ phase) and endpoint (θ_ζ endpoint difference) is locked directly; no iterative approximation. -/
theorem phase_align_two_zeta_lift_eq_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    2 * (uLift T hz 1 - uLift T hz 0) = thetaLift T 1 - thetaLift T 0 := by
  let f : unitInterval → ℂ := fun s => 2 * uLift T hz s - thetaLift T s
  have hk : ∀ s : unitInterval, f s ∈ expKernel := by
    intro s
    rw [expKernel]
    dsimp [f]
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    rw [zeta_unit_sq_eq_chi (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  let f' : unitInterval → {z : ℂ // z ∈ expKernel} := fun s => ⟨f s, hk s⟩
  have hf' : Continuous f' := by
    have hf : Continuous f := by
      dsimp [f]
      exact (continuous_const.mul (uLift T hz).continuous).sub (thetaLift T).continuous
    exact Continuous.subtype_mk hf (fun s => hk s)
  have hc : f' 0 = f' 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hf'.continuousOn (by trivial) (by trivial)
  have hf01 : f 0 = f 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  dsimp [f] at hf01
  -- hf01 : 2·u0 - t0 = 2·u1 - t1 ⟹ 目标 2(u1-u0) = t1-t0
  calc
    2 * (uLift T hz 1 - uLift T hz 0)
        = 2 * uLift T hz 1 - 2 * uLift T hz 0 := by ring
    _ = (2 * uLift T hz 1 - thetaLift T 1) + (thetaLift T 1 - 2 * uLift T hz 0) := by ring
    _ = (2 * uLift T hz 0 - thetaLift T 0) + (thetaLift T 1 - 2 * uLift T hz 0) := by
      rw [← hf01]
    _ = thetaLift T 1 - thetaLift T 0 := by ring

end RiemannUnifiedObservation
