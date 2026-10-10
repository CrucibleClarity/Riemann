import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# T6e: S(T) 的整数层结构 — θ_ζ - θ_χ/2 ∈ πiℤ (pat ±1 过程的 0pat 形式)

S(T) 的振荡 = 符号翻转序列: 由 T6d (2θ_ζ - θ_χ ∈ expKernel = 2πiℤ 逐点),
除以 2 得:
    θ_ζ(s) - θ_χ(s)/2 ∈ πiℤ  (逐点, 整数层)
即 S(T) = (1/(πi))·(θ_ζ - θ_χ/2) 是分段常数整数函数, 每跨零点跳 ±1 —
符号改变, 位置 (零点) 不变 = pat 正负 1 过程。翻转 = 乘 -1 = i² (i 的迭代),
整数层 = 2πi 的迭代计数。θ_χ 显式 (快路径), 整数层 = 翻转计数 — 全快路径。

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

/-- χ 沿临界线非零。 
English: χ is nonzero on the critical line. -/
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

/-- 提升起点 y₀ = log χ(1/2)。 
English: Lift basepoint y₀ = log χ(1/2). -/
noncomputable def theta0 (_T : ℝ) : ℂ :=
  Complex.log (chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I))

lemma exp_theta0 (T : ℝ) :
    Complex.exp (theta0 T) = chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I) := by
  dsimp [theta0]
  exact Complex.exp_log (chi_ne_zero_on_line 0)

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

/-- χ 沿临界线在 [0,1] 上的路径。 
English: χ path on [0,1] along the critical line. -/
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

/-- liftPath 的起点条件。 
English: Starting-point condition for liftPath. -/
private lemma liftPath_γ0 (T : ℝ) :
    chiPath T 0 = (⟨Complex.exp (theta0 T), Complex.exp_ne_zero (theta0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  dsimp [chiPath]
  have hzero : ((T * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by
    simp
  rw [hzero]
  simpa using (exp_theta0 T).symm

/-- χ 的连续幅角提升: exp(θ(s)) = χ(1/2 + T·s·i)。 
English: Continuous argument lift of χ: exp(θ(s)) = χ(1/2 + T·s·i). -/
noncomputable def thetaLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (chiPath T) (theta0 T) (liftPath_γ0 T)

/-- 提升性质。 
English: Lifting property. -/
lemma thetaLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (thetaLift T s) = chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I) := by
  have h := (isCoveringMap_exp.liftPath_lifts (chiPath T) (theta0 T) (liftPath_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [thetaLift]
  simpa [chiPath] using hs

/-- u 沿临界线的路径 (无零点区间)。 
English: u path along the critical line (zero-free interval). -/
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

/-- u 的提升起点。 
English: u's lift basepoint. -/
noncomputable def uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : ℂ :=
  Complex.log ((uPath T hz 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    Complex.exp (uLift0 T hz) = (uPath T hz 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [uLift0]
  exact Complex.exp_log (uPath T hz 0).2

/-- liftPath 的起点条件。 
English: Starting-point condition for liftPath. -/
private lemma uLift_γ0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uPath T hz 0 = (⟨Complex.exp (uLift0 T hz), Complex.exp_ne_zero (uLift0 T hz)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_uLift0 T hz).symm

/-- u 的连续幅角提升。 
English: Continuous argument lift of u. -/
noncomputable def uLift (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- 提升性质。 
English: Lifting property. -/
lemma uLift_lifts (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (uLift T hz s) =
      riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖ := by
  have h := (isCoveringMap_exp.liftPath_lifts (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [uLift]
  simpa [uPath] using hs

/-- exp 的核: exp z = 1。 
English: Kernel of exp: exp z = 1. -/
def expKernel : Set ℂ := {z | Complex.exp z = 1}

/-- expKernel = 2πiℤ。 
English: expKernel = 2πiℤ. -/
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

/-- u² = χ (T5): 无零点处 (ζ/‖ζ‖)² = χ (def chi 形式)。 
English: u² = χ (T5): at zero-free points (ζ/‖ζ‖)² = χ (def chi form). -/
lemma zeta_unit_sq_eq_chi_short (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ : ℂ) ^ 2 = chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) := by
  simpa [chi] using (zeta_unit_sq_eq_chi t hz)

/-- **S(T) 的整数层结构**: θ_ζ - θ_χ/2 ∈ πiℤ 逐点 —
    符号改变 (翻转 ±1) 但位置 (零点) 不变 = pat 正负 1 过程。
    整数层 = 2πi 的迭代计数 (i 的迭代), θ_χ 显式 (快路径)。 
English: **Integer layer structure of S(T)**: θ_ζ - θ_χ/2 ∈ πiℤ pointwise — sign change (flip ±1) but position (zero) unchanged = pat ±1 process. Integer layer = iteration count of 2πi (iteration of i); θ_χ explicit (fast path). -/
theorem zeta_lift_half_chi_lift_pi_int (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0)
    (s : unitInterval) :
    ∃ n : ℤ, uLift T hz s - thetaLift T s / 2 = (n : ℂ) * (↑Real.pi * Complex.I) := by
  -- 2θ_ζ - θ_χ ∈ expKernel = 2πiℤ (从 u² = χ: exp(2θ_ζ) = u² = χ = exp(θ_χ))
  have hk : 2 * uLift T hz s - thetaLift T s ∈ expKernel := by
    rw [expKernel]
    change Complex.exp (2 * uLift T hz s - thetaLift T s) = 1
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    -- u² = χ (T5)
    rw [zeta_unit_sq_eq_chi_short (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  -- 2θ_ζ - θ_χ = 2πi·n ⟹ θ_ζ - θ_χ/2 = πi·n
  rcases (expKernel_mem_iff (2 * uLift T hz s - thetaLift T s)).1 hk with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- hn : 2θ_ζ - θ_χ = n·2πi
  -- 目标: θ_ζ - θ_χ/2 = n·πi
  calc
    uLift T hz s - thetaLift T s / 2 = (2 * uLift T hz s - thetaLift T s) / 2 := by ring
    _ = (n : ℂ) * (2 * ↑Real.pi * Complex.I) / 2 := by rw [hn]
    _ = (n : ℂ) * (↑Real.pi * Complex.I) := by ring


/-- **周期发散桥 (反转对接)**: 2·Δθ_ζ = Δθ_χ + 2πi·m —
    每翻转一次 (u → -u, 离散 ±1) χ 转一整圈 (连续 2π)。 
English: **Period-divergence bridge (flip docking)**: 2·Δθ_ζ = Δθ_χ + 2πi·m — each flip (u → -u, discrete ±1) makes χ wind one full circle (continuous 2π). -/
theorem flip_chi_circle_bridge (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, 2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
      = (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rcases (zeta_lift_half_chi_lift_pi_int T hz 1) with ⟨n1, h1⟩
  rcases (zeta_lift_half_chi_lift_pi_int T hz 0) with ⟨n0, h0⟩
  refine ⟨n1 - n0, ?_⟩
  -- h1 : θ_ζ(1) - θ_χ(1)/2 = n1·πi; h0 : θ_ζ(0) - θ_χ(0)/2 = n0·πi
  -- 2Δθ_ζ - Δθ_χ = 2·[(θ_ζ(1)-θ_χ(1)/2) - (θ_ζ(0)-θ_χ(0)/2)]
  calc
    2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
        = 2 * ((uLift T hz 1 - thetaLift T 1 / 2) - (uLift T hz 0 - thetaLift T 0 / 2)) := by ring
    _ = 2 * ((n1 : ℂ) * (↑Real.pi * Complex.I) - (n0 : ℂ) * (↑Real.pi * Complex.I)) := by
      rw [h1, h0]
    _ = ((n1 - n0 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast
      ring

/-- **连续离散逆桥**: 净翻转 m = (2·Δθ_ζ - Δθ_χ)/(2πi) ∈ ℤ —
    从连续提升的端点差重构离散翻转计数。 
English: **Continuous-discrete inverse bridge**: net flip m = (2·Δθ_ζ - Δθ_χ)/(2πi) ∈ ℤ — reconstructs the discrete flip count from endpoint differences of the continuous lifts. -/
theorem net_flip_from_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, ((2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)) /
      (2 * ↑Real.pi * Complex.I)) = (m : ℂ) := by
  rcases (flip_chi_circle_bridge T hz) with ⟨m, hm⟩
  rw [hm]
  -- (m·2πi)/(2πi) = m ∈ ℤ
  have h2pi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast (Real.pi_ne_zero) : (↑Real.pi : ℂ) ≠ 0)) Complex.I_ne_zero
  rw [show (m : ℂ) * (2 * ↑Real.pi * Complex.I) / (2 * ↑Real.pi * Complex.I) = (m : ℂ) by
    exact mul_div_cancel_right₀ (m : ℂ) h2pi]
  exact ⟨m, rfl⟩

end RiemannUnifiedObservation
