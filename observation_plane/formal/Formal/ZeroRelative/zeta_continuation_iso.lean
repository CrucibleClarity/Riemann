import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# T6j: (0,1) 段 ζ(x) < 0 — 欧拉-麦克劳林延拓 (假实轴框架补完)

ζ 在 (1,∞) 由级数 Σ n^{-x} 给出且恒正 (riemannZeta_pos_of_one_lt), 假实轴框架
已给出 Re<0 无零点与实轴实值。剩 (0,1) 段: 用欧拉-麦克劳林延拓
(第一不等式 zeta_partial_sum_lt_integral_bound 的逐项版) 构造

    R_N(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1)          (块 A: 初等可导)
    R(s)   = lim_N R_N(s)  (块 B/C: 柯西估计 ⟹ 局部一致收敛)
    Weierstrass ⟹ R 解析;  G_N := (s-1)·Σ + N^{1-s} 消分母 ⟹ G = lim G_N
    解析于 {0<re<2} (块 D)
    R = ζ on (1,2)                                     (块 E: 级数 + 修正项→0)
    R_N 递减 + R_1 = s/(s-1) < 0 ⟹ R < 0 on (0,1)      (块 F)
    G = (s-1)·ζ on (1,2) ⟹ 恒等定理 ⟹ G = (s-1)·ζ on {0<re<2}
    ⟹ ζ = R on (0,1) (块 G) ⟹ ζ(x) < 0 on (0,1)

纪律: 纯 mathlib 卷已知定理 (级数 zeta_eq_tsum_one_div_nat_cpow / 积分 FTC /
Weierstrass TendstoLocallyUniformlyOn.differentiableOn / 恒等定理), 不造轮子。

English: Euler--Maclaurin continuation: Blocks A--B (closed form, differentiability, Layer 13) -/

open Complex
open Filter
open scoped Topology BigOperators

namespace RiemannUnifiedObservation

/-! ## 块 A: R_N / G_N 定义与初等可导性 -/

/-- R_N(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1): 欧拉-麦克劳林延拓的部分和核 
English: R_N(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1): the partial-sum kernel of the Euler–Maclaurin continuation. -/
noncomputable def zetaEmR_N (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s))) + (N : ℂ) ^ (1 - s) / (s - 1)

/-- G_N(s) = (s-1)·Σ_{n=1}^N n^{-s} + N^{1-s}: (s-1)·R_N 消分母版 (在 1 处良定) 
English: G_N(s) = (s-1)·Σ_{n=1}^N n^{-s} + N^{1-s}: the denominator-eliminating version (s-1)·R_N (well-defined at 1). -/
noncomputable def zetaEmG_N (N : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s))) + (N : ℂ) ^ (1 - s)

lemma zetaEmG_N_eq_smul (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaEmG_N N s = (s - 1) * zetaEmR_N N s := by
  unfold zetaEmG_N zetaEmR_N
  rw [mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hs)]

/-- R_N 在 {s | s ≠ 1} 上可导 (初等: cpow 底正实数 + 有理函数) 
English: R_N is differentiable on {s | s ≠ 1} (elementary: cpow with positive real base + rational function). -/
lemma zetaEmR_N_differentiableOn (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ (zetaEmR_N N) {s : ℂ | s ≠ 1} := by
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hterm : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => ((n + 1 : ℂ) ^ (-s))) {s : ℂ | s ≠ 1} := by
    intro n
    have hbase : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log ((n + 1 : ℂ)) * (-s))) {s : ℂ | s ≠ 1} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hbase (-s))
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | s ≠ 1} := by
    have hsum' : DifferentiableOn ℂ
        (∑ n ∈ (Finset.range N), (fun s : ℂ => ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | s ≠ 1} := by
      exact DifferentiableOn.sum (u := Finset.range N) (A := fun n s => ((n + 1 : ℂ) ^ (-s)))
        (fun n hn => hterm n)
    exact hsum'.congr (fun s hs => by simp)
  have hnum : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (1 - s)) {s : ℂ | s ≠ 1} := by
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log (N : ℂ) * (1 - s))) {s : ℂ | s ≠ 1} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hN0 (1 - s))
  have hden : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | s ≠ 1} := by
    fun_prop
  have hden0 : ∀ x ∈ {s : ℂ | s ≠ 1}, x - 1 ≠ 0 := by
    intro x hx
    exact sub_ne_zero.mpr hx
  exact hsum.add (hnum.div hden hden0)

/-- G_N 在带 {0 < re < 2} 上可导 (分母已消, 处处良定) 
English: G_N is differentiable on the strip {0 < re < 2} (denominator eliminated, well-defined everywhere). -/
lemma zetaEmG_N_differentiableOn (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ (zetaEmG_N N) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hterm : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => ((n + 1 : ℂ) ^ (-s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    intro n
    have hbase : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log ((n + 1 : ℂ)) * (-s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hbase (-s))
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    have hsum' : DifferentiableOn ℂ
        (∑ n ∈ (Finset.range N), (fun s : ℂ => ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      exact DifferentiableOn.sum (u := Finset.range N) (A := fun n s => ((n + 1 : ℂ) ^ (-s)))
        (fun n hn => hterm n)
    exact hsum'.congr (fun s hs => by simp)
  have hid : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    fun_prop
  have hnum : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (1 - s)) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log (N : ℂ) * (1 - s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hN0 (1 - s))
  unfold zetaEmG_N
  exact (hid.mul hsum).add hnum

/-! ## 块 B1: 实数参数 cpow 的导数 (卷 mathlib HasDerivAt.cpow_const) -/

/-- u ↦ (u:ℂ)^s 的实数导数: s·x^{s-1} (x > 0, 卷 HasDerivAt.cpow_const) 
English: Real derivative of u ↦ (u:ℂ)^s: s·x^{s-1} (x > 0, library HasDerivAt.cpow_const). -/
lemma cpow_ofReal_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id (x : ℂ)) (ofReal_mem_slitPlane.2 hx)
  simpa only [mul_one] using! t.comp_ofReal

/-- u ↦ (u:ℂ)^(-s) 的实数导数 (块 B2 的一次 FTC 用) 
English: Real derivative of u ↦ (u:ℂ)^(-s) (used by one FTC in block B2). -/
lemma cpow_ofReal_neg_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  simpa using cpow_ofReal_hasDerivAt (-s) hx


/-! ## 块 B: 欧拉-麦克劳林项 term 的 ℂ 版闭式 (卷 ZetaAsymptotics 体系)

mathlib 已实现欧拉-麦克劳林第一项 (Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean):
    term n s = ∫ₙ^{n+1} (x-n)/x^{s+1} dx,  termTSum s = Σ term (n+1) s
并给出 s > 1 的恒等式 (zeta_limit_aux1):
    Σ' 1/(n+1)^s - 1/(s-1) = 1 - s·termTSum s    ⟹   ζ(s) = 1/(s-1) + 1 - s·termTSum s
右边对 0 < s 良定义 (term_welldef 只需 0 < s)。本块: 把 term 提升到 ℂ
(底正实数的 cpow), 给闭式 (分部积分) ⟹ 逐项解析; 局部一致收敛 ⟹
Weierstrass ⟹ termTSum 解析延拓到 {0 < re < 2}. 对称延拓: 恒等定理
把 s > 1 侧的恒等式唯一延拓到 (0,1) 段。 -/

/-- uIcc n (n+1) 中 x ≥ n (n ≤ n+1 已知) 
English: x ≥ n within uIcc n (n+1) (n ≤ n+1 known). -/
lemma zeta_uIcc_ge {n : ℕ} {x : ℝ} (hx : x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1)) :
    (n : ℝ) ≤ x := by
  rcases (Set.mem_uIcc.mp hx) with h | h
  · exact h.1
  · exact le_trans (by simp) h.1

/-- term 的 ℂ 版: ∫ₙ^{n+1} (x-n)/x^{s+1} dx (cpow, 底正实数) 
English: Complex version of term: ∫ₙ^{n+1} (x-n)/x^{s+1} dx (cpow, positive real base). -/
noncomputable def zetaTermC (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), (((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1))

/-- x ↦ (x:ℂ)^s 连续于 x > 0 (卷 ContinuousAt.cpow, 底正实数 ∈ slitPlane) 
English: x ↦ (x:ℂ)^s is continuous at x > 0 (library ContinuousAt.cpow, positive real base ∈ slitPlane). -/
lemma zeta_cpow_ofReal_continuousAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun u : ℝ => (u : ℂ) ^ s) x :=
  ContinuousAt.cpow (f := fun u : ℝ => (u : ℂ)) (g := fun _ : ℝ => s)
    continuous_ofReal.continuousAt continuousAt_const (ofReal_mem_slitPlane.2 hx)

/-- FTC: ∂_x (x:ℂ)^{1-s} = (1-s)·(x:ℂ)^{-s} 于 x > 0 (卷 cpow_ofReal_hasDerivAt) 
English: FTC: ∂_x (x:ℂ)^{1-s} = (1-s)·(x:ℂ)^{-s} at x > 0 (library cpow_ofReal_hasDerivAt). -/
lemma zetaTermC_fund_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs1 : s ≠ 1) :
    (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))
      = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)) := by
  have hd : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (1 - s)) ((1 - s) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
    have hd' := cpow_ofReal_hasDerivAt (1 - s) hxpos
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hd'
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint.const_mul (1 - s))
  -- hftc : ∫ (1-s)·x^{-s} = (n+1)^{1-s} - n^{1-s} ⟹ ∫ x^{-s} = 差/(1-s)
  rw [intervalIntegral.integral_const_mul] at hftc
  calc
    (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))
        = ((1 - s) * (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))) / (1 - s) := by
            field_simp [sub_ne_zero.mpr hs1]
    _ = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)) := by
            rw [hftc]
            simp [Complex.ofReal_natCast, Complex.ofReal_add]

/-- term n s 的闭式 (分部积分, s ≠ 0, 1):
    term n s = ((n+1)^{1-s} - n^{1-s})/(s(1-s)) - 1/(s·(n+1)^s) 
English: Closed form of term n s (integration by parts, s ≠ 0, 1): term n s = ((n+1)^{1-s} - n^{1-s})/(s(1-s)) - 1/(s·(n+1)^s). -/
lemma zetaTermC_closed_form {n : ℕ} (hn : 0 < n) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaTermC n s = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (s * (1 - s)))
        - 1 / (s * (n + 1 : ℂ) ^ s) := by
  -- 被积代数: (x-n)/x^{s+1} = x^{-s} - n·x^{-s-1} (x > 0)
  have hf : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      (((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1))
        = ((x : ℂ) ^ (-s)) - (n : ℂ) * ((x : ℂ) ^ (-s - 1)) := by
    intro x hx
    have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hxpos)
    have hx1 : (x : ℂ) ^ (1 : ℂ) = (x : ℂ) := by simp
    have hxpow : (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
      nth_rewrite 1 [← hx1]
      rw [← Complex.cpow_add 1 (-(s + 1)) hx0]
      congr 1
      ring
    calc
      ((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1)
          = (x : ℂ) / (x : ℂ) ^ (s + 1) - (n : ℂ) / (x : ℂ) ^ (s + 1) := by rw [sub_div]
      _ = (x : ℂ) * (x : ℂ) ^ (-(s + 1)) - (n : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
            congr 2
            · rw [div_eq_mul_inv, ← Complex.cpow_neg]
            · rw [div_eq_mul_inv, ← Complex.cpow_neg]
      _ = (x : ℂ) ^ (-s) - (n : ℂ) * (x : ℂ) ^ (-s - 1) := by
            rw [hxpow]
            congr 1
            rw [show (-(s + 1) : ℂ) = -s - 1 by ring]
  -- ∫ x^{-s} 与 ∫ x^{-s-1} 的 FTC
  have hint2 : (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))
      = (((n + 1 : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s)) := by
    have hd2 : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x := by
      intro x hx
      have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        cpow_ofReal_hasDerivAt (-s) hxpos
    have hint' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume
        (n : ℝ) ((n : ℝ) + 1) := by
      exact ContinuousOn.intervalIntegrable (fun x hx =>
        (zeta_cpow_ofReal_continuousAt (-s - 1) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
    have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 (hint'.const_mul (-s))
    rw [intervalIntegral.integral_const_mul] at hftc2
    calc
      (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))
          = ((-s) * (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))) / (-s) := by
              field_simp [hs0]
      _ = (((n + 1 : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s)) := by
            rw [hftc2]
            simp [Complex.ofReal_natCast, Complex.ofReal_add]
  -- 组装: ∫(x^{-s} - n·x^{-s-1}) = ∫x^{-s} - n·∫x^{-s-1}
  have hint3 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  have hint4 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s - 1) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  rw [zetaTermC, intervalIntegral.integral_congr hf]
  rw [intervalIntegral.integral_sub hint3 (hint4.const_mul (n : ℂ))]
  rw [intervalIntegral.integral_const_mul (n : ℂ)]
  rw [zetaTermC_fund_integral hn hs1, hint2]
  -- 目标: A/(1-s) - n·(C-D)/(-s) = A/(s(1-s)) - 1/(sE)  (A=(n+1)^{1-s}-n^{1-s}, ...)
  -- cpow 合并引理
  have hnp1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hmerge1 : ((n + 1 : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s) = (n + 1 : ℂ) := by
    rw [← Complex.cpow_add (1 - s) s hnp1]
    have : (1 - s) + s = 1 := by ring
    rw [this]
    simp
  have hmerge2 : ((n + 1 : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s) = 1 := by
    rw [← Complex.cpow_add (-s) s hnp1]
    have : (-s) + s = 0 := by ring
    rw [this]
    simp
  have hmerge3 : (n : ℂ) * ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (1 - s) := by
    nth_rewrite 1 [← Complex.cpow_one (n : ℂ)]
    rw [← Complex.cpow_add 1 (-s) hnn]
    congr 1
  -- 通分到 s(1-s), calc 链化简 (每步 ring + 单 rw, 控制 cpow 乘积形态)
  field_simp [hs0, sub_ne_zero.mpr hs1]
  calc
    (s * (((n + 1 : ℂ) ^ (1 - s)) - ((n : ℂ) ^ (1 - s)))
        - -(n * (1 - s) * (((n + 1 : ℂ) ^ (-s)) - ((n : ℂ) ^ (-s))))) * ((n + 1 : ℂ) ^ s)
        = s * ((((n + 1 : ℂ) ^ (1 - s)) - ((n : ℂ) ^ (1 - s))) * ((n + 1 : ℂ) ^ s))
            + n * (1 - s) * ((((n + 1 : ℂ) ^ (-s)) - ((n : ℂ) ^ (-s))) * ((n + 1 : ℂ) ^ s)) := by
            ring
    _ = s * ((((n + 1 : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s))
            - (((n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s)))
            + n * (1 - s) * ((((n + 1 : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))
            - (((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))) := by
            ring
    _ = s * (((n + 1 : ℂ)) - (((n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s)))
            + n * (1 - s) * (1 - (((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))) := by
            rw [hmerge1, hmerge2]
    _ = s * (n + 1 : ℂ) + n * (1 - s) - (n : ℂ) * ((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s) := by
            conv_lhs => rw [← hmerge3]
            ring
    _ = ((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s) - (1 - s) := by
            rw [hmerge3]
            rw [sub_mul, hmerge1]
            ring


end RiemannUnifiedObservation
