import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# 反演翻转发散化 (InversionFlip) — 2026-08-27 用户构造 (annals 人机合作)

## 用户全部要求 (原话完整记录)

背景: O₂ = 奇素数欧拉积 Π_{p奇}(1−p⁻ˢ)⁻¹ (Re>1 收敛) — 带内 ρ 处
O₂(ρ) = 0, 但带内已发散 (欧拉积不收敛), "没法继续发散"。

用户构造 (原话): "如果已经发散了, 没法继续发散, 我有个注意, 我们在构造
那个和复平面正交的平面时, 两个正交轴都用周期圆轴, 观测投影后发散化,
等于把 re 0-1 的部分和其他部分翻转, 让原本收敛的发散、原本发散的收敛。"

分解 (数学落地):
① 与复平面正交的观测平面 (AxisExactObservation 的 obsCoord: u = Re−1/2,
   v = Im) — 两轴周期圆化 (每根轴 = 圆参数, 观测平面 → 环面 T²);
② 观测投影后"发散化" = 反演翻转: 把 Re ∈ (0,1) (发散域, 欧拉积不收敛)
   翻转到 Re > 1 (收敛域, 欧拉积可用) — 原本发散的收敛; 反向亦然;
③ 翻转的数学形式: 反演 s ↦ 1/s — 临界线圆 (‖s−1/2‖ = 1/2, 圆心 1/2
   半径 1/2, 过 0 与 1 的圆) 在反演下 = 直线 Re = 1 (临界线); 圆内部
   (Re∈(0,1) 的圆内部分) ⟹ Re(1/s) > 1 (收敛域!) — 发散域翻转收敛。

本文件机证: 反演翻转的精确代数 (②③的机证侧):
- inversion_re: (1/ρ).re = ρ.re / ‖ρ‖² (反演实部公式)
- critical_circle_inverts_to_line: ‖ρ−1/2‖ = 1/2 ⟹ Re(1/ρ) = 1
  (临界线圆 → 临界线 Re=1 — 反演把圆映射到直线)
- critical_circle_inner_inverts_to_convergence: ‖ρ−1/2‖ < 1/2 ⟹ 1 < Re(1/ρ)
  (圆内 = 带内圆内部分 ⟹ 反演后进收敛域 Re>1 — **原本发散的收敛**)
- critical_circle_outer_inverts_to_divergence: ‖ρ−1/2‖ > 1/2 ⟹ Re(1/ρ) < 1
  (圆外 ⟹ 反演后出收敛域 — 原本收敛的发散, 反向翻转)

诚实缺口 (记录): 反演只翻转临界线圆**内**部分 (带内大 |Im| 点在圆外,
反演后仍非收敛域); 且 O₂(ρ)=0 与 O₂(1/ρ) 的连接公式不存在 (函数方程只
连 s ↔ 1−s, 无 s ↦ 1/s 公式) — 翻转把点带进收敛域, 但函数值连接桥
(周期圆轴上翻转后的值对应) 是开放件。

English: Inversion flip of convergence/divergence — the user's construction:
the observation plane with periodic-circle axes; projection followed by
inversion (s ↦ 1/s) flips the divergence domain (Re∈(0,1), where the
Euler product diverges) into the convergence domain (Re>1): the critical
circle ‖s−1/2‖ = 1/2 inverts to the line Re = 1, its interior to Re > 1.
-/

noncomputable section

open Complex
open scoped Topology

namespace ZeroRelative

/-! ## 1. 反演实部公式 -/

/-- **反演实部公式**: Re(1/ρ) = Re ρ / ‖ρ‖² (ρ ≠ 0) —
    反演 s ↦ 1/s 的实部显式 (翻转的代数核). -/
theorem inversion_re {ρ : ℂ} (hρ0 : ρ ≠ 0) : (1 / ρ).re = ρ.re / ‖ρ‖ ^ 2 := by
  have hns : Complex.normSq ρ = ‖ρ‖ ^ 2 := Complex.normSq_eq_norm_sq ρ
  have hinv : (1 / ρ) = (starRingEnd ℂ) ρ * ((Complex.normSq ρ)⁻¹ : ℝ) := by
    rw [one_div, Complex.inv_def ρ]
  calc
    (1 / ρ).re = ((starRingEnd ℂ) ρ * ((Complex.normSq ρ)⁻¹ : ℝ)).re := by rw [hinv]
    _ = ρ.re * ((Complex.normSq ρ)⁻¹ : ℝ) := by
      simp
    _ = ρ.re / ‖ρ‖ ^ 2 := by
      rw [hns]
      rw [← div_eq_mul_inv]

/-! ## 2. 临界线圆 → 临界线 (反演把圆映射到直线) -/

/-- 圆条件 ⟺ 代数条件: ‖ρ−1/2‖² = 1/4 ⟺ ‖ρ‖² = ρ.re (圆上),
    < ⟺ ‖ρ‖² < ρ.re (圆内), > ⟺ ‖ρ‖² > ρ.re (圆外). -/
lemma critical_circle_sq {ρ : ℂ} :
    ‖ρ - 1 / 2‖ ^ 2 = ‖ρ‖ ^ 2 - ρ.re + 1 / 4 := by
  calc
    ‖ρ - 1 / 2‖ ^ 2 = Complex.normSq (ρ - 1 / 2) := (Complex.normSq_eq_norm_sq _).symm
    _ = (ρ - 1 / 2).re * (ρ - 1 / 2).re + (ρ - 1 / 2).im * (ρ - 1 / 2).im := by
      rw [Complex.normSq_apply]
    _ = (ρ.re - 1 / 2) * (ρ.re - 1 / 2) + ρ.im * ρ.im := by
      simp
    _ = ‖ρ‖ ^ 2 - ρ.re + 1 / 4 := by
      have hns : ‖ρ‖ ^ 2 = ρ.re * ρ.re + ρ.im * ρ.im := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      rw [hns]
      ring

/-- **临界线圆 → Re=1 直线**: ‖ρ−1/2‖ = 1/2 ⟹ Re(1/ρ) = 1 —
    反演把临界线圆 (过 0 与 1, 圆心 1/2) 映射到收敛域边界 Re = 1. -/
theorem critical_circle_inverts_to_line {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ = 1 / 2) : (1 / ρ).re = 1 := by
  have hsq : ‖ρ - 1 / 2‖ ^ 2 = (1 / 2) ^ 2 := by rw [hcirc]
  have hmain : ‖ρ‖ ^ 2 - ρ.re = 0 := by
    rw [critical_circle_sq] at hsq
    linarith
  have hρre : ρ.re = ‖ρ‖ ^ 2 := by linarith
  have hden : ‖ρ‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hρ0))
  rw [inversion_re hρ0]
  rw [hρre]
  rw [div_self hden]

/-- **★原本发散的收敛**: ‖ρ−1/2‖ < 1/2 (临界线圆内, 欧拉积发散域)
    ⟹ Re(1/ρ) > 1 (反演后进收敛域, 欧拉积可用) — 反演翻转把发散域
    翻进收敛域 ("观测投影后发散化"). -/
theorem critical_circle_inner_inverts_to_convergence {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) : 1 < (1 / ρ).re := by
  have hsq : ‖ρ - 1 / 2‖ ^ 2 < (1 / 2) ^ 2 := by
    exact sq_lt_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      exact hcirc)
  have hmain : ‖ρ‖ ^ 2 - ρ.re < 0 := by
    rw [critical_circle_sq] at hsq
    linarith
  have hpos : 0 < ρ.re := by
    have hnn : 0 ≤ ‖ρ‖ ^ 2 := sq_nonneg _
    nlinarith
  have hden : 0 < ‖ρ‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hρ0)
  have hle : ‖ρ‖ ^ 2 < ρ.re := by linarith
  rw [inversion_re hρ0]
  exact (one_lt_div hden).mpr hle

/-- **原本收敛的发散 (反向翻转)**: ‖ρ−1/2‖ > 1/2 (临界线圆外) ⟹
    Re(1/ρ) < 1 (反演后出收敛域). -/
theorem critical_circle_outer_inverts_to_divergence {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hcirc : 1 / 2 < ‖ρ - 1 / 2‖) : (1 / ρ).re < 1 := by
  have hsq : (1 / 2) ^ 2 < ‖ρ - 1 / 2‖ ^ 2 := by
    exact sq_lt_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      exact hcirc)
  have hmain : 0 < ‖ρ‖ ^ 2 - ρ.re := by
    rw [critical_circle_sq] at hsq
    linarith
  have hden : 0 < ‖ρ‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hρ0)
  rw [inversion_re hρ0]
  rw [div_lt_one hden]
  linarith

end ZeroRelative
