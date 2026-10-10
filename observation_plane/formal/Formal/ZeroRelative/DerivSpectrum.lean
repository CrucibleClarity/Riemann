import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# 导数谱系原子件 (DerivSpectrum) — 2026-08-27 用户方向 1

用户方向 (原话): "你如果试试 n/logn 的轴谱系呢? 通过精确多阶导数,
有没有可能把这玩意改造成一个连续的函数?"

数学落地: 素数轴 (n/log n 尺度, 对数尺度) 的谱系 = 显式公式语言 —
ψ(x) = x − Σ_ρ x^ρ/ρ + ... (零点贡献项 x^ρ/ρ)。**多阶导数谱**:
d^k/dx^k (x^ρ) = ρ(ρ−1)···(ρ−k+1)·x^(ρ−k) — 每阶导数把零点 ρ 的
贡献乘以下降因子 (ρ−j), 振幅 x^(ρ−k) 的指数降 k — k ≥ 2 阶导数消去
主项 x (素数定理主项), 只留零点谱 (频率 = Im ρ, 沿对数轴 log x 是
周期振荡 e^{it·log x}) — 连续函数 (ψ 分段连续) 的谱化。

本文件机证: 谱系原子件 (ℝ 指数版, 下降因子结构) —
x ↦ x^a 的 k 阶导数闭式: (∏_{j<k}(a−j))·x^(a−k) (归纳 + HasDerivAt.rpow)。
复数指数版 (x^ρ, ρ : ℂ, 零点谱频率) 用 HasDerivAt.cpow_const 同构 (slitPlane
条件 x > 0), 待补。

English: Derivative-spectrum atom (real-exponent version) — the k-th
derivative of x ↦ x^a is (∏_{j<k}(a−j))·x^(a−k): falling factors + lowered
exponent. The atom of the n/log n axis spectrum (explicit-formula
language; k-th derivatives strip the main term for k ≥ 2 and leave the
zero spectrum).
-/

noncomputable section

open scoped Topology BigOperators

namespace ZeroRelative

/-- **单步导数**: d/dx (x^a) = a·x^(a−1) (x > 0) — 谱系单步 (rpow 导数). -/
theorem deriv_rpow_pos (a : ℝ) (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => y ^ a) x = a * x ^ (a - 1) := by
  have hg : HasDerivAt (fun y : ℝ => y ^ a) (a * x ^ (a - 1)) x := by
    simpa using (hasDerivAt_id x).rpow_const (Or.inl (ne_of_gt hx))
  exact hg.deriv

/-- **★k 阶导数闭式**: d^k/dx^k (x^a) = (∏_{j<k}(a−j))·x^(a−k) (x > 0) —
    导数谱系原子件: 每阶导数乘下降因子 (a−j), 指数降 k
    (显式公式零点贡献 x^ρ 的 k 阶谱的实数指数版). -/
theorem deriv_iterate_rpow (a : ℝ) (x : ℝ) (hx : 0 < x) (k : ℕ) :
    (deriv^[k] (fun y : ℝ => y ^ a)) x =
      (∏ j ∈ Finset.range k, (a - (j : ℝ))) * x ^ (a - (k : ℝ)) := by
  revert x hx
  induction k with
  | zero =>
      intro x hx
      simp
  | succ k ih =>
      intro x hx
      have hstep : deriv (fun y : ℝ => (deriv^[k] (fun z : ℝ => z ^ a)) y) x =
          (∏ j ∈ Finset.range k, (a - (j : ℝ))) * (a - (k : ℝ)) * x ^ (a - (k + 1 : ℕ)) := by
        have hform : ∀ y : ℝ, 0 < y →
            (deriv^[k] (fun z : ℝ => z ^ a)) y =
              (∏ j ∈ Finset.range k, (a - (j : ℝ))) * y ^ (a - (k : ℝ)) := by
          intro y hy
          exact ih y hy
        have hg : HasDerivAt (fun y : ℝ => y ^ (a - (k : ℝ)))
            ((a - (k : ℝ)) * x ^ (a - (k : ℝ) - 1)) x := by
          simpa using (hasDerivAt_id x).rpow_const (Or.inl (ne_of_gt hx))
        have hc : HasDerivAt (fun y : ℝ =>
            (∏ j ∈ Finset.range k, (a - (j : ℝ))) * y ^ (a - (k : ℝ)))
            ((∏ j ∈ Finset.range k, (a - (j : ℝ))) * (a - (k : ℝ)) * x ^ (a - (k : ℝ) - 1)) x := by
          simpa [mul_assoc] using hg.const_mul (∏ j ∈ Finset.range k, (a - (j : ℝ)))
        have hloc : (fun y : ℝ => (deriv^[k] (fun z : ℝ => z ^ a)) y) =ᶠ[𝓝 x]
            (fun y : ℝ => (∏ j ∈ Finset.range k, (a - (j : ℝ))) * y ^ (a - (k : ℝ))) := by
          have hnhds : {y : ℝ | 0 < y} ∈ 𝓝 x := IsOpen.mem_nhds isOpen_Ioi hx
          filter_upwards [hnhds] with y hy
          exact hform y hy
        have hd : HasDerivAt (fun y : ℝ => (deriv^[k] (fun z : ℝ => z ^ a)) y)
            ((∏ j ∈ Finset.range k, (a - (j : ℝ))) * (a - (k : ℝ)) * x ^ (a - (k : ℝ) - 1)) x :=
          hc.congr_of_eventuallyEq hloc
        rw [hd.deriv]
        congr 1
        rw [show a - (k : ℝ) - 1 = a - ((k + 1 : ℕ) : ℝ) by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring]
      calc
        (deriv^[k + 1] (fun y : ℝ => y ^ a)) x
            = deriv (fun y : ℝ => (deriv^[k] (fun z : ℝ => z ^ a)) y) x := by
              rw [Function.iterate_succ_apply']
        _ = (∏ j ∈ Finset.range k, (a - (j : ℝ))) * (a - (k : ℝ)) * x ^ (a - (k + 1 : ℕ)) := hstep
        _ = (∏ j ∈ Finset.range (k + 1), (a - (j : ℝ))) * x ^ (a - (k + 1 : ℕ)) := by
          rw [Finset.prod_range_succ]

end ZeroRelative
