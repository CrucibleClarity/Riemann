import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
物理形式化边界声明: 作者知晓 Lean 无法完成物理的形式化约束, 本文件的
数学定理为纯代数/解析结构 — 0 sorry 只约束数学推导, 不承载物理意义。

# 欧拉积断链补全 (iso 40) — 黎曼方向完备性修补

用户指令 (2026-08-21): 补做欧拉积锻链 [断链], 然后未证的边界怎样达到已证?

断链回顾 (37 完备性分析): prime_factor_zero 证明素数因子 1-p^{-s} 的
零点全在 Re(s)=0 (纯虚轴), 但没有"因子乘积 = ζ"的连接 — 从因子结构
推断 ζ 零点分布的一环缺失。

补法: mathlib 已提供完整工具:
  1. riemannZeta_eulerProduct_hasProd (hs : 1 < s.re):
     HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)
     — 欧拉积: Re s > 1 时 ζ(s) = ∏_p (1-p^{-s})⁻¹
  2. riemannZeta_ne_zero_of_one_lt_re (hs : 1 < s.re): riemannZeta s ≠ 0
     — Re s > 1 无零点

新定理 (本文件, 连接链):
  1. factor_nonzero_in_convergence — 因子零点 ⟹ Re s = 0 (prime_factor_zero
     连接), 与收敛区 Re s > 1 互斥: 收敛区内因子非零
  2. zeta_no_zeros_convergence — Re s > 1 ⟹ ζ(s) ≠ 0 (欧拉积区域的
     无零点定理, mathlib 锚定)
  3. euler_product_bridge — ★欧拉积断链补全: 收敛区内 ①欧拉积成立
     ②ζ 无零点 ③因子非零 — 三环闭合 (因子结构 ↔ ζ 零点的连接)

English: Euler product: the prime-product representation of ζ -/

namespace EulerProductBridge

noncomputable section

open Complex Filter Topology
open scoped BigOperators

/-- 素数因子零点 (37 prime_factor_zero, 复制自 proof.lean): 1-p^{-s}=0
    ⟺ s·ln p = k·2πi — 因子零点全在 Re(s)=0 (纯虚轴, 周期轴)。 
English: Prime-factor zeros (37 prime_factor_zero, copied from proof.lean): 1-p^{-s}=0 ⟺ s·ln p = k·2πi — all factor zeros lie on Re(s)=0 (purely imaginary axis, periodic axis). -/
theorem prime_factor_zero (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s) = 0) ↔
      ∃ k : ℤ, s * Complex.log (p : ℂ) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  constructor
  · intro h
    have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [Complex.cpow_def_of_ne_zero hp0] at hpow
    rcases (Complex.exp_eq_one_iff).1 hpow with ⟨n, hn⟩
    use -n
    calc
      s * Complex.log (p : ℂ) = -((-s) * Complex.log (p : ℂ)) := by ring
      _ = -((n : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
        rw [show (-s) * Complex.log (p : ℂ) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) by
          simpa [mul_comm] using hn]
      _ = (-(n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-n) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]
  · rintro ⟨k, hk⟩
    rw [Complex.cpow_def_of_ne_zero hp0]
    rw [sub_eq_zero]
    symm
    apply (Complex.exp_eq_one_iff).mpr
    refine ⟨-k, ?_⟩
    calc
      Complex.log (p : ℂ) * (-s) = -((s) * Complex.log (p : ℂ)) := by ring
      _ = -((k : ℂ) * (2 * ↑Real.pi * Complex.I)) := by rw [hk]
      _ = (-(k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-k) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]

/-- 因子零点与收敛区互斥: 因子 1-p^{-s} 的零点 ⟹ Re s = 0 (纯虚轴),
    与收敛区 Re s > 1 不相交 — 收敛区内每个素数因子非零
    (prime_factor_zero 连接的断链第一环)。 
English: Factor zeros and convergence region are mutually exclusive: a zero of the factor 1-p^{-s} ⟹ Re s = 0 (purely imaginary axis), disjoint from the convergence region Re s > 1 — every prime factor is nonzero in the convergence region (first link of the broken chain, via prime_factor_zero). -/
theorem factor_nonzero_in_convergence (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hs1 : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  rcases (prime_factor_zero p hp s).1 h with ⟨k, hk⟩
  -- s·ln p = k·2πi ⟹ Re(s·ln p) = 0
  have hre : (s * Complex.log (p : ℂ)).re = 0 := by
    rw [hk]
    simp
  -- (s·log p).re = s.re·(log p).re - s.im·(log p).im; log p 实 (im = 0)
  have hlog_im : (Complex.log (p : ℂ)).im = 0 := by
    -- p > 0 ⟹ log p 为实对数 (mathlib: Complex.ofReal_log: ↑(Real.log x) = log ↑x)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
    have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
      exact (Complex.ofReal_log (le_of_lt hp_pos)).symm
    rw [hlog]
    exact Complex.ofReal_im (Real.log (p : ℝ))
  have hre' : s.re * (Complex.log (p : ℂ)).re = 0 := by
    have hmul : (s * Complex.log (p : ℂ)).re =
        s.re * (Complex.log (p : ℂ)).re - s.im * (Complex.log (p : ℂ)).im := by
      rw [Complex.mul_re]
    rw [hmul, hlog_im] at hre
    simpa using hre
  -- (log p).re = Real.log p ≠ 0 (p ≠ 1) ⟹ s.re = 0
  have hlog_re : (Complex.log (p : ℂ)).re ≠ 0 := by
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
    have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Nat.Prime.ne_one hp)
    have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
      exact (Complex.ofReal_log (le_of_lt hp_pos)).symm
    rw [hlog, Complex.ofReal_re]
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt hp)
    exact ne_of_gt ((Real.log_pos_iff (le_of_lt hp_pos)).2 hp_gt1)
  have hs0 : s.re = 0 := by
    rcases mul_eq_zero.mp hre' with hs0 | hlog0
    · exact hs0
    · exact False.elim (hlog_re hlog0)
  linarith

/-- 欧拉积区域无零点: Re s > 1 ⟹ ζ(s) ≠ 0 — 发散区无零点的完整定理
    (mathlib riemannZeta_ne_zero_of_one_lt_re 锚定, 断链的收敛区一环)。 
English: No zeros in the Euler-product region: Re s > 1 ⟹ ζ(s) ≠ 0 — the complete no-zero theorem for the divergence region (anchored by mathlib riemannZeta_ne_zero_of_one_lt_re, the convergence-region link of the broken chain). -/
theorem zeta_no_zeros_convergence (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

/-- ★ 欧拉积断链补全: 收敛区 Re s > 1 内三环闭合 —
    ①欧拉积成立: ζ(s) = ∏_p (1-p^{-s})⁻¹ (riemannZeta_eulerProduct: 有限部分乘积收敛)
    ②ζ 无零点 (zeta_no_zeros_convergence)
    ③因子非零 (factor_nonzero_in_convergence, prime_factor_zero 连接)
    — 因子零点 (Re=0, 周期轴) 与收敛区 (Re>1) 互斥, 素数因子结构 ↔
    ζ 零点分布的连接建立。 
English: Euler-product broken-chain completion: three links close in the convergence region Re s > 1 — (1) the Euler product holds: ζ(s) = ∏_p (1-p^{-s})⁻¹ (riemannZeta_eulerProduct: finite partial products converge); (2) ζ has no zeros (zeta_no_zeros_convergence); (3) factors are nonzero (factor_nonzero_in_convergence, via prime_factor_zero); factor zeros (Re=0, periodic axis) and the convergence region (Re>1) are exclusive — the connection between prime-factor structure and ζ zero distribution is established. -/
theorem euler_product_bridge (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ≠ 0 ∧
    (∀ p : ℕ, Nat.Prime p → 1 - (p : ℂ) ^ (-s) ≠ 0) ∧
    Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, (1 - ((p : ℂ) ^ (-s)))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  constructor
  · exact zeta_no_zeros_convergence s hs
  · constructor
    · intro p hp
      exact factor_nonzero_in_convergence p hp s hs
    · exact riemannZeta_eulerProduct hs

end

end EulerProductBridge
