import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# 多轴相位叠加: 每项 n^{-s} 在临界线的显式相位 (1 2 3 4 各有各的相位)

用户洞察 (2026-08-19): 相位绕转的本质 = 多轴相位叠加 — 每项
n^{-s} 有自己的相位 (频率 ln n), 在正交对称性 (Re/Im 的 cos/sin
调制) 下合成总相位。

0pat 形式化 (term_on_line_explicit): 临界线上
  n^{-(1/2+it)} = n^{-1/2}·(cos(t·ln n) - i·sin(t·ln n))
每一项: 模 n^{-1/2}, 相位 -t·ln n (线性, 频率 ln n)。

cpow_two/pi 显式定理的 n 任意化 — 多轴相位叠加的每轴显式。

English: term phase: the phase decomposition of the series term -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 每项 n^{-s} 在临界线的显式相位: n^{-(1/2+it)} = n^{-1/2}·(cos(t·ln n) - i·sin(t·ln n))。
    "1 2 3 4 各有各的相位": 频率 ln n, 模 n^{-1/2}, 相位 -t·ln n (线性)。 
English: Explicit phase of each term n^{−s} on the critical line: n^{−(1/2+it)} = n^{−1/2}·(cos(t·ln n) − i·sin(t·ln n)). “1 2 3 4 each has its own phase”: frequency ln n, modulus n^{−1/2}, phase −t·ln n (linear). -/
theorem term_on_line_explicit (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I) : ℂ)
      = (Real.exp (-Real.log n / 2) : ℂ) * (Real.cos (t * Real.log n) : ℂ)
        - (Real.exp (-Real.log n / 2) : ℂ) * (Real.sin (t * Real.log n) : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  have hdecomp : (Real.log n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
      = ((-Real.log n / 2 : ℝ) : ℂ) + ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  -- exp((-(t·ln n))·I) = cos(t·ln n) - i·sin(t·ln n)
  rw [Complex.exp_mul_I]
  simp
  ring

end RiemannUnifiedObservation
