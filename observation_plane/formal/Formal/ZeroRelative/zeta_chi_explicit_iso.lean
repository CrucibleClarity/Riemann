import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Ring

/-!
# χ 的显式相位 — 非 Γ 部分的 0pat 显式化 (N(T) 拆解)

χ(s) = 2^s·π^(s-1)·sin(πs/2)·Γ(1-s) 沿临界线的相位 (N(T) = (1/π)Δ arg ξ
的乘子部分):
  arg 2^(1/2+it)        = t·ln 2          (cpow_two_on_line_explicit)
  arg π^(-1/2+it)       = t·ln π          (cpow_pi_on_line_explicit)
  sin(π/4 + iπt/2)      = sin(π/4)cosh(πt/2) + i·cos(π/4)sinh(πt/2)
                            (sin_pi_quarter_add_mul_I; 实部 = sin(π/4)cosh > 0
                             恒正 ⟹ arg = arctan(tanh(πt/2)))
  arg Γ(1/2-it)         = Im log Γ        = Stirling (唯一缺口, mathlib 无)

这三个定理把 χ 的绕转拆成显式项 (线性 + arctan(tanh)) — N(T) 的
Stirling 主项之外的相位全部显式, 0pat (纯 cpow/三角恒等式)。

English: explicit chi: the product/sine/Gamma factorization on the critical line -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 2^s 沿临界线显式: 2^(1/2+it) = exp(ln 2 / 2) · (cos(t·ln 2) + i·sin(t·ln 2))。
    相位 = t·ln 2 (线性), 模 = 2^(1/2)。 
English: 2^s explicit on the critical line: 2^(1/2+it) = exp(ln 2 / 2) · (cos(t·ln 2) + i·sin(t·ln 2)); phase = t·ln 2 (linear), modulus = 2^(1/2). -/
theorem cpow_two_on_line_explicit (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        + (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((t * Real.log 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- π^(s-1) 沿临界线显式: π^(-1/2+it) = exp(-ln π / 2) · (cos(t·ln π) + i·sin(t·ln π))。
    相位 = t·ln π (线性), 模 = π^(-1/2)。 
English: π^(s-1) explicit on the critical line: π^(-1/2+it) = exp(-ln π / 2) · (cos(t·ln π) + i·sin(t·ln π)); phase = t·ln π (linear), modulus = π^(-1/2). -/
theorem cpow_pi_on_line_explicit (t : ℝ) :
    (↑Real.pi : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.cos (t * Real.log Real.pi) : ℂ)
        + (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.sin (t * Real.log Real.pi) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
  have hlog : Complex.log (↑Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    exact (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  rw [hlog]
  have hdecomp : (Real.log Real.pi : ℂ) * (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((-Real.log Real.pi / 2 : ℝ) : ℂ) + ((t * Real.log Real.pi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- sin(πs/2) 沿临界线显式 (s = 1/2+it):
    sin(π/4 + iπt/2) = sin(π/4)·cosh(πt/2) + i·cos(π/4)·sinh(πt/2)。
    实部 = sin(π/4)·cosh(πt/2) > 0 恒正 ⟹ arg = arctan(tanh(πt/2))。 
English: sin(πs/2) explicit on the critical line (s = 1/2+it): sin(π/4 + iπt/2) = sin(π/4)·cosh(πt/2) + i·cos(π/4)·sinh(πt/2); real part = sin(π/4)·cosh(πt/2) > 0 always ⟹ arg = arctan(tanh(πt/2)). -/
theorem sin_pi_quarter_add_mul_I (t : ℝ) :
    Complex.sin (↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I)
      = Complex.sin (↑Real.pi / 4) * Complex.cosh ((Real.pi / 2 * t : ℝ) : ℂ)
        + Complex.cos (↑Real.pi / 4) * Complex.sinh ((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I := by
  have h := Complex.sin_add_mul_I (↑(Real.pi / 4) : ℂ) ((Real.pi / 2 * t : ℝ) : ℂ)
  have hL : ↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I
      = ↑(Real.pi / 4) + ↑(Real.pi / 2 * t) * Complex.I := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add]
    ring
  rw [hL]
  simpa using h

end RiemannUnifiedObservation
