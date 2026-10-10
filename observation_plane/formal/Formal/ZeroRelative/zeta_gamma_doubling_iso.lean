import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Γ 相位的对称约化 — Legendre 倍增 + 反射 (N(T) 差项的快速路径)

N(T) - N₀(T) 的 Γ 相位组合:
  G(t) = (1/2)·arg Γ(1/2-it) + arg Γ(1/4+it/2)
用对称性完全约化 (无 Stirling):

  倍增 (s = 1/4+it/2):  Γ(1/4+it/2)·Γ(3/4+it/2) = Γ(1/2+it)·2^{1-2s}·√π
  反射 (s = 3/4+it/2):  Γ(3/4+it/2)·Γ(1/4-it/2) = π/sin(π(3/4+it/2))
  共轭:                   arg Γ(1/4-it/2) = -arg Γ(1/4+it/2)

⟹ arg Γ(1/4+it/2) = (1/2)[arg Γ(1/2+it) - t·ln2 + arg sin(3π/4+iπt/2)]
⟹ G(t) = (1/2)[-t·ln2 + arg sin(3π/4+iπt/2)]   ← Γ 完全消去, 全显式!

乘子 2^{1-2s} 的相位 (s = 1/4+it/2): 2^{1/2-it} = √2·(cos(t·ln2) - i·sin(t·ln2)),
相位 = -t·ln2 (线性)。0pat: mathlib Gamma_mul_Gamma_add_half (无条件) +
Gamma_mul_Gamma_one_sub + Gamma_conj + sin 显式。

English: Gamma doubling: the duplication formula at 1+it -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 倍增乘子的显式相位: 2^(1/2-it) = √2·(cos(t·ln2) - i·sin(t·ln2)),
    相位 = -t·ln2 (线性) — Legendre 倍增公式 2^{1-2s} 在 s = 1/4+it/2 的乘子。 
English: Explicit phase of the doubling multiplier: 2^(1/2-it) = √2·(cos(t·ln2) - i·sin(t·ln2)), phase = -t·ln2 (linear) — the multiplier of the Legendre duplication formula 2^{1-2s} at s = 1/4+it/2. -/
theorem cpow_two_half_minus_im (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        - (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((-(t * Real.log 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

end RiemannUnifiedObservation
