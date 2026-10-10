import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# 奇偶拆分不奇异: 相位差显式化 (2026-08-26, 用户主张验证)

用户主张: "0点奇偶拆分后就不奇异了对吧" — 奇偶拆分 (O₂ = (1−2⁻ˢ)ζ,
E₂ = 2⁻ˢζ) 后, 三桥/相位提升的奇异点 (ζ 的零点) 不奇异。

**验证结论 (精确形式, 全部机证)**:
- 单提升仍奇异: ζ(ρ) = 0 ⟹ O₂(ρ) = E₂(ρ) = 0 (奇偶公共零点 ⟺ ζ 零点,
  机证 odd_even_common_zero_iff) — 单个提升 u_O/u_E 在零点处仍无定义。
- **但差结构不奇异** (本文件): 带内 (0 < Re s) 拆分因子非零
  (2⁻ˢ ≠ 1 ⟹ 1−2⁻ˢ ≠ 0 ∧ 2ˢ−1 ≠ 0); 相位比显式:
  u_O/u_E = (2ˢ−1)/‖2ˢ−1‖ — 处处良定义 (含零点处: 2ᵖ−1 ≠ 0)。
- 即: 奇偶拆分把奇异集中到"零点的相位", 而相位差 arg(2ˢ−1) 是
  显式指数函数的相位, 与 ζ 的零点无关 — "不奇异" = 差结构不奇异。
  三桥输入 (ζ ≠ 0 路径) 的奇异留在单提升; 差结构给出新的显式刚性量。

English: Odd-even split non-singularity — the phase difference between the
odd part and the even part is explicit: u_O/u_E = (2^s−1)/‖2^s−1‖, well
defined everywhere in the strip (also at zeros), while individual lifts
remain singular at common zeros.
-/

noncomputable section

open Complex
open scoped Topology

namespace RH_OddEven

/-- 奇部 (基点 2): O₂(s) = (1 − 2⁻ˢ)·ζ(s). -/
def oddPart (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s

/-- 偶部 (基点 2): E₂(s) = 2⁻ˢ·ζ(s). -/
def evenPart (s : ℂ) : ℂ := (2 : ℂ) ^ (-s : ℂ) * riemannZeta s

/-! ## 1. 拆分因子非零 (差结构的定义域) -/

/-- **拆分因子非零**: 2⁻ˢ ≠ 1 ⟹ (1−2⁻ˢ) ≠ 0 ∧ 2ˢ ≠ 1 —
    差结构 (2ˢ−1) 的定义域: 因子零点 (2⁻ˢ = 1) 只在虚轴. -/
theorem split_factors_ne_zero {s : ℂ} (hne : (2 : ℂ) ^ (-s : ℂ) ≠ 1) :
    (1 - (2 : ℂ) ^ (-s : ℂ)) ≠ 0 ∧ (2 : ℂ) ^ s ≠ 1 := by
  constructor
  · intro h
    exact hne (sub_eq_zero.mp h).symm
  · intro h1
    have hneg : (2 : ℂ) ^ (-s : ℂ) = ((2 : ℂ) ^ s)⁻¹ := by
      exact Complex.cpow_neg (2 : ℂ) s
    rw [h1] at hneg
    exact hne (by simpa using hneg)

/-- **带内 (0 < Re s) ⟹ 2⁻ˢ ≠ 1**: 奇偶拆分在带内无额外零点
    (2⁻ˢ = 1 ⟹ s 纯虚, 不进带; 奇部独有零点在虚轴, 机证
    odd_part_extra_zero_on_imag_axis 的因子侧). -/
theorem two_pow_neg_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (2 : ℂ) ^ (-s : ℂ) ≠ 1 := by
  intro h
  have hdef : (2 : ℂ) ^ (-s : ℂ) = Complex.exp (Complex.log (2 : ℂ) * (-s : ℂ)) := by
    exact Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (-s : ℂ)
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hexp : Complex.exp (Complex.log (2 : ℂ) * (-s : ℂ)) = 1 := by
    rwa [hdef] at h
  rw [hlog] at hexp
  rcases (Complex.exp_eq_exp_iff_exists_int
      (x := (Real.log 2 : ℂ) * (-s : ℂ)) (y := 0)).mp (by simpa using hexp) with ⟨k, hk⟩
  -- (ln2)·(-s) = 2πi·k ⟹ 实部: ln2·(-s.re) = 0
  have hre : ((Real.log 2 : ℂ) * (-s : ℂ)).re =
      (0 + (k : ℂ) * (2 * Real.pi * Complex.I)).re := by
    rw [hk]
  have hleft : ((Real.log 2 : ℂ) * (-s : ℂ)).re = Real.log 2 * -s.re := by
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.neg_re]
    ring
  have hright : (0 + (k : ℂ) * (2 * Real.pi * Complex.I)).re = 0 := by
    simp
  have hre0 : Real.log 2 * -s.re = 0 := by
    rw [hleft, hright] at hre
    exact hre
  have hs0 : s.re = 0 := by
    have hl2 : Real.log 2 ≠ 0 := (Real.log_ne_zero).mpr (by norm_num)
    have hz : -s.re = 0 := (mul_eq_zero.mp hre0).resolve_left hl2
    linarith
  exact (ne_of_gt hs) hs0

/-! ## 2. 相位差显式化 (不奇异) -/

/-- **★奇偶相位比显式**: u_O/u_E = (2ˢ−1)/‖2ˢ−1‖ (ζ ≠ 0 处, 带内) —
    相位差 = 显式指数函数的相位, 与 ζ 的结构无关 (不奇异).
    Odd-even phase ratio: the phase difference is the explicit
    unit-modulus function (2^s−1)/‖2^s−1‖. -/
theorem odd_even_phase_ratio (s : ℂ) (hζ : riemannZeta s ≠ 0)
    (hne : (2 : ℂ) ^ (-s : ℂ) ≠ 1) :
    (oddPart s / (‖oddPart s‖ : ℂ)) / (evenPart s / (‖evenPart s‖ : ℂ))
      = ((2 : ℂ) ^ s - 1) / (‖(2 : ℂ) ^ s - 1‖ : ℂ) := by
  unfold oddPart evenPart
  have hf : (1 - (2 : ℂ) ^ (-s : ℂ)) ≠ 0 := (split_factors_ne_zero hne).1
  have h2ne : (2 : ℂ) ^ s ≠ 1 := (split_factors_ne_zero hne).2
  have hO : (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s ≠ 0 := mul_ne_zero hf hζ
  have hE : (2 : ℂ) ^ (-s : ℂ) * riemannZeta s ≠ 0 :=
    mul_ne_zero ((Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))) hζ
  -- O/E = 2ˢ − 1
  have hratio : ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s) /
        ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s) = (2 : ℂ) ^ s - 1 := by
    calc
      ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s) / ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s)
          = (1 - (2 : ℂ) ^ (-s : ℂ)) / (2 : ℂ) ^ (-s : ℂ) := by
            field_simp [hζ]
      _ = (1 - (2 : ℂ) ^ (-s : ℂ)) * ((2 : ℂ) ^ (-s : ℂ))⁻¹ := rfl
      _ = (1 - (2 : ℂ) ^ (-s : ℂ)) * (2 : ℂ) ^ s := by
        congr 1
        have hneg : (2 : ℂ) ^ (-s : ℂ) = ((2 : ℂ) ^ s)⁻¹ := Complex.cpow_neg (2 : ℂ) s
        rw [hneg]
        exact inv_inv ((2 : ℂ) ^ s)
      _ = (2 : ℂ) ^ s - 1 := by
        calc
          (1 - (2 : ℂ) ^ (-s : ℂ)) * (2 : ℂ) ^ s
              = 1 * (2 : ℂ) ^ s - (2 : ℂ) ^ (-s : ℂ) * (2 : ℂ) ^ s := by ring
          _ = (2 : ℂ) ^ s - 1 := by
            have h2 : (2 : ℂ) ^ (-s : ℂ) * (2 : ℂ) ^ s = 1 := by
              rw [← Complex.cpow_add (x := (2 : ℂ)) (y := (-s : ℂ)) (z := s)
                (by norm_num : (2 : ℂ) ≠ 0)]
              simp
            rw [h2, one_mul]
  -- (O/‖O‖)/(E/‖E‖) = (O/E)·(‖E‖/‖O‖)
  have hstep1 : ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s /
        (‖((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)‖ : ℂ)) /
      (((2 : ℂ) ^ (-s : ℂ) * riemannZeta s) /
        (‖((2 : ℂ) ^ (-s : ℂ) * riemannZeta s)‖ : ℂ))
      = (((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s) /
          ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s)) *
          ((‖((2 : ℂ) ^ (-s : ℂ) * riemannZeta s)‖ : ℂ) /
            (‖((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)‖ : ℂ)) := by
    field_simp [hO, hE, norm_ne_zero_iff]
  rw [hstep1]
  rw [hratio]
  -- ‖E‖/‖O‖ = ‖E/O‖ (范数乘法性)
  have hnorm : (‖((2 : ℂ) ^ (-s : ℂ) * riemannZeta s)‖ : ℂ) /
        (‖((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)‖ : ℂ)
      = ‖((2 : ℂ) ^ (-s : ℂ) * riemannZeta s) / ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)‖ := by
    rw [← Complex.ofReal_div, Complex.norm_div]
  rw [hnorm]
  -- E/O = (2ˢ−1)⁻¹
  have hEratio : ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s) / ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)
      = ((2 : ℂ) ^ s - 1)⁻¹ := by
    calc
      ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s) / ((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s)
          = (((1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s) /
              ((2 : ℂ) ^ (-s : ℂ) * riemannZeta s))⁻¹ := by
            field_simp [hO, hE]
      _ = ((2 : ℂ) ^ s - 1)⁻¹ := by rw [hratio]
  rw [hEratio]
  -- ‖(2ˢ−1)⁻¹‖ = ‖2ˢ−1‖⁻¹ (范数乘性)
  have hnorm_inv : ‖((2 : ℂ) ^ s - 1)⁻¹‖ = (‖(2 : ℂ) ^ s - 1‖)⁻¹ := by
    exact norm_inv _
  rw [hnorm_inv]
  -- (2ˢ−1)·(‖2ˢ−1‖ : ℂ)⁻¹ = (2ˢ−1)/(‖2ˢ−1‖ : ℂ) — cast 归并 + 除法定义
  rw [Complex.ofReal_inv]
  rfl

/-- **★零点处差结构良好**: 若 ρ 是零点 (ζ(ρ) = 0) 且 2⁻ᵖ ≠ 1 (带内),
    则 2ᵖ ≠ 1 — 相位差 arg(2ˢ−1) 在零点处仍处处良定义.
    (单提升 u_O/u_E 在公共零点处奇异 — 零点本身是奇点;
     差结构 (2ˢ−1) 是显式解析量, 与 ζ 的零点无关.)
    Phase-difference well-definedness at zeros: the explicit difference
    structure (2^s−1) is nonvanishing at every zero in the strip. -/
theorem phase_diff_well_defined_at_zero {s : ℂ} (_hζ : riemannZeta s = 0)
    (hne : (2 : ℂ) ^ (-s : ℂ) ≠ 1) : (2 : ℂ) ^ s ≠ 1 :=
  (split_factors_ne_zero hne).2

end RH_OddEven
