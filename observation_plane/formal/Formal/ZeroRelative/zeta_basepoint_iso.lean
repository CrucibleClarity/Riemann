import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 基点移动不能消掉反演 (仿射保直线)

用户方向 (2026-08-19): "让基点移动到可以消掉反演的位置" — 希望存在
基点 (仿射坐标变换 z ↦ a·z + c) 使临界线 Re z = 1/2 直接呈现为圆。

数学事实: 仿射变换保持直线性。临界线是直线, 在任何基点移动下仍是
直线 — 圆性只来自反演 (1/z, recip_on_critical_circle_iff:
Re z = 1/2 ⟺ 1/z ∈ 临界线圆)。"消掉反演"在坐标意义下不存在;
黎曼球视角 (直线 = 过 ∞ 的圆) 是同一事实的射影说法。

定理: 仿射像 {z | Re(a·z + c) = 1/2} 是直线 (方向 d = i·ā ≠ 0,
过点 p = (1/2 - Re c)·ā/|a|²)。这是"基点移动保持直线"的精确形式。

English: basepoint stability: basepoint independence in the equivalence framework (T1/T2) -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 仿射基点移动保持临界线的直线性: Re(a·z + c) = 1/2 是直线
    (方向 d = i·ā ≠ 0, 过点 p = (1/2 - Re c)·ā/|a|²)。 
English: Affine basepoint shifts preserve the straightness of the critical line: Re(a·z + c) = 1/2 is a line (direction d = i·ā ≠ 0, through p = (1/2 - Re c)·ā/|a|²). -/
theorem affine_image_critical_line_is_line (a c : ℂ) (ha : a ≠ 0) :
    ∃ (p : ℂ) (d : ℂ), d ≠ 0 ∧
      {z : ℂ | (a * z + c).re = 1 / 2} = {p + s • d | s : ℝ} := by
  let d : ℂ := Complex.I * (starRingEnd ℂ a)
  let p : ℂ := ((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hn_c : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  have hnorm_c : (‖a‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn_c
  -- a·p = (1/2 - Re c) 是实数 (a·ā = |a|² 对消)
  have hapeq : a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
      = ((1 / 2 : ℝ) - c.re : ℂ) := by
    calc
      a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
          = ((1 / 2 : ℝ) - c.re) * (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
      _ = ((1 / 2 : ℝ) - c.re) * (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by
        rw [Complex.mul_conj]
      _ = ((1 / 2 : ℝ) - c.re) * ((‖a‖ : ℂ) ^ 2) / ((‖a‖ : ℂ) ^ 2) := by
        rw [Complex.normSq_eq_norm_sq]
        norm_num
      _ = ((1 / 2 : ℝ) - c.re : ℂ) := by
        field_simp [hnorm_c, hn_c]
  -- a⁻¹ = ā / |a|²
  have hinv : a⁻¹ = starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2 := by
    have hmul : a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = 1 := by
      calc
        a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
        _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by rw [Complex.mul_conj]
        _ = (‖a‖ : ℂ) ^ 2 / (‖a‖ : ℂ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          norm_num
        _ = 1 := by
          field_simp [hnorm_c, hn_c]
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  refine ⟨p, d, ?_, ?_⟩
  · -- d ≠ 0: I·ā ≠ 0 (I ≠ 0, ā ≠ 0)
    have hconj : starRingEnd ℂ a ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have : a = 0 := by simpa using h'
      exact ha this
    exact mul_ne_zero (by norm_num : Complex.I ≠ 0) hconj
  · ext z
    constructor
    · -- Re(az+c) = 1/2 ⟹ z = p + s·d (w = a(z-p) 纯虚 ⟹ z-p = (w.im/|a|²)·d)
      intro hz
      let w : ℂ := a * (z - p)
      have haz_re : (a * z).re = 1 / 2 - c.re := by
        have hz' : (a * z).re + c.re = 1 / 2 := by
          simpa [Complex.add_re, Complex.ofReal_re] using hz
        linarith
      have hap_re : (a * p).re = 1 / 2 - c.re := by
        have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
          dsimp [p]
          exact hapeq
        rw [hpeq]
        simp [Complex.ofReal_re]
      have hwre : w.re = 0 := by
        dsimp [w]
        have hsub : a * (z - p) = a * z - a * p := by ring
        rw [hsub, Complex.sub_re, haz_re, hap_re]
        ring
      have hw_pure : w = w.im * Complex.I := by
        apply Complex.ext <;> simp [hwre]
      have hzpe : z - p = a⁻¹ * w := by
        calc
          z - p = 1 * (z - p) := by simp
          _ = (a⁻¹ * a) * (z - p) := by rw [inv_mul_cancel₀ ha]
          _ = a⁻¹ * (a * (z - p)) := by ring
      -- wim = w.im (避免 rw 污染投影)
      let wim : ℝ := w.im
      have hw_pure' : w = wim * Complex.I := by
        dsimp [wim]
        exact hw_pure
      have hzpd : z - p = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
        rw [hzpe, hw_pure']
        -- 乘法形式: a⁻¹·(wim·I) = (wim:ℂ)/|a|²·(I·ā)
        have hm : a⁻¹ * (wim * Complex.I)
            = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
          calc
            a⁻¹ * (wim * Complex.I) = wim * (a⁻¹ * Complex.I) := by ring
            _ = wim * (Complex.I * starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) := by
              rw [hinv]
              ring
            _ = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
              ring
        -- 转成标量形式: (wim:ℂ)/|a|²·x = (wim/|a|² : ℝ) • x
        have hm' : (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
            = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
          calc
            (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
                = ((wim / ‖a‖ ^ 2 : ℝ) : ℂ) * (Complex.I * starRingEnd ℂ a) := by
                  have hden : (‖a‖ : ℂ) ^ 2 = ((‖a‖ ^ 2 : ℝ) : ℂ) := by norm_num
                  rw [hden]
                  -- ↑wim / ↑(‖a‖²) · x = ↑(wim/‖a‖²) · x: 先分离共同因子 x
                  congr 1
                  norm_num
            _ = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
                  simp [smul_eq_mul]
        exact hm.trans hm'
      refine ⟨wim / ‖a‖ ^ 2, ?_⟩
      rw [← hzpd]
      ring
    · -- z = p + s·d ⟹ Re(az+c) = 1/2 (s·d 纯虚 + ap 实)
      rintro ⟨s, rfl⟩
      have hsd : (a * (s • (Complex.I * starRingEnd ℂ a))).re = 0 := by
        -- a·(s·(I·ā)) = s·(I·(a·ā)) = s·(I·|a|²) 纯虚
        calc
          (a * (s • (Complex.I * starRingEnd ℂ a))).re
              = (a * ((s : ℂ) * (Complex.I * starRingEnd ℂ a))).re := by
                simp
          _ = ((s : ℂ) * (Complex.I * (a * starRingEnd ℂ a))).re := by
                congr 1
                ring
          _ = ((s : ℂ) * (Complex.I * (Complex.normSq a : ℂ))).re := by
                rw [Complex.mul_conj]
          _ = 0 := by
                simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      calc
        (a * (p + s • (Complex.I * starRingEnd ℂ a)) + c).re
            = (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re := by
              rw [mul_add]
        _ = (a * p + c).re := by
              -- (a·(s•d)).re = 0 (hsd): 展开 re 后替换
              calc
                (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re
                    = (a * p).re + (a * (s • (Complex.I * starRingEnd ℂ a))).re + c.re := by
                      simp [Complex.add_re]
                _ = (a * p).re + 0 + c.re := by rw [hsd]
                _ = (a * p + c).re := by
                      simp [Complex.add_re]
        _ = 1 / 2 := by
          have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
            dsimp [p]
            exact hapeq
          rw [hpeq]
          simp [Complex.add_re, Complex.ofReal_re]

end RiemannUnifiedObservation
