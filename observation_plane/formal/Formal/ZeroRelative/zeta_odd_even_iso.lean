import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ζ 的奇偶拆分 (基点 p 的 p-adic 拆分)

用户洞察 (2026-08-19): 把基点移到素数相关位置 — 基点 2 (奇偶拆分):
奇侧 (非 2 倍数项) 与偶侧 (2 倍数项) 的公共零点 = ζ 零点。

Re s > 1 的级数事实 (解析延拓后成为代数拆分):
  ζ(s) = Σ_{2∤n} 1/n^s + Σ_{2∣n} 1/n^s
  Σ_{2∣n} 1/n^s = 2⁻ˢ·ζ(s)          (偶部分, 2 的倍数项)
  Σ_{2∤n} 1/n^s = (1 - 2⁻ˢ)·ζ(s)    (奇部分, 非 2 倍数项)

对任意基点 p ≠ 0 成立 (p 素数时 = p-adic 拆分; p = 2 即奇偶拆分):
  ζ = O_p + E_p,  O_p = (1-p⁻ˢ)ζ,  E_p = p⁻ˢζ
  零点 = 两部分公共零点: ζ = 0 ⟺ O_p = 0 ∧ E_p = 0
  奇部分独有零点 (非公共): p⁻ˢ = 1 ⟺ s·ln p ∈ 2πiℤ ⟺ Re s = 0 (素数因子零点, 虚轴)

"奇侧偶侧只在 1/2 相交" = RH 本身 (不可预设); 可证的是:
  交点 (奇偶公共零点) = ζ 零点, 且 ⊆ 临界带 (观测 V + 临界带钉死)。

English: Prime-factor zero theorem: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi. Zeros of every prime factor (1-p^{-s}) all lie on Re(s) = 0 (pure imaginary axis) — the exact content of 'prime complex-base decomposition' (Complex.exp_eq_one_iff). (Duplicate: same theorem in proof.lean; isolated file self-contained.) -/

noncomputable section

open scoped BigOperators
open Complex

namespace RiemannUnifiedObservation

/-- 素数因子零点定理: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi。
    每个素数因子 (1-p^{-s}) 的零点全在 Re(s) = 0 上 (纯虚轴) —
    "素数复数进制分解"的精确内容 (Complex.exp_eq_one_iff)。
    (副本: proof.lean 同定理, 隔离文件自包含依赖) 
English: Prime-factor zero theorem: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi. Zeros of every prime factor (1-p^{-s}) all lie on Re(s) = 0 (pure imaginary axis) — the exact content of 'prime complex-base decomposition' (Complex.exp_eq_one_iff). (Duplicate: same theorem in proof.lean; isolated file self-contained.) -/
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
    -- 从 hn: log p · (-s) = n·2πi 推出 s·log p = (-n)·2πi = ↑(-n)·2πi
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
    -- 目标: log p · (-s) = ↑(-k)·2πi; 从 hk: s·log p = k·2πi
    calc
      Complex.log (p : ℂ) * (-s) = -((s) * Complex.log (p : ℂ)) := by ring
      _ = -((k : ℂ) * (2 * ↑Real.pi * Complex.I)) := by rw [hk]
      _ = (-(k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-k) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]

/-- 拆分恒等式: ζ = 奇部分 + 偶部分 (任意基点 p ≠ 0, 代数拆分). 
English: Splitting identity: ζ = odd part + even part (any basepoint p ≠ 0, algebraic splitting). -/
theorem zeta_eq_odd_add_even (p : ℂ) (s : ℂ) :
    riemannZeta s = (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s
      + (p : ℂ) ^ (-s : ℂ) * riemannZeta s := by
  ring

/-- 零点 = 奇偶公共零点: ζ(s) = 0 ⟺ O_p(s) = 0 ∧ E_p(s) = 0 (任意基点 p ≠ 0).
    奇侧偶侧同时为 0 (用户: "奇偶同时为 0") 的精确形式. 
English: Zeros = common zeros of odd and even parts: ζ(s) = 0 ⟺ O_p(s) = 0 ∧ E_p(s) = 0 (any basepoint p ≠ 0). Exact form of 'odd and even sides simultaneously 0'. -/
theorem zeta_eq_zero_iff_p_split {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    riemannZeta s = 0 ↔
      (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ∧
        (p : ℂ) ^ (-s : ℂ) * riemannZeta s = 0 := by
  constructor
  · intro hz
    constructor <;> simp [hz]
  · intro h
    have hpz : (p : ℂ) ^ (-s : ℂ) ≠ 0 := by
      exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hp)
    -- 偶部分 E_p = p⁻ˢ·ζ = 0 且 p⁻ˢ ≠ 0 ⟹ ζ = 0 (ℂ 是域)
    exact (mul_eq_zero.mp h.2).resolve_left hpz

/-- 奇部分零点分解: O_p = 0 ⟺ ζ = 0 ∨ p⁻ˢ = 1 (ℂ 域乘法为零).
    奇部分的零点 = ζ 零点 ∪ 素数因子零点. 
English: Odd-part zero decomposition: O_p = 0 ⟺ ζ = 0 ∨ p⁻ˢ = 1 (field multiplication zero in ℂ). Zeros of the odd part = ζ zeros ∪ prime-factor zeros. -/
theorem p_split_mul_zero_iff {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ↔
      riemannZeta s = 0 ∨ (p : ℂ) ^ (-s : ℂ) = 1 := by
  rw [mul_eq_zero, sub_eq_zero]
  tauto

/-- 奇部分独有零点全在虚轴 (p = 2 奇偶拆分):
    若 O₂(s) = 0 且 ζ(s) ≠ 0, 则 2⁻ˢ = 1 ⟹ s·ln 2 ∈ 2πiℤ ⟹ Re s = 0.
    即奇偶拆分的非公共零点不进入临界带 — 交点只能来自 ζ 本身. 
English: Odd-part-only zeros all on the imaginary axis (p = 2 odd-even split): if O₂(s) = 0 and ζ(s) ≠ 0, then 2⁻ˢ = 1 ⟹ s·ln 2 ∈ 2πiℤ ⟹ Re s = 0. Non-common zeros of the odd-even split never enter the critical strip — intersections can only come from ζ itself. -/
theorem odd_part_extra_zero_on_imag_axis (s : ℂ) :
    (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 → riemannZeta s ≠ 0 → s.re = 0 := by
  intro h hz
  have hcases := (p_split_mul_zero_iff (p := (2 : ℂ)) (by norm_num) s).mp h
  rcases hcases with hz' | hone
  · exact False.elim (hz hz')
  · -- 2⁻ˢ = 1 ⟹ 1 - 2⁻ˢ = 0 ⟹ (prime_factor_zero 2) ∃k, s·log 2 = 2πik
    have hsub : 1 - (2 : ℂ) ^ (-s : ℂ) = 0 := sub_eq_zero.mpr hone.symm
    have hp2 : Nat.Prime 2 := Nat.prime_two
    have hpf := (prime_factor_zero 2 hp2 s).mp hsub
    rcases hpf with ⟨k, hk⟩
    -- Re(s·log 2) = Re(k·2πi) = 0; log 2 是实数且非零 ⟹ s.re = 0
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    have hre0 : (s * Complex.log (2 : ℂ)).re = 0 := by
      have hk' : s * Complex.log ((2 : ℂ)) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        simpa using hk
      rw [hk']
      simp
    have hre' : s.re * Real.log 2 = 0 := by
      calc
        s.re * Real.log 2 = (s * (Real.log 2 : ℂ)).re := by
          rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]
        _ = 0 := by rw [← hlog, hre0]
    have hl2 : Real.log 2 ≠ 0 := by
      exact (Real.log_ne_zero).mpr (by norm_num)
    exact (mul_eq_zero.mp hre').resolve_right hl2

end RiemannUnifiedObservation
