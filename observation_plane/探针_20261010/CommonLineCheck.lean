/-
  公共垂线等价核对 (2026-10-10)。

  用户命题 (原话要点): "并不需要一个完整的刚性生成过程; 只要有一个弱证明,
  证明非平凡零点都在同一条垂线上就好, 对吧?"

  机证结论: 该命题 ⟺ RiemannHypothesis (RH 本身) — 不是比 RH 更弱的目标;
  任何对它的证明自动是 RH 的证明 (机证等价, 本文件)。

  机制 (两步, 全部机证):
    ① 反射配对 (函数方程): 带内离线零点 z 的反射 1−z 是另一个带内零点,
       实部从 σ 变到 1−σ (PrimeCircle.ZetaZeroReflection.zeta_zero_offline_pair,
       proof.lean:676);
    ② 若全部带内零点共实部 σ 而 σ ≠ 1/2, 则 z 与 1−z 给出两个实部不同的零点,
       矛盾 ⟹ σ = 1/2; 再经 rh_iff_all_zeros_on_line_in_strips (proof.lean:4161)
       收尾 (该等价件本身即"RH ⟺ 带内零点全在 Re=1/2")。
    反向: RH ⟹ 公共线取 σ = 1/2 (显然)。

  边界 (陈述口径):
    · 量词是本质: 固定 T 的版本 (∃σ_T, 仅 |im| ≤ T 的零点共线) 是有限弱命题 —
      数值上已知 (前 10^13 个零点在线), 不推 RH, 也未被此件覆盖;
      本件证的是 ∀T 全称版 (T 截断版见 common_line_strip_iff_RH)。
    · 本件 = 逻辑核对 (等价改写): 不产生新约束, 缺口② (带内刚性/发生器) 不变;
      不声称 RH 已证/可证。
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

import Formal.ZeroRelative.proof

noncomputable section

namespace CommonLineProbe

/-- 公共垂线 (无截断版) ⟺ RH: 存在 σ, 使全部带内零点满足 Re = σ。
    Common-line form iff RH: ∃σ, every in-strip zero has real part σ. -/
theorem common_line_iff_RH :
    (∃ σ : ℝ, ∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 → z.re = σ)
      ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply PrimeCircle.RiemannUnifiedObservation.rh_iff_all_zeros_on_line_in_strips.mpr
    intro T _hT z hz h0 h1 _him
    rcases h with ⟨σ, hσ⟩
    have hzσ : z.re = σ := hσ z hz h0 h1
    -- 迫使 σ = 1/2: 否则反射配对给出实部 1−σ 的第二个带内零点
    have hσhalf : σ = 1 / 2 := by
      by_contra hne
      -- 边界提升: 闭带条件 + 无零 ⟹ 开带 (Re=0 与 Re=1 均无零点)
      have hz0 : 0 < z.re := by
        rcases lt_or_eq_of_le h0 with hlt | heq
        · exact hlt
        · exfalso
          by_cases hz00 : z = 0
          · subst hz00
            rw [riemannZeta_zero] at hz
            norm_num at hz
          · exact (PrimeCircle.RiemannUnifiedObservation.riemannZeta_ne_zero_of_re_eq_zero
              z heq.symm hz00) hz
      have hz1 : z.re < 1 := by
        rcases lt_or_eq_of_le h1 with hlt | heq
        · exact hlt
        · exfalso
          exact (riemannZeta_ne_zero_of_one_le_re (s := z) (le_of_eq heq.symm)) hz
      have hstrip : 0 < z.re ∧ z.re < 1 := ⟨hz0, hz1⟩
      have htriv : ∀ n : ℕ, z ≠ -(n : ℂ) := by
        intro n hn
        have hre : z.re = -(n : ℝ) := by
          have h' := congrArg Complex.re hn
          simpa using h'
        have hnge : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hone : z ≠ 1 := by
        intro hzz
        have h' := congrArg Complex.re hzz
        rw [Complex.one_re] at h'
        linarith
      have hoff : z.re ≠ 1 / 2 := by
        rw [hzσ]
        exact hne
      obtain ⟨-, hzref, hre0, hre1⟩ :=
        PrimeCircle.ZetaZeroReflection.zeta_zero_offline_pair hz hstrip htriv hone hoff
      -- 反射点也在带内 ⟹ 也满足公共实部 σ; 但它的实部 = 1 − σ
      have hrefσ : (1 - z).re = σ :=
        hσ (1 - z) hzref (le_of_lt hre0) (le_of_lt hre1)
      have hrefval : (1 - z).re = 1 - z.re := by
        rw [Complex.sub_re, Complex.one_re]
      exact hne (by linarith [hzσ, hrefσ, hrefval])
    rw [hzσ, hσhalf]
  · intro hRH
    refine ⟨1 / 2, ?_⟩
    intro z hz h0 h1
    exact PrimeCircle.RiemannUnifiedObservation.rh_iff_all_zeros_on_line_in_strips.mp hRH
      |z.im| (abs_nonneg z.im) z hz h0 h1 le_rfl

/-- 公共垂线 (T 截断全称版) ⟺ RH — 与 rh_iff_all_zeros_on_line_in_strips 的
    RHS 同形。注意: 对 ∀T 全称是本质; 把 T 固定即降为有限弱命题 (不推 RH)。
    Stripped common-line form (∀T) iff RH. -/
theorem common_line_strip_iff_RH :
    (∃ σ : ℝ, ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 →
      |z.im| ≤ T → z.re = σ)
      ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply common_line_iff_RH.mp
    rcases h with ⟨σ, hσ⟩
    exact ⟨σ, fun z hz h0 h1 =>
      hσ |z.im| (abs_nonneg z.im) z hz h0 h1 le_rfl⟩
  · intro hRH
    refine ⟨1 / 2, ?_⟩
    intro T hT z hz h0 h1 him
    exact PrimeCircle.RiemannUnifiedObservation.rh_iff_all_zeros_on_line_in_strips.mp
      hRH T hT z hz h0 h1 him

end CommonLineProbe
