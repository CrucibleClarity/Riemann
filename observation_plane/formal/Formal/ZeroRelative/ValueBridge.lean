import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.Linarith

import Formal.ZeroRelative.proof
import Formal.ZeroRelative.FoldObservation
import Formal.ZeroRelative.zeta_argument_multiplicity_iso

open Metric
open Complex

noncomputable section

namespace ValueBridge


/-! ## 值桥链条重建 (annals_v3 包, 2026-08-27)

旧骨架 (proof_v3_1.lean) 在 v3 旧副本; 本文件在论文包内重新机证
值桥的计数骨架, 并接入 FoldObservation 的八点签名.
- count_eq_iff_all_on_line: 计数一致 ⟺ 离线空 (值桥计数核心)
- rh_iff_N0_eq_N: RH ⟺ 线上零点数 = 带内零点数
- quota_contradiction: 配额矛盾收尾判定
- offline_implies_count_excess: 离线 ρ ⟹ 计数严格小 (输入侧)
- eight_point_signature_implies_count_excess: 八点签名接入计数链 -/

/-- **计数一致 ⟺ 离线空**: 带内零点全在临界线上 ⟺ 线上零点数 = 带内
    零点总数 (Nat.card) — 值桥的计数骨架: 离线 ρ ⟹ 在线集 ⊂ 带内集
    (真子集) ⟹ 计数严格小 ⟹ 计数不一致 (反证方向, 已机证).
    Counting agreement iff no off-line zero: the counting skeleton of
    the value bridge. -/
theorem count_eq_iff_all_on_line (T : ℝ) :
    (∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ T → z.re = 1 / 2)
      ↔ Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) =
          Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) := by
  constructor
  · intro hzeq
    have heq : ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
        : Set ℂ) = {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨hzA, hzB, hzC, hzD, hzE⟩
        exact ⟨hzA, hzC, hzD, hzE⟩
      · intro hz
        rcases hz with ⟨hzA, hzC, hzD, hzE⟩
        exact ⟨hzA, hzeq z hzA hzC hzD hzE, hzC, hzD, hzE⟩
    rw [heq]
  · intro hcard
    intro z hz h0 h1 him
    by_contra hne
    have hzin : z ∈ ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} : Set ℂ) :=
      ⟨hz, h0, h1, him⟩
    have hsub : ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
        : Set ℂ) ⊂ {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases hx with ⟨hxA, hxB, hxC, hxD, hxE⟩
        exact ⟨hxA, hxC, hxD, hxE⟩
      · intro hdisj
        have : z ∈ ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
            : Set ℂ) := hdisj hzin
        exact hne this.2.1
    have hcardlt : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) <
        Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) := by
      exact (Set.Finite.card_lt_card
        (s := {z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T})
        (t := {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T})
        (PrimeCircle.RiemannUnifiedObservation.RiemannUnifiedObservation.RiemannUnifiedObservation.zeta_zeros_finite_in_strip T) hsub)
    linarith

/-- **RH ⟺ 计数一致**: RH ⟺ 带内零点全在线 (T1) ⟺ 线上零点数 = 带内
    零点总数 (count_eq 组合, 命名).
    RH iff counting agreement: the named combination of the equivalent
    reduction and the counting skeleton. -/
theorem rh_iff_N0_eq_N :
    RiemannHypothesis ↔
      ∀ T : ℝ, 0 ≤ T →
        Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) =
          Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) := by
  constructor
  · intro hRH T hT
    exact (count_eq_iff_all_on_line T).mp ((PrimeCircle.RiemannUnifiedObservation.rh_iff_all_zeros_on_line_in_strips.mp hRH) T hT)
  · intro hcard
    exact (PrimeCircle.RiemannUnifiedObservation.rh_iff_all_zeros_on_line_in_strips.mpr)
      (fun T hT => (count_eq_iff_all_on_line T).mpr (hcard T hT))

/-- **配额矛盾**: K = N ∧ N > K ⟹ False — 计数超额与配额一致的收尾
    判定 (Hardy 反证收尾形态).
    Quota contradiction: the closing judgement of the counting excess
    against the agreed quota. -/
theorem quota_contradiction {K N : ℕ} (heq : K = N) (hgt : N > K) : False := by
  linarith

/-- **离线 ⟹ 计数超额**: 带内零点 ρ 离线 (href) ⟹ 在线集 ⊂ 带内集
    (真子集) ⟹ Nat.card 严格小 — 值桥的输入侧 (离线零点进入计数链). -/
theorem offline_implies_count_excess {T : ℝ} {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (him : |ρ.im| ≤ T)
    (href : ρ.re ≠ 1 / 2) :
    Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) <
      Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) := by
  have hzin : ρ ∈ ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} : Set ℂ) :=
    ⟨hρ, h0, h1, him⟩
  have hsub : ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
      : Set ℂ) ⊂ {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with ⟨hxA, hxB, hxC, hxD, hxE⟩
      exact ⟨hxA, hxC, hxD, hxE⟩
    · intro hdisj
      have : ρ ∈ ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
          : Set ℂ) := hdisj hzin
      exact href this.2.1
  exact (Set.Finite.card_lt_card
    (s := {z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T})
    (t := {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T})
    (PrimeCircle.RiemannUnifiedObservation.RiemannUnifiedObservation.RiemannUnifiedObservation.zeta_zeros_finite_in_strip T) hsub)

/-- **八点签名接入计数链**: 离线 ρ (带内, 临界圆内) 的八点签名 (ζ 侧
    塌缩 + p 侧显式 + 反演点还原, FoldObservation 机证) ⟹ 在线 ⊂ 带内
    (真子集) ⟹ 计数严格小 — 观测签名进入值桥计数链: 值桥的输入侧 =
    八点签名 (观测), 骨架 = 计数严格小 (本文件), 收尾 = 配额矛盾.
    Eight-point signature enters the counting chain: the complete
    observation of the off-line zero implies the strict counting
    shortfall — the input side of the value bridge. -/
theorem eight_point_signature_implies_count_excess {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hcirc : ‖ρ - 1 / 2‖ < 1 / 2) (href : ρ.re ≠ 1 / 2)
    (hρ : riemannZeta ρ = 0) :
    Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ |ρ.im|}) <
      Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ |ρ.im|}) := by
  -- 八点签名 (ζ 侧塌缩 + 离线 + p 侧显式 + 反演点还原) — 其中离线即 href
  have hsig := FoldObservation.eight_point_observation hρ0 hρ1 hcirc href hρ
  -- 接入计数链: 离线 ⟹ 计数严格小
  have h0 : 0 ≤ ρ.re := le_of_lt hρ0
  have h1 : ρ.re ≤ 1 := le_of_lt hρ1
  exact offline_implies_count_excess (T := |ρ.im|) hρ h0 h1 le_rfl href


/-! ## 相位侧圈数配额 (翻转计数族重建, 纯代数 0 自动化) -/

/-- **重数和**: (Σ m·2π)/2π = Σm — 围道-计数桥的求和核心
    (每零点重数 m 贡献 m·2π, 除 2π 得圈数). -/
theorem lift_sum_over (K : ℕ) (m : Fin K → ℕ) :
    (∑ k : Fin K, ((m k : ℕ) : ℝ) * (2 * Real.pi)) / (2 * Real.pi)
      = ∑ k : Fin K, ((m k : ℕ) : ℝ) := by
  calc
    (∑ k : Fin K, ((m k : ℕ) : ℝ) * (2 * Real.pi)) / (2 * Real.pi)
        = ∑ k : Fin K, (((m k : ℕ) : ℝ) * (2 * Real.pi)) / (2 * Real.pi) := by
          rw [Finset.sum_div]
    _ = ∑ k : Fin K, ((m k : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [mul_div_cancel_right₀ (a := (m k : ℝ)) (b := 2 * Real.pi)
        (Real.two_pi_pos.ne')]

/-- **围道-计数桥**: 闭路径相位提升分解为每零点贡献 (重数 × 2π;
    连接段贡献 0 已吸收) ⟹ 圈数 = 重数和 — 相位侧圈数配额的骨架
    (输入 hseg: 零点分解, 分析侧; hclosed: 闭合整数性). -/
theorem contour_count_bridge {K : ℕ} (m : Fin K → ℕ) (L : ℝ)
    (_hclosed : ∃ n : ℤ, L = (n : ℝ) * (2 * Real.pi))
    (hseg : L = ∑ k : Fin K, ((m k : ℕ) : ℝ) * (2 * Real.pi)) :
    L / (2 * Real.pi) = ∑ k : Fin K, ((m k : ℕ) : ℝ) := by
  rw [hseg]
  exact lift_sum_over K m

/-- **重数和 ≥ 零点数 (全奇阶)**: m_k 全奇 ⟹ 每 m_k ≥ 1 ⟹ Σ m_k ≥ K
    — 翻转数 (K) ≤ 重数和 (Σ m_k) 的代数骨架 (每翻转至少一圈). -/
theorem odd_order_winding_lower {K : ℕ} (m : Fin K → ℕ)
    (hodd : ∀ k : Fin K, Odd (m k)) :
    (K : ℝ) ≤ ∑ k : Fin K, ((m k : ℕ) : ℝ) := by
  have hge : ∀ k : Fin K, (1 : ℝ) ≤ ((m k : ℕ) : ℝ) := by
    intro k
    have hm : 1 ≤ m k := Nat.succ_le_of_lt (Odd.pos (hodd k))
    exact_mod_cast hm
  have hsum : (∑ k : Fin K, (1 : ℝ)) ≤ ∑ k : Fin K, ((m k : ℕ) : ℝ) := by
    exact Finset.sum_le_sum (fun k _hk => hge k)
  have hsum1 : (∑ k : Fin K, (1 : ℝ)) = (K : ℝ) := by
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    rw [mul_one]
    rw [Finset.card_fin]
  rwa [hsum1] at hsum

/-- **翻转数 ≤ 圈数**: 全奇阶 (每零点奇阶 ⟹ 一次翻转) ⟹
    翻转数 K ≤ 圈数 L/2π = Σm_k (odd_order_winding_lower + 桥).
    Hardy 翻转计数的组合侧: 翻转不超圈数 (每翻转至少一圈). -/
theorem flip_le_winding {K : ℕ} (m : Fin K → ℕ) (L : ℝ)
    (hodd : ∀ k : Fin K, Odd (m k))
    (hclosed : ∃ n : ℤ, L = (n : ℝ) * (2 * Real.pi))
    (hseg : L = ∑ k : Fin K, ((m k : ℕ) : ℝ) * (2 * Real.pi)) :
    (K : ℝ) ≤ L / (2 * Real.pi) := by
  have hlower : (K : ℝ) ≤ ∑ k : Fin K, ((m k : ℕ) : ℝ) :=
    odd_order_winding_lower (K := K) m hodd
  have hw := contour_count_bridge (K := K) m L hclosed hseg
  rwa [← hw] at hlower

/-- **圈数 = 零点数 (全简单)**: 提升差 L 分解为 K 个简单零点
    每点贡献 1·2π (hseg) ⟹ L/2π = K — 翻转计数 = 零点数的组合核心
    (每零点一圈). -/
theorem simple_zero_winding_count {K : ℕ} (L : ℝ)
    (_hclosed : ∃ n : ℤ, L = (n : ℝ) * (2 * Real.pi))
    (hseg : L = ∑ k : Fin K, (1 : ℝ) * (2 * Real.pi)) :
    L / (2 * Real.pi) = (K : ℝ) := by
  rw [hseg]
  calc
    (∑ k : Fin K, (1 : ℝ) * (2 * Real.pi)) / (2 * Real.pi)
        = ∑ k : Fin K, ((1 : ℝ) * (2 * Real.pi)) / (2 * Real.pi) := by
          rw [Finset.sum_div]
    _ = ∑ k : Fin K, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [one_mul]
      exact div_self (Real.two_pi_pos.ne')
    _ = (K : ℝ) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      rw [mul_one]
      rw [Finset.card_fin]

/-- **全简单: 翻转数 = 圈数 = 零点数 (上下夹)**: m ≡ 1 时
    K ≤ L/2π (flip_le_winding) 且 L/2π = K (simple_zero_winding_count)
    — 翻转计数与围道计数夹逼到同一整数 K — 相位侧圈数配额
    (分析侧输入 hseg 显式). -/
theorem flip_eq_winding_simple {K : ℕ} (L : ℝ)
    (hclosed : ∃ n : ℤ, L = (n : ℝ) * (2 * Real.pi))
    (hseg : L = ∑ k : Fin K, (1 : ℝ) * (2 * Real.pi)) :
    (K : ℝ) ≤ L / (2 * Real.pi) ∧ L / (2 * Real.pi) = (K : ℝ) := by
  constructor
  · have hseg' : L = ∑ k : Fin K, (((1 : ℕ) : ℝ)) * (2 * Real.pi) := by
      rw [← Nat.cast_one] at hseg
      exact hseg
    exact flip_le_winding (K := K) (m := fun _ => 1) L
      (fun _ => ⟨0, rfl⟩)
      hclosed
      hseg'
  · exact simple_zero_winding_count (K := K) L hclosed hseg

/-- **翻转跳求和**: K 次翻转 (每跳 π) 的总跳 = K·π — 翻转的
    π 跳组合求和. -/
theorem flip_jump_sum (K : ℕ) :
    (∑ k : Fin K, (Real.pi : ℝ)) = (K : ℝ) * Real.pi := by
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Finset.card_fin]

/-- **双倍翻转跳**: 2θ 语言下 K 次翻转的总 π 跳 = K·2π. -/
theorem flip_jump_sum_two (K : ℕ) :
    (∑ k : Fin K, (2 * Real.pi : ℝ)) = (K : ℝ) * (2 * Real.pi) := by
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Finset.card_fin]


/-! ## hseg 分析输入接入 (幅角原理 ζ 实例: 圈数配额的分析侧) -/

/-- **圈数配额 (全简单, 幅角原理 ζ 实例)**: K 个全简单带内零点,
    全局围道 ∮_Γ ζ'/ζ 分解为每零点小圈 (hΓ 挖洞) ⟹
    ∮_Γ/(2πi) = K — 每零点一圈: 相位侧圈数配额的 hseg 分析侧
    (幅角原理内容, m≡1 实例化 contour_total_bridge; 输入 hExp/hne/
    hΓ 显式, 由局部展开/孤立零点/环域 Goursat 给出). -/
theorem zeta_winding_quota_simple {K : ℕ} (s : Fin K → ℂ) {c : ℂ} {RΓ : ℝ}
    (hs : ∀ k : Fin K, s k ≠ 1)
    (hz : ∀ k : Fin K, riemannZeta (s k) = 0)
    {R : Fin K → ℝ} (hR : ∀ k : Fin K, 0 < R k)
    (hR1 : ∀ k : Fin K, ball (s k) (R k) ⊆ ({1}ᶜ : Set ℂ))
    (hExp : ∀ k : Fin K, ∃ g : ℂ → ℂ,
      (∀ z ∈ ball (s k) (R k), riemannZeta z = (z - s k) ^ (1 : ℕ) * g z) ∧
      g (s k) ≠ 0 ∧ AnalyticOn ℂ g (ball (s k) (R k)))
    (hne : ∀ k : Fin K, ∀ z ∈ ball (s k) (R k), z ≠ s k → riemannZeta z ≠ 0)
    (hΓ : (∮ z in C(c, RΓ), deriv riemannZeta z / riemannZeta z) =
      ∑ k : Fin K, (∮ z in C(s k, R k / 2), deriv riemannZeta z / riemannZeta z)) :
    (∮ z in C(c, RΓ), deriv riemannZeta z / riemannZeta z) / (2 * ↑Real.pi * Complex.I) = (K : ℂ) := by
  have htot := RiemannUnifiedObservation.contour_total_bridge (s := s) (m := fun _ => 1)
    (c := c) (RΓ := RΓ) hs hz hR hR1 hExp hne hΓ
  -- ∮ = (Σ 1:ℂ)·2πi = (K:ℂ)·2πi
  have hsum : (∑ k : Fin K, ((1 : ℕ) : ℂ)) = (K : ℂ) := by
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    rw [Finset.card_fin]
    norm_num
  rw [htot]
  calc
    ((∑ k : Fin K, ((1 : ℕ) : ℂ)) * (2 * ↑Real.pi * Complex.I)) / (2 * ↑Real.pi * Complex.I)
        = ∑ k : Fin K, ((1 : ℕ) : ℂ) := by
          rw [mul_div_cancel_right₀ (a := ∑ k : Fin K, ((1 : ℕ) : ℂ))
            (b := 2 * ↑Real.pi * Complex.I)
            (by
              have hpi : (2 * ↑Real.pi : ℂ) ≠ 0 := by
                exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
                  (by exact_mod_cast Real.pi_ne_zero)
              exact mul_ne_zero hpi (by norm_num : (Complex.I : ℂ) ≠ 0))]
    _ = (K : ℂ) := hsum


/-! ## 值桥组装 (约束定理: 翻转数 = 圈数 ⟹ 无离线零点) -/

/-- **值桥组装 (约束定理)**: 翻转数 = 在线零点数 (hN0, 翻转计数侧) ∧
    圈数 = 带内零点数 (hN, 幅角原理侧) ∧ 翻转数 = 圈数 (hflip_eq,
    单条开放假设 — 计数形式的 RH 等价) ⟹ 无离线零点 (计数一致,
    count_eq_iff_all_on_line.mpr) — 值桥的完整形态: 三侧组装成
    单条假设的推论.
    Value bridge assembly: flip count = winding count (single open
    hypothesis) implies no off-line zero, via the counting bridges. -/
theorem value_bridge_assembly {T : ℝ} {K_flip K_wind : ℕ}
    (hN0 : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) = K_flip)
    (hN : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) = K_wind)
    (hflip_eq : K_flip = K_wind) :
    ∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ T → z.re = 1 / 2 := by
  have hcard : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) =
      Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) := by
    rw [hN0, hN]
    exact hflip_eq
  exact (count_eq_iff_all_on_line T).mpr hcard

/-- **值桥矛盾 (完整形态)**: 翻转数 = 圈数 ∧ 离线零点 ρ 存在 ⟹ False —
    离线 ρ ⟹ 计数严格小 (offline_implies_count_excess: N₀ < N) ⟹
    K_flip < K_wind (经计数桥) ⟹ 与 K_flip = K_wind 矛盾
    (quota_contradiction) — 值桥 = 翻转数 = 圈数 假设下的反证收尾.
    Value bridge contradiction: flip count = winding count together
    with an off-line zero is false — the quota closing. -/
theorem value_bridge_contradiction {T : ℝ} {K_flip K_wind : ℕ}
    (hN0 : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) = K_flip)
    (hN : Nat.card ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}) = K_wind)
    (hflip_eq : K_flip = K_wind)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1)
    (him : |ρ.im| ≤ T) (href : ρ.re ≠ 1 / 2) : False := by
  have hlt := offline_implies_count_excess (T := T) hρ h0 h1 him href
  have hlt' : K_flip < K_wind := by
    rw [hN0, hN] at hlt
    exact hlt
  exact quota_contradiction (K := K_flip) (N := K_wind) hflip_eq hlt'


/-! ## η 圈数分解 (约束的新呈现: 圈数(ζ) = 圈数(η)) -/

/-- **对数导乘积分解**: (f·g)'/(f·g) = f'/f + g'/g (可导 + 乘积非零)
    — 对数导的乘法线性 (η = 因子·ζ 的拆分核心). -/
theorem logDeriv_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hfg : f z * g z ≠ 0) :
    deriv (fun w => f w * g w) z / (f z * g z) = deriv f z / f z + deriv g z / g z := by
  have hdm := deriv_mul (𝕜 := ℂ) hf hg
  have hfz : f z ≠ 0 := (mul_ne_zero_iff.mp hfg).1
  have hgz : g z ≠ 0 := (mul_ne_zero_iff.mp hfg).2
  have hfg_eq : f * g = fun w => f w * g w := by
    funext w
    rfl
  have hdm' : deriv (fun w => f w * g w) z = deriv f z * g z + f z * deriv g z := by
    rw [← hfg_eq]
    exact hdm
  rw [hdm']
  field_simp [hfz, hgz]

/-- **η 对数导拆分**: η'/η = ζ'/ζ + 因子'/因子 (η = (1−2^{1−s})·ζ,
    对数导乘法线性) — 圈数(η) = 圈数(ζ) + 因子圈数; 因子带内无零
    ⟹ 因子圈数 = 0 (下一步). -/
theorem eta_logDeriv_split (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hζ : riemannZeta s ≠ 0) :
    deriv (fun w => (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w) s /
        ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      = deriv (fun w => 1 - (2 : ℂ) ^ (1 - w)) s / (1 - (2 : ℂ) ^ (1 - s))
      + deriv riemannZeta s / riemannZeta s := by
  have hfac : DifferentiableAt ℂ (fun w => 1 - (2 : ℂ) ^ (1 - w)) s := by
    -- cpow 可导 (底 2 ∈ slitPlane: arg 2 = 0 ≠ π) + 线性组合
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      have h0 : (2 : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by norm_num)
      rw [h0]
      exact Real.pi_ne_zero.symm
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) s := by
      fun_prop
    fun_prop
  have hzeta : DifferentiableAt ℂ riemannZeta s := by
    exact analyticOn_riemannZeta.analyticOn.analyticAt
      (isOpen_compl_singleton.mem_nhds (by
        rw [Set.mem_compl_singleton_iff]
        intro h1
        have : s.re = 1 := by rw [h1]; simp
        linarith [hs1])) |>.differentiableAt
  have hfac0 : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := FoldObservation.eta_factor_ne_zero_of_strip hs0 hs1
  have hfg : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0 := mul_ne_zero hfac0 hζ
  exact logDeriv_mul (f := fun w => 1 - (2 : ℂ) ^ (1 - w)) (g := riemannZeta)
    hfac hzeta hfg


/-! ## 因子解析性 + 矩形 Goursat (因子圈数 = 0) -/

/-- **η 因子解析**: 1 − 2^{1−s} 处处解析 — 2^{1−s} = exp((1−s)·log 2)
    (cpow_def_of_ne_zero, 2 ≠ 0) + exp 复合解析 (AnalyticAt.cexp') +
    仿射解析. -/
theorem eta_factor_analytic (x : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => 1 - (2 : ℂ) ^ (1 - t)) x := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hpow : AnalyticAt ℂ (fun t : ℂ => (2 : ℂ) ^ (1 - t)) x := by
    have h_eq : (fun t : ℂ => (2 : ℂ) ^ (1 - t)) =
        fun t => Complex.exp (Complex.log (2 : ℂ) * (1 - t)) := by
      funext t
      exact Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (1 - t)
    rw [h_eq]
    have haff : AnalyticAt ℂ (fun t : ℂ => Complex.log (2 : ℂ) * (1 - t)) x := by
      fun_prop
    exact haff.cexp'
  have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x := by
    fun_prop
  exact hone.sub hpow

/-- **η 因子矩形 Goursat**: 因子 1−2^{1−s} 在带内矩形无零 (hstrip) ⟹
    因子对数导的矩形边界积分 = 0 — 因子圈数 = 0 (η 圈数分解的
    分析件: 圈数(ζ) = 圈数(η), 因子不贡献圈数). -/
theorem eta_factor_rect_goursat (z w : ℂ)
    (hstrip : ∀ x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)),
      0 < x.re ∧ x.re < 1) :
    (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + z.im * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I)))) -
      (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + w.im * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I)))) +
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re w + y * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I)))) -
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re z + y * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I)))) = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (f := fun x => deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) x / (1 - (2 : ℂ) ^ (1 - x)))
    (z := z) (w := w) (s := ∅)
  · simp
  · intro x hx
    have hxst := hstrip x hx
    have hfac0 : 1 - (2 : ℂ) ^ (1 - x) ≠ 0 := FoldObservation.eta_factor_ne_zero_of_strip hxst.1 hxst.2
    have hana : AnalyticAt ℂ (fun t => 1 - (2 : ℂ) ^ (1 - t)) x := eta_factor_analytic x
    exact ((hana.deriv.continuousAt).div hana.continuousAt hfac0).continuousWithinAt
  · intro x hx
    rcases hx with ⟨hxr, hxr'⟩
    have hxcb : x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
      exact ⟨Set.Ioo_subset_Icc_self hxr.1, Set.Ioo_subset_Icc_self hxr.2⟩
    have hxst := hstrip x hxcb
    have hfac0 : 1 - (2 : ℂ) ^ (1 - x) ≠ 0 := FoldObservation.eta_factor_ne_zero_of_strip hxst.1 hxst.2
    have hana : AnalyticAt ℂ (fun t => 1 - (2 : ℂ) ^ (1 - t)) x := eta_factor_analytic x
    exact ((hana.deriv).div hana hfac0).differentiableAt


/-! ## 路径连续性引理 (圈数等式的可积性义务) -/

/-- **η 路径连续 (x 边)**: η'/η 沿水平边连续 (η 解析 + 分母非零). -/
lemma eta_path_continuous_x (z w : ℂ) (c : ℂ)
    (hstrip : ∀ x ∈ Set.uIcc z.re w.re, 0 < (x + c * Complex.I).re ∧ (x + c * Complex.I).re < 1)
    (hζne : ∀ x ∈ Set.uIcc z.re w.re, riemannZeta (x + c * Complex.I) ≠ 0) :
    ContinuousOn (fun x : ℝ => deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + c * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (x + c * Complex.I))) * riemannZeta (x + c * Complex.I)))
      (Set.uIcc z.re w.re) := by
  intro x hx
  have hxst := hstrip x hx
  have hfac0 : 1 - (2 : ℂ) ^ (1 - (x + c * Complex.I)) ≠ 0 :=
    FoldObservation.eta_factor_ne_zero_of_strip hxst.1 hxst.2
  have hη0 : (1 - (2 : ℂ) ^ (1 - (x + c * Complex.I))) * riemannZeta (x + c * Complex.I) ≠ 0 :=
    mul_ne_zero hfac0 (hζne x hx)
  have hana_ζ : AnalyticAt ℂ riemannZeta (x + c * Complex.I) :=
    analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds (by
      rw [Set.mem_compl_singleton_iff]
      intro h1
      have : (x + c * Complex.I).re = 1 := by rw [h1]; simp
      linarith [hxst.2]))
  have hana : AnalyticAt ℂ (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + c * Complex.I) :=
    (eta_factor_analytic (x + c * Complex.I)).mul hana_ζ
  have hlin : ContinuousAt (fun y : ℝ => (y : ℂ) + c * Complex.I) x := by fun_prop
  have hnum : ContinuousAt (fun y : ℝ => deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (y + c * Complex.I)) x := by
    change ContinuousAt ((deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t)) ∘ (fun y : ℝ => (y : ℂ) + c * Complex.I)) x
    exact hana.deriv.continuousAt.comp (f := fun y : ℝ => (y : ℂ) + c * Complex.I) hlin
  have hden : ContinuousAt (fun y : ℝ => (1 - (2 : ℂ) ^ (1 - (y + c * Complex.I))) * riemannZeta (y + c * Complex.I)) x := by
    change ContinuousAt ((fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) ∘ (fun y : ℝ => (y : ℂ) + c * Complex.I)) x
    exact hana.continuousAt.comp (f := fun y : ℝ => (y : ℂ) + c * Complex.I) hlin
  exact (hnum.div hden hη0).continuousWithinAt

/-- **η 路径连续 (y 边)**: η'/η 沿垂直边连续. -/
lemma eta_path_continuous_y (z w : ℂ) (c : ℝ)
    (hstrip : ∀ y ∈ Set.uIcc z.im w.im, 0 < (c + y * Complex.I).re ∧ (c + y * Complex.I).re < 1)
    (hζne : ∀ y ∈ Set.uIcc z.im w.im, riemannZeta (c + y * Complex.I) ≠ 0) :
    ContinuousOn (fun y : ℝ => deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (c + y * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (c + y * Complex.I))) * riemannZeta (c + y * Complex.I)))
      (Set.uIcc z.im w.im) := by
  intro y hy
  have hyst := hstrip y hy
  have hfac0 : 1 - (2 : ℂ) ^ (1 - (c + y * Complex.I)) ≠ 0 :=
    FoldObservation.eta_factor_ne_zero_of_strip hyst.1 hyst.2
  have hη0 : (1 - (2 : ℂ) ^ (1 - (c + y * Complex.I))) * riemannZeta (c + y * Complex.I) ≠ 0 :=
    mul_ne_zero hfac0 (hζne y hy)
  have hana_ζ : AnalyticAt ℂ riemannZeta (c + y * Complex.I) :=
    analyticOn_riemannZeta.analyticOn.analyticAt (isOpen_compl_singleton.mem_nhds (by
      rw [Set.mem_compl_singleton_iff]
      intro h1
      have : (c + y * Complex.I).re = 1 := by rw [h1]; simp
      linarith [hyst.2]))
  have hana : AnalyticAt ℂ (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (c + y * Complex.I) :=
    (eta_factor_analytic (c + y * Complex.I)).mul hana_ζ
  have hlin : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) y := by fun_prop
  have hnum : ContinuousAt (fun t : ℝ => deriv (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) (c + t * Complex.I)) y := by
    change ContinuousAt ((deriv (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) ∘ (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)) y
    exact hana.deriv.continuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hlin
  have hden : ContinuousAt (fun t : ℝ => (1 - (2 : ℂ) ^ (1 - (c + t * Complex.I))) * riemannZeta (c + t * Complex.I)) y := by
    change ContinuousAt ((fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) ∘ (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)) y
    exact hana.continuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hlin
  exact (hnum.div hden hη0).continuousWithinAt

/-- **因子路径连续 (x 边)**: 因子'/因子 沿水平边连续 (因子解析 + 无零). -/
lemma factor_path_continuous_x (z w : ℂ) (c : ℂ)
    (hstrip : ∀ x ∈ Set.uIcc z.re w.re, 0 < (x + c * Complex.I).re ∧ (x + c * Complex.I).re < 1) :
    ContinuousOn (fun x : ℝ => deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + c * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (x + c * Complex.I)))) (Set.uIcc z.re w.re) := by
  intro x hx
  have hxst := hstrip x hx
  have hfac0 : 1 - (2 : ℂ) ^ (1 - (x + c * Complex.I)) ≠ 0 :=
    FoldObservation.eta_factor_ne_zero_of_strip hxst.1 hxst.2
  have hana : AnalyticAt ℂ (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + c * Complex.I) :=
    eta_factor_analytic (x + c * Complex.I)
  have hlin : ContinuousAt (fun y : ℝ => (y : ℂ) + c * Complex.I) x := by fun_prop
  have hnum : ContinuousAt (fun y : ℝ => deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (y + c * Complex.I)) x := by
    change ContinuousAt ((deriv (fun t => 1 - (2 : ℂ) ^ (1 - t))) ∘ (fun y : ℝ => (y : ℂ) + c * Complex.I)) x
    exact hana.deriv.continuousAt.comp (f := fun y : ℝ => (y : ℂ) + c * Complex.I) hlin
  have hden : ContinuousAt (fun y : ℝ => 1 - (2 : ℂ) ^ (1 - (y + c * Complex.I))) x := by
    change ContinuousAt ((fun t => 1 - (2 : ℂ) ^ (1 - t)) ∘ (fun y : ℝ => (y : ℂ) + c * Complex.I)) x
    exact hana.continuousAt.comp (f := fun y : ℝ => (y : ℂ) + c * Complex.I) hlin
  exact (hnum.div hden hfac0).continuousWithinAt

/-- **因子路径连续 (y 边)**. -/
lemma factor_path_continuous_y (z w : ℂ) (c : ℝ)
    (hstrip : ∀ y ∈ Set.uIcc z.im w.im, 0 < (c + y * Complex.I).re ∧ (c + y * Complex.I).re < 1) :
    ContinuousOn (fun y : ℝ => deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (c + y * Complex.I) /
        (1 - (2 : ℂ) ^ (1 - (c + y * Complex.I)))) (Set.uIcc z.im w.im) := by
  intro y hy
  have hyst := hstrip y hy
  have hfac0 : 1 - (2 : ℂ) ^ (1 - (c + y * Complex.I)) ≠ 0 :=
    FoldObservation.eta_factor_ne_zero_of_strip hyst.1 hyst.2
  have hana : AnalyticAt ℂ (fun t => 1 - (2 : ℂ) ^ (1 - t)) (c + y * Complex.I) :=
    eta_factor_analytic (c + y * Complex.I)
  have hlin : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) y := by fun_prop
  have hnum : ContinuousAt (fun t : ℝ => deriv (fun s => 1 - (2 : ℂ) ^ (1 - s)) (c + t * Complex.I)) y := by
    change ContinuousAt ((deriv (fun s => 1 - (2 : ℂ) ^ (1 - s))) ∘ (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)) y
    exact hana.deriv.continuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hlin
  have hden : ContinuousAt (fun t : ℝ => 1 - (2 : ℂ) ^ (1 - (c + t * Complex.I))) y := by
    change ContinuousAt ((fun s => 1 - (2 : ℂ) ^ (1 - s)) ∘ (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)) y
    exact hana.continuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hlin
  exact (hnum.div hden hfac0).continuousWithinAt

/-! ## 圈数等式 (∮ζ'/ζ = ∮η'/η — η 圈数分解的最后一环) -/

/-- **圈数等式 (矩形)**: 带内矩形 (hstrip, hζne) 上
    ∮_rect ζ'/ζ = ∮_rect η'/η — 逐点对数导拆分 (η'/η = ζ'/ζ +
    因子'/因子) + 积分线性 + 因子圈数 = 0 (eta_factor_rect_goursat)
    ⟹ 圈数完全由 η (带内收敛差结构) 承载.
    Winding equality: the winding count of ζ equals that of η over an
    in-strip rectangle — the eta decomposition completed. -/
theorem zeta_rect_winding_eq_eta (z w : ℂ)
    (hstrip : ∀ x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)),
      0 < x.re ∧ x.re < 1)
    (hζne : ∀ x ∈ ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)), riemannZeta x ≠ 0) :
    (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + z.im * Complex.I) / riemannZeta (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + w.im * Complex.I) / riemannZeta (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re w + y * Complex.I) / riemannZeta (re w + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re z + y * Complex.I) / riemannZeta (re z + y * Complex.I))
    = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I))) -
      (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I))) +
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I))) -
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
        ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I))) := by
  -- 逐点拆分: ζ'/ζ = η'/η − 因子'/因子 (矩形边界上)
  have hsplit : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s ≠ 0 →
      deriv riemannZeta s / riemannZeta s
        = deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) s /
            ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        - deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) s / (1 - (2 : ℂ) ^ (1 - s)) := by
    intro s hs0 hs1 hζ
    have h := eta_logDeriv_split s hs0 hs1 hζ
    rw [h]
    ring
  -- 因子 Goursat (矩形): 因子圈数 = 0
  have hfac0_rect := eta_factor_rect_goursat z w hstrip
  -- 段 1 (底边): ∫ ζ'/ζ = ∫ η'/η − ∫ 因子'/因子
  have hseg1 :
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + z.im * Complex.I) / riemannZeta (x + z.im * Complex.I))
      = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I)))
      - (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + z.im * Complex.I) /
          (1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I)))) := by
    calc
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + z.im * Complex.I) / riemannZeta (x + z.im * Complex.I))
          = ∫ x : ℝ in z.re..w.re,
              (deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
                ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I)))
              - (deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + z.im * Complex.I) /
                (1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I)))) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hxcb : (x + z.im * Complex.I) ∈
                ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
              have hxre : (x + z.im * Complex.I).re ∈ Set.uIcc z.re w.re := by
                simpa using hx
              exact ⟨hxre, by simp⟩
            have hxst := hstrip (x + z.im * Complex.I) hxcb
            exact hsplit (x + z.im * Complex.I) hxst.1 hxst.2 (hζne (x + z.im * Complex.I) hxcb)
      _ = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I)))
        - (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + z.im * Complex.I) /
            (1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I)))) := by
          rw [intervalIntegral.integral_sub]
          · exact ContinuousOn.intervalIntegrable
              (eta_path_continuous_x z w (z.im : ℂ)
                (by intro x hx; exact hstrip (x + (z.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩)
                (by intro x hx; exact hζne (x + (z.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩))
          · exact ContinuousOn.intervalIntegrable
              (factor_path_continuous_x z w (z.im : ℂ)
                (by intro x hx; exact hstrip (x + (z.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩))
  -- 段 2 (顶边): 同 (w.im)
  have hseg2 :
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + w.im * Complex.I) / riemannZeta (x + w.im * Complex.I))
      = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I)))
      - (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + w.im * Complex.I) /
          (1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I)))) := by
    calc
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + w.im * Complex.I) / riemannZeta (x + w.im * Complex.I))
          = ∫ x : ℝ in z.re..w.re,
              (deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
                ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I)))
              - (deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + w.im * Complex.I) /
                (1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I)))) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hxcb : (x + w.im * Complex.I) ∈
                ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
              have hxre : (x + w.im * Complex.I).re ∈ Set.uIcc z.re w.re := by
                simpa using hx
              exact ⟨hxre, by simp⟩
            have hxst := hstrip (x + w.im * Complex.I) hxcb
            exact hsplit (x + w.im * Complex.I) hxst.1 hxst.2 (hζne (x + w.im * Complex.I) hxcb)
      _ = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I)))
        - (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + w.im * Complex.I) /
            (1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I)))) := by
          rw [intervalIntegral.integral_sub]
          · exact ContinuousOn.intervalIntegrable
              (eta_path_continuous_x z w (w.im : ℂ)
                (by intro x hx; exact hstrip (x + (w.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩)
                (by intro x hx; exact hζne (x + (w.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩))
          · exact ContinuousOn.intervalIntegrable
              (factor_path_continuous_x z w (w.im : ℂ)
                (by intro x hx; exact hstrip (x + (w.im : ℂ) * Complex.I) ⟨by simpa using hx, by simp⟩))
  -- 段 3 (右边): I•∫
  have hseg3 :
      (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re w + y * Complex.I) / riemannZeta (re w + y * Complex.I))
      = (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I)))
      - (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re w + y * Complex.I) /
          (1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I)))) := by
    calc
      (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re w + y * Complex.I) / riemannZeta (re w + y * Complex.I))
          = ∫ y : ℝ in z.im..w.im,
              (deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
                ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I)))
              - (deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re w + y * Complex.I) /
                (1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I)))) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hycb : (re w + y * Complex.I) ∈
                ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
              have hyim : (re w + y * Complex.I).im ∈ Set.uIcc z.im w.im := by
                simpa using hy
              exact ⟨by simp, hyim⟩
            have hyst := hstrip (re w + y * Complex.I) hycb
            exact hsplit (re w + y * Complex.I) hyst.1 hyst.2 (hζne (re w + y * Complex.I) hycb)
      _ = (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I)))
        - (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re w + y * Complex.I) /
            (1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I)))) := by
          rw [intervalIntegral.integral_sub]
          · exact ContinuousOn.intervalIntegrable
              (eta_path_continuous_y z w (re w)
                (by intro y hy; exact hstrip (re w + y * Complex.I) ⟨by simp, by simpa using hy⟩)
                (by intro y hy; exact hζne (re w + y * Complex.I) ⟨by simp, by simpa using hy⟩))
          · exact ContinuousOn.intervalIntegrable
              (factor_path_continuous_y z w (re w)
                (by intro y hy; exact hstrip (re w + y * Complex.I) ⟨by simp, by simpa using hy⟩))
  -- 段 4 (左边): I•∫
  have hseg4 :
      (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re z + y * Complex.I) / riemannZeta (re z + y * Complex.I))
      = (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I)))
      - (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re z + y * Complex.I) /
          (1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I)))) := by
    calc
      (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re z + y * Complex.I) / riemannZeta (re z + y * Complex.I))
          = ∫ y : ℝ in z.im..w.im,
              (deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
                ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I)))
              - (deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re z + y * Complex.I) /
                (1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I)))) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hycb : (re z + y * Complex.I) ∈
                ((Set.uIcc z.re w.re) ×ℂ (Set.uIcc z.im w.im)) := by
              have hyim : (re z + y * Complex.I).im ∈ Set.uIcc z.im w.im := by
                simpa using hy
              exact ⟨by simp, hyim⟩
            have hyst := hstrip (re z + y * Complex.I) hycb
            exact hsplit (re z + y * Complex.I) hyst.1 hyst.2 (hζne (re z + y * Complex.I) hycb)
      _ = (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I)))
        - (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re z + y * Complex.I) /
            (1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I)))) := by
          rw [intervalIntegral.integral_sub]
          · exact ContinuousOn.intervalIntegrable
              (eta_path_continuous_y z w (re z)
                (by intro y hy; exact hstrip (re z + y * Complex.I) ⟨by simp, by simpa using hy⟩)
                (by intro y hy; exact hζne (re z + y * Complex.I) ⟨by simp, by simpa using hy⟩))
          · exact ContinuousOn.intervalIntegrable
              (factor_path_continuous_y z w (re z)
                (by intro y hy; exact hstrip (re z + y * Complex.I) ⟨by simp, by simpa using hy⟩))
  -- 组装: rect(f) = rect(g) − rect(h), rect(h) = 0 ⟹ rect(f) = rect(g)
  calc
    (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + z.im * Complex.I) / riemannZeta (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, deriv riemannZeta (x + w.im * Complex.I) / riemannZeta (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re w + y * Complex.I) / riemannZeta (re w + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, deriv riemannZeta (re z + y * Complex.I) / riemannZeta (re z + y * Complex.I))
        = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I))) -
          (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I))) +
          Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I))) -
          Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
            ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I)))
          - ((∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + z.im * Complex.I) /
              (1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I)))) -
            (∫ x : ℝ in z.re..w.re, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (x + w.im * Complex.I) /
              (1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I)))) +
            Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re w + y * Complex.I) /
              (1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I)))) -
            Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => 1 - (2 : ℂ) ^ (1 - t)) (re z + y * Complex.I) /
              (1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))))) := by
          rw [hseg1, hseg2, hseg3, hseg4]
          ring
    _ = (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + z.im * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (x + z.im * Complex.I))) * riemannZeta (x + z.im * Complex.I))) -
        (∫ x : ℝ in z.re..w.re, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (x + w.im * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (x + w.im * Complex.I))) * riemannZeta (x + w.im * Complex.I))) +
        Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re w + y * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (re w + y * Complex.I))) * riemannZeta (re w + y * Complex.I))) -
        Complex.I • (∫ y : ℝ in z.im..w.im, deriv (fun t => (1 - (2 : ℂ) ^ (1 - t)) * riemannZeta t) (re z + y * Complex.I) /
          ((1 - (2 : ℂ) ^ (1 - (re z + y * Complex.I))) * riemannZeta (re z + y * Complex.I))) := by
        rw [hfac0_rect]
        ring

end ValueBridge

end
