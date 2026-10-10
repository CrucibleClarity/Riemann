/-
表示层→已知对象 机证桥 (隔离文件, mathlib-only, 0 error 0 sorry):
  * ComplexAxis (⟨a,b⟩ = a+bJ, J² = -1) → mathlib ℂ (a+bi): 保加/保乘/保单位/ J↦i / 范数 = |·|²
  * SplitComplex (⟨a,b⟩ = a+bj, j² = +1) → ℝ×ℝ 对角同构 (a+bj ↦ (a+b, a-b)): 保加/保乘/保单位/伪范数 = 分量积
用途: 论文声明"表示层对象 = 已知数学"由机证支撑 (非文本自述)。

English: machine-verified bridges of the representation layer to known objects: the coordinate model ?a,b? to mathlib's Complex (ε = -1), and the product plane ℝ×ℝ in diagonal coordinates (ε = +1)-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ZeroRelative

namespace ComplexAxis

-- ==== 定义复制 (自 proof.lean, 独立成文件) ====
structure ComplexAxis where
  a : ℝ
  b : ℝ

def add (x y : ComplexAxis) : ComplexAxis := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : ComplexAxis) : ComplexAxis := ⟨-x.a, -x.b⟩
def zero : ComplexAxis := ⟨0, 0⟩
def one : ComplexAxis := ⟨1, 0⟩

/-- 90° 旋转 J (J² = -1) 
English: Rotational unit J (J² = -1) -/
def J : ComplexAxis := ⟨0, 1⟩

/-- 乘法 (复数乘法): (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J 
English: Complex multiplication: (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J -/
def mul (x y : ComplexAxis) : ComplexAxis :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

def sub (x y : ComplexAxis) : ComplexAxis := ⟨x.a - y.a, x.b - y.b⟩

instance instAdd : Add ComplexAxis := ⟨add⟩
instance instNeg : Neg ComplexAxis := ⟨neg⟩
instance instSub : Sub ComplexAxis := ⟨sub⟩
instance instZero : Zero ComplexAxis := ⟨zero⟩
instance instOne : One ComplexAxis := ⟨one⟩
instance instMul : Mul ComplexAxis := ⟨mul⟩

@[ext] theorem ext (x y : ComplexAxis) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp at ha hb
      simp [ha, hb]

/-- 抬升: 实数轴嵌入 (标量部分, 保加法乘法) 
English: Lift: the real-axis embedding (scalar part, additive and multiplicative) -/
def lift (t : ℝ) : ComplexAxis := ⟨t, 0⟩

/-- 范数: 半径平方 (norm z = a² + b²) 
English: Norm: the squared radius (norm z = a² + b²) -/
def norm (z : ComplexAxis) : ℝ := z.a ^ 2 + z.b ^ 2

end ComplexAxis

namespace SplitComplex

-- ==== 定义复制 (自 proof.lean, 独立成文件) ====
structure SplitComplex where
  re : ℝ
  im : ℝ

/-- 虚数单位 j (j² = +1)。 
English: Involutive unit j (j² = +1) -/
def j : SplitComplex := ⟨0, 1⟩

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre him
      simp [hre, him]

instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl
@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 
English: Pseudo-norm (Minkowski form): ‖a + bj‖² = a² - b² -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 乘法逆: (a+bj)⁻¹ = (a-bj)/(a²-b²), 当伪范数非零。 
English: Multiplicative inverse: (a+bj)⁻¹ = (a-bj)/(a²-b²) when the pseudo-norm is nonzero -/
noncomputable instance instInv : Inv SplitComplex :=
  ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩

@[simp] theorem re_inv (z : SplitComplex) : (z⁻¹).re = z.re / normSq z := rfl
@[simp] theorem im_inv (z : SplitComplex) : (z⁻¹).im = -z.im / normSq z := rfl

/-- 逆是乘法逆 (当伪范数非零)。 
English: The inverse is a multiplicative inverse (when the pseudo-norm is nonzero) -/
theorem inv_mul_self {z : SplitComplex} (hz : normSq z ≠ 0) : z⁻¹ * z = 1 := by
  have hz' : z.re ^ 2 - z.im ^ 2 ≠ 0 := by simpa [normSq] using hz
  ext <;> simp [normSq] <;> field_simp [hz'] <;> ring

end SplitComplex

-- ==== 桥 1: ComplexAxis → mathlib ℂ (坐标模型 = 复数) ====
namespace ComplexAxis

open ComplexAxis

/-- 坐标模型到 mathlib ℂ: ⟨a,b⟩ ↦ a + bi 
English: The coordinate model into mathlib's ℂ: ⟨a,b⟩ ↦ a + bi -/
def toComplex (z : ComplexAxis) : ℂ := (z.a : ℂ) + (z.b : ℂ) * Complex.I

/-- J ↦ i (0pat 的 J 就是 mathlib 的虚单位) 
English: J ↦ i (the 0pat J is mathlib's imaginary unit) -/
theorem toComplex_J : toComplex J = Complex.I := by
  simp [toComplex, J]

/-- 1 ↦ 1 
English: 1 ↦ 1 -/
theorem toComplex_one : toComplex (one : ComplexAxis) = (1 : ℂ) := by
  apply Complex.ext <;> simp [toComplex, one, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- lift ↦ 实嵌入 (实数轴一致) 
English: lift ↦ the real embedding (agreement on the real axis) -/
theorem toComplex_lift (t : ℝ) : toComplex (lift t) = (t : ℂ) := by
  simp [toComplex, lift]

/-- 保加: 坐标模型加法 = mathlib 复数加法 
English: Additive: coordinate-model addition = mathlib complex addition -/
theorem toComplex_add (x y : ComplexAxis) :
    toComplex (add x y) = toComplex x + toComplex y := by
  apply Complex.ext <;> simp [toComplex, add, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im] <;> ring

/-- 保乘: 坐标模型乘法 = mathlib 复数乘法 
English: Multiplicative: coordinate-model multiplication = mathlib complex multiplication -/
theorem toComplex_mul (x y : ComplexAxis) :
    toComplex (mul x y) = toComplex x * toComplex y := by
  apply Complex.ext <;> simp [toComplex, mul, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

/-- J² = -1 机证 (坐标模型的定义性代数性质, 由乘法定义直接给出) 
English: J² = -1, machine-verified (the defining algebra fact of the coordinate model) -/
theorem J_sq : mul J J = neg one := by
  ext <;> simp [mul, J, one, neg]

/-- 范数一致: 坐标模型的范数 = mathlib 范数的平方 (normSq) 
English: Norms agree: the coordinate norm = mathlib's squared modulus (normSq) -/
theorem norm_eq (z : ComplexAxis) : norm z = Complex.normSq (toComplex z) := by
  simp [toComplex, norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end ComplexAxis

-- ==== 桥 2: SplitComplex → ℝ×ℝ 对角 (分裂复数 = 已知代数) ====
namespace SplitComplex

open SplitComplex

/-- 对角同构: a + bj ↦ (a+b, a-b) (ℝ[x]/(x²-1) ≅ ℝ×ℝ 的标准环同构) 
English: Diagonal isomorphism: a + bj ↦ (a+b, a-b) (the standard ring isomorphism ℝ[x]/(x²-1) ≅ ℝ×ℝ) -/
def toProd (z : SplitComplex) : ℝ × ℝ := ⟨z.re + z.im, z.re - z.im⟩

/-- j ↦ (1,-1) 
English: j ↦ (1,-1) -/
theorem toProd_j : toProd j = (1, -1) := by
  simp [toProd, j]

/-- 1 ↦ (1,1) 
English: 1 ↦ (1,1) -/
theorem toProd_one : toProd (⟨1, 0⟩ : SplitComplex) = (1, 1) := by
  simp [toProd]

/-- 保加 
English: Additive -/
theorem toProd_add (z w : SplitComplex) :
    toProd (z + w) = ((toProd z).1 + (toProd w).1, (toProd z).2 + (toProd w).2) := by
  ext <;> simp [toProd] <;> ring

/-- 保乘 (对角同构的关键: 分裂复数的乘性) 
English: Multiplicative (the key of the diagonal isomorphism: multiplicativity of the split algebra) -/
theorem toProd_mul (z w : SplitComplex) :
    toProd (z * w) = ((toProd z).1 * (toProd w).1, (toProd z).2 * (toProd w).2) := by
  ext <;> simp [toProd, re_mul, im_mul] <;> ring

/-- 伪范数 = 对角分量积: a²-b² = (a+b)(a-b) 
English: The pseudo-norm = the diagonal component product: a²-b² = (a+b)(a-b) -/
theorem normSq_eq_prod (z : SplitComplex) :
    normSq z = (toProd z).1 * (toProd z).2 := by
  simp [normSq, toProd]
  ring

/-- j² = 1 (分裂复数定义性代数性质, 机证) 
English: j² = 1, machine-verified (defining algebra fact of the split complex numbers) -/
theorem j_sq : j * j = (1 : SplitComplex) := by
  ext <;> simp [j]

/-- 伪范数乘性 (与对角表示下的分量积一致) 
English: Multiplicativity of the pseudo-norm (consistent with the component product in the diagonal representation) -/
theorem normSq_mul (z w : SplitComplex) : normSq (z * w) = normSq z * normSq w := by
  simp [normSq, re_mul, im_mul]
  ring

end SplitComplex

end ZeroRelative
