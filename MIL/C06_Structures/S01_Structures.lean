import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

/- TEXT:
.. _section_structures:

定义结构体
-------------------

广义上来说，结构体约定了数据集合的规范，同时可能包括这些数据必须满足的约束条件。
而结构体的实例则是一组满足约束的具体数据。例如，我们可以规定一个点是由三个实数组成的三元组：
BOTH: -/
-- QUOTE:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
-- QUOTE.

/- TEXT:
上面用到的 ``@[ext]`` 注解让 Lean 自动生成一个定理，内容是当该结构体的两个实例各组成部分对应相同时，这两个实例相等。该属性也称为外延性（extensionality）。
EXAMPLES: -/
-- QUOTE:
#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption
-- QUOTE.

/- TEXT:
接着我们定义一个 ``Point`` 结构体的实例。
Lean 提供多种实例化方式来达成目的。
EXAMPLES: -/
-- QUOTE:
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4
-- QUOTE.

/- TEXT:
..
  Because Lean knows that the expected type of
  ``myPoint1`` is a ``Point``, you can start the definition by
  writing an underscore, ``_``. Clicking on the light bulb
  that appears nearby in VS Code will then
  give you the option of inserting a template definition
  with the field names listed for you.

第一个例子中，我们明确地指明了结构体的各个字段。
而在定义 ``myPoint3`` 时用到的函数 ``Point.mk`` 叫做 ``Point`` 结构体的构造函数（constructor），用于构造结构体成员。
你也可以为构造函数指定一个不同的名字，比如 ``build``。
EXAMPLES: -/
-- QUOTE:
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4
-- QUOTE.

/- TEXT:
接下来的两个例子展示了如何定义结构体的函数。
第二个例子中明确指出了构造函数 ``Point.mk`` 中的字段名，而第一个例子则使用更为简洁的匿名构造函数。
Lean 能根据 ``add`` 的目标类型推断出所需的构造函数。
通常，我们会将与结构体（例如这里的 ``Point``）相关的定义和定理放在一个同名的命名空间（namespace）中。
在下面的示例中，由于我们启用了 ``Point`` 命名空间，所以 ``add`` 的完整名称实际是 ``Point.add``。
当命名空间没被启用时，就得使用完整名称。
不过这时也可以使用匿名投影记号（anonymous projection notation），它允许我们用 ``a.add b`` 代替 ``Point.add a b``。
因为 a 的类型是 ``Point``，Lean 能在没有开启对应命名空间的时候将 ``a.add b`` 推断为 ``Point.add a b``。
BOTH: -/
-- QUOTE:
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

-- EXAMPLES:
def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2
-- QUOTE.

/- TEXT:
接下来我们继续在相关命名空间中添加定义，但在引用的代码片段中会省略开关命名空间相关的指令。
在证明加法函数性质时，可使用 ``rw`` 来展开定义，并用 ``ext`` 来将结构体两个实例之间的等式转化为它们组成部分之间的等式。
下面的代码使用 ``protected`` 关键字，使得在命名空间打开的情况下定理的名字依然是 ``Point.add_comm``。
当我们希望避免与更通用的定理如 ``add_comm`` 产生歧义时，这样做是有帮助的。
EXAMPLES: -/
namespace Point

-- QUOTE:
protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
-- QUOTE.

/- TEXT:
Because Lean can unfold definitions and simplify projections
internally, sometimes the equations we want hold definitionally.
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl
-- QUOTE.

/- TEXT:
It is also possible to define functions on structures using
pattern matching,
in a manner similar to the way we defined recursive functions in
:numref:`section_induction_and_recursion`.
The definitions ``addAlt`` and ``addAlt'`` below are essentially the
same; the only difference is that we use anonymous constructor notation
in the second.
Although it is sometimes convenient to define functions this way, and structural eta-reduction makes
this alternative definitionally equivalent, it can make things less convenient in later proofs.
In particular, `rw [addAlt]` leaves us with a messier goal view containing a `match` statement.
EXAMPLES: -/
-- QUOTE:
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm
-- QUOTE.

/- TEXT:
Mathematical constructions often involve taking apart bundled information and
putting it together again in different ways.
It therefore makes sense that Lean and Mathlib offer so many ways
of doing this efficiently.
As an exercise, try proving that ``Point.add`` is associative.
Then define scalar multiplication for a point and show that it
distributes over addition.
BOTH: -/
-- QUOTE:
protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, add_assoc]
-- BOTH:

def smul (r : ℝ) (a : Point) : Point :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ⟨r * a.x, r * a.y, r * a.z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, smul, mul_add]
-- BOTH:
-- QUOTE.

end Point

/- TEXT:
Using structures is only the first step on the road to
algebraic abstraction.
We don't yet have a way to link ``Point.add`` to the generic ``+`` symbol,
or to connect ``Point.add_comm`` and ``Point.add_assoc`` to
the generic ``add_comm`` and ``add_assoc`` theorems.
These tasks belong to the *algebraic* aspect of using structures,
and we will explain how to carry them out in the next section.
For now, just think of a structure as a way of bundling together objects
and information.

It is especially useful that a structure can specify not only
data types but also constraints that the data must satisfy.
In Lean, the latter are represented as fields of type ``Prop``.
For example, the *standard 2-simplex* is defined to be the set of
points :math:`(x, y, z)` satisfying :math:`x ≥ 0`, :math:`y ≥ 0`, :math:`z ≥ 0`,
and :math:`x + y + z = 1`.
If you are not familiar with the notion, you should draw a picture,
and convince yourself that this set is
the equilateral triangle in three-space with vertices
:math:`(1, 0, 0)`, :math:`(0, 1, 0)`, and :math:`(0, 0, 1)`,
together with its interior.
We can represent it in Lean as follows:
BOTH: -/
-- QUOTE:
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1
-- QUOTE.

/- TEXT:
Notice that the last four fields refer to ``x``, ``y``, and ``z``,
that is, the first three fields.
We can define a map from the two-simplex to itself that swaps ``x`` and ``y``:
BOTH: -/
namespace StandardTwoSimplex

-- EXAMPLES:
-- QUOTE:
def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]
-- QUOTE.

-- OMIT: (TODO) add a link when we have a good explanation of noncomputable section.
/- TEXT:
More interestingly, we can compute the midpoint of two points on
the simplex. We have added the phrase ``noncomputable section``
at the beginning of this file in order to use division on the real numbers.
BOTH: -/
-- QUOTE:
noncomputable section

-- EXAMPLES:
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]
-- QUOTE.

/- TEXT:
Here we have established ``x_nonneg``, ``y_nonneg``, and ``z_nonneg``
with concise proof terms, but establish ``sum_eq`` in tactic mode,
using ``by``.

Given a parameter :math:`\lambda` satisfying :math:`0 \le \lambda \le 1`,
we can take the weighted average :math:`\lambda a + (1 - \lambda) b`
of two points :math:`a` and :math:`b` in the standard 2-simplex.
We challenge you to define that function, in analogy to the ``midpoint``
function above.
BOTH: -/
-- QUOTE:
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
/- EXAMPLES:
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  sorry
SOLUTIONS: -/
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)
  sum_eq := by
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    · ring
    simp [a.sum_eq, b.sum_eq]
-- QUOTE.
-- BOTH:

end

end StandardTwoSimplex

/- TEXT:
Structures can depend on parameters.
For example, we can generalize the standard 2-simplex to the standard
:math:`n`-simplex for any :math:`n`.
At this stage, you don't have to know anything about the type ``Fin n``
except that it has :math:`n` elements, and that Lean knows
how to sum over it.
BOTH: -/
-- QUOTE:
open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex
-- QUOTE.

/- TEXT:
As an exercise, see if you can define the weighted average of
two points in the standard :math:`n`-simplex.
You can use ``Finset.sum_add_distrib``
and ``Finset.mul_sum`` to manipulate the relevant sums.
SOLUTIONS: -/
namespace StandardSimplex

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := lambda * a.V i + (1 - lambda) * b.V i
  NonNeg i :=
    add_nonneg (mul_nonneg lambda_nonneg (a.NonNeg i)) (mul_nonneg (by linarith) (b.NonNeg i))
  sum_eq_one := by
    trans (lambda * ∑ i, a.V i) + (1 - lambda) * ∑ i, b.V i
    · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp [a.sum_eq_one, b.sum_eq_one]

end StandardSimplex

/- TEXT:
We have seen that structures can be used to bundle together data
and properties.
Interestingly, they can also be used to bundle together properties
without the data.
For example, the next structure, ``IsLinear``, bundles together
the two components of linearity.
EXAMPLES: -/
-- QUOTE:
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
-- QUOTE.

/- TEXT:
It is worth pointing out that structures are not the only way to bundle
together data.
The ``Point`` data structure can be defined using the generic type product,
and ``IsLinear`` can be defined with a simple ``and``.
EXAMPLES: -/
-- QUOTE:
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x
-- QUOTE.

/- TEXT:
Generic type constructions can even be used in place of structures
with dependencies between their components.
For example, the *subtype* construction combines a piece of data with
a property.
You can think of the type ``PReal`` in the next example as being
the type of positive real numbers.
Any ``x : PReal`` has two components: the value, and the property of being
positive.
You can access these components as ``x.val``, which has type ``ℝ``,
and ``x.property``, which represents the fact ``0 < x.val``.
EXAMPLES: -/
-- QUOTE:
def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end
-- QUOTE.

/- TEXT:
We could have used subtypes to define the standard 2-simplex,
as well as the standard :math:`n`-simplex for an arbitrary :math:`n`.
EXAMPLES: -/
-- QUOTE:
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }
-- QUOTE.

/- TEXT:
Similarly, *Sigma types* are generalizations of ordered pairs,
whereby the type of the second component depends on the type of
the first.
EXAMPLES: -/
-- QUOTE:
def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
-- QUOTE.

/- TEXT:
Given ``s : StdSimplex``, the first component ``s.fst`` is a natural
number, and the second component is an element of the corresponding
simplex ``StandardSimplex s.fst``.
The difference between a Sigma type and a subtype is that
the second component of a Sigma type is data rather than a proposition.

But even though we can use products, subtypes, and Sigma types
instead of structures, using structures has a number of advantages.
Defining a structure abstracts away the underlying representation
and provides custom names for the functions that access the components.
This makes proofs more robust:
proofs that rely only on the interface to a structure
will generally continue to work when we change the definition,
as long as we redefine the old accessors in terms of the new definition.
Moreover, as we are about to see, Lean provides support for
weaving structures together into a rich, interconnected hierarchy,
and for managing the interactions between them.
TEXT. -/
/- OMIT: (TODO)
Comments from Patrick:
We could make this paragraph much less abstract by showing how to access the components of a point with the definition def point'' := ℝ × ℝ × ℝ. However if we do that it would probably be honest to also mention the possibility of using fin 3 → ℝ as the definition. This interesting anyhow, because I think very few mathematician realize that defining ℝ^n as an iterated cartesian product is a polite lie that would be a nightmare if taken seriously.

By the way, should be include some comment about similarities and differences with object-oriented programming? All the examples from that page would clearly fit very well with classes in python say. And we'll have to face the name-clash between classes in Lean and classes in C++ or python sooner or later. Life would be so much simpler if classes in Lean could use another name...
OMIT. -/
