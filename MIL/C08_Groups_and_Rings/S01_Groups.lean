-- BOTH:
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

/- TEXT:
.. _groups:

幺半群与群
------------------

.. index:: monoid
.. index:: group (algebraic structure)

幺半群和同态
^^^^^^^^^^^^^^^^^^^^^^^^^^^

抽象代数课程往往会从群讲起，一步步推进到环、域直至向量空间。这样的做法常会为讨论环上的乘法这样并不来自于群结构的运算带来不必要的曲折：许多群中的定理的证明方法其实也能适用，但我们却要再证一遍。
一般来说，当你是对着书本学习数学时，一行 “以下留作习题” 便是多数作者解决此窘境的方法。不过，在 Lean 中，我们有另一种虽然不那么方便，但却更安全，更对形式化友好的方法：引入幺半群 (monoid)。

类型 `M` 上的 **幺半群** 是一个在内部具有结合律和单位元的复合法则。幺半群被引入的首要目的是同时涵盖群和环上的乘法结构。有些较为自然的例子：比如，自然数与加法就构成一个幺半群。

从实际应用的角度来说，你几乎可以忘记 Mathlib 中的幺半群。不过你最好记得它存在，不然当你在为一个实际上并不需要元素可逆的命题寻找引理时，你可能不会想起它们在幺半群而不是群的相关文件中。

类型 ``M`` 上的幺半群被写作 ``Monoid M``.
函数 ``Monoid`` 是一个类型类，所以它几乎总是作为隐式实例参数而出现。（即出现在方括号中）
``Monoid`` 默认使用乘号作为运算的记号。要使用加号，可以用 ``AddMonoid`` 代替。
如果需要带有交换律，可使用 ``CommMonoid``.
EXAMPLES: -/
-- QUOTE:
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
-- QUOTE.

/- TEXT:
注意：虽然库中确实定义了 ``AddMonoid``，但对非交换的运算使用加号往往会给人带来迷惑。

幺半群 ``M`` 与 ``N`` 间的同态的类型称为 ``MonoidHom M N``，可写作 ``M →* N``. 在将一个同态作用于类型 ``M`` 的元素时，Lean 将自动将其视为一个由 ``M`` 到 ``N`` 的函数。相应的加法版本被称为 ``AddMonoidHom``, 对应写作 ``M →+ N``.
``M →* N``.
EXAMPLES: -/
-- QUOTE:
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
-- QUOTE.

/- TEXT:
同态其实是一系列映射, 即：同态映射本身和它的一些性质。
:numref:`section_hierarchies_morphisms` 中对这样的系列映射有过解释。
现在，我们发现这也产生了些许不妙的效果：我们无法使用常规的函数复合来组合两个映射。对此，有 ``MonoidHom.comp`` 和 ``AddMonoidHom.comp`` 作为替代方法.
EXAMPLES: -/
-- QUOTE:
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
-- QUOTE.

/- TEXT:
群和同态
^^^^^^^^^^^^^^^^^^^^^^^^^^

对于群，我们有更多可以探讨的。群，就是幺半群加上每一个元素都有逆元的性质。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x
-- QUOTE.

/- TEXT:

.. index:: group (tactic), tactics ; group

正如之前我们看到的 ``ring`` 策略，我们有 ``group`` 策略用来证明所有群所共同满足的恒等式。
(即自由群所满足的恒等式)

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
-- QUOTE.

/- TEXT:
.. index:: abel, tactics ; abel

对满足交换律的群，还有 ``abel`` 策略.

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel
-- QUOTE.

/- TEXT:
有趣的是，群同态所需满足的实际上与幺半群别无二致。所以我们之前的例子可以照搬过来。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y
-- QUOTE.

/- TEXT:
当然也有点新性质：
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x
-- QUOTE.

/- TEXT:
你也许会担心构造一个群同态需要枉费些不必要的工夫：幺半群同态的定义需要映射保持幺元，可这是群的情况下由第一条保持运算的性质就能自动得到的。虽然在实际中多做这一步并不困难，但我们可以避免它。接下来的函数可以由保持运算的群间映射给出群同态.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h
-- QUOTE.

/- TEXT:
同样对于群（幺半群）同构，我们有类型 ``MulEquiv`` , 记为 ``≃*`` (对应加号版本
``AddEquiv`` 记为 ``≃+``).
 ``f : G ≃* H`` 的逆是 ``MulEquiv.symm f : H ≃* G``,
 ``f`` 和 ``g`` 的复合是 ``MulEquiv.trans f g``, ``G`` 到自身的恒等同构 ``M̀ulEquiv.refl G``.
使用匿名投影子记号, 前两个可对应写作 ``f.symm`` 和
``f.trans g``.
这些类型的元素将在必要时自动提升为同态或函数.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
你可以用 ``MulEquiv.ofBijective`` 从一个也是双射的同态构造同构.
这样同时会使逆映射被标记为不可计算的 (noncomputable).
EXAMPLES: -/
-- QUOTE:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h
-- QUOTE.

/- TEXT:
Subgroups
^^^^^^^^^

就像群同态是一系列映射，``G`` 的子群也是一个由类型 ``G`` 的集合和相应的封闭性质共同构成结构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx
-- QUOTE.

/- TEXT:
In the example above, it is important to understand that ``Subgroup G`` is the type of subgroups
of ``G``, rather than a predicate ``IsSubgroup H`` where ``H`` is an element of ``Set G``.
``Subgroup G`` is endowed with a coercion to ``Set G`` and a membership predicate on ``G``.
See :numref:`section_hierarchies_subobjects` for an explanation of how and why this is done.

Of course, two subgroups are the same if and only if they have the same elements. This fact
is registered for use with the ``ext`` tactic, which can be used to prove two subgroups are
equal in the same way it is used to prove that two sets are equal.

To state and prove, for example, that ``ℤ`` is an additive subgroup of ``ℚ``,
what we really want is to construct a term of type ``AddSubgroup ℚ`` whose projection to
``Set ℚ`` is ``ℤ``, or, more precisely, the image of ``ℤ`` in ``ℚ``.
EXAMPLES: -/
-- QUOTE:
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp
-- QUOTE.

/- TEXT:
Using type classes, Mathlib knows that a subgroup of a group inherits a group structure.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance
-- QUOTE.

/- TEXT:
This example is subtle. The object ``H`` is not a type, but Lean automatically coerces it to
a type by interpreting it as a subtype of ``G``.
So the above example can be restated more explicitly as:
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
-- QUOTE.

/- TEXT:
An important benefit of having a type ``Subgroup G`` instead of a predicate
``IsSubgroup : Set G → Prop`` is that one can easily endow ``Subgroup G`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subgroups of ``G`` is again a subgroup, we
have used the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
lemmas about lattices to the construction.

Let us check that the set underlying the infimum of two subgroups is indeed, by definition,
their intersection.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl
-- QUOTE.

/- TEXT:
It may look strange to have a different notation for what amounts to the intersection of the
underlying sets, but the correspondence does not carry over to the supremum operation and set
union, since a union of subgroups is not, in general, a subgroup.
Instead one needs to use the subgroup generated by the union, which is done
using ``Subgroup.closure``.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]
-- QUOTE.

/- TEXT:
Another subtlety is that ``G`` itself does not have type ``Subgroup G``,
so we need a way to talk about ``G`` seen as a subgroup of ``G``.
This is also provided by the lattice structure: the full subgroup is the top element of
this lattice.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
-- QUOTE.

/- TEXT:
Similarly the bottom element of this lattice is the subgroup whose only element is the
neutral element.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot
-- QUOTE.

/- TEXT:
As an exercise in manipulating groups and subgroups, you can define the conjugate of a subgroup
by an element of the ambient group.
BOTH: -/
-- QUOTE:
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
-- BOTH:
  inv_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
-- BOTH:
  mul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
-- BOTH:
-- QUOTE.

/- TEXT:
Tying the previous two topics together, one can push forward and pull back subgroups using
group morphisms. The naming convention in Mathlib is to call those operations ``map``
and ``comap``.
These are not the common mathematical terms, but they have the advantage of being
shorter than "pushforward" and "direct image."
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap
-- QUOTE.

/- TEXT:
In particular, the preimage of the bottom subgroup under a morphism ``f`` is a subgroup called
the *kernel* of ``f``, and the range of ``f`` is also a subgroup.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range
-- QUOTE.

/- TEXT:
As exercises in manipulating group morphisms and subgroups, let us prove some elementary properties.
They are already proved in Mathlib, so do not use ``exact?`` too quickly if you want to benefit
from these exercises.
BOTH: -/
-- QUOTE:
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_comap] at * -- Lean does not need this line
  exact hST hx
-- BOTH:

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_map] at * -- Lean does not need this line
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy
-- BOTH:

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  -- The whole proof could be ``rfl``, but let's decompose it a bit.
  ext x
  simp only [mem_comap]
  rfl
-- BOTH:

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    calc ψ.comp φ z = ψ (φ z) := rfl
    _               = ψ y := by congr
    _               = x := hy
-- BOTH:

end exercises
-- QUOTE.

/- TEXT:
Let us finish this introduction to subgroups in Mathlib with two very classical results.
Lagrange theorem states the cardinality of a subgroup of a finite group divides the cardinality of
the group. Sylow's first theorem is a famous partial converse to Lagrange's theorem.

While this corner of Mathlib is partly set up to allow computation, we can tell
Lean to use nonconstructive logic anyway using the following ``open scoped`` command.
BOTH: -/
-- QUOTE:
open scoped Classical

-- EXAMPLES:

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

-- BOTH:
open Subgroup

-- EXAMPLES:
example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- QUOTE.

/- TEXT:
The next two exercises derive a corollary of Lagrange's lemma. (This is also already in Mathlib,
so do not use ``exact?`` too quickly.)
BOTH: -/
-- QUOTE:
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨y, -, hy'⟩ x hx
    calc x = y := hy' x hx
    _      = 1 := (hy' 1 H.one_mem).symm
-- EXAMPLES:

#check card_dvd_of_le
-- BOTH:

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have D₁ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  exact eq_bot_iff_card.2 (Nat.eq_one_of_dvd_coprimes h D₁ D₂)
-- QUOTE.

/- TEXT:
Concrete groups
^^^^^^^^^^^^^^^

One can also manipulate concrete groups in Mathlib, although this is typically more complicated
than working with the abstract theory.
For instance, given any type ``X``, the group of permutations of ``X`` is ``Equiv.Perm X``.
In particular the symmetric group :math:`\mathfrak{S}_n` is ``Equiv.Perm (Fin n)``.
One can state abstract results about this group, for instance saying that ``Equiv.Perm X`` is
generated by cycles if ``X`` is finite.
EXAMPLES: -/
-- QUOTE:
open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle
-- QUOTE.

/- TEXT:
One can be fully concrete and compute actual products of cycles. Below we use the ``#simp`` command,
which calls the ``simp`` tactic on a given expression. The notation ``c[]`` is used to define a
cyclic permutation. In the example, the result is a permutation of ``ℕ``. One could use a type
ascription such as ``(1 : Fin 5)`` on the first number appearing to make it a computation in
``Perm (Fin 5)``.
EXAMPLES: -/
-- QUOTE:
#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]
-- QUOTE.

/- TEXT:
Another way to work with concrete groups is to use free groups and group presentations.
The free group on a type ``α`` is ``FreeGroup α`` and the inclusion map is
``FreeGroup.of : α → FreeGroup α``. For instance let us define a type ``S`` with three elements denoted
by ``a``, ``b`` and ``c``, and the element ``ab⁻¹`` of the corresponding free group.
EXAMPLES: -/
-- QUOTE:
section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹
-- QUOTE.

/- TEXT:
Note that we gave the expected type of the definition so that Lean knows that ``.of`` means
``FreeGroup.of``.

The universal property of free groups is embodied as the equivalence ``FreeGroup.lift``.
For example, let us define the group morphism from ``FreeGroup S`` to ``Perm (Fin 5)`` that
sends ``a`` to ``c[1, 2, 3]``, ``b`` to ``c[2, 3, 1]``, and ``c`` to ``c[2, 3]``,
EXAMPLES: -/
-- QUOTE:
def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]

-- QUOTE.

/- TEXT:
As a last concrete example, let us see how to define a group generated by a single element whose
cube is one (so that group will be isomorphic to :math:`\mathbb{Z}/3`) and build a morphism
from that group to ``Perm (Fin 5)``.

As a type with exactly one element, we will use ``Unit`` whose
only element is denoted by ``()``. The function ``PresentedGroup`` takes a set of relations,
i.e. a set of elements of some free group, and returns a group that is this free group quotiented
by a normal subgroup generated by relations. (We will see how to handle more general quotients
in :numref:`quotient_groups`.) Since we somehow hide this behind a definition, we use ``deriving Group`` to force creation
of a group instance on ``myGroup``.
EXAMPLES: -/
-- QUOTE:
def myGroup := PresentedGroup {.of () ^ 3} deriving Group
-- QUOTE.

/- TEXT:
The universal property of presented groups ensures that morphisms out of this group can be built
from functions that send the relations to the neutral element of the target group.
So we need such a function and a proof that the condition holds. Then we can feed this proof
to ``PresentedGroup.toGroup`` to get the desired group morphism.
EXAMPLES: -/
-- QUOTE:
def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup
-- QUOTE.

/- TEXT:
Group actions
^^^^^^^^^^^^^

One important way that group theory interacts with the rest of mathematics is through
the use of group actions.
An action of a group ``G`` on some type ``X`` is nothing more than a morphism from ``G`` to
``Equiv.Perm X``. So in a sense group actions are already covered by the previous discussion.
But we don't want to carry this morphism around; instead, we want it to be inferred automatically
by Lean as much as possible. So we have a type class for this, which is ``MulAction G X``.
The downside of this setup is that having multiple actions of the same group on the same type
requires some contortions, such as defining type synonyms, each of which carries different
type class instances.

This allows us in particular to use ``g • x`` to denote the action of a group element ``g`` on
a point ``x``.
BOTH: -/
-- QUOTE:
noncomputable section GroupActions

-- EXAMPLES:
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
-- QUOTE.

/- TEXT:
There is also a version for additive group called ``AddAction``, where the action is denoted by
``+ᵥ``. This is used for instance in the definition of affine spaces.
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm
-- QUOTE.

/- TEXT:
The underlying group morphism is called ``MulAction.toPermHom``.
EXAMPLES: -/
-- QUOTE:
open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X
-- QUOTE.

/- TEXT:
As an illustration let us see how to define the Cayley isomorphism embedding of any group ``G`` into
a permutation group, namely ``Perm G``.
EXAMPLES: -/
-- QUOTE:
def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G
-- QUOTE.

/- TEXT:
Note that nothing before the above definition required having a group rather than a monoid (or any
type endowed with a multiplication operation really).

The group condition really enters the picture when we will want to partition ``X`` into orbits.
The corresponding equivalence relation on ``X`` is called ``MulAction.orbitRel``.
It is not declared as a global instance.
EXAMPLES: -/
/- OMIT:
TODO: We need to explain `Setoid` somewhere.
EXAMPLES. -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X
-- QUOTE.

/- TEXT:
Using this we can state that ``X`` is partitioned into orbits under the action of ``G``.
More precisely, we get a bijection between ``X`` and the dependent product
``(ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω))``
where ``Quotient.out' ω`` simply chooses an element that projects to ``ω``.
Recall that elements of this dependent product are pairs ``⟨ω, x⟩`` where the type
``orbit G (Quotient.out' ω)`` of ``x`` depends on ``ω``.
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X
-- QUOTE.

/- TEXT:
In particular, when X is finite, this can be combined with ``Fintype.card_congr`` and
``Fintype.card_sigma`` to deduce that the cardinality of ``X`` is the sum of the cardinalities
of the orbits.
Furthermore, the orbits are in bijection with the quotient of ``G`` under the action of the
stabilizers by left translation.
This action of a subgroup by left-translation is used to define quotients of a group by a
subgroup with notation `/` so we can use the following concise statement.
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x
-- QUOTE.

/- TEXT:
An important special case of combining the above two results is when ``X`` is a group ``G``
equipped with the action of a subgroup ``H`` by translation.
In this case all stabilizers are trivial so every orbit is in bijection with ``H`` and we get:
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup
-- QUOTE.

/- TEXT:
This is the conceptual variant of the version of Lagrange theorem that we saw above.
Note this version makes no finiteness assumption.

As an exercise for this section, let us build the action of a group on its subgroup by
conjugation, using our definition of ``conjugate`` from a previous exercise.
BOTH: -/
-- QUOTE:
variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp [conjugate]
-- BOTH:

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact conjugate_one
-- BOTH:
  mul_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro x y H
    ext z
    constructor
    · rintro ⟨h, h_in, rfl⟩
      use y*h*y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
      use h, h_in
      group
-- BOTH:

end GroupActions
-- QUOTE.

/- TEXT:
.. _quotient_groups:

Quotient groups
^^^^^^^^^^^^^^^

In the above discussion of subgroups acting on groups, we saw the quotient ``G ⧸ H`` appear.
In general this is only a type. It can be endowed with a group structure such that the quotient
map is a group morphism if and only if ``H`` is a normal subgroup (and this group structure is
then unique).

The normality assumption is a type class ``Subgroup.Normal`` so that type class inference can use it
to derive the group structure on the quotient.
BOTH: -/
-- QUOTE:
noncomputable section QuotientGroup

-- EXAMPLES:
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
-- QUOTE.

/- TEXT:
The universal property of quotient groups is accessed through ``QuotientGroup.lift``:
a group morphism ``φ`` descends to ``G ⧸ N`` as soon as its kernel contains ``N``.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h
-- QUOTE.

/- TEXT:
The fact that the target group is called ``M`` is the above snippet is a clue that having a
monoid structure on ``M`` would be enough.

An important special case is when ``N = ker φ``. In that case the descended morphism is
injective and we get a group isomorphism onto its image. This result is often called
the first isomorphism theorem.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
-- QUOTE.

/- TEXT:
Applying the universal property to a composition of a morphism ``φ : G →* G'``
with a quotient group projection ``Quotient.mk' N'``,
we can also aim for a morphism from ``G ⧸ N`` to ``G' ⧸ N'``.
The condition required on ``φ`` is usually formulated by saying "``φ`` should send ``N`` inside
``N'``." But this is equivalent to asking that ``φ`` should pull ``N'`` back over
``N``, and the latter condition is nicer to work with since the definition of pullback does not
involve an existential quantifier.
EXAMPLES: -/
-- QUOTE:
example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h
-- QUOTE.

/- TEXT:
One subtle point to keep in mind is that the type ``G ⧸ N`` really depends on ``N``
(up to definitional equality), so having a proof that two normal subgroups ``N`` and ``M`` are equal
is not enough to make the corresponding quotients equal. However the universal properties does give
an isomorphism in this case.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
-- QUOTE.

/- TEXT:
As a final series of exercises for this section, we will prove that if ``H`` and ``K`` are disjoint
normal subgroups of a finite group ``G`` such that the product of their cardinalities is equal to
the cardinality of ``G``
then ``G`` is isomorphic to ``H × K``. Recall that disjoint in this context means ``H ⊓ K = ⊥``.

We start with playing a bit with Lagrange's lemma, without assuming the subgroups are normal
or disjoint.
BOTH: -/
-- QUOTE:
section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := calc
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by rw [← H.index_eq_card, H.index_mul_card]
    _                             = Nat.card K * Nat.card H := by rw [h', mul_comm]

  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
-- QUOTE.

/- TEXT:
From now on, we assume that our subgroups are normal and disjoint, and we assume the cardinality
condition. Now we construct the first building block of the desired isomorphism.
BOTH: -/
-- QUOTE:
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ [Fintype G] (h : Disjoint H K) (h' : Nat.card G = Nat.card H * Nat.card K) : K ≃* G ⧸ H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp [h]
  · symm
    exact aux_card_eq h'
-- QUOTE.

/- TEXT:
Now we can define our second building block.
We will need ``MonoidHom.prod``, which builds a morphism from ``G₀`` to ``G₁ × G₂`` out of
morphisms from ``G₀`` to ``G₁`` and ``G₂``.
BOTH: -/
-- QUOTE:
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' H)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H) _▸ h'), h']
-- QUOTE.

/- TEXT:
We are ready to put all pieces together.
EXAMPLES: -/
-- QUOTE:
#check MulEquiv.prodCongr

-- BOTH:
def finalIso : G ≃* H × K :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm

end
end QuotientGroup
-- QUOTE.
