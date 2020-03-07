---
src       : "src/plfa/part1/Induction.lagda.md"
title     : "Induction: 归纳证明"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
translators : ["Oling Cat"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="176" class="Keyword">module</a> <a id="183" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.part1.Induction</a> <a id="204" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf
{:/}

> 归纳会让你对无中生有感到内疚
> ……但它却是文明中最伟大的思想之一。
> —— Herbert Wilf

{::comment}
Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.
{:/}

现在我们定义了自然数及其运算，下一步是学习如何证明它们满足的性质。顾名思义，**归纳数据类型（Inductive Datatype）**是通过**归纳（Induction）**来证明的。

{::comment}
## Imports
{:/}

## 导入

{::comment}
We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{:/}

我们需要上一章中的相等性，加上自然数及其运算。我们还导入了一些新的运算：
`cong`、`sym` 和 `_≡⟨_⟩_`，之后会解释它们：

{% raw %}<pre class="Agda"><a id="1099" class="Keyword">import</a> <a id="1106" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1144" class="Symbol">as</a> <a id="1147" class="Module">Eq</a>
<a id="1150" class="Keyword">open</a> <a id="1155" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1158" class="Keyword">using</a> <a id="1164" class="Symbol">(</a><a id="1165" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1168" class="Symbol">;</a> <a id="1170" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1174" class="Symbol">;</a> <a id="1176" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1180" class="Symbol">;</a> <a id="1182" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1185" class="Symbol">)</a>
<a id="1187" class="Keyword">open</a> <a id="1192" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1207" class="Keyword">using</a> <a id="1213" class="Symbol">(</a><a id="1214" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1220" class="Symbol">;</a> <a id="1222" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1227" class="Symbol">;</a> <a id="1229" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1235" class="Symbol">;</a> <a id="1237" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1239" class="Symbol">)</a>
<a id="1241" class="Keyword">open</a> <a id="1246" class="Keyword">import</a> <a id="1253" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1262" class="Keyword">using</a> <a id="1268" class="Symbol">(</a><a id="1269" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1270" class="Symbol">;</a> <a id="1272" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1276" class="Symbol">;</a> <a id="1278" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1281" class="Symbol">;</a> <a id="1283" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1286" class="Symbol">;</a> <a id="1288" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1291" class="Symbol">;</a> <a id="1293" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1296" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Properties of operators
{:/}

## 运算符的性质

{::comment}
Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.
{:/}

运算符随处可见，而数学家们统一了一些最常见的性质的名称。

{::comment}
* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.
{:/}

* **幺元（Identity）**：对于所有的 `n`，若 `0 + n ≡ n`，则 `+` 有左幺元 `0`；
  若 `n + 0 ≡ n`，则 `+` 有右幺元 `0`。同时为左幺元和右幺元的值称简称幺元。
  幺元有时也称作**单位元（Unit）**。

* **结合律（Associativity）**：若括号的位置无关紧要，则称运算符 `+` 满足结合律，
  即对于所有的 `m`、`n` 和 `p`，有 `(m + n) + p ≡ m + (n + p)`。

* **交换律（Commutativity）**：若参数的顺序无关紧要，则称运算符 `+` 满足交换律，
  即对于所有的 `m` 和 `n`，有 `m + n ≡ n + m`。

* **分配律（Distributivity）**：对于所有的 `m`、`n` 和 `p`，若
  `(m + n) * p ≡ (m * p) + (n * p)`，则运算符 `*` 对运算符 `+` 满足左分配律；
  对于所有的 `m`、`n` 和 `p`，若 `m * (p + q) ≡ (m * p) + (m * q)`，则满足右分配律。

{::comment}
Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.
{:/}

加法的幺元为 `0`，乘法的幺元为 `1`。加法和乘法都满足结合律和交换律，乘法对加法满足分配律。

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

如果你在一个舞会上碰见了一位操作员，那么你可以跟他闲聊，问问他是否有单位元，能不能结合或者交换。如果你碰见了两位操作员，那么可以问他们某一位是否在另一位上面分布。

【译注：作者的双关冷笑话，运算符（Operator）也有操作员的意思。】

{::comment}
Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.
{:/}

正经来说，如果你在阅读技术论文时遇到了一个运算符，那么你可以考察它是否拥有幺元，是否满足结合律或分配律，或者是否对另一个运算符满足分配律，这能为你提供一种视角。细心的作者通常会指出它们是否满足这些性质，比如说指明一个新引入的运算符满足结合律但不满足交换律。

{::comment}
#### Exercise `operators` (practice) {#operators}
{:/}

#### 练习 `operators`（实践） {#operators}

{::comment}
Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
{:/}

请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配律。
（你不必证明这些性质）

{::comment}
{% raw %}<pre class="Agda"><a id="4313" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="4350" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Give an example of an operator that has an identity and is
associative but is not commutative.
{:/}

请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。
（你不必证明这些性质）

{::comment}
{% raw %}<pre class="Agda"><a id="4542" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="4579" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Associativity
{:/}

## 结合律

{::comment}
One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:
{:/}

加法的一个性质是满足**结合律**，即括号的位置无关紧要：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `m`, `n`, and `p` are variables that range over all natural numbers.
{:/}

这里的变量 `m`、`n` 和 `p` 的取值范围都是全体自然数。

{::comment}
We can test the proposition by choosing specific numbers for the three
variables:
{:/}

我们可以为这三个变量选取特定的数值来验证此命题：

{% raw %}<pre class="Agda"><a id="5095" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#5095" class="Function">_</a> <a id="5097" class="Symbol">:</a> <a id="5099" class="Symbol">(</a><a id="5100" class="Number">3</a> <a id="5102" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5104" class="Number">4</a><a id="5105" class="Symbol">)</a> <a id="5107" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5109" class="Number">5</a> <a id="5111" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5113" class="Number">3</a> <a id="5115" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5117" class="Symbol">(</a><a id="5118" class="Number">4</a> <a id="5120" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5122" class="Number">5</a><a id="5123" class="Symbol">)</a>
<a id="5125" class="Symbol">_</a> <a id="5127" class="Symbol">=</a>
  <a id="5131" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="5141" class="Symbol">(</a><a id="5142" class="Number">3</a> <a id="5144" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5146" class="Number">4</a><a id="5147" class="Symbol">)</a> <a id="5149" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5151" class="Number">5</a>
  <a id="5155" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5163" class="Number">7</a> <a id="5165" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5167" class="Number">5</a>
  <a id="5171" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5179" class="Number">12</a>
  <a id="5184" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5192" class="Number">3</a> <a id="5194" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5196" class="Number">9</a>
  <a id="5200" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5208" class="Number">3</a> <a id="5210" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5212" class="Symbol">(</a><a id="5213" class="Number">4</a> <a id="5215" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5217" class="Number">5</a><a id="5218" class="Symbol">)</a>
  <a id="5222" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.
{:/}

在这里，我们将计算过程写成了等式链，每行一个式子。这样的等式链通常非常易读，你可以从上到下，直到遇到最简形式（本例中为 `12`），也可以从下到上，直到回到同样的式子。

{::comment}
The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?
{:/}

该测试揭示了结合律可能没有它初看起来那么显然。为什么 `7 + 5` 与 `3 + 9` 相同？我们可能需要收集更多证据，选择其它的数值来验证此命题。但由于自然数是无限的，因此测试永远无法完成。那么我们还有其它可以确保结合律对于**所有**自然数都成立的方法吗？

{::comment}
The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.
{:/}

当然有！我们可以用**归纳证明（Proof by Induction）**来确保某个性质对于所有的自然数都成立。


{::comment}
## Proof by induction
{:/}

## 归纳证明

{::comment}
Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.
{:/}

回想自然数的定义，它由一个**起始步骤**「`zero` 是一个自然数」
和一个**归纳步骤**「若 `m` 是一个自然数，则 `suc m` 也是一个自然数」构成。

{::comment}
Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.
{:/}

归纳证明遵循此定义的结构。要通过归纳证明自然数的某个性质，我们需要两个步骤。其一是**起始步骤**，即需要证明此性质对 `zero` 成立。其二是**归纳步骤**，即假设此性质对一个任意自然数 `m` 成立（我们称之为**归纳假设（Induction
Hypothesis）**），然后证明该性质对 `suc m` 必定成立。

{::comment}
If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:
{:/}

若将 `m` 的某种性质（Property）写作 `P m`，那么我们需要证明的就是以下两个推导规则：

    ------
    P zero

    P m
    ---------
    P (suc m)

{::comment}
Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.
{:/}

先来分析一下这些规则。第一条规则是起始步骤，它需要我们证明性质 `P` 对 `zero`
成立。第二条规则是归纳步骤，它需要我们证明若归纳假设「`P` 对 `m` 成立」，那么 `P` 也对 `suc m` 成立。

{::comment}
Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:
{:/}

为什么可以这样做呢？它也可以用创世故事来讲解。起初，我们对性质一无所知：

{::comment}
    -- In the beginning, no properties are known.
{:/}

    -- 起初，世上没有已知的性质。

{::comment}
Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:
{:/}

现在我们对所有已知的性质应用上述两条规则。起始步骤告诉我们 `P zero` 成立，所以我们将它加入已知的性质集合中。归纳步骤告诉我们若「昨天的」`P m` 成立，那么「今天的」`P (suc m)` 也成立。我们在今天之前并不知道任何性质，因此归纳步骤在这里不适用：

{::comment}
    -- On the first day, one property is known.
    P zero
{:/}

    -- 第一天，我们知道了一个性质。
    P zero

{::comment}
Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:
{:/}

然后我们重复此过程。在接下来的一天我们知道今天之前的所有性质，以及任何通过此规则添加的性质。起始步骤告诉我们 `P zero`
成立，我们已经知道这件事了。而如今归纳步骤告诉我们，由于 `P zero`
在昨天成立，那么 `P (suc zero)` 今天也成立。

{::comment}
    -- On the second day, two properties are known.
    P zero
    P (suc zero)
{:/}

    -- 第二天，我们知道了两个性质。
    P zero
    P (suc zero)

{::comment}
And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:
{:/}

我们再重复此过程。现在归纳步骤告诉我们由于 `P zero` 和 `P (suc zero)` 都成立，因此 `P (suc zero)` 和 `P (suc (suc zero))` 也成立。我们已经知道第一个成立了，但第二个是新引入的：

{::comment}
    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
{:/}

    -- 第三天，我们知道了三个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))
{:/}

    -- 第四天，我们知道了四个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

{::comment}
The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.
{:/}

此过程可以继续下去。在第 *n* 天会有 *n* 个不同的性质成立。每个自然数的性质都会在某一天出现。具体来说，性质 `P n` 会在第 *n+1* 天首次出现。


{::comment}
## Our first proof: associativity
{:/}

## 第一个证明：结合律

{::comment}
To prove associativity, we take `P m` to be the property:
{:/}

要证明结合律，我们需要将 `P m` 看做以下性质：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:
{:/}

这里的 `n` 和 `p` 是任意自然数，因此若我们可以证明该等式对所有的 `m`
都成立，那么它也会对所有的 `n` 和 `p` 成立。其推理规则的对应实例如下：

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
If we can demonstrate both of these, then associativity of addition
follows by induction.
{:/}

如果我们可以证明这两条规则，那么加法结合律就可以用归纳法来证明。

{::comment}
Here is the proposition's statement and proof:
{:/}

以下为此性质的陈述和证明：

{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="11558" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="11566" class="Symbol">:</a> <a id="11568" class="Symbol">∀</a> <a id="11570" class="Symbol">(</a><a id="11571" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11571" class="Bound">m</a> <a id="11573" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11573" class="Bound">n</a> <a id="11575" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11575" class="Bound">p</a> <a id="11577" class="Symbol">:</a> <a id="11579" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11580" class="Symbol">)</a> <a id="11582" class="Symbol">→</a> <a id="11584" class="Symbol">(</a><a id="11585" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11571" class="Bound">m</a> <a id="11587" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11589" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11573" class="Bound">n</a><a id="11590" class="Symbol">)</a> <a id="11592" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11594" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11575" class="Bound">p</a> <a id="11596" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11598" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11571" class="Bound">m</a> <a id="11600" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11602" class="Symbol">(</a><a id="11603" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11573" class="Bound">n</a> <a id="11605" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11607" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11575" class="Bound">p</a><a id="11608" class="Symbol">)</a>
<a id="11610" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="11618" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11623" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11625" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a> <a id="11627" class="Symbol">=</a>
  <a id="11631" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11641" class="Symbol">(</a><a id="11642" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11647" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11649" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a><a id="11650" class="Symbol">)</a> <a id="11652" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11654" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a>
  <a id="11658" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11666" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11668" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11670" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a>
  <a id="11674" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11682" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11687" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11689" class="Symbol">(</a><a id="11690" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11692" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11694" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a><a id="11695" class="Symbol">)</a>
  <a id="11699" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="11701" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="11709" class="Symbol">(</a><a id="11710" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11714" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a><a id="11715" class="Symbol">)</a> <a id="11717" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a> <a id="11719" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a> <a id="11721" class="Symbol">=</a>
  <a id="11725" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11735" class="Symbol">(</a><a id="11736" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11740" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11742" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11744" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a><a id="11745" class="Symbol">)</a> <a id="11747" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11749" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a>
  <a id="11753" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11761" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11765" class="Symbol">(</a><a id="11766" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11768" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11770" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a><a id="11771" class="Symbol">)</a> <a id="11773" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11775" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a>
  <a id="11779" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11787" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11791" class="Symbol">((</a><a id="11793" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11795" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11797" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a><a id="11798" class="Symbol">)</a> <a id="11800" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11802" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a><a id="11803" class="Symbol">)</a>
  <a id="11807" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11810" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11815" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11819" class="Symbol">(</a><a id="11820" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="11828" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11830" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a> <a id="11832" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a><a id="11833" class="Symbol">)</a> <a id="11835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11841" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11845" class="Symbol">(</a><a id="11846" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11848" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11850" class="Symbol">(</a><a id="11851" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a> <a id="11853" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11855" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a><a id="11856" class="Symbol">))</a>
  <a id="11861" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11869" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11873" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11714" class="Bound">m</a> <a id="11875" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11877" class="Symbol">(</a><a id="11878" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11717" class="Bound">n</a> <a id="11880" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11882" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11719" class="Bound">p</a><a id="11883" class="Symbol">)</a>
  <a id="11887" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.
{:/}

我们将此证明命名为 `+-assoc`。在 Agda 中，标识符可以由除空格和 `@.(){};_`
之外的任何字符序列构成。

{::comment}
Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:
{:/}

我们来分析一下这段代码。其签名（Signature）描述了我们定义的标识符 `+-assoc`
为以下命题提供了证据（Evidence）：

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.
{:/}

倒 A 符号读作「对于所有（for all）」，而该命题断言对于所有的自然数 `m`、`n`
和 `p`，等式 `(m + n) + p ≡ m + (n + p)` 成立。该命题的证据是一个接受三个自然数的函数，将它们绑定到 `m`、`n` 和 `p`，并返回该等式对应实例的证据。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

用加法的起始步骤化简等式两边会得到：

    n + p ≡ n + p

{::comment}
This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.
{:/}

此式平凡成立。阅读此证明中起始步骤中的等式链，其最初和最末的式子分别匹配待证等式的两边，从上到下或从下到上读都会让我们在中间遇到 `n + p` 。此步骤无需多言，化简即可。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

用加法的归纳步骤化简等式两边会得到：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    (m + n) + p ≡ m + (n + p)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:
{:/}

阅读此证明中归纳步骤的等式链，其最初和最末的式子分别匹配待证等式的两边，从上到下或从下到上读都会让我们到达上面化简等式的地方。剩下的等式单化简还不行，我们还需要为推理链使用一个附加的运算符 `_≡⟨_⟩_`，并将等式的依据放在尖括号中。这里给出的依据是：

    ⟨ cong suc (+-assoc m n p) ⟩

{::comment}
Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.
{:/}

在这里，递归调用的 `+-assoc m n p` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。

{::comment}
A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.
{:/}

若某个关系在应用了给定的函数后仍然保持不变，则称该关系满足**合同性（Congruence）**。若 `e` 是 `x ≡ y` 的证据，那么对于任意函数 `f`，`cong f e` 就是 `f x ≡ f y` 的证据。

{::comment}
Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.
{:/}

在这里并未假定归纳假设，而是通过递归调用我们定义的函数 `+-assoc m n p` 来证明。对于加法，这是良基的（well-founded），因为更大数值的结合律可基于更小数值的结合律来证明。在此步骤中，`assoc (suc m) n p` 是用 `assoc m n p` 证明的。归纳证明和递归定义之间的这种对应是 Agda 中最吸引人的方面之一。

{::comment}
## Induction as recursion
{:/}

## 归纳即递归

{::comment}
As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.
{:/}

下面是归纳如何对应于递归的具体例子，它是在结合律的证明中，将 `m` 实例化为 `2`
时的计算过程。

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="16216" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16216" class="Function">+-assoc-2</a> <a id="16226" class="Symbol">:</a> <a id="16228" class="Symbol">∀</a> <a id="16230" class="Symbol">(</a><a id="16231" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16231" class="Bound">n</a> <a id="16233" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">p</a> <a id="16235" class="Symbol">:</a> <a id="16237" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16238" class="Symbol">)</a> <a id="16240" class="Symbol">→</a> <a id="16242" class="Symbol">(</a><a id="16243" class="Number">2</a> <a id="16245" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16247" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16231" class="Bound">n</a><a id="16248" class="Symbol">)</a> <a id="16250" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16252" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">p</a> <a id="16254" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16256" class="Number">2</a> <a id="16258" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16260" class="Symbol">(</a><a id="16261" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16231" class="Bound">n</a> <a id="16263" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16265" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">p</a><a id="16266" class="Symbol">)</a>
<a id="16268" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16216" class="Function">+-assoc-2</a> <a id="16278" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a> <a id="16280" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a> <a id="16282" class="Symbol">=</a>
  <a id="16286" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16296" class="Symbol">(</a><a id="16297" class="Number">2</a> <a id="16299" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16301" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a><a id="16302" class="Symbol">)</a> <a id="16304" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16306" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a>
  <a id="16310" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16318" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16322" class="Symbol">(</a><a id="16323" class="Number">1</a> <a id="16325" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16327" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a><a id="16328" class="Symbol">)</a> <a id="16330" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16332" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a>
  <a id="16336" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16344" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16348" class="Symbol">((</a><a id="16350" class="Number">1</a> <a id="16352" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16354" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a><a id="16355" class="Symbol">)</a> <a id="16357" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16359" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a><a id="16360" class="Symbol">)</a>
  <a id="16364" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16367" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16372" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16376" class="Symbol">(</a><a id="16377" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16452" class="Function">+-assoc-1</a> <a id="16387" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a> <a id="16389" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a><a id="16390" class="Symbol">)</a> <a id="16392" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16398" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16402" class="Symbol">(</a><a id="16403" class="Number">1</a> <a id="16405" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16407" class="Symbol">(</a><a id="16408" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a> <a id="16410" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16412" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a><a id="16413" class="Symbol">))</a>
  <a id="16418" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16426" class="Number">2</a> <a id="16428" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16430" class="Symbol">(</a><a id="16431" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16278" class="Bound">n</a> <a id="16433" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16435" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16280" class="Bound">p</a><a id="16436" class="Symbol">)</a>
  <a id="16440" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="16444" class="Keyword">where</a>
  <a id="16452" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16452" class="Function">+-assoc-1</a> <a id="16462" class="Symbol">:</a> <a id="16464" class="Symbol">∀</a> <a id="16466" class="Symbol">(</a><a id="16467" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16467" class="Bound">n</a> <a id="16469" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16469" class="Bound">p</a> <a id="16471" class="Symbol">:</a> <a id="16473" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16474" class="Symbol">)</a> <a id="16476" class="Symbol">→</a> <a id="16478" class="Symbol">(</a><a id="16479" class="Number">1</a> <a id="16481" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16483" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16467" class="Bound">n</a><a id="16484" class="Symbol">)</a> <a id="16486" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16488" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16469" class="Bound">p</a> <a id="16490" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16492" class="Number">1</a> <a id="16494" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16496" class="Symbol">(</a><a id="16497" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16467" class="Bound">n</a> <a id="16499" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16501" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16469" class="Bound">p</a><a id="16502" class="Symbol">)</a>
  <a id="16506" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16452" class="Function">+-assoc-1</a> <a id="16516" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a> <a id="16518" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a> <a id="16520" class="Symbol">=</a>
    <a id="16526" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="16538" class="Symbol">(</a><a id="16539" class="Number">1</a> <a id="16541" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16543" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a><a id="16544" class="Symbol">)</a> <a id="16546" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16548" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a>
    <a id="16554" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16564" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16568" class="Symbol">(</a><a id="16569" class="Number">0</a> <a id="16571" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16573" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a><a id="16574" class="Symbol">)</a> <a id="16576" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16578" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a>
    <a id="16584" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16594" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16598" class="Symbol">((</a><a id="16600" class="Number">0</a> <a id="16602" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16604" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a><a id="16605" class="Symbol">)</a> <a id="16607" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16609" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a><a id="16610" class="Symbol">)</a>
    <a id="16616" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16619" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16624" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16628" class="Symbol">(</a><a id="16629" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16716" class="Function">+-assoc-0</a> <a id="16639" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a> <a id="16641" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a><a id="16642" class="Symbol">)</a> <a id="16644" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="16652" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16656" class="Symbol">(</a><a id="16657" class="Number">0</a> <a id="16659" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16661" class="Symbol">(</a><a id="16662" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a> <a id="16664" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16666" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a><a id="16667" class="Symbol">))</a>
    <a id="16674" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16684" class="Number">1</a> <a id="16686" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16688" class="Symbol">(</a><a id="16689" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16516" class="Bound">n</a> <a id="16691" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16693" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16518" class="Bound">p</a><a id="16694" class="Symbol">)</a>
    <a id="16700" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="16706" class="Keyword">where</a>
    <a id="16716" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16716" class="Function">+-assoc-0</a> <a id="16726" class="Symbol">:</a> <a id="16728" class="Symbol">∀</a> <a id="16730" class="Symbol">(</a><a id="16731" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16731" class="Bound">n</a> <a id="16733" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16733" class="Bound">p</a> <a id="16735" class="Symbol">:</a> <a id="16737" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16738" class="Symbol">)</a> <a id="16740" class="Symbol">→</a> <a id="16742" class="Symbol">(</a><a id="16743" class="Number">0</a> <a id="16745" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16747" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16731" class="Bound">n</a><a id="16748" class="Symbol">)</a> <a id="16750" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16752" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16733" class="Bound">p</a> <a id="16754" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16756" class="Number">0</a> <a id="16758" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16760" class="Symbol">(</a><a id="16761" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16731" class="Bound">n</a> <a id="16763" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16765" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16733" class="Bound">p</a><a id="16766" class="Symbol">)</a>
    <a id="16772" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16716" class="Function">+-assoc-0</a> <a id="16782" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16782" class="Bound">n</a> <a id="16784" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16784" class="Bound">p</a> <a id="16786" class="Symbol">=</a>
      <a id="16794" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="16808" class="Symbol">(</a><a id="16809" class="Number">0</a> <a id="16811" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16813" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16782" class="Bound">n</a><a id="16814" class="Symbol">)</a> <a id="16816" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16818" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16784" class="Bound">p</a>
      <a id="16826" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16838" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16782" class="Bound">n</a> <a id="16840" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16842" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16784" class="Bound">p</a>
      <a id="16850" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16862" class="Number">0</a> <a id="16864" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16866" class="Symbol">(</a><a id="16867" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16782" class="Bound">n</a> <a id="16869" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16871" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16784" class="Bound">p</a><a id="16872" class="Symbol">)</a>
      <a id="16880" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}

{::comment}
## Terminology and notation
{:/}

## 术语与记法

{::comment}
The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}/Quantifiers/).
{:/}

在结合律的陈述中出现的符号 `∀` 表示它对于所有的 `m`、`n` 和 `p` 都成立。我们将 `∀` 称为**全称量词**（Universal Quantifier），我们会在
[Quantifiers]({{ site.baseurl }}/Quantifiers/) 章节中进一步讨论。

{::comment}
Evidence for a universal quantifier is a function.  The notations
{:/}

全称量词的证据是一个函数。记法

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
and
{:/}

和

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.
{:/}

是等价的。和 `ℕ → ℕ → ℕ` 这样的函数类型不同，上述函数中的变量与每一个实参类型相关联，且其结果类型可能会涉及（或依赖于）这些变量，因此它们叫做**依赖函数**（Dependent Function）。


{::comment}
## Our second proof: commutativity
{:/}

## 第二个证明：交换律

{::comment}
Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:
{:/}

加法的另一个重要性质是满足**交换律（Commutativity）**，即运算数的顺序无关紧要：

    m + n ≡ n + m

{::comment}
The proof requires that we first demonstrate two lemmas.
{:/}

要证明它，我们需要先证明两条引理（Lemma）。

{::comment}
### The first lemma
{:/}

### 第一条引理

{::comment}
The base case of the definition of addition states that zero
is a left-identity:
{:/}

加法定义的起始步骤说明零是一个左幺元：

    zero + n ≡ n

{::comment}
Our first lemma states that zero is also a right-identity:
{:/}

我们的第一条引理则说明零也是一个右幺元：

    m + zero ≡ m

{::comment}
Here is the lemma's statement and proof:
{:/}

以下是此引理的证明：

{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="18751" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18751" class="Function">+-identityʳ</a> <a id="18763" class="Symbol">:</a> <a id="18765" class="Symbol">∀</a> <a id="18767" class="Symbol">(</a><a id="18768" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18768" class="Bound">m</a> <a id="18770" class="Symbol">:</a> <a id="18772" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18773" class="Symbol">)</a> <a id="18775" class="Symbol">→</a> <a id="18777" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18768" class="Bound">m</a> <a id="18779" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18781" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18786" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18788" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18768" class="Bound">m</a>
<a id="18790" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18751" class="Function">+-identityʳ</a> <a id="18802" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18807" class="Symbol">=</a>
  <a id="18811" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18821" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18826" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18828" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18843" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18850" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="18852" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18751" class="Function">+-identityʳ</a> <a id="18864" class="Symbol">(</a><a id="18865" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18869" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18869" class="Bound">m</a><a id="18870" class="Symbol">)</a> <a id="18872" class="Symbol">=</a>
  <a id="18876" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18886" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18890" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18869" class="Bound">m</a> <a id="18892" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18894" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18901" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18909" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18913" class="Symbol">(</a><a id="18914" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18869" class="Bound">m</a> <a id="18916" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18918" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="18922" class="Symbol">)</a>
  <a id="18926" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18929" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18934" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18938" class="Symbol">(</a><a id="18939" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18751" class="Function">+-identityʳ</a> <a id="18951" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18869" class="Bound">m</a><a id="18952" class="Symbol">)</a> <a id="18954" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18960" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18964" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18869" class="Bound">m</a>
  <a id="18968" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:
{:/}

其签名说明我们定义的标识符 `+-identityʳ` 提供了以下命题的证据：

    ∀ (m : ℕ) → m + zero ≡ m

{::comment}
Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受一个自然数，将其绑定到 `m`，然后返回该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + zero ≡ zero

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很显然。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m) + zero = suc m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + zero) = suc m

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + zero ≡ m

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:
{:/}

阅读此等式链，从上到下和从下到上读都会让我们到达上面化简等式的地方。剩下的等式可由以下依据得出：

    ⟨ cong suc (+-identityʳ m) ⟩

{::comment}
Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.
{:/}

在这里，递归调用的 `+-identityʳ m` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第一条引理证毕。

{::comment}
### The second lemma
{:/}

### 第二条引理

{::comment}
The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:
{:/}

加法定义的归纳步骤将第一个参数的 `suc` 推到了外面：

    suc m + n ≡ suc (m + n)

{::comment}
Our second lemma does the same for `suc` on the second argument:
{:/}

我们的第二条引理则对第二个参数的 `suc` 做同样的事情：

    m + suc n ≡ suc (m + n)

{::comment}
Here is the lemma's statement and proof:
{:/}

下面是该引理的陈述和证明：

{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="21069" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21069" class="Function">+-suc</a> <a id="21075" class="Symbol">:</a> <a id="21077" class="Symbol">∀</a> <a id="21079" class="Symbol">(</a><a id="21080" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21080" class="Bound">m</a> <a id="21082" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21082" class="Bound">n</a> <a id="21084" class="Symbol">:</a> <a id="21086" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21087" class="Symbol">)</a> <a id="21089" class="Symbol">→</a> <a id="21091" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21080" class="Bound">m</a> <a id="21093" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21095" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21099" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21082" class="Bound">n</a> <a id="21101" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="21103" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21107" class="Symbol">(</a><a id="21108" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21080" class="Bound">m</a> <a id="21110" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21112" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21082" class="Bound">n</a><a id="21113" class="Symbol">)</a>
<a id="21115" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21069" class="Function">+-suc</a> <a id="21121" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21126" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21126" class="Bound">n</a> <a id="21128" class="Symbol">=</a>
  <a id="21132" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="21142" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21147" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21149" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21153" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21126" class="Bound">n</a>
  <a id="21157" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21165" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21169" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21126" class="Bound">n</a>
  <a id="21173" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21181" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21185" class="Symbol">(</a><a id="21186" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21191" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21193" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21126" class="Bound">n</a><a id="21194" class="Symbol">)</a>
  <a id="21198" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="21200" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21069" class="Function">+-suc</a> <a id="21206" class="Symbol">(</a><a id="21207" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21211" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a><a id="21212" class="Symbol">)</a> <a id="21214" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a> <a id="21216" class="Symbol">=</a>
  <a id="21220" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="21230" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21234" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a> <a id="21236" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21238" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21242" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a>
  <a id="21246" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21254" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21258" class="Symbol">(</a><a id="21259" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a> <a id="21261" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21263" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21267" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a><a id="21268" class="Symbol">)</a>
  <a id="21272" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="21275" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="21280" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21284" class="Symbol">(</a><a id="21285" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21069" class="Function">+-suc</a> <a id="21291" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a> <a id="21293" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a><a id="21294" class="Symbol">)</a> <a id="21296" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="21302" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21306" class="Symbol">(</a><a id="21307" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21311" class="Symbol">(</a><a id="21312" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a> <a id="21314" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21316" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a><a id="21317" class="Symbol">))</a>
  <a id="21322" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21330" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21334" class="Symbol">(</a><a id="21335" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21339" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21211" class="Bound">m</a> <a id="21341" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21343" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21214" class="Bound">n</a><a id="21344" class="Symbol">)</a>
  <a id="21348" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:
{:/}

其签名说明我们定义的标识符 `+-suc` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

{::comment}
Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，并返回该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + suc n ≡ suc (zero + n)

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很显然。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    suc m + suc n ≡ suc (suc m + n)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + suc n) ≡ suc (suc (m + n))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + suc n ≡ suc (m + n)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:
{:/}

从上到下或从下到上阅读等式链都会让我们在中间遇到化简后的等式。剩下的等式可由以下依据得出：

    ⟨ cong suc (+-suc m n) ⟩

{::comment}
Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.
{:/}

在这里，递归调用的 `+-suc m n` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第二条引理证毕。

{::comment}
### The proposition
{:/}

### 命题

{::comment}
Finally, here is our proposition's statement and proof:
{:/}

最后，以下是我们的命题的陈述和证明：

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="23203" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23203" class="Function">+-comm</a> <a id="23210" class="Symbol">:</a> <a id="23212" class="Symbol">∀</a> <a id="23214" class="Symbol">(</a><a id="23215" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23215" class="Bound">m</a> <a id="23217" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23217" class="Bound">n</a> <a id="23219" class="Symbol">:</a> <a id="23221" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23222" class="Symbol">)</a> <a id="23224" class="Symbol">→</a> <a id="23226" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23215" class="Bound">m</a> <a id="23228" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23230" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23217" class="Bound">n</a> <a id="23232" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23234" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23217" class="Bound">n</a> <a id="23236" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23238" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23215" class="Bound">m</a>
<a id="23240" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23203" class="Function">+-comm</a> <a id="23247" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Bound">m</a> <a id="23249" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23254" class="Symbol">=</a>
  <a id="23258" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23268" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Bound">m</a> <a id="23270" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23272" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="23279" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23282" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18751" class="Function">+-identityʳ</a> <a id="23294" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Bound">m</a> <a id="23296" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23302" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Bound">m</a>
  <a id="23306" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23314" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23319" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23321" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Bound">m</a>
  <a id="23325" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="23327" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23203" class="Function">+-comm</a> <a id="23334" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a> <a id="23336" class="Symbol">(</a><a id="23337" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23341" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a><a id="23342" class="Symbol">)</a> <a id="23344" class="Symbol">=</a>
  <a id="23348" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23358" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a> <a id="23360" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23362" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23366" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a>
  <a id="23370" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23373" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21069" class="Function">+-suc</a> <a id="23379" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a> <a id="23381" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a> <a id="23383" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23389" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23393" class="Symbol">(</a><a id="23394" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a> <a id="23396" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23398" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a><a id="23399" class="Symbol">)</a>
  <a id="23403" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23406" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="23411" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23415" class="Symbol">(</a><a id="23416" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23203" class="Function">+-comm</a> <a id="23423" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a> <a id="23425" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a><a id="23426" class="Symbol">)</a> <a id="23428" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23434" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23438" class="Symbol">(</a><a id="23439" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a> <a id="23441" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23443" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a><a id="23444" class="Symbol">)</a>
  <a id="23448" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23456" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23460" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23341" class="Bound">n</a> <a id="23462" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23464" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23334" class="Bound">m</a>
  <a id="23468" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:
{:/}

第一行说明我们定义的标识符 `+-comm` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，并返回该等式对应实例的证据。它通过对 `n` 进行归纳来证明。（这次不是 `m`！）

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    m + zero ≡ zero + m

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    m + zero ≡ m

{::comment}
The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.
{:/}

剩下的等式可由依据 `⟨ +-identityʳ m ⟩` 得出，它调用第一条引理。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    m + suc n ≡ suc n + m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    m + suc n ≡ suc (n + m)

{::comment}
We show this in two steps.  First, we have:
{:/}

我们分两步来证明它。首先，我们有：

    m + suc n ≡ suc (m + n)

{::comment}
which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have
{:/}

它依据第二条引理 `⟨ +-suc m n ⟩` 得出。之后我们有：

    suc (m + n) ≡ suc (n + m)

{::comment}
which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.
{:/}

它依据合同性和归纳假设 `⟨ cong suc (+-comm m n) ⟩` 得出。证毕。

{::comment}
Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.
{:/}

Agda 要求标识符必须在使用前定义，因此我们必须在主命题之前列出引理，如前例所示。在实践中，我们通常会先试着证明主命题，之后所需的等式会说明需要证明哪些引理。


{::comment}
## Our first corollary: rearranging {#sections}
{:/}

## 第一个推论：重排定理 {#sections}

{::comment}
We can apply associativity to rearrange parentheses however we like.
Here is an example:
{:/}

我们可以随意应用结合律来重排括号。例如：

{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="25710" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25710" class="Function">+-rearrange</a> <a id="25722" class="Symbol">:</a> <a id="25724" class="Symbol">∀</a> <a id="25726" class="Symbol">(</a><a id="25727" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25727" class="Bound">m</a> <a id="25729" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25729" class="Bound">n</a> <a id="25731" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25731" class="Bound">p</a> <a id="25733" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25733" class="Bound">q</a> <a id="25735" class="Symbol">:</a> <a id="25737" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25738" class="Symbol">)</a> <a id="25740" class="Symbol">→</a> <a id="25742" class="Symbol">(</a><a id="25743" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25727" class="Bound">m</a> <a id="25745" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25747" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25729" class="Bound">n</a><a id="25748" class="Symbol">)</a> <a id="25750" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25752" class="Symbol">(</a><a id="25753" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25731" class="Bound">p</a> <a id="25755" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25757" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25733" class="Bound">q</a><a id="25758" class="Symbol">)</a> <a id="25760" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25762" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25727" class="Bound">m</a> <a id="25764" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25766" class="Symbol">(</a><a id="25767" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25729" class="Bound">n</a> <a id="25769" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25771" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25731" class="Bound">p</a><a id="25772" class="Symbol">)</a> <a id="25774" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25776" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25733" class="Bound">q</a>
<a id="25778" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25710" class="Function">+-rearrange</a> <a id="25790" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25792" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25794" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a> <a id="25796" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a> <a id="25798" class="Symbol">=</a>
  <a id="25802" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="25812" class="Symbol">(</a><a id="25813" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25815" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25817" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a><a id="25818" class="Symbol">)</a> <a id="25820" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25822" class="Symbol">(</a><a id="25823" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a> <a id="25825" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25827" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25828" class="Symbol">)</a>
  <a id="25832" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25835" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="25843" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25845" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25847" class="Symbol">(</a><a id="25848" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a> <a id="25850" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25852" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25853" class="Symbol">)</a> <a id="25855" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25861" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25863" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25865" class="Symbol">(</a><a id="25866" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25868" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25870" class="Symbol">(</a><a id="25871" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a> <a id="25873" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25875" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25876" class="Symbol">))</a>
  <a id="25881" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25884" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="25889" class="Symbol">(</a><a id="25890" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25892" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="25894" class="Symbol">)</a> <a id="25896" class="Symbol">(</a><a id="25897" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25901" class="Symbol">(</a><a id="25902" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="25910" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25912" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a> <a id="25914" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25915" class="Symbol">))</a> <a id="25918" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25924" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25926" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25928" class="Symbol">((</a><a id="25930" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25932" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25934" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a><a id="25935" class="Symbol">)</a> <a id="25937" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25939" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25940" class="Symbol">)</a>
  <a id="25944" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25947" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25951" class="Symbol">(</a><a id="25952" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11558" class="Function">+-assoc</a> <a id="25960" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25962" class="Symbol">(</a><a id="25963" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25965" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25967" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a><a id="25968" class="Symbol">)</a> <a id="25970" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a><a id="25971" class="Symbol">)</a> <a id="25973" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25979" class="Symbol">(</a><a id="25980" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25790" class="Bound">m</a> <a id="25982" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25984" class="Symbol">(</a><a id="25985" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25792" class="Bound">n</a> <a id="25987" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25989" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25794" class="Bound">p</a><a id="25990" class="Symbol">))</a> <a id="25993" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25995" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25796" class="Bound">q</a>
  <a id="25999" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
No induction is required, we simply apply associativity twice.
A few points are worthy of note.
{:/}

无需归纳法，我们只不过应用了两次结合律就完成了证明。其中有几点需要注意的地方。

{::comment}
First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.
{:/}

第一，加法是左结合的，因此 `m + (n + p) + q` 表示 `(m + (n + p)) + q`。

{::comment}
Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:
{:/}

第二，我们用 `sym` 来交换等式的两边。命题 `+-assoc n p q` 会将括号从右边移到左边：

    (n + p) + q ≡ n + (p + q)

{::comment}
To shift them the other way, we use `sym (+-assoc m n p)`:
{:/}

要往另一个方向移动括号，我们要用 `sym (+-assoc m n p)`：

    n + (p + q) ≡ (n + p) + q

{::comment}
In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.
{:/}

一般来说，若 `e` 提供了 `x ≡ y` 的证据，那么 `sym e` 就提供了 `y ≡ x` 的证据。

{::comment}
Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:
{:/}

第三，Agda 支持 Richard Bird 引入的**片段（Section）**记法。我们将应用到
`y` 并返回 `x + y` 的函数写作 `(x +_)`。因此，应用合同性 `cong (m +_)`
会将上面的等式转换成：

    m + (n + (p + q)) ≡ m + ((n + p) + q)

{::comment}
Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.
{:/}

类似地，我们将应用到 `y` 并返回 `y + x` 的函数写作 `(_+ x)`。这同样适用于任何中缀运算符。


{::comment}
## Creation, one last time
{:/}

## 创世，最后一次

{::comment}
Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:
{:/}

我们回到结合律的证明上来，把归纳证明（或等价的递归定义）看做一个创世故事会有助于理解。这次我们专注于判断结合律的断言：

{::comment}
     -- In the beginning, we know nothing about associativity.
{:/}

     -- 起初，我们对结合律一无所知。

{::comment}
Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if
`(m + n) + p ≡ m + (n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:
{:/}

现在，我们将规则应用到所有已知的判断上来。起始步骤告诉我们对于所有的自然数
`n` 和 `p` 来说，`(zero + n) + p ≡ zero + (n + p)`。归纳步骤告我我们若
`(m + n) + p ≡ m + (n + p)`（在昨天）成立，那么 `(suc m + n) + p ≡ suc m + (n + p)`
（在今天）也成立。我们在今天之前并不知道任何关于结合律的判断，因此此规则并未给出任何新的判断：

{::comment}
    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
{:/}

    -- 第一天，我们知道了关于 0 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

{::comment}
Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:
{:/}

之后我们重复此过程，因此接下来一天我们知道今天以前的所有判断，以及任何通过此规则添加的判断。起始步骤并未告诉我们新的东西，而如今归归纳步骤添加了更多的判断：

{::comment}
    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
{:/}

    -- 第二天，我们知道了关于 0 和 1 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

{::comment}
And we repeat the process again:
{:/}

我们再次重复此过程：

{::comment}
    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
{:/}

    -- 第三天，我们知道了关于 0、1 和 2 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...
{:/}

    -- 第四天，我们知道了关于 0、1、2 和 3 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

{::comment}
The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.
{:/}

此过程可以继续下去。在第 *m* 天我们会知道所有第一个数小于 *m* 的判断。

{::comment}
There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.
{:/}

还有一种完全有限的方法来生成同样的等式，它的证明留作读者的练习。

{::comment}
#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}
{:/}

#### 练习 `finite-+-assoc`（延伸） {#finite-plus-assoc}

{::comment}
Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).
{:/}

请参考[前文]({{ site.baseurl }}/Naturals/#finite-creation)
写出前四天已知的加法结合律的创世故事。

{::comment}
{% raw %}<pre class="Agda"><a id="31688" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31725" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Associativity with rewrite
{:/}

## 用改写来证明结合律

{::comment}
There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{:/}

证明可不止一种方法。下面是第二种在 Agda 中证明加法结合律的方法，使用 `rewrite`（改写）
而非等式链：

{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="32040" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32040" class="Function">+-assoc′</a> <a id="32049" class="Symbol">:</a> <a id="32051" class="Symbol">∀</a> <a id="32053" class="Symbol">(</a><a id="32054" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32054" class="Bound">m</a> <a id="32056" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32056" class="Bound">n</a> <a id="32058" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32058" class="Bound">p</a> <a id="32060" class="Symbol">:</a> <a id="32062" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32063" class="Symbol">)</a> <a id="32065" class="Symbol">→</a> <a id="32067" class="Symbol">(</a><a id="32068" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32054" class="Bound">m</a> <a id="32070" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32072" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32056" class="Bound">n</a><a id="32073" class="Symbol">)</a> <a id="32075" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32077" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32058" class="Bound">p</a> <a id="32079" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="32081" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32054" class="Bound">m</a> <a id="32083" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32085" class="Symbol">(</a><a id="32086" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32056" class="Bound">n</a> <a id="32088" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32090" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32058" class="Bound">p</a><a id="32091" class="Symbol">)</a>
<a id="32093" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32040" class="Function">+-assoc′</a> <a id="32102" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="32110" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32110" class="Bound">n</a> <a id="32112" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32112" class="Bound">p</a>                          <a id="32139" class="Symbol">=</a>  <a id="32142" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="32147" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32040" class="Function">+-assoc′</a> <a id="32156" class="Symbol">(</a><a id="32157" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="32161" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32161" class="Bound">m</a><a id="32162" class="Symbol">)</a> <a id="32164" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32164" class="Bound">n</a> <a id="32166" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32166" class="Bound">p</a>  <a id="32169" class="Keyword">rewrite</a> <a id="32177" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32040" class="Function">+-assoc′</a> <a id="32186" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32161" class="Bound">m</a> <a id="32188" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32164" class="Bound">n</a> <a id="32190" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32166" class="Bound">p</a>  <a id="32193" class="Symbol">=</a>  <a id="32196" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    n + p ≡ n + p

{::comment}
This holds trivially. The proof that a term is equal to itself is written `refl`.
{:/}

此式平凡成立。一个项等于其自身的证明写作 `refl`（自反性）。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.
{:/}

在根据归纳假设改写后，这两项相等，其证明同样由 `refl` 给出。根据给定的等式进行改写可用关键字 `rewrite` 后跟一个该等式的证明来表示。改写不仅可以省去等式链还可以避免调用 `cong`.


{::comment}
## Commutativity with rewrite
{:/}

## 使用改写证明交换律

{::comment}
Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{:/}

下面是加法交换律的第二个证明，使用 `rewrite` 而非等式链：

{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="33498" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33498" class="Function">+-identity′</a> <a id="33510" class="Symbol">:</a> <a id="33512" class="Symbol">∀</a> <a id="33514" class="Symbol">(</a><a id="33515" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33515" class="Bound">n</a> <a id="33517" class="Symbol">:</a> <a id="33519" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33520" class="Symbol">)</a> <a id="33522" class="Symbol">→</a> <a id="33524" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33515" class="Bound">n</a> <a id="33526" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33528" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33533" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33535" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33515" class="Bound">n</a>
<a id="33537" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33498" class="Function">+-identity′</a> <a id="33549" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33554" class="Symbol">=</a> <a id="33556" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33561" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33498" class="Function">+-identity′</a> <a id="33573" class="Symbol">(</a><a id="33574" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33578" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33578" class="Bound">n</a><a id="33579" class="Symbol">)</a> <a id="33581" class="Keyword">rewrite</a> <a id="33589" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33498" class="Function">+-identity′</a> <a id="33601" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33578" class="Bound">n</a> <a id="33603" class="Symbol">=</a> <a id="33605" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="33611" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33611" class="Function">+-suc′</a> <a id="33618" class="Symbol">:</a> <a id="33620" class="Symbol">∀</a> <a id="33622" class="Symbol">(</a><a id="33623" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33623" class="Bound">m</a> <a id="33625" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33625" class="Bound">n</a> <a id="33627" class="Symbol">:</a> <a id="33629" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33630" class="Symbol">)</a> <a id="33632" class="Symbol">→</a> <a id="33634" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33623" class="Bound">m</a> <a id="33636" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33638" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33642" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33625" class="Bound">n</a> <a id="33644" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33646" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33650" class="Symbol">(</a><a id="33651" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33623" class="Bound">m</a> <a id="33653" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33655" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33625" class="Bound">n</a><a id="33656" class="Symbol">)</a>
<a id="33658" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33611" class="Function">+-suc′</a> <a id="33665" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33670" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33670" class="Bound">n</a> <a id="33672" class="Symbol">=</a> <a id="33674" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33679" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33611" class="Function">+-suc′</a> <a id="33686" class="Symbol">(</a><a id="33687" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33691" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33691" class="Bound">m</a><a id="33692" class="Symbol">)</a> <a id="33694" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33694" class="Bound">n</a> <a id="33696" class="Keyword">rewrite</a> <a id="33704" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33611" class="Function">+-suc′</a> <a id="33711" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33691" class="Bound">m</a> <a id="33713" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33694" class="Bound">n</a> <a id="33715" class="Symbol">=</a> <a id="33717" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="33723" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33723" class="Function">+-comm′</a> <a id="33731" class="Symbol">:</a> <a id="33733" class="Symbol">∀</a> <a id="33735" class="Symbol">(</a><a id="33736" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33736" class="Bound">m</a> <a id="33738" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33738" class="Bound">n</a> <a id="33740" class="Symbol">:</a> <a id="33742" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33743" class="Symbol">)</a> <a id="33745" class="Symbol">→</a> <a id="33747" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33736" class="Bound">m</a> <a id="33749" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33751" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33738" class="Bound">n</a> <a id="33753" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33755" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33738" class="Bound">n</a> <a id="33757" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33759" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33736" class="Bound">m</a>
<a id="33761" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33723" class="Function">+-comm′</a> <a id="33769" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33769" class="Bound">m</a> <a id="33771" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33776" class="Keyword">rewrite</a> <a id="33784" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33498" class="Function">+-identity′</a> <a id="33796" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33769" class="Bound">m</a> <a id="33798" class="Symbol">=</a> <a id="33800" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33805" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33723" class="Function">+-comm′</a> <a id="33813" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33813" class="Bound">m</a> <a id="33815" class="Symbol">(</a><a id="33816" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33820" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33820" class="Bound">n</a><a id="33821" class="Symbol">)</a> <a id="33823" class="Keyword">rewrite</a> <a id="33831" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33611" class="Function">+-suc′</a> <a id="33838" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33813" class="Bound">m</a> <a id="33840" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33820" class="Bound">n</a> <a id="33842" class="Symbol">|</a> <a id="33844" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33723" class="Function">+-comm′</a> <a id="33852" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33813" class="Bound">m</a> <a id="33854" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33820" class="Bound">n</a> <a id="33856" class="Symbol">=</a> <a id="33858" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.
{:/}

在最后一行中，用两个等式进行改写被表示为用一条竖线分隔两个相关等式的证明。左边的改写会在右边之前被执行。


{::comment}
## Building proofs interactively
{:/}

## 交互式构造证明

{::comment}
It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:
{:/}

看看如何在 Emacs 中用 Agda 的交互式特性来构造另一种结合律的证明会很有启发性。我们从输入以下内容开始：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

{::comment}
The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:
{:/}

其中的问号表示你想要 Agda 帮你填充的代码。如果你按下 `C-c C-l`
（先按 Ctrl-c 再按 Ctrl-l），那么问号会被替换为：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

{::comment}
The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:
{:/}

空的大括号叫做**洞（Hole）**，0 是用来指代此洞的编号。洞可能会以绿色高亮显示。
Emacs 还会在屏幕下方创建一个新的窗口并显示文本：

    ?0 : ((m + n) + p) ≡ (m + (n + p))

{::comment}
This indicates that hole 0 is to be filled in with a proof of
the stated judgment.
{:/}

这表示 0 号洞需要以所提示的判断的证明来填充。

{::comment}
We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:
{:/}

我们希望对 `m` 进行归纳来证明此命题。将光标移动到洞中并按下
`C-c C-c`。它会给出提示：

    pattern variables to case (empty for split on result):

{::comment}
Typing `m` will cause a split on that variable, resulting
in an update to the code:
{:/}

按下 `m` 会拆分该变量，并更新此代码：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

{::comment}
There are now two holes, and the window at the bottom tells you what
each is required to prove:
{:/}

现在有两个洞了，下方的窗口会告诉你每个洞中需要证明的内容：

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

{::comment}
Going into hole 0 and typing `C-c C-,` will display the text:
{:/}

进入 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

{::comment}
This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:
{:/}

它表示在化简之后，0 号洞的目标如上所示，所示类型的变量 `p` 和 `n` 可在证明中使用。给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充。按下 `C-c C-l`
会将剩下的洞重新编号为 0：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

{::comment}
Going into the new hole 0 and typing `C-c C-,` will display the text:
{:/}

进入新的 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:
{:/}

同样，它会给出化简后的目标和可用的变量。在此步骤中，我们需要根据归纳假设进行改写，于是我们来编辑这些文本：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

{::comment}
Going into the remaining hole and typing `C-c C-,` will display the text:
{:/}

进入剩下的洞中并按下 `C-c C-,` 会显示以下文本：

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:
{:/}

给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充并完成证明：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


{::comment}
#### Exercise `+-swap` (recommended) {#plus-swap}
{:/}

#### 练习：`+-swap`（推荐） {#plus-swap}

{::comment}
Show
{:/}

请证明对于所有的自然数 `m`、`n` 和 `p`，

    m + (n + p) ≡ n + (m + p)

{::comment}
for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.
{:/}

成立。无需归纳证明，只需应用前面满足结合律和交换律的结果即可。

{::comment}
{% raw %}<pre class="Agda"><a id="38529" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38566" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}
{:/}

#### 练习 `*-distrib-+`（推荐） {#times-distrib-plus}

{::comment}
Show multiplication distributes over addition, that is,
{:/}

请证明乘法对加法满足分配律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m + n) * p ≡ m * p + n * p

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
{% raw %}<pre class="Agda"><a id="38937" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38974" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `*-assoc` (recommended) {#times-assoc}
{:/}

#### 练习 `*-assoc`（推荐） {#times-assoc}

{::comment}
Show multiplication is associative, that is,
{:/}

请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m * n) * p ≡ m * (n * p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
{% raw %}<pre class="Agda"><a id="39307" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39344" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `*-comm` (practice) {#times-comm}
{:/}

#### 练习 `*-comm`（实践） {#times-comm}

{::comment}
Show multiplication is commutative, that is,
{:/}

请证明乘法满足交换律，即对于所有的自然数 `m` 和 `n`，

    m * n ≡ n * m

{::comment}
for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.
{:/}

成立。和加法交换律一样，你需要陈述并证明配套的引理。

{::comment}
{% raw %}<pre class="Agda"><a id="39761" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39798" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `0∸n≡0` (practice) {#zero-monus}
{:/}

#### 练习 `0∸n≡0`（实践） {#zero-monus}

{::comment}
Show
{:/}

请证明对于所有的自然数 `n`，

    zero ∸ n ≡ zero

{::comment}
for all naturals `n`. Did your proof require induction?
{:/}

成立。你的证明需要归纳法吗？

{::comment}
{% raw %}<pre class="Agda"><a id="40085" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="40122" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}
{:/}

#### 练习 `∸-+-assoc`（实践） {#monus-plus-assoc}

{::comment}
Show that monus associates with addition, that is,
{:/}

请证明饱和减法与加法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    m ∸ n ∸ p ≡ m ∸ (n + p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
{% raw %}<pre class="Agda"><a id="40476" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="40513" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `+*^` (stretch)
{:/}

#### 练习 `+*^` （延伸）

{::comment}
Show the following three laws
{:/}

证明下列三条定律

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

{::comment}
for all `m`, `n`, and `p`.
{:/}

对于所有 `m`、`n` 和 `p` 成立。

{::comment}
#### Exercise `Bin-laws` (stretch) {#Bin-laws}
{:/}

#### 练习 `Bin-laws`（延伸） {#Bin-laws}

{::comment}
Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions
{:/}

回想练习 [Bin]({{ site.baseurl }}/Naturals/#Bin)
中定义的一种表示自然数的比特串数据类型 `Bin`
以及要求你定义的函数：

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

{::comment}
Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:
{:/}

考虑以下定律，其中 `n` 表示自然数，`b` 表示比特串：

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

{::comment}
For each law: if it holds, prove; if not, give a counterexample.
{:/}

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

{::comment}
{% raw %}<pre class="Agda"><a id="41654" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="41691" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中类似的定义可在标准库中找到：

{% raw %}<pre class="Agda"><a id="41880" class="Keyword">import</a> <a id="41887" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="41907" class="Keyword">using</a> <a id="41913" class="Symbol">(</a><a id="41914" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="41921" class="Symbol">;</a> <a id="41923" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="41934" class="Symbol">;</a> <a id="41936" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="41941" class="Symbol">;</a> <a id="41943" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="41949" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Unicode
{:/}

## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

本章中使用了以下 Unicode：

{::comment}
    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')
{:/}

    ∀  U+2200  对于所有 (\forall, \all)
    ʳ  U+02B3  修饰符小写字母 r (\^r)
    ′  U+2032  撇号 (\')
    ″  U+2033  双撇号 (\')
    ‴  U+2034  三撇号 (\')
    ⁗  U+2057  四撇号 (\')

{::comment}
Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
{:/}

与 `\r` 类似，命令 `\^r` 列出了多种上标右箭头的变体，以及上标的字母 `r`。命令 `\'` 列出了一些撇号（`′ ″ ‴ ⁗`）。
