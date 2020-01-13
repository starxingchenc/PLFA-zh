---
src       : "src/plfa/Induction.lagda.md"
title     : "Induction: 归纳证明"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
translators : ["Oling Cat"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="176" class="Keyword">module</a> <a id="183" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.Induction</a> <a id="198" class="Keyword">where</a>
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

{% raw %}<pre class="Agda"><a id="1093" class="Keyword">import</a> <a id="1100" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1138" class="Symbol">as</a> <a id="1141" class="Module">Eq</a>
<a id="1144" class="Keyword">open</a> <a id="1149" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1152" class="Keyword">using</a> <a id="1158" class="Symbol">(</a><a id="1159" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1162" class="Symbol">;</a> <a id="1164" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1168" class="Symbol">;</a> <a id="1170" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1174" class="Symbol">;</a> <a id="1176" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1179" class="Symbol">)</a>
<a id="1181" class="Keyword">open</a> <a id="1186" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1201" class="Keyword">using</a> <a id="1207" class="Symbol">(</a><a id="1208" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1214" class="Symbol">;</a> <a id="1216" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1221" class="Symbol">;</a> <a id="1223" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1229" class="Symbol">;</a> <a id="1231" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1233" class="Symbol">)</a>
<a id="1235" class="Keyword">open</a> <a id="1240" class="Keyword">import</a> <a id="1247" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1256" class="Keyword">using</a> <a id="1262" class="Symbol">(</a><a id="1263" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1264" class="Symbol">;</a> <a id="1266" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1270" class="Symbol">;</a> <a id="1272" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1275" class="Symbol">;</a> <a id="1277" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1280" class="Symbol">;</a> <a id="1282" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1285" class="Symbol">;</a> <a id="1287" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1290" class="Symbol">)</a>
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
#### Exercise `operators` {#operators}
{:/}

#### 练习 `operators` {#operators}

{::comment}
Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
{:/}

请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配律。

{::comment}
{% raw %}<pre class="Agda"><a id="4280" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="4317" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Give an example of an operator that has an identity and is
associative but is not commutative.
{:/}

请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。

{::comment}
{% raw %}<pre class="Agda"><a id="4497" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="4534" class="Comment">-- 请将代码写在此处。</a>
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

{% raw %}<pre class="Agda"><a id="5050" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#5050" class="Function">_</a> <a id="5052" class="Symbol">:</a> <a id="5054" class="Symbol">(</a><a id="5055" class="Number">3</a> <a id="5057" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5059" class="Number">4</a><a id="5060" class="Symbol">)</a> <a id="5062" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5064" class="Number">5</a> <a id="5066" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5068" class="Number">3</a> <a id="5070" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5072" class="Symbol">(</a><a id="5073" class="Number">4</a> <a id="5075" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5077" class="Number">5</a><a id="5078" class="Symbol">)</a>
<a id="5080" class="Symbol">_</a> <a id="5082" class="Symbol">=</a>
  <a id="5086" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="5096" class="Symbol">(</a><a id="5097" class="Number">3</a> <a id="5099" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5101" class="Number">4</a><a id="5102" class="Symbol">)</a> <a id="5104" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5106" class="Number">5</a>
  <a id="5110" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5118" class="Number">7</a> <a id="5120" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5122" class="Number">5</a>
  <a id="5126" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5134" class="Number">12</a>
  <a id="5139" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5147" class="Number">3</a> <a id="5149" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5151" class="Number">9</a>
  <a id="5155" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5163" class="Number">3</a> <a id="5165" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5167" class="Symbol">(</a><a id="5168" class="Number">4</a> <a id="5170" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5172" class="Number">5</a><a id="5173" class="Symbol">)</a>
  <a id="5177" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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

{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="11513" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="11521" class="Symbol">:</a> <a id="11523" class="Symbol">∀</a> <a id="11525" class="Symbol">(</a><a id="11526" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11526" class="Bound">m</a> <a id="11528" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11528" class="Bound">n</a> <a id="11530" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11530" class="Bound">p</a> <a id="11532" class="Symbol">:</a> <a id="11534" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11535" class="Symbol">)</a> <a id="11537" class="Symbol">→</a> <a id="11539" class="Symbol">(</a><a id="11540" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11526" class="Bound">m</a> <a id="11542" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11544" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11528" class="Bound">n</a><a id="11545" class="Symbol">)</a> <a id="11547" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11549" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11530" class="Bound">p</a> <a id="11551" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11553" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11526" class="Bound">m</a> <a id="11555" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11557" class="Symbol">(</a><a id="11558" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11528" class="Bound">n</a> <a id="11560" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11562" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11530" class="Bound">p</a><a id="11563" class="Symbol">)</a>
<a id="11565" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="11573" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11578" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11578" class="Bound">n</a> <a id="11580" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11580" class="Bound">p</a> <a id="11582" class="Symbol">=</a>
  <a id="11586" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11596" class="Symbol">(</a><a id="11597" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11602" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11604" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11578" class="Bound">n</a><a id="11605" class="Symbol">)</a> <a id="11607" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11609" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11580" class="Bound">p</a>
  <a id="11613" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11621" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11578" class="Bound">n</a> <a id="11623" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11625" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11580" class="Bound">p</a>
  <a id="11629" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11637" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11642" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11644" class="Symbol">(</a><a id="11645" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11578" class="Bound">n</a> <a id="11647" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11649" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11580" class="Bound">p</a><a id="11650" class="Symbol">)</a>
  <a id="11654" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="11656" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="11664" class="Symbol">(</a><a id="11665" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11669" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a><a id="11670" class="Symbol">)</a> <a id="11672" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a> <a id="11674" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a> <a id="11676" class="Symbol">=</a>
  <a id="11680" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11690" class="Symbol">(</a><a id="11691" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11695" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11697" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11699" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a><a id="11700" class="Symbol">)</a> <a id="11702" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11704" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a>
  <a id="11708" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11716" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11720" class="Symbol">(</a><a id="11721" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11723" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11725" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a><a id="11726" class="Symbol">)</a> <a id="11728" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11730" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a>
  <a id="11734" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11742" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11746" class="Symbol">((</a><a id="11748" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11750" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11752" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a><a id="11753" class="Symbol">)</a> <a id="11755" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11757" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a><a id="11758" class="Symbol">)</a>
  <a id="11762" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11765" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11770" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11774" class="Symbol">(</a><a id="11775" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="11783" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11785" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a> <a id="11787" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a><a id="11788" class="Symbol">)</a> <a id="11790" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11796" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11800" class="Symbol">(</a><a id="11801" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11803" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11805" class="Symbol">(</a><a id="11806" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a> <a id="11808" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11810" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a><a id="11811" class="Symbol">))</a>
  <a id="11816" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11824" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11828" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11669" class="Bound">m</a> <a id="11830" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11832" class="Symbol">(</a><a id="11833" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11672" class="Bound">n</a> <a id="11835" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11837" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11674" class="Bound">p</a><a id="11838" class="Symbol">)</a>
  <a id="11842" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="16171" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16171" class="Function">+-assoc-2</a> <a id="16181" class="Symbol">:</a> <a id="16183" class="Symbol">∀</a> <a id="16185" class="Symbol">(</a><a id="16186" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16186" class="Bound">n</a> <a id="16188" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16188" class="Bound">p</a> <a id="16190" class="Symbol">:</a> <a id="16192" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16193" class="Symbol">)</a> <a id="16195" class="Symbol">→</a> <a id="16197" class="Symbol">(</a><a id="16198" class="Number">2</a> <a id="16200" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16202" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16186" class="Bound">n</a><a id="16203" class="Symbol">)</a> <a id="16205" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16207" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16188" class="Bound">p</a> <a id="16209" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16211" class="Number">2</a> <a id="16213" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16215" class="Symbol">(</a><a id="16216" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16186" class="Bound">n</a> <a id="16218" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16220" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16188" class="Bound">p</a><a id="16221" class="Symbol">)</a>
<a id="16223" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16171" class="Function">+-assoc-2</a> <a id="16233" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16235" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a> <a id="16237" class="Symbol">=</a>
  <a id="16241" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16251" class="Symbol">(</a><a id="16252" class="Number">2</a> <a id="16254" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16256" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a><a id="16257" class="Symbol">)</a> <a id="16259" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16261" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a>
  <a id="16265" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16273" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16277" class="Symbol">(</a><a id="16278" class="Number">1</a> <a id="16280" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16282" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a><a id="16283" class="Symbol">)</a> <a id="16285" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16287" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a>
  <a id="16291" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16299" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16303" class="Symbol">((</a><a id="16305" class="Number">1</a> <a id="16307" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16309" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a><a id="16310" class="Symbol">)</a> <a id="16312" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16314" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a><a id="16315" class="Symbol">)</a>
  <a id="16319" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16322" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16327" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16331" class="Symbol">(</a><a id="16332" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16407" class="Function">+-assoc-1</a> <a id="16342" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16344" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a><a id="16345" class="Symbol">)</a> <a id="16347" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16353" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16357" class="Symbol">(</a><a id="16358" class="Number">1</a> <a id="16360" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16362" class="Symbol">(</a><a id="16363" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16365" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16367" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a><a id="16368" class="Symbol">))</a>
  <a id="16373" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16381" class="Number">2</a> <a id="16383" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16385" class="Symbol">(</a><a id="16386" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16388" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16390" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a><a id="16391" class="Symbol">)</a>
  <a id="16395" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="16399" class="Keyword">where</a>
  <a id="16407" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16407" class="Function">+-assoc-1</a> <a id="16417" class="Symbol">:</a> <a id="16419" class="Symbol">∀</a> <a id="16421" class="Symbol">(</a><a id="16422" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16422" class="Bound">n</a> <a id="16424" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16424" class="Bound">p</a> <a id="16426" class="Symbol">:</a> <a id="16428" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16429" class="Symbol">)</a> <a id="16431" class="Symbol">→</a> <a id="16433" class="Symbol">(</a><a id="16434" class="Number">1</a> <a id="16436" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16438" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16422" class="Bound">n</a><a id="16439" class="Symbol">)</a> <a id="16441" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16443" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16424" class="Bound">p</a> <a id="16445" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16447" class="Number">1</a> <a id="16449" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16451" class="Symbol">(</a><a id="16452" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16422" class="Bound">n</a> <a id="16454" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16456" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16424" class="Bound">p</a><a id="16457" class="Symbol">)</a>
  <a id="16461" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16407" class="Function">+-assoc-1</a> <a id="16471" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a> <a id="16473" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a> <a id="16475" class="Symbol">=</a>
    <a id="16481" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="16493" class="Symbol">(</a><a id="16494" class="Number">1</a> <a id="16496" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16498" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a><a id="16499" class="Symbol">)</a> <a id="16501" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16503" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a>
    <a id="16509" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16519" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16523" class="Symbol">(</a><a id="16524" class="Number">0</a> <a id="16526" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16528" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a><a id="16529" class="Symbol">)</a> <a id="16531" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16533" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a>
    <a id="16539" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16549" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16553" class="Symbol">((</a><a id="16555" class="Number">0</a> <a id="16557" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16559" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a><a id="16560" class="Symbol">)</a> <a id="16562" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16564" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a><a id="16565" class="Symbol">)</a>
    <a id="16571" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16574" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16579" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16583" class="Symbol">(</a><a id="16584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16671" class="Function">+-assoc-0</a> <a id="16594" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a> <a id="16596" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a><a id="16597" class="Symbol">)</a> <a id="16599" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="16607" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16611" class="Symbol">(</a><a id="16612" class="Number">0</a> <a id="16614" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16616" class="Symbol">(</a><a id="16617" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a> <a id="16619" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16621" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a><a id="16622" class="Symbol">))</a>
    <a id="16629" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16639" class="Number">1</a> <a id="16641" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16643" class="Symbol">(</a><a id="16644" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16471" class="Bound">n</a> <a id="16646" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16648" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16473" class="Bound">p</a><a id="16649" class="Symbol">)</a>
    <a id="16655" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="16661" class="Keyword">where</a>
    <a id="16671" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16671" class="Function">+-assoc-0</a> <a id="16681" class="Symbol">:</a> <a id="16683" class="Symbol">∀</a> <a id="16685" class="Symbol">(</a><a id="16686" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16686" class="Bound">n</a> <a id="16688" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16688" class="Bound">p</a> <a id="16690" class="Symbol">:</a> <a id="16692" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16693" class="Symbol">)</a> <a id="16695" class="Symbol">→</a> <a id="16697" class="Symbol">(</a><a id="16698" class="Number">0</a> <a id="16700" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16702" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16686" class="Bound">n</a><a id="16703" class="Symbol">)</a> <a id="16705" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16707" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16688" class="Bound">p</a> <a id="16709" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16711" class="Number">0</a> <a id="16713" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16715" class="Symbol">(</a><a id="16716" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16686" class="Bound">n</a> <a id="16718" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16720" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16688" class="Bound">p</a><a id="16721" class="Symbol">)</a>
    <a id="16727" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16671" class="Function">+-assoc-0</a> <a id="16737" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16737" class="Bound">n</a> <a id="16739" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16739" class="Bound">p</a> <a id="16741" class="Symbol">=</a>
      <a id="16749" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="16763" class="Symbol">(</a><a id="16764" class="Number">0</a> <a id="16766" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16768" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16737" class="Bound">n</a><a id="16769" class="Symbol">)</a> <a id="16771" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16773" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16739" class="Bound">p</a>
      <a id="16781" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16793" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16737" class="Bound">n</a> <a id="16795" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16797" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16739" class="Bound">p</a>
      <a id="16805" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16817" class="Number">0</a> <a id="16819" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16821" class="Symbol">(</a><a id="16822" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16737" class="Bound">n</a> <a id="16824" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16826" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16739" class="Bound">p</a><a id="16827" class="Symbol">)</a>
      <a id="16835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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
in that variables are associated with the each argument type, and the
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

{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="18710" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18710" class="Function">+-identityʳ</a> <a id="18722" class="Symbol">:</a> <a id="18724" class="Symbol">∀</a> <a id="18726" class="Symbol">(</a><a id="18727" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18727" class="Bound">m</a> <a id="18729" class="Symbol">:</a> <a id="18731" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18732" class="Symbol">)</a> <a id="18734" class="Symbol">→</a> <a id="18736" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18727" class="Bound">m</a> <a id="18738" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18740" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18745" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18747" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18727" class="Bound">m</a>
<a id="18749" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18710" class="Function">+-identityʳ</a> <a id="18761" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18766" class="Symbol">=</a>
  <a id="18770" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18780" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18785" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18787" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18794" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18802" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18809" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="18811" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18710" class="Function">+-identityʳ</a> <a id="18823" class="Symbol">(</a><a id="18824" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18828" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18828" class="Bound">m</a><a id="18829" class="Symbol">)</a> <a id="18831" class="Symbol">=</a>
  <a id="18835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18845" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18849" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18828" class="Bound">m</a> <a id="18851" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18853" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18860" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18868" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18872" class="Symbol">(</a><a id="18873" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18828" class="Bound">m</a> <a id="18875" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18877" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="18881" class="Symbol">)</a>
  <a id="18885" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18888" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18893" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18897" class="Symbol">(</a><a id="18898" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18710" class="Function">+-identityʳ</a> <a id="18910" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18828" class="Bound">m</a><a id="18911" class="Symbol">)</a> <a id="18913" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18919" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18923" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18828" class="Bound">m</a>
  <a id="18927" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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

{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="21028" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21028" class="Function">+-suc</a> <a id="21034" class="Symbol">:</a> <a id="21036" class="Symbol">∀</a> <a id="21038" class="Symbol">(</a><a id="21039" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21039" class="Bound">m</a> <a id="21041" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21041" class="Bound">n</a> <a id="21043" class="Symbol">:</a> <a id="21045" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21046" class="Symbol">)</a> <a id="21048" class="Symbol">→</a> <a id="21050" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21039" class="Bound">m</a> <a id="21052" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21054" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21058" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21041" class="Bound">n</a> <a id="21060" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="21062" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21066" class="Symbol">(</a><a id="21067" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21039" class="Bound">m</a> <a id="21069" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21071" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21041" class="Bound">n</a><a id="21072" class="Symbol">)</a>
<a id="21074" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21028" class="Function">+-suc</a> <a id="21080" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21085" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21085" class="Bound">n</a> <a id="21087" class="Symbol">=</a>
  <a id="21091" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="21101" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21106" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21108" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21112" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21085" class="Bound">n</a>
  <a id="21116" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21124" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21128" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21085" class="Bound">n</a>
  <a id="21132" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21140" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21144" class="Symbol">(</a><a id="21145" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="21150" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21152" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21085" class="Bound">n</a><a id="21153" class="Symbol">)</a>
  <a id="21157" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="21159" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21028" class="Function">+-suc</a> <a id="21165" class="Symbol">(</a><a id="21166" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21170" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a><a id="21171" class="Symbol">)</a> <a id="21173" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a> <a id="21175" class="Symbol">=</a>
  <a id="21179" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="21189" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21193" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a> <a id="21195" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21197" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21201" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a>
  <a id="21205" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21213" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21217" class="Symbol">(</a><a id="21218" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a> <a id="21220" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21222" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21226" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a><a id="21227" class="Symbol">)</a>
  <a id="21231" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="21234" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="21239" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21243" class="Symbol">(</a><a id="21244" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21028" class="Function">+-suc</a> <a id="21250" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a> <a id="21252" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a><a id="21253" class="Symbol">)</a> <a id="21255" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="21261" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21265" class="Symbol">(</a><a id="21266" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21270" class="Symbol">(</a><a id="21271" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a> <a id="21273" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21275" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a><a id="21276" class="Symbol">))</a>
  <a id="21281" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21289" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21293" class="Symbol">(</a><a id="21294" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21298" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21170" class="Bound">m</a> <a id="21300" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21302" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21173" class="Bound">n</a><a id="21303" class="Symbol">)</a>
  <a id="21307" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="23162" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23162" class="Function">+-comm</a> <a id="23169" class="Symbol">:</a> <a id="23171" class="Symbol">∀</a> <a id="23173" class="Symbol">(</a><a id="23174" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23174" class="Bound">m</a> <a id="23176" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23176" class="Bound">n</a> <a id="23178" class="Symbol">:</a> <a id="23180" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23181" class="Symbol">)</a> <a id="23183" class="Symbol">→</a> <a id="23185" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23174" class="Bound">m</a> <a id="23187" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23189" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23176" class="Bound">n</a> <a id="23191" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23193" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23176" class="Bound">n</a> <a id="23195" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23197" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23174" class="Bound">m</a>
<a id="23199" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23162" class="Function">+-comm</a> <a id="23206" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a> <a id="23208" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23213" class="Symbol">=</a>
  <a id="23217" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23227" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a> <a id="23229" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23231" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="23238" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23241" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18710" class="Function">+-identityʳ</a> <a id="23253" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a> <a id="23255" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23261" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a>
  <a id="23265" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23273" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23278" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23280" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a>
  <a id="23284" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="23286" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23162" class="Function">+-comm</a> <a id="23293" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23295" class="Symbol">(</a><a id="23296" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23300" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a><a id="23301" class="Symbol">)</a> <a id="23303" class="Symbol">=</a>
  <a id="23307" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23317" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23319" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23321" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23325" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a>
  <a id="23329" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23332" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21028" class="Function">+-suc</a> <a id="23338" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23340" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a> <a id="23342" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23348" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23352" class="Symbol">(</a><a id="23353" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23355" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23357" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a><a id="23358" class="Symbol">)</a>
  <a id="23362" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23365" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="23370" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23374" class="Symbol">(</a><a id="23375" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23162" class="Function">+-comm</a> <a id="23382" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23384" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a><a id="23385" class="Symbol">)</a> <a id="23387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23393" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23397" class="Symbol">(</a><a id="23398" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a> <a id="23400" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23402" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a><a id="23403" class="Symbol">)</a>
  <a id="23407" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23415" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23419" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23300" class="Bound">n</a> <a id="23421" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23423" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a>
  <a id="23427" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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

{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="25669" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25669" class="Function">+-rearrange</a> <a id="25681" class="Symbol">:</a> <a id="25683" class="Symbol">∀</a> <a id="25685" class="Symbol">(</a><a id="25686" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25686" class="Bound">m</a> <a id="25688" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25688" class="Bound">n</a> <a id="25690" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25690" class="Bound">p</a> <a id="25692" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25692" class="Bound">q</a> <a id="25694" class="Symbol">:</a> <a id="25696" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25697" class="Symbol">)</a> <a id="25699" class="Symbol">→</a> <a id="25701" class="Symbol">(</a><a id="25702" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25686" class="Bound">m</a> <a id="25704" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25706" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25688" class="Bound">n</a><a id="25707" class="Symbol">)</a> <a id="25709" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25711" class="Symbol">(</a><a id="25712" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25690" class="Bound">p</a> <a id="25714" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25716" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25692" class="Bound">q</a><a id="25717" class="Symbol">)</a> <a id="25719" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25721" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25686" class="Bound">m</a> <a id="25723" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25725" class="Symbol">(</a><a id="25726" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25688" class="Bound">n</a> <a id="25728" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25730" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25690" class="Bound">p</a><a id="25731" class="Symbol">)</a> <a id="25733" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25735" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25692" class="Bound">q</a>
<a id="25737" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25669" class="Function">+-rearrange</a> <a id="25749" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25751" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25753" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a> <a id="25755" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a> <a id="25757" class="Symbol">=</a>
  <a id="25761" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="25771" class="Symbol">(</a><a id="25772" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25774" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25776" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a><a id="25777" class="Symbol">)</a> <a id="25779" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25781" class="Symbol">(</a><a id="25782" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a> <a id="25784" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25786" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25787" class="Symbol">)</a>
  <a id="25791" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25794" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="25802" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25804" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25806" class="Symbol">(</a><a id="25807" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a> <a id="25809" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25811" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25812" class="Symbol">)</a> <a id="25814" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25820" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25822" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25824" class="Symbol">(</a><a id="25825" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25827" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25829" class="Symbol">(</a><a id="25830" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a> <a id="25832" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25834" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25835" class="Symbol">))</a>
  <a id="25840" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25843" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="25848" class="Symbol">(</a><a id="25849" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25851" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="25853" class="Symbol">)</a> <a id="25855" class="Symbol">(</a><a id="25856" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25860" class="Symbol">(</a><a id="25861" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="25869" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25871" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a> <a id="25873" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25874" class="Symbol">))</a> <a id="25877" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25883" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25885" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25887" class="Symbol">((</a><a id="25889" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25891" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25893" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a><a id="25894" class="Symbol">)</a> <a id="25896" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25898" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25899" class="Symbol">)</a>
  <a id="25903" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25906" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25910" class="Symbol">(</a><a id="25911" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Function">+-assoc</a> <a id="25919" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25921" class="Symbol">(</a><a id="25922" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25924" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25926" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a><a id="25927" class="Symbol">)</a> <a id="25929" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a><a id="25930" class="Symbol">)</a> <a id="25932" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25938" class="Symbol">(</a><a id="25939" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25749" class="Bound">m</a> <a id="25941" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25943" class="Symbol">(</a><a id="25944" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25751" class="Bound">n</a> <a id="25946" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25948" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25753" class="Bound">p</a><a id="25949" class="Symbol">))</a> <a id="25952" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25954" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25755" class="Bound">q</a>
  <a id="25958" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
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
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
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
#### Exercise `finite-|-assoc` (stretch) {#finite-plus-assoc}
{:/}

#### 练习 `finite-|-assoc`（延伸） {#finite-plus-assoc}

{::comment}
Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).
{:/}

请参考[前文]({{ site.baseurl }}/Naturals/#finite-creation)
写出前四天已知的加法结合律的创世故事。

{::comment}
{% raw %}<pre class="Agda"><a id="31647" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31684" class="Comment">-- 请将代码写在此处。</a>
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

{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="31999" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31999" class="Function">+-assoc′</a> <a id="32008" class="Symbol">:</a> <a id="32010" class="Symbol">∀</a> <a id="32012" class="Symbol">(</a><a id="32013" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32013" class="Bound">m</a> <a id="32015" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32015" class="Bound">n</a> <a id="32017" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32017" class="Bound">p</a> <a id="32019" class="Symbol">:</a> <a id="32021" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32022" class="Symbol">)</a> <a id="32024" class="Symbol">→</a> <a id="32026" class="Symbol">(</a><a id="32027" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32013" class="Bound">m</a> <a id="32029" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32031" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32015" class="Bound">n</a><a id="32032" class="Symbol">)</a> <a id="32034" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32036" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32017" class="Bound">p</a> <a id="32038" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="32040" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32013" class="Bound">m</a> <a id="32042" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32044" class="Symbol">(</a><a id="32045" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32015" class="Bound">n</a> <a id="32047" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32049" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32017" class="Bound">p</a><a id="32050" class="Symbol">)</a>
<a id="32052" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31999" class="Function">+-assoc′</a> <a id="32061" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="32069" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32069" class="Bound">n</a> <a id="32071" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32071" class="Bound">p</a>                          <a id="32098" class="Symbol">=</a>  <a id="32101" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="32106" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31999" class="Function">+-assoc′</a> <a id="32115" class="Symbol">(</a><a id="32116" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="32120" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32120" class="Bound">m</a><a id="32121" class="Symbol">)</a> <a id="32123" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32123" class="Bound">n</a> <a id="32125" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32125" class="Bound">p</a>  <a id="32128" class="Keyword">rewrite</a> <a id="32136" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31999" class="Function">+-assoc′</a> <a id="32145" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32120" class="Bound">m</a> <a id="32147" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32123" class="Bound">n</a> <a id="32149" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#32125" class="Bound">p</a>  <a id="32152" class="Symbol">=</a>  <a id="32155" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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

{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="33457" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33457" class="Function">+-identity′</a> <a id="33469" class="Symbol">:</a> <a id="33471" class="Symbol">∀</a> <a id="33473" class="Symbol">(</a><a id="33474" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33474" class="Bound">n</a> <a id="33476" class="Symbol">:</a> <a id="33478" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33479" class="Symbol">)</a> <a id="33481" class="Symbol">→</a> <a id="33483" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33474" class="Bound">n</a> <a id="33485" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33487" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33492" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33494" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33474" class="Bound">n</a>
<a id="33496" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33457" class="Function">+-identity′</a> <a id="33508" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33513" class="Symbol">=</a> <a id="33515" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33520" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33457" class="Function">+-identity′</a> <a id="33532" class="Symbol">(</a><a id="33533" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33537" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33537" class="Bound">n</a><a id="33538" class="Symbol">)</a> <a id="33540" class="Keyword">rewrite</a> <a id="33548" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33457" class="Function">+-identity′</a> <a id="33560" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33537" class="Bound">n</a> <a id="33562" class="Symbol">=</a> <a id="33564" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="33570" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33570" class="Function">+-suc′</a> <a id="33577" class="Symbol">:</a> <a id="33579" class="Symbol">∀</a> <a id="33581" class="Symbol">(</a><a id="33582" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33582" class="Bound">m</a> <a id="33584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33584" class="Bound">n</a> <a id="33586" class="Symbol">:</a> <a id="33588" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33589" class="Symbol">)</a> <a id="33591" class="Symbol">→</a> <a id="33593" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33582" class="Bound">m</a> <a id="33595" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33597" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33601" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33584" class="Bound">n</a> <a id="33603" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33605" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33609" class="Symbol">(</a><a id="33610" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33582" class="Bound">m</a> <a id="33612" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33614" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33584" class="Bound">n</a><a id="33615" class="Symbol">)</a>
<a id="33617" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33570" class="Function">+-suc′</a> <a id="33624" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33629" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33629" class="Bound">n</a> <a id="33631" class="Symbol">=</a> <a id="33633" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33638" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33570" class="Function">+-suc′</a> <a id="33645" class="Symbol">(</a><a id="33646" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33650" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33650" class="Bound">m</a><a id="33651" class="Symbol">)</a> <a id="33653" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33653" class="Bound">n</a> <a id="33655" class="Keyword">rewrite</a> <a id="33663" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33570" class="Function">+-suc′</a> <a id="33670" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33650" class="Bound">m</a> <a id="33672" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33653" class="Bound">n</a> <a id="33674" class="Symbol">=</a> <a id="33676" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="33682" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33682" class="Function">+-comm′</a> <a id="33690" class="Symbol">:</a> <a id="33692" class="Symbol">∀</a> <a id="33694" class="Symbol">(</a><a id="33695" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33695" class="Bound">m</a> <a id="33697" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33697" class="Bound">n</a> <a id="33699" class="Symbol">:</a> <a id="33701" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33702" class="Symbol">)</a> <a id="33704" class="Symbol">→</a> <a id="33706" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33695" class="Bound">m</a> <a id="33708" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33710" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33697" class="Bound">n</a> <a id="33712" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33714" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33697" class="Bound">n</a> <a id="33716" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33718" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33695" class="Bound">m</a>
<a id="33720" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33682" class="Function">+-comm′</a> <a id="33728" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33728" class="Bound">m</a> <a id="33730" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33735" class="Keyword">rewrite</a> <a id="33743" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33457" class="Function">+-identity′</a> <a id="33755" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33728" class="Bound">m</a> <a id="33757" class="Symbol">=</a> <a id="33759" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33764" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33682" class="Function">+-comm′</a> <a id="33772" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33772" class="Bound">m</a> <a id="33774" class="Symbol">(</a><a id="33775" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33779" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33779" class="Bound">n</a><a id="33780" class="Symbol">)</a> <a id="33782" class="Keyword">rewrite</a> <a id="33790" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33570" class="Function">+-suc′</a> <a id="33797" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33772" class="Bound">m</a> <a id="33799" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33779" class="Bound">n</a> <a id="33801" class="Symbol">|</a> <a id="33803" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33682" class="Function">+-comm′</a> <a id="33811" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33772" class="Bound">m</a> <a id="33813" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33779" class="Bound">n</a> <a id="33815" class="Symbol">=</a> <a id="33817" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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
{% raw %}<pre class="Agda"><a id="38488" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38525" class="Comment">-- 请将代码写在此处。</a>
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
{% raw %}<pre class="Agda"><a id="38896" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38933" class="Comment">-- 请将代码写在此处。</a>
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
{% raw %}<pre class="Agda"><a id="39266" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39303" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `*-comm` {#times-comm}
{:/}

#### 练习 `*-comm` {#times-comm}

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
{% raw %}<pre class="Agda"><a id="39705" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39742" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `0∸n≡0` {#zero-monus}
{:/}

#### 练习 `0∸n≡0` {#zero-monus}

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
{% raw %}<pre class="Agda"><a id="40014" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="40051" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `∸-|-assoc` {#monus-plus-assoc}
{:/}

#### 练习 `∸-|-assoc` {#monus-plus-assoc}

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
{% raw %}<pre class="Agda"><a id="40390" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="40427" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `+*^` (stretch)
{:/}

#### 练习 `+*^` （延伸）

{::comment}
Show the following three laws
{:/}

证明下列三条定律

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

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
defines a datatype of bitstrings representing natural numbers
{:/}

回想练习 [Bin]({{ site.baseurl }}/Naturals/#Bin)
中定义的一种表示自然数的比特串数据类型：

{% raw %}<pre class="Agda"><a id="41057" class="Keyword">data</a> <a id="Bin"></a><a id="41062" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a> <a id="41066" class="Symbol">:</a> <a id="41068" class="PrimitiveType">Set</a> <a id="41072" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="41080" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41080" class="InductiveConstructor">nil</a> <a id="41084" class="Symbol">:</a> <a id="41086" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="41092" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41092" class="InductiveConstructor Operator">x0_</a> <a id="41096" class="Symbol">:</a> <a id="41098" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a> <a id="41102" class="Symbol">→</a> <a id="41104" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="41110" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41110" class="InductiveConstructor Operator">x1_</a> <a id="41114" class="Symbol">:</a> <a id="41116" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a> <a id="41120" class="Symbol">→</a> <a id="41122" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#41062" class="Datatype">Bin</a>
</pre>{% endraw %}
{::comment}
and asks you to define functions
{:/}

以及要求你定义的函数

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

{::comment}
Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:
{:/}

考虑以下定律，其中 `n` 表示自然数，`x` 表示比特串：

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

{::comment}
For each law: if it holds, prove; if not, give a counterexample.
{:/}

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

{::comment}
{% raw %}<pre class="Agda"><a id="41596" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="41633" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中类似的定义可在标准库中找到：

{% raw %}<pre class="Agda"><a id="41822" class="Keyword">import</a> <a id="41829" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="41849" class="Keyword">using</a> <a id="41855" class="Symbol">(</a><a id="41856" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="41863" class="Symbol">;</a> <a id="41865" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="41876" class="Symbol">;</a> <a id="41878" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="41883" class="Symbol">;</a> <a id="41885" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="41891" class="Symbol">)</a>
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
