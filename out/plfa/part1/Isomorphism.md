---
src       : "src/plfa/part1/Isomorphism.lagda.md"
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="185" class="Keyword">module</a> <a id="192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="215" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

本部分介绍同构（Isomorphism）与嵌入（Embedding）。同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。


{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="749" class="Keyword">import</a> <a id="756" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="794" class="Symbol">as</a> <a id="797" class="Module">Eq</a>
<a id="800" class="Keyword">open</a> <a id="805" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="808" class="Keyword">using</a> <a id="814" class="Symbol">(</a><a id="815" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="818" class="Symbol">;</a> <a id="820" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="824" class="Symbol">;</a> <a id="826" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="830" class="Symbol">;</a> <a id="832" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a><a id="840" class="Symbol">)</a>
<a id="842" class="Keyword">open</a> <a id="847" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="883" class="Keyword">using</a> <a id="889" class="Symbol">(</a><a id="890" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="891" class="Symbol">;</a> <a id="893" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="897" class="Symbol">;</a> <a id="899" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="902" class="Symbol">;</a> <a id="904" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="907" class="Symbol">)</a>
<a id="909" class="Keyword">open</a> <a id="914" class="Keyword">import</a> <a id="921" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="941" class="Keyword">using</a> <a id="947" class="Symbol">(</a><a id="948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="954" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Lambda expressions
{:/}

## Lambda 表达式

{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。

{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

{::comment}
is equivalent to a function `f` defined by the equations
{:/}

等同于定义一个函数 `f`，使用下列等式：

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。

{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：

    λ x → N

{::comment}
or
{:/}

或者

    λ (x : A) → N

{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。

{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。


{::comment}
## Function composition
{:/}

## 函数组合 （Function Composition）

{::comment}
In what follows, we will make use of function composition:
{:/}

接下来，我们将使用函数组合：

{% raw %}<pre class="Agda"><a id="_∘_"></a><a id="2709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2709" class="Function Operator">_∘_</a> <a id="2713" class="Symbol">:</a> <a id="2715" class="Symbol">∀</a> <a id="2717" class="Symbol">{</a><a id="2718" href="plfa.part1.Isomorphism.html#2718" class="Bound">A</a> <a id="2720" href="plfa.part1.Isomorphism.html#2720" class="Bound">B</a> <a id="2722" href="plfa.part1.Isomorphism.html#2722" class="Bound">C</a> <a id="2724" class="Symbol">:</a> <a id="2726" class="PrimitiveType">Set</a><a id="2729" class="Symbol">}</a> <a id="2731" class="Symbol">→</a> <a id="2733" class="Symbol">(</a><a id="2734" href="plfa.part1.Isomorphism.html#2720" class="Bound">B</a> <a id="2736" class="Symbol">→</a> <a id="2738" href="plfa.part1.Isomorphism.html#2722" class="Bound">C</a><a id="2739" class="Symbol">)</a> <a id="2741" class="Symbol">→</a> <a id="2743" class="Symbol">(</a><a id="2744" href="plfa.part1.Isomorphism.html#2718" class="Bound">A</a> <a id="2746" class="Symbol">→</a> <a id="2748" href="plfa.part1.Isomorphism.html#2720" class="Bound">B</a><a id="2749" class="Symbol">)</a> <a id="2751" class="Symbol">→</a> <a id="2753" class="Symbol">(</a><a id="2754" href="plfa.part1.Isomorphism.html#2718" class="Bound">A</a> <a id="2756" class="Symbol">→</a> <a id="2758" href="plfa.part1.Isomorphism.html#2722" class="Bound">C</a><a id="2759" class="Symbol">)</a>
<a id="2761" class="Symbol">(</a><a id="2762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2762" class="Bound">g</a> <a id="2764" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="2766" href="plfa.part1.Isomorphism.html#2766" class="Bound">f</a><a id="2767" class="Symbol">)</a> <a id="2769" href="plfa.part1.Isomorphism.html#2769" class="Bound">x</a>  <a id="2772" class="Symbol">=</a> <a id="2774" href="plfa.part1.Isomorphism.html#2762" class="Bound">g</a> <a id="2776" class="Symbol">(</a><a id="2777" href="plfa.part1.Isomorphism.html#2766" class="Bound">f</a> <a id="2779" href="plfa.part1.Isomorphism.html#2769" class="Bound">x</a><a id="2780" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}

`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。一个等价的定义，使用 lambda 表达式，如下：

{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="3019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3019" class="Function Operator">_∘′_</a> <a id="3024" class="Symbol">:</a> <a id="3026" class="Symbol">∀</a> <a id="3028" class="Symbol">{</a><a id="3029" href="plfa.part1.Isomorphism.html#3029" class="Bound">A</a> <a id="3031" href="plfa.part1.Isomorphism.html#3031" class="Bound">B</a> <a id="3033" href="plfa.part1.Isomorphism.html#3033" class="Bound">C</a> <a id="3035" class="Symbol">:</a> <a id="3037" class="PrimitiveType">Set</a><a id="3040" class="Symbol">}</a> <a id="3042" class="Symbol">→</a> <a id="3044" class="Symbol">(</a><a id="3045" href="plfa.part1.Isomorphism.html#3031" class="Bound">B</a> <a id="3047" class="Symbol">→</a> <a id="3049" href="plfa.part1.Isomorphism.html#3033" class="Bound">C</a><a id="3050" class="Symbol">)</a> <a id="3052" class="Symbol">→</a> <a id="3054" class="Symbol">(</a><a id="3055" href="plfa.part1.Isomorphism.html#3029" class="Bound">A</a> <a id="3057" class="Symbol">→</a> <a id="3059" href="plfa.part1.Isomorphism.html#3031" class="Bound">B</a><a id="3060" class="Symbol">)</a> <a id="3062" class="Symbol">→</a> <a id="3064" class="Symbol">(</a><a id="3065" href="plfa.part1.Isomorphism.html#3029" class="Bound">A</a> <a id="3067" class="Symbol">→</a> <a id="3069" href="plfa.part1.Isomorphism.html#3033" class="Bound">C</a><a id="3070" class="Symbol">)</a>
<a id="3072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3072" class="Bound">g</a> <a id="3074" href="plfa.part1.Isomorphism.html#3019" class="Function Operator">∘′</a> <a id="3077" href="plfa.part1.Isomorphism.html#3077" class="Bound">f</a>  <a id="3080" class="Symbol">=</a>  <a id="3083" class="Symbol">λ</a> <a id="3085" href="plfa.part1.Isomorphism.html#3085" class="Bound">x</a> <a id="3087" class="Symbol">→</a> <a id="3089" href="plfa.part1.Isomorphism.html#3072" class="Bound">g</a> <a id="3091" class="Symbol">(</a><a id="3092" href="plfa.part1.Isomorphism.html#3077" class="Bound">f</a> <a id="3094" href="plfa.part1.Isomorphism.html#3085" class="Bound">x</a><a id="3095" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Extensionality {#extensionality}
{:/}

## 外延性（Extensionality） {#extensionality}

{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier]({{ site.baseurl }}/Equality/#cong).
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，那么两个函数相同。这是 `cong-app` 的逆命题，在[之前]({{ site.baseurl }}/Equality/#cong)有所介绍。

{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}

Agda 并不预设外延性，但我们可以假设其成立：

{% raw %}<pre class="Agda"><a id="3752" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="3764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3764" class="Postulate">extensionality</a> <a id="3779" class="Symbol">:</a> <a id="3781" class="Symbol">∀</a> <a id="3783" class="Symbol">{</a><a id="3784" href="plfa.part1.Isomorphism.html#3784" class="Bound">A</a> <a id="3786" href="plfa.part1.Isomorphism.html#3786" class="Bound">B</a> <a id="3788" class="Symbol">:</a> <a id="3790" class="PrimitiveType">Set</a><a id="3793" class="Symbol">}</a> <a id="3795" class="Symbol">{</a><a id="3796" href="plfa.part1.Isomorphism.html#3796" class="Bound">f</a> <a id="3798" href="plfa.part1.Isomorphism.html#3798" class="Bound">g</a> <a id="3800" class="Symbol">:</a> <a id="3802" href="plfa.part1.Isomorphism.html#3784" class="Bound">A</a> <a id="3804" class="Symbol">→</a> <a id="3806" href="plfa.part1.Isomorphism.html#3786" class="Bound">B</a><a id="3807" class="Symbol">}</a>
    <a id="3813" class="Symbol">→</a> <a id="3815" class="Symbol">(∀</a> <a id="3818" class="Symbol">(</a><a id="3819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3819" class="Bound">x</a> <a id="3821" class="Symbol">:</a> <a id="3823" href="plfa.part1.Isomorphism.html#3784" class="Bound">A</a><a id="3824" class="Symbol">)</a> <a id="3826" class="Symbol">→</a> <a id="3828" href="plfa.part1.Isomorphism.html#3796" class="Bound">f</a> <a id="3830" href="plfa.part1.Isomorphism.html#3819" class="Bound">x</a> <a id="3832" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3834" href="plfa.part1.Isomorphism.html#3798" class="Bound">g</a> <a id="3836" href="plfa.part1.Isomorphism.html#3819" class="Bound">x</a><a id="3837" class="Symbol">)</a>
      <a id="3845" class="Comment">-----------------------</a>
    <a id="3873" class="Symbol">→</a> <a id="3875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3796" class="Bound">f</a> <a id="3877" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3879" href="plfa.part1.Isomorphism.html#3798" class="Bound">g</a>
</pre>{% endraw %}
{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.
{:/}

假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。

{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals]({{ site.baseurl }}/Naturals/),
and one where it is defined the other way around.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals][plfa.Naturals]
章节中那样定义，另一个如下，反过来定义：

{% raw %}<pre class="Agda"><a id="_+′_"></a><a id="4370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4370" class="Function Operator">_+′_</a> <a id="4375" class="Symbol">:</a> <a id="4377" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4379" class="Symbol">→</a> <a id="4381" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4383" class="Symbol">→</a> <a id="4385" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4387" class="Bound">m</a> <a id="4389" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">+′</a> <a id="4392" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="4398" class="Symbol">=</a> <a id="4400" href="plfa.part1.Isomorphism.html#4387" class="Bound">m</a>
<a id="4402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4402" class="Bound">m</a> <a id="4404" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">+′</a> <a id="4407" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4411" href="plfa.part1.Isomorphism.html#4411" class="Bound">n</a> <a id="4413" class="Symbol">=</a> <a id="4415" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4419" class="Symbol">(</a><a id="4420" href="plfa.part1.Isomorphism.html#4402" class="Bound">m</a> <a id="4422" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">+′</a> <a id="4425" href="plfa.part1.Isomorphism.html#4411" class="Bound">n</a><a id="4426" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}

通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，会返回相同的值：

{% raw %}<pre class="Agda"><a id="same-app"></a><a id="4619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4619" class="Function">same-app</a> <a id="4628" class="Symbol">:</a> <a id="4630" class="Symbol">∀</a> <a id="4632" class="Symbol">(</a><a id="4633" href="plfa.part1.Isomorphism.html#4633" class="Bound">m</a> <a id="4635" href="plfa.part1.Isomorphism.html#4635" class="Bound">n</a> <a id="4637" class="Symbol">:</a> <a id="4639" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4640" class="Symbol">)</a> <a id="4642" class="Symbol">→</a> <a id="4644" href="plfa.part1.Isomorphism.html#4633" class="Bound">m</a> <a id="4646" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">+′</a> <a id="4649" href="plfa.part1.Isomorphism.html#4635" class="Bound">n</a> <a id="4651" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4653" href="plfa.part1.Isomorphism.html#4633" class="Bound">m</a> <a id="4655" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4657" href="plfa.part1.Isomorphism.html#4635" class="Bound">n</a>
<a id="4659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4619" class="Function">same-app</a> <a id="4668" href="plfa.part1.Isomorphism.html#4668" class="Bound">m</a> <a id="4670" href="plfa.part1.Isomorphism.html#4670" class="Bound">n</a> <a id="4672" class="Keyword">rewrite</a> <a id="4680" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="4687" href="plfa.part1.Isomorphism.html#4668" class="Bound">m</a> <a id="4689" href="plfa.part1.Isomorphism.html#4670" class="Bound">n</a> <a id="4691" class="Symbol">=</a> <a id="4693" href="plfa.part1.Isomorphism.html#4714" class="Function">helper</a> <a id="4700" href="plfa.part1.Isomorphism.html#4668" class="Bound">m</a> <a id="4702" href="plfa.part1.Isomorphism.html#4670" class="Bound">n</a>
  <a id="4706" class="Keyword">where</a>
  <a id="4714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4714" class="Function">helper</a> <a id="4721" class="Symbol">:</a> <a id="4723" class="Symbol">∀</a> <a id="4725" class="Symbol">(</a><a id="4726" href="plfa.part1.Isomorphism.html#4726" class="Bound">m</a> <a id="4728" href="plfa.part1.Isomorphism.html#4728" class="Bound">n</a> <a id="4730" class="Symbol">:</a> <a id="4732" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4733" class="Symbol">)</a> <a id="4735" class="Symbol">→</a> <a id="4737" href="plfa.part1.Isomorphism.html#4726" class="Bound">m</a> <a id="4739" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">+′</a> <a id="4742" href="plfa.part1.Isomorphism.html#4728" class="Bound">n</a> <a id="4744" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4746" href="plfa.part1.Isomorphism.html#4728" class="Bound">n</a> <a id="4748" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4750" href="plfa.part1.Isomorphism.html#4726" class="Bound">m</a>
  <a id="4754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4714" class="Function">helper</a> <a id="4761" href="plfa.part1.Isomorphism.html#4761" class="Bound">m</a> <a id="4763" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="4771" class="Symbol">=</a> <a id="4773" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
  <a id="4780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4714" class="Function">helper</a> <a id="4787" href="plfa.part1.Isomorphism.html#4787" class="Bound">m</a> <a id="4789" class="Symbol">(</a><a id="4790" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4794" href="plfa.part1.Isomorphism.html#4794" class="Bound">n</a><a id="4795" class="Symbol">)</a> <a id="4797" class="Symbol">=</a> <a id="4799" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="4804" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4808" class="Symbol">(</a><a id="4809" href="plfa.part1.Isomorphism.html#4714" class="Function">helper</a> <a id="4816" href="plfa.part1.Isomorphism.html#4787" class="Bound">m</a> <a id="4818" href="plfa.part1.Isomorphism.html#4794" class="Bound">n</a><a id="4819" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：

{% raw %}<pre class="Agda"><a id="same"></a><a id="5038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5038" class="Function">same</a> <a id="5043" class="Symbol">:</a> <a id="5045" href="plfa.part1.Isomorphism.html#4370" class="Function Operator">_+′_</a> <a id="5050" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5052" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a>
<a id="5056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5038" class="Function">same</a> <a id="5061" class="Symbol">=</a> <a id="5063" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="5078" class="Symbol">(λ</a> <a id="5081" href="plfa.part1.Isomorphism.html#5081" class="Bound">m</a> <a id="5083" class="Symbol">→</a> <a id="5085" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="5100" class="Symbol">(λ</a> <a id="5103" href="plfa.part1.Isomorphism.html#5103" class="Bound">n</a> <a id="5105" class="Symbol">→</a> <a id="5107" href="plfa.part1.Isomorphism.html#4619" class="Function">same-app</a> <a id="5116" href="plfa.part1.Isomorphism.html#5081" class="Bound">m</a> <a id="5118" href="plfa.part1.Isomorphism.html#5103" class="Bound">n</a><a id="5119" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}

我们偶尔需要在之后的情况中假设外延性。

More generally, we may wish to postulate extensionality for
dependent functions.
{% raw %}<pre class="Agda"><a id="5317" class="Keyword">postulate</a>
  <a id="∀-extensionality"></a><a id="5329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5329" class="Postulate">∀-extensionality</a> <a id="5346" class="Symbol">:</a> <a id="5348" class="Symbol">∀</a> <a id="5350" class="Symbol">{</a><a id="5351" href="plfa.part1.Isomorphism.html#5351" class="Bound">A</a> <a id="5353" class="Symbol">:</a> <a id="5355" class="PrimitiveType">Set</a><a id="5358" class="Symbol">}</a> <a id="5360" class="Symbol">{</a><a id="5361" href="plfa.part1.Isomorphism.html#5361" class="Bound">B</a> <a id="5363" class="Symbol">:</a> <a id="5365" href="plfa.part1.Isomorphism.html#5351" class="Bound">A</a> <a id="5367" class="Symbol">→</a> <a id="5369" class="PrimitiveType">Set</a><a id="5372" class="Symbol">}</a> <a id="5374" class="Symbol">{</a><a id="5375" href="plfa.part1.Isomorphism.html#5375" class="Bound">f</a> <a id="5377" href="plfa.part1.Isomorphism.html#5377" class="Bound">g</a> <a id="5379" class="Symbol">:</a> <a id="5381" class="Symbol">∀(</a><a id="5383" href="plfa.part1.Isomorphism.html#5383" class="Bound">x</a> <a id="5385" class="Symbol">:</a> <a id="5387" href="plfa.part1.Isomorphism.html#5351" class="Bound">A</a><a id="5388" class="Symbol">)</a> <a id="5390" class="Symbol">→</a> <a id="5392" href="plfa.part1.Isomorphism.html#5361" class="Bound">B</a> <a id="5394" href="plfa.part1.Isomorphism.html#5383" class="Bound">x</a><a id="5395" class="Symbol">}</a>
    <a id="5401" class="Symbol">→</a> <a id="5403" class="Symbol">(∀</a> <a id="5406" class="Symbol">(</a><a id="5407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5407" class="Bound">x</a> <a id="5409" class="Symbol">:</a> <a id="5411" href="plfa.part1.Isomorphism.html#5351" class="Bound">A</a><a id="5412" class="Symbol">)</a> <a id="5414" class="Symbol">→</a> <a id="5416" href="plfa.part1.Isomorphism.html#5375" class="Bound">f</a> <a id="5418" href="plfa.part1.Isomorphism.html#5407" class="Bound">x</a> <a id="5420" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5422" href="plfa.part1.Isomorphism.html#5377" class="Bound">g</a> <a id="5424" href="plfa.part1.Isomorphism.html#5407" class="Bound">x</a><a id="5425" class="Symbol">)</a>
      <a id="5433" class="Comment">-----------------------</a>
    <a id="5461" class="Symbol">→</a> <a id="5463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5375" class="Bound">f</a> <a id="5465" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5467" href="plfa.part1.Isomorphism.html#5377" class="Bound">g</a>
</pre>{% endraw %}Here the type of `f` and `g` has changed from `A → B` to
`∀ (x : A) → B x`, generalising ordinary functions to
dependent functions.


{::comment}
## Isomorphism
{:/}

## 同构（Isomorphism）

{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。下面是同构的正式定义：

{% raw %}<pre class="Agda"><a id="5830" class="Keyword">infix</a> <a id="5836" class="Number">0</a> <a id="5838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">_≃_</a>
<a id="5842" class="Keyword">record</a> <a id="_≃_"></a><a id="5849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">_≃_</a> <a id="5853" class="Symbol">(</a><a id="5854" href="plfa.part1.Isomorphism.html#5854" class="Bound">A</a> <a id="5856" href="plfa.part1.Isomorphism.html#5856" class="Bound">B</a> <a id="5858" class="Symbol">:</a> <a id="5860" class="PrimitiveType">Set</a><a id="5863" class="Symbol">)</a> <a id="5865" class="Symbol">:</a> <a id="5867" class="PrimitiveType">Set</a> <a id="5871" class="Keyword">where</a>
  <a id="5879" class="Keyword">field</a>
    <a id="_≃_.to"></a><a id="5889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>   <a id="5894" class="Symbol">:</a> <a id="5896" href="plfa.part1.Isomorphism.html#5854" class="Bound">A</a> <a id="5898" class="Symbol">→</a> <a id="5900" href="plfa.part1.Isomorphism.html#5856" class="Bound">B</a>
    <a id="_≃_.from"></a><a id="5906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a> <a id="5911" class="Symbol">:</a> <a id="5913" href="plfa.part1.Isomorphism.html#5856" class="Bound">B</a> <a id="5915" class="Symbol">→</a> <a id="5917" href="plfa.part1.Isomorphism.html#5854" class="Bound">A</a>
    <a id="_≃_.from∘to"></a><a id="5923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="5931" class="Symbol">:</a> <a id="5933" class="Symbol">∀</a> <a id="5935" class="Symbol">(</a><a id="5936" href="plfa.part1.Isomorphism.html#5936" class="Bound">x</a> <a id="5938" class="Symbol">:</a> <a id="5940" href="plfa.part1.Isomorphism.html#5854" class="Bound">A</a><a id="5941" class="Symbol">)</a> <a id="5943" class="Symbol">→</a> <a id="5945" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="5950" class="Symbol">(</a><a id="5951" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="5954" href="plfa.part1.Isomorphism.html#5936" class="Bound">x</a><a id="5955" class="Symbol">)</a> <a id="5957" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5959" href="plfa.part1.Isomorphism.html#5936" class="Bound">x</a>
    <a id="_≃_.to∘from"></a><a id="5965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="5973" class="Symbol">:</a> <a id="5975" class="Symbol">∀</a> <a id="5977" class="Symbol">(</a><a id="5978" href="plfa.part1.Isomorphism.html#5978" class="Bound">y</a> <a id="5980" class="Symbol">:</a> <a id="5982" href="plfa.part1.Isomorphism.html#5856" class="Bound">B</a><a id="5983" class="Symbol">)</a> <a id="5985" class="Symbol">→</a> <a id="5987" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="5990" class="Symbol">(</a><a id="5991" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="5996" href="plfa.part1.Isomorphism.html#5978" class="Bound">y</a><a id="5997" class="Symbol">)</a> <a id="5999" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="6001" href="plfa.part1.Isomorphism.html#5978" class="Bound">y</a>
<a id="6003" class="Keyword">open</a> <a id="6008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Module Operator">_≃_</a>
</pre>{% endraw %}
{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。

{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：

{% raw %}<pre class="Agda"><a id="7173" class="Keyword">data</a> <a id="_≃′_"></a><a id="7178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7178" class="Datatype Operator">_≃′_</a> <a id="7183" class="Symbol">(</a><a id="7184" href="plfa.part1.Isomorphism.html#7184" class="Bound">A</a> <a id="7186" href="plfa.part1.Isomorphism.html#7186" class="Bound">B</a> <a id="7188" class="Symbol">:</a> <a id="7190" class="PrimitiveType">Set</a><a id="7193" class="Symbol">):</a> <a id="7196" class="PrimitiveType">Set</a> <a id="7200" class="Keyword">where</a>
  <a id="_≃′_.mk-≃′"></a><a id="7208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7208" class="InductiveConstructor">mk-≃′</a> <a id="7214" class="Symbol">:</a> <a id="7216" class="Symbol">∀</a> <a id="7218" class="Symbol">(</a><a id="7219" href="plfa.part1.Isomorphism.html#7219" class="Bound">to</a> <a id="7222" class="Symbol">:</a> <a id="7224" href="plfa.part1.Isomorphism.html#7184" class="Bound">A</a> <a id="7226" class="Symbol">→</a> <a id="7228" href="plfa.part1.Isomorphism.html#7186" class="Bound">B</a><a id="7229" class="Symbol">)</a> <a id="7231" class="Symbol">→</a>
          <a id="7243" class="Symbol">∀</a> <a id="7245" class="Symbol">(</a><a id="7246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7246" class="Bound">from</a> <a id="7251" class="Symbol">:</a> <a id="7253" href="plfa.part1.Isomorphism.html#7186" class="Bound">B</a> <a id="7255" class="Symbol">→</a> <a id="7257" href="plfa.part1.Isomorphism.html#7184" class="Bound">A</a><a id="7258" class="Symbol">)</a> <a id="7260" class="Symbol">→</a>
          <a id="7272" class="Symbol">∀</a> <a id="7274" class="Symbol">(</a><a id="7275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7275" class="Bound">from∘to</a> <a id="7283" class="Symbol">:</a> <a id="7285" class="Symbol">(∀</a> <a id="7288" class="Symbol">(</a><a id="7289" href="plfa.part1.Isomorphism.html#7289" class="Bound">x</a> <a id="7291" class="Symbol">:</a> <a id="7293" href="plfa.part1.Isomorphism.html#7184" class="Bound">A</a><a id="7294" class="Symbol">)</a> <a id="7296" class="Symbol">→</a> <a id="7298" href="plfa.part1.Isomorphism.html#7246" class="Bound">from</a> <a id="7303" class="Symbol">(</a><a id="7304" href="plfa.part1.Isomorphism.html#7219" class="Bound">to</a> <a id="7307" href="plfa.part1.Isomorphism.html#7289" class="Bound">x</a><a id="7308" class="Symbol">)</a> <a id="7310" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7312" href="plfa.part1.Isomorphism.html#7289" class="Bound">x</a><a id="7313" class="Symbol">))</a> <a id="7316" class="Symbol">→</a>
          <a id="7328" class="Symbol">∀</a> <a id="7330" class="Symbol">(</a><a id="7331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7331" class="Bound">to∘from</a> <a id="7339" class="Symbol">:</a> <a id="7341" class="Symbol">(∀</a> <a id="7344" class="Symbol">(</a><a id="7345" href="plfa.part1.Isomorphism.html#7345" class="Bound">y</a> <a id="7347" class="Symbol">:</a> <a id="7349" href="plfa.part1.Isomorphism.html#7186" class="Bound">B</a><a id="7350" class="Symbol">)</a> <a id="7352" class="Symbol">→</a> <a id="7354" href="plfa.part1.Isomorphism.html#7219" class="Bound">to</a> <a id="7357" class="Symbol">(</a><a id="7358" href="plfa.part1.Isomorphism.html#7246" class="Bound">from</a> <a id="7363" href="plfa.part1.Isomorphism.html#7345" class="Bound">y</a><a id="7364" class="Symbol">)</a> <a id="7366" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7368" href="plfa.part1.Isomorphism.html#7345" class="Bound">y</a><a id="7369" class="Symbol">))</a> <a id="7372" class="Symbol">→</a>
          <a id="7384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7184" class="Bound">A</a> <a id="7386" href="plfa.part1.Isomorphism.html#7178" class="Datatype Operator">≃′</a> <a id="7389" href="plfa.part1.Isomorphism.html#7186" class="Bound">B</a>

<a id="to′"></a><a id="7392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7392" class="Function">to′</a> <a id="7396" class="Symbol">:</a> <a id="7398" class="Symbol">∀</a> <a id="7400" class="Symbol">{</a><a id="7401" href="plfa.part1.Isomorphism.html#7401" class="Bound">A</a> <a id="7403" href="plfa.part1.Isomorphism.html#7403" class="Bound">B</a> <a id="7405" class="Symbol">:</a> <a id="7407" class="PrimitiveType">Set</a><a id="7410" class="Symbol">}</a> <a id="7412" class="Symbol">→</a> <a id="7414" class="Symbol">(</a><a id="7415" href="plfa.part1.Isomorphism.html#7401" class="Bound">A</a> <a id="7417" href="plfa.part1.Isomorphism.html#7178" class="Datatype Operator">≃′</a> <a id="7420" href="plfa.part1.Isomorphism.html#7403" class="Bound">B</a><a id="7421" class="Symbol">)</a> <a id="7423" class="Symbol">→</a> <a id="7425" class="Symbol">(</a><a id="7426" href="plfa.part1.Isomorphism.html#7401" class="Bound">A</a> <a id="7428" class="Symbol">→</a> <a id="7430" href="plfa.part1.Isomorphism.html#7403" class="Bound">B</a><a id="7431" class="Symbol">)</a>
<a id="7433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7392" class="Function">to′</a> <a id="7437" class="Symbol">(</a><a id="7438" href="plfa.part1.Isomorphism.html#7208" class="InductiveConstructor">mk-≃′</a> <a id="7444" href="plfa.part1.Isomorphism.html#7444" class="Bound">f</a> <a id="7446" href="plfa.part1.Isomorphism.html#7446" class="Bound">g</a> <a id="7448" href="plfa.part1.Isomorphism.html#7448" class="Bound">g∘f</a> <a id="7452" href="plfa.part1.Isomorphism.html#7452" class="Bound">f∘g</a><a id="7455" class="Symbol">)</a> <a id="7457" class="Symbol">=</a> <a id="7459" href="plfa.part1.Isomorphism.html#7444" class="Bound">f</a>

<a id="from′"></a><a id="7462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7462" class="Function">from′</a> <a id="7468" class="Symbol">:</a> <a id="7470" class="Symbol">∀</a> <a id="7472" class="Symbol">{</a><a id="7473" href="plfa.part1.Isomorphism.html#7473" class="Bound">A</a> <a id="7475" href="plfa.part1.Isomorphism.html#7475" class="Bound">B</a> <a id="7477" class="Symbol">:</a> <a id="7479" class="PrimitiveType">Set</a><a id="7482" class="Symbol">}</a> <a id="7484" class="Symbol">→</a> <a id="7486" class="Symbol">(</a><a id="7487" href="plfa.part1.Isomorphism.html#7473" class="Bound">A</a> <a id="7489" href="plfa.part1.Isomorphism.html#7178" class="Datatype Operator">≃′</a> <a id="7492" href="plfa.part1.Isomorphism.html#7475" class="Bound">B</a><a id="7493" class="Symbol">)</a> <a id="7495" class="Symbol">→</a> <a id="7497" class="Symbol">(</a><a id="7498" href="plfa.part1.Isomorphism.html#7475" class="Bound">B</a> <a id="7500" class="Symbol">→</a> <a id="7502" href="plfa.part1.Isomorphism.html#7473" class="Bound">A</a><a id="7503" class="Symbol">)</a>
<a id="7505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7462" class="Function">from′</a> <a id="7511" class="Symbol">(</a><a id="7512" href="plfa.part1.Isomorphism.html#7208" class="InductiveConstructor">mk-≃′</a> <a id="7518" href="plfa.part1.Isomorphism.html#7518" class="Bound">f</a> <a id="7520" href="plfa.part1.Isomorphism.html#7520" class="Bound">g</a> <a id="7522" href="plfa.part1.Isomorphism.html#7522" class="Bound">g∘f</a> <a id="7526" href="plfa.part1.Isomorphism.html#7526" class="Bound">f∘g</a><a id="7529" class="Symbol">)</a> <a id="7531" class="Symbol">=</a> <a id="7533" href="plfa.part1.Isomorphism.html#7520" class="Bound">g</a>

<a id="from∘to′"></a><a id="7536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7536" class="Function">from∘to′</a> <a id="7545" class="Symbol">:</a> <a id="7547" class="Symbol">∀</a> <a id="7549" class="Symbol">{</a><a id="7550" href="plfa.part1.Isomorphism.html#7550" class="Bound">A</a> <a id="7552" href="plfa.part1.Isomorphism.html#7552" class="Bound">B</a> <a id="7554" class="Symbol">:</a> <a id="7556" class="PrimitiveType">Set</a><a id="7559" class="Symbol">}</a> <a id="7561" class="Symbol">→</a> <a id="7563" class="Symbol">(</a><a id="7564" href="plfa.part1.Isomorphism.html#7564" class="Bound">A≃B</a> <a id="7568" class="Symbol">:</a> <a id="7570" href="plfa.part1.Isomorphism.html#7550" class="Bound">A</a> <a id="7572" href="plfa.part1.Isomorphism.html#7178" class="Datatype Operator">≃′</a> <a id="7575" href="plfa.part1.Isomorphism.html#7552" class="Bound">B</a><a id="7576" class="Symbol">)</a> <a id="7578" class="Symbol">→</a> <a id="7580" class="Symbol">(∀</a> <a id="7583" class="Symbol">(</a><a id="7584" href="plfa.part1.Isomorphism.html#7584" class="Bound">x</a> <a id="7586" class="Symbol">:</a> <a id="7588" href="plfa.part1.Isomorphism.html#7550" class="Bound">A</a><a id="7589" class="Symbol">)</a> <a id="7591" class="Symbol">→</a> <a id="7593" href="plfa.part1.Isomorphism.html#7462" class="Function">from′</a> <a id="7599" href="plfa.part1.Isomorphism.html#7564" class="Bound">A≃B</a> <a id="7603" class="Symbol">(</a><a id="7604" href="plfa.part1.Isomorphism.html#7392" class="Function">to′</a> <a id="7608" href="plfa.part1.Isomorphism.html#7564" class="Bound">A≃B</a> <a id="7612" href="plfa.part1.Isomorphism.html#7584" class="Bound">x</a><a id="7613" class="Symbol">)</a> <a id="7615" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7617" href="plfa.part1.Isomorphism.html#7584" class="Bound">x</a><a id="7618" class="Symbol">)</a>
<a id="7620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7536" class="Function">from∘to′</a> <a id="7629" class="Symbol">(</a><a id="7630" href="plfa.part1.Isomorphism.html#7208" class="InductiveConstructor">mk-≃′</a> <a id="7636" href="plfa.part1.Isomorphism.html#7636" class="Bound">f</a> <a id="7638" href="plfa.part1.Isomorphism.html#7638" class="Bound">g</a> <a id="7640" href="plfa.part1.Isomorphism.html#7640" class="Bound">g∘f</a> <a id="7644" href="plfa.part1.Isomorphism.html#7644" class="Bound">f∘g</a><a id="7647" class="Symbol">)</a> <a id="7649" class="Symbol">=</a> <a id="7651" href="plfa.part1.Isomorphism.html#7640" class="Bound">g∘f</a>

<a id="to∘from′"></a><a id="7656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7656" class="Function">to∘from′</a> <a id="7665" class="Symbol">:</a> <a id="7667" class="Symbol">∀</a> <a id="7669" class="Symbol">{</a><a id="7670" href="plfa.part1.Isomorphism.html#7670" class="Bound">A</a> <a id="7672" href="plfa.part1.Isomorphism.html#7672" class="Bound">B</a> <a id="7674" class="Symbol">:</a> <a id="7676" class="PrimitiveType">Set</a><a id="7679" class="Symbol">}</a> <a id="7681" class="Symbol">→</a> <a id="7683" class="Symbol">(</a><a id="7684" href="plfa.part1.Isomorphism.html#7684" class="Bound">A≃B</a> <a id="7688" class="Symbol">:</a> <a id="7690" href="plfa.part1.Isomorphism.html#7670" class="Bound">A</a> <a id="7692" href="plfa.part1.Isomorphism.html#7178" class="Datatype Operator">≃′</a> <a id="7695" href="plfa.part1.Isomorphism.html#7672" class="Bound">B</a><a id="7696" class="Symbol">)</a> <a id="7698" class="Symbol">→</a> <a id="7700" class="Symbol">(∀</a> <a id="7703" class="Symbol">(</a><a id="7704" href="plfa.part1.Isomorphism.html#7704" class="Bound">y</a> <a id="7706" class="Symbol">:</a> <a id="7708" href="plfa.part1.Isomorphism.html#7672" class="Bound">B</a><a id="7709" class="Symbol">)</a> <a id="7711" class="Symbol">→</a> <a id="7713" href="plfa.part1.Isomorphism.html#7392" class="Function">to′</a> <a id="7717" href="plfa.part1.Isomorphism.html#7684" class="Bound">A≃B</a> <a id="7721" class="Symbol">(</a><a id="7722" href="plfa.part1.Isomorphism.html#7462" class="Function">from′</a> <a id="7728" href="plfa.part1.Isomorphism.html#7684" class="Bound">A≃B</a> <a id="7732" href="plfa.part1.Isomorphism.html#7704" class="Bound">y</a><a id="7733" class="Symbol">)</a> <a id="7735" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7737" href="plfa.part1.Isomorphism.html#7704" class="Bound">y</a><a id="7738" class="Symbol">)</a>
<a id="7740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#7656" class="Function">to∘from′</a> <a id="7749" class="Symbol">(</a><a id="7750" href="plfa.part1.Isomorphism.html#7208" class="InductiveConstructor">mk-≃′</a> <a id="7756" href="plfa.part1.Isomorphism.html#7756" class="Bound">f</a> <a id="7758" href="plfa.part1.Isomorphism.html#7758" class="Bound">g</a> <a id="7760" href="plfa.part1.Isomorphism.html#7760" class="Bound">g∘f</a> <a id="7764" href="plfa.part1.Isomorphism.html#7764" class="Bound">f∘g</a><a id="7767" class="Symbol">)</a> <a id="7769" class="Symbol">=</a> <a id="7771" href="plfa.part1.Isomorphism.html#7764" class="Bound">f∘g</a>
</pre>{% endraw %}
{::comment}
We construct values of the record type with the syntax
{:/}

我们用下面的语法来构造一个记录类型的值：

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

这与使用相应的归纳类型的构造子对应：

    mk-≃′ f g g∘f f∘g

{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。


{::comment}
## Isomorphism is an equivalence
{:/}

## 同构是一个等价关系

{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数作为 `to` 和 `from`：

{% raw %}<pre class="Agda"><a id="≃-refl"></a><a id="8561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8561" class="Function">≃-refl</a> <a id="8568" class="Symbol">:</a> <a id="8570" class="Symbol">∀</a> <a id="8572" class="Symbol">{</a><a id="8573" href="plfa.part1.Isomorphism.html#8573" class="Bound">A</a> <a id="8575" class="Symbol">:</a> <a id="8577" class="PrimitiveType">Set</a><a id="8580" class="Symbol">}</a>
    <a id="8586" class="Comment">-----</a>
  <a id="8594" class="Symbol">→</a> <a id="8596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8573" class="Bound">A</a> <a id="8598" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="8600" href="plfa.part1.Isomorphism.html#8573" class="Bound">A</a>
<a id="8602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8561" class="Function">≃-refl</a> <a id="8609" class="Symbol">=</a>
  <a id="8613" class="Keyword">record</a>
    <a id="8624" class="Symbol">{</a> <a id="8626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="8634" class="Symbol">=</a> <a id="8636" class="Symbol">λ{</a><a id="8638" href="plfa.part1.Isomorphism.html#8638" class="Bound">x</a> <a id="8640" class="Symbol">→</a> <a id="8642" href="plfa.part1.Isomorphism.html#8638" class="Bound">x</a><a id="8643" class="Symbol">}</a>
    <a id="8649" class="Symbol">;</a> <a id="8651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="8659" class="Symbol">=</a> <a id="8661" class="Symbol">λ{</a><a id="8663" href="plfa.part1.Isomorphism.html#8663" class="Bound">y</a> <a id="8665" class="Symbol">→</a> <a id="8667" href="plfa.part1.Isomorphism.html#8663" class="Bound">y</a><a id="8668" class="Symbol">}</a>
    <a id="8674" class="Symbol">;</a> <a id="8676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="8684" class="Symbol">=</a> <a id="8686" class="Symbol">λ{</a><a id="8688" href="plfa.part1.Isomorphism.html#8688" class="Bound">x</a> <a id="8690" class="Symbol">→</a> <a id="8692" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8696" class="Symbol">}</a>
    <a id="8702" class="Symbol">;</a> <a id="8704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="8712" class="Symbol">=</a> <a id="8714" class="Symbol">λ{</a><a id="8716" href="plfa.part1.Isomorphism.html#8716" class="Bound">y</a> <a id="8718" class="Symbol">→</a> <a id="8720" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8724" class="Symbol">}</a>
    <a id="8730" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。

{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：

{% raw %}<pre class="Agda"><a id="≃-sym"></a><a id="9384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9384" class="Function">≃-sym</a> <a id="9390" class="Symbol">:</a> <a id="9392" class="Symbol">∀</a> <a id="9394" class="Symbol">{</a><a id="9395" href="plfa.part1.Isomorphism.html#9395" class="Bound">A</a> <a id="9397" href="plfa.part1.Isomorphism.html#9397" class="Bound">B</a> <a id="9399" class="Symbol">:</a> <a id="9401" class="PrimitiveType">Set</a><a id="9404" class="Symbol">}</a>
  <a id="9408" class="Symbol">→</a> <a id="9410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9395" class="Bound">A</a> <a id="9412" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="9414" href="plfa.part1.Isomorphism.html#9397" class="Bound">B</a>
    <a id="9420" class="Comment">-----</a>
  <a id="9428" class="Symbol">→</a> <a id="9430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9397" class="Bound">B</a> <a id="9432" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="9434" href="plfa.part1.Isomorphism.html#9395" class="Bound">A</a>
<a id="9436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9384" class="Function">≃-sym</a> <a id="9442" href="plfa.part1.Isomorphism.html#9442" class="Bound">A≃B</a> <a id="9446" class="Symbol">=</a>
  <a id="9450" class="Keyword">record</a>
    <a id="9461" class="Symbol">{</a> <a id="9463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="9471" class="Symbol">=</a> <a id="9473" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="9478" href="plfa.part1.Isomorphism.html#9442" class="Bound">A≃B</a>
    <a id="9486" class="Symbol">;</a> <a id="9488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="9496" class="Symbol">=</a> <a id="9498" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a>   <a id="9503" href="plfa.part1.Isomorphism.html#9442" class="Bound">A≃B</a>
    <a id="9511" class="Symbol">;</a> <a id="9513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="9521" class="Symbol">=</a> <a id="9523" href="plfa.part1.Isomorphism.html#5965" class="Field">to∘from</a> <a id="9531" href="plfa.part1.Isomorphism.html#9442" class="Bound">A≃B</a>
    <a id="9539" class="Symbol">;</a> <a id="9541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="9549" class="Symbol">=</a> <a id="9551" href="plfa.part1.Isomorphism.html#5923" class="Field">from∘to</a> <a id="9559" href="plfa.part1.Isomorphism.html#9442" class="Bound">A≃B</a>
    <a id="9567" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：

{% raw %}<pre class="Agda"><a id="≃-trans"></a><a id="9781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9781" class="Function">≃-trans</a> <a id="9789" class="Symbol">:</a> <a id="9791" class="Symbol">∀</a> <a id="9793" class="Symbol">{</a><a id="9794" href="plfa.part1.Isomorphism.html#9794" class="Bound">A</a> <a id="9796" href="plfa.part1.Isomorphism.html#9796" class="Bound">B</a> <a id="9798" href="plfa.part1.Isomorphism.html#9798" class="Bound">C</a> <a id="9800" class="Symbol">:</a> <a id="9802" class="PrimitiveType">Set</a><a id="9805" class="Symbol">}</a>
  <a id="9809" class="Symbol">→</a> <a id="9811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9794" class="Bound">A</a> <a id="9813" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="9815" href="plfa.part1.Isomorphism.html#9796" class="Bound">B</a>
  <a id="9819" class="Symbol">→</a> <a id="9821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9796" class="Bound">B</a> <a id="9823" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="9825" href="plfa.part1.Isomorphism.html#9798" class="Bound">C</a>
    <a id="9831" class="Comment">-----</a>
  <a id="9839" class="Symbol">→</a> <a id="9841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9794" class="Bound">A</a> <a id="9843" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="9845" href="plfa.part1.Isomorphism.html#9798" class="Bound">C</a>
<a id="9847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9781" class="Function">≃-trans</a> <a id="9855" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="9859" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="9863" class="Symbol">=</a>
  <a id="9867" class="Keyword">record</a>
    <a id="9878" class="Symbol">{</a> <a id="9880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>       <a id="9889" class="Symbol">=</a> <a id="9891" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a>   <a id="9896" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="9900" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="9902" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a>   <a id="9907" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a>
    <a id="9915" class="Symbol">;</a> <a id="9917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>     <a id="9926" class="Symbol">=</a> <a id="9928" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="9933" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="9937" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="9939" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="9944" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a>
    <a id="9952" class="Symbol">;</a> <a id="9954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a>  <a id="9963" class="Symbol">=</a> <a id="9965" class="Symbol">λ{</a><a id="9967" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a> <a id="9969" class="Symbol">→</a>
        <a id="9979" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="9995" class="Symbol">(</a><a id="9996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a> <a id="10001" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10005" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="10007" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10012" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a><a id="10015" class="Symbol">)</a> <a id="10017" class="Symbol">((</a><a id="10019" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10022" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10026" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="10028" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10031" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a><a id="10034" class="Symbol">)</a> <a id="10036" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a><a id="10037" class="Symbol">)</a>
        <a id="10047" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="10061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a> <a id="10066" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10070" class="Symbol">(</a><a id="10071" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10076" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10080" class="Symbol">(</a><a id="10081" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10084" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10088" class="Symbol">(</a><a id="10089" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10092" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10096" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a><a id="10097" class="Symbol">)))</a>
        <a id="10109" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10112" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10117" class="Symbol">(</a><a id="10118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a> <a id="10123" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a><a id="10126" class="Symbol">)</a> <a id="10128" class="Symbol">(</a><a id="10129" href="plfa.part1.Isomorphism.html#5923" class="Field">from∘to</a> <a id="10137" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10141" class="Symbol">(</a><a id="10142" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10145" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10149" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a><a id="10150" class="Symbol">))</a> <a id="10153" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a> <a id="10170" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10174" class="Symbol">(</a><a id="10175" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10178" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10182" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a><a id="10183" class="Symbol">)</a>
        <a id="10193" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="10204" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10208" href="plfa.part1.Isomorphism.html#9967" class="Bound">x</a> <a id="10210" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9967" class="Bound">x</a>
        <a id="10232" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="10233" class="Symbol">}</a>
    <a id="10239" class="Symbol">;</a> <a id="10241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="10249" class="Symbol">=</a> <a id="10251" class="Symbol">λ{</a><a id="10253" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a> <a id="10255" class="Symbol">→</a>
        <a id="10265" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="10281" class="Symbol">(</a><a id="10282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a> <a id="10285" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10289" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="10291" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10294" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a><a id="10297" class="Symbol">)</a> <a id="10299" class="Symbol">((</a><a id="10301" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10306" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10310" href="plfa.part1.Isomorphism.html#2709" class="Function Operator">∘</a> <a id="10312" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10317" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a><a id="10320" class="Symbol">)</a> <a id="10322" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a><a id="10323" class="Symbol">)</a>
        <a id="10333" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="10347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a> <a id="10350" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10354" class="Symbol">(</a><a id="10355" href="plfa.part1.Isomorphism.html#5889" class="Field">to</a> <a id="10358" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10362" class="Symbol">(</a><a id="10363" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10368" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10372" class="Symbol">(</a><a id="10373" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10378" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10382" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a><a id="10383" class="Symbol">)))</a>
        <a id="10395" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10398" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10403" class="Symbol">(</a><a id="10404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a> <a id="10407" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a><a id="10410" class="Symbol">)</a> <a id="10412" class="Symbol">(</a><a id="10413" href="plfa.part1.Isomorphism.html#5965" class="Field">to∘from</a> <a id="10421" href="plfa.part1.Isomorphism.html#9855" class="Bound">A≃B</a> <a id="10425" class="Symbol">(</a><a id="10426" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10431" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10435" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a><a id="10436" class="Symbol">))</a> <a id="10439" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a> <a id="10454" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10458" class="Symbol">(</a><a id="10459" href="plfa.part1.Isomorphism.html#5906" class="Field">from</a> <a id="10464" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10468" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a><a id="10469" class="Symbol">)</a>
        <a id="10479" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="10490" href="plfa.part1.Isomorphism.html#9859" class="Bound">B≃C</a> <a id="10494" href="plfa.part1.Isomorphism.html#10253" class="Bound">y</a> <a id="10496" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10253" class="Bound">y</a>
        <a id="10518" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="10519" class="Symbol">}</a>
     <a id="10526" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Equational reasoning for isomorphism
{:/}

## 同构的相等性论证

{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：

{% raw %}<pre class="Agda"><a id="10986" class="Keyword">module</a> <a id="≃-Reasoning"></a><a id="10993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">≃-Reasoning</a> <a id="11005" class="Keyword">where</a>

  <a id="11014" class="Keyword">infix</a>  <a id="11021" class="Number">1</a> <a id="11023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11069" class="Function Operator">≃-begin_</a>
  <a id="11034" class="Keyword">infixr</a> <a id="11041" class="Number">2</a> <a id="11043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11153" class="Function Operator">_≃⟨_⟩_</a>
  <a id="11052" class="Keyword">infix</a>  <a id="11059" class="Number">3</a> <a id="11061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11272" class="Function Operator">_≃-∎</a>

  <a id="≃-Reasoning.≃-begin_"></a><a id="11069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11069" class="Function Operator">≃-begin_</a> <a id="11078" class="Symbol">:</a> <a id="11080" class="Symbol">∀</a> <a id="11082" class="Symbol">{</a><a id="11083" href="plfa.part1.Isomorphism.html#11083" class="Bound">A</a> <a id="11085" href="plfa.part1.Isomorphism.html#11085" class="Bound">B</a> <a id="11087" class="Symbol">:</a> <a id="11089" class="PrimitiveType">Set</a><a id="11092" class="Symbol">}</a>
    <a id="11098" class="Symbol">→</a> <a id="11100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11083" class="Bound">A</a> <a id="11102" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11104" href="plfa.part1.Isomorphism.html#11085" class="Bound">B</a>
      <a id="11112" class="Comment">-----</a>
    <a id="11122" class="Symbol">→</a> <a id="11124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11083" class="Bound">A</a> <a id="11126" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11128" href="plfa.part1.Isomorphism.html#11085" class="Bound">B</a>
  <a id="11132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11069" class="Function Operator">≃-begin</a> <a id="11140" href="plfa.part1.Isomorphism.html#11140" class="Bound">A≃B</a> <a id="11144" class="Symbol">=</a> <a id="11146" href="plfa.part1.Isomorphism.html#11140" class="Bound">A≃B</a>

  <a id="≃-Reasoning._≃⟨_⟩_"></a><a id="11153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11153" class="Function Operator">_≃⟨_⟩_</a> <a id="11160" class="Symbol">:</a> <a id="11162" class="Symbol">∀</a> <a id="11164" class="Symbol">(</a><a id="11165" href="plfa.part1.Isomorphism.html#11165" class="Bound">A</a> <a id="11167" class="Symbol">:</a> <a id="11169" class="PrimitiveType">Set</a><a id="11172" class="Symbol">)</a> <a id="11174" class="Symbol">{</a><a id="11175" href="plfa.part1.Isomorphism.html#11175" class="Bound">B</a> <a id="11177" href="plfa.part1.Isomorphism.html#11177" class="Bound">C</a> <a id="11179" class="Symbol">:</a> <a id="11181" class="PrimitiveType">Set</a><a id="11184" class="Symbol">}</a>
    <a id="11190" class="Symbol">→</a> <a id="11192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11165" class="Bound">A</a> <a id="11194" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11196" href="plfa.part1.Isomorphism.html#11175" class="Bound">B</a>
    <a id="11202" class="Symbol">→</a> <a id="11204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11175" class="Bound">B</a> <a id="11206" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11208" href="plfa.part1.Isomorphism.html#11177" class="Bound">C</a>
      <a id="11216" class="Comment">-----</a>
    <a id="11226" class="Symbol">→</a> <a id="11228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11165" class="Bound">A</a> <a id="11230" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11232" href="plfa.part1.Isomorphism.html#11177" class="Bound">C</a>
  <a id="11236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11236" class="Bound">A</a> <a id="11238" href="plfa.part1.Isomorphism.html#11153" class="Function Operator">≃⟨</a> <a id="11241" href="plfa.part1.Isomorphism.html#11241" class="Bound">A≃B</a> <a id="11245" href="plfa.part1.Isomorphism.html#11153" class="Function Operator">⟩</a> <a id="11247" href="plfa.part1.Isomorphism.html#11247" class="Bound">B≃C</a> <a id="11251" class="Symbol">=</a> <a id="11253" href="plfa.part1.Isomorphism.html#9781" class="Function">≃-trans</a> <a id="11261" href="plfa.part1.Isomorphism.html#11241" class="Bound">A≃B</a> <a id="11265" href="plfa.part1.Isomorphism.html#11247" class="Bound">B≃C</a>

  <a id="≃-Reasoning._≃-∎"></a><a id="11272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11272" class="Function Operator">_≃-∎</a> <a id="11277" class="Symbol">:</a> <a id="11279" class="Symbol">∀</a> <a id="11281" class="Symbol">(</a><a id="11282" href="plfa.part1.Isomorphism.html#11282" class="Bound">A</a> <a id="11284" class="Symbol">:</a> <a id="11286" class="PrimitiveType">Set</a><a id="11289" class="Symbol">)</a>
      <a id="11297" class="Comment">-----</a>
    <a id="11307" class="Symbol">→</a> <a id="11309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11282" class="Bound">A</a> <a id="11311" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="11313" href="plfa.part1.Isomorphism.html#11282" class="Bound">A</a>
  <a id="11317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11317" class="Bound">A</a> <a id="11319" href="plfa.part1.Isomorphism.html#11272" class="Function Operator">≃-∎</a> <a id="11323" class="Symbol">=</a> <a id="11325" href="plfa.part1.Isomorphism.html#8561" class="Function">≃-refl</a>

<a id="11333" class="Keyword">open</a> <a id="11338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Embedding
{:/}

## 嵌入（Embedding）

{::comment}
We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.
{:/}

我们同时也需要*嵌入*的概念，它是同构的弱化概念。同构要求证明两个类型之间的一一对应，而嵌入只需要第一种类型涵盖在第二种类型内，所以两个类型之间有一对多的对应关系。

{::comment}
Here is the formal definition of embedding:
{:/}

嵌入的正式定义如下：

{% raw %}<pre class="Agda"><a id="11906" class="Keyword">infix</a> <a id="11912" class="Number">0</a> <a id="11914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">_≲_</a>
<a id="11918" class="Keyword">record</a> <a id="_≲_"></a><a id="11925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">_≲_</a> <a id="11929" class="Symbol">(</a><a id="11930" href="plfa.part1.Isomorphism.html#11930" class="Bound">A</a> <a id="11932" href="plfa.part1.Isomorphism.html#11932" class="Bound">B</a> <a id="11934" class="Symbol">:</a> <a id="11936" class="PrimitiveType">Set</a><a id="11939" class="Symbol">)</a> <a id="11941" class="Symbol">:</a> <a id="11943" class="PrimitiveType">Set</a> <a id="11947" class="Keyword">where</a>
  <a id="11955" class="Keyword">field</a>
    <a id="_≲_.to"></a><a id="11965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a>      <a id="11973" class="Symbol">:</a> <a id="11975" href="plfa.part1.Isomorphism.html#11930" class="Bound">A</a> <a id="11977" class="Symbol">→</a> <a id="11979" href="plfa.part1.Isomorphism.html#11932" class="Bound">B</a>
    <a id="_≲_.from"></a><a id="11985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a>    <a id="11993" class="Symbol">:</a> <a id="11995" href="plfa.part1.Isomorphism.html#11932" class="Bound">B</a> <a id="11997" class="Symbol">→</a> <a id="11999" href="plfa.part1.Isomorphism.html#11930" class="Bound">A</a>
    <a id="_≲_.from∘to"></a><a id="12005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="12013" class="Symbol">:</a> <a id="12015" class="Symbol">∀</a> <a id="12017" class="Symbol">(</a><a id="12018" href="plfa.part1.Isomorphism.html#12018" class="Bound">x</a> <a id="12020" class="Symbol">:</a> <a id="12022" href="plfa.part1.Isomorphism.html#11930" class="Bound">A</a><a id="12023" class="Symbol">)</a> <a id="12025" class="Symbol">→</a> <a id="12027" class="Field">from</a> <a id="12032" class="Symbol">(</a><a id="12033" class="Field">to</a> <a id="12036" href="plfa.part1.Isomorphism.html#12018" class="Bound">x</a><a id="12037" class="Symbol">)</a> <a id="12039" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12041" href="plfa.part1.Isomorphism.html#12018" class="Bound">x</a>
<a id="12043" class="Keyword">open</a> <a id="12048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Module Operator">_≲_</a>
</pre>{% endraw %}
{::comment}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.
{:/}

除了它缺少了 `to∘from` 字段以外，嵌入的定义和同构是一样的。因此，我们可以得知 `from` 是 `to`
的左逆，但是 `from` 不是 `to` 的右逆。

{::comment}
Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
{:/}

嵌入是自反和传递的，但不是对称的。证明与同构类似，不过去除了不需要的部分：

{% raw %}<pre class="Agda"><a id="≲-refl"></a><a id="12526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12526" class="Function">≲-refl</a> <a id="12533" class="Symbol">:</a> <a id="12535" class="Symbol">∀</a> <a id="12537" class="Symbol">{</a><a id="12538" href="plfa.part1.Isomorphism.html#12538" class="Bound">A</a> <a id="12540" class="Symbol">:</a> <a id="12542" class="PrimitiveType">Set</a><a id="12545" class="Symbol">}</a> <a id="12547" class="Symbol">→</a> <a id="12549" href="plfa.part1.Isomorphism.html#12538" class="Bound">A</a> <a id="12551" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="12553" href="plfa.part1.Isomorphism.html#12538" class="Bound">A</a>
<a id="12555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12526" class="Function">≲-refl</a> <a id="12562" class="Symbol">=</a>
  <a id="12566" class="Keyword">record</a>
    <a id="12577" class="Symbol">{</a> <a id="12579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a>      <a id="12587" class="Symbol">=</a> <a id="12589" class="Symbol">λ{</a><a id="12591" href="plfa.part1.Isomorphism.html#12591" class="Bound">x</a> <a id="12593" class="Symbol">→</a> <a id="12595" href="plfa.part1.Isomorphism.html#12591" class="Bound">x</a><a id="12596" class="Symbol">}</a>
    <a id="12602" class="Symbol">;</a> <a id="12604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a>    <a id="12612" class="Symbol">=</a> <a id="12614" class="Symbol">λ{</a><a id="12616" href="plfa.part1.Isomorphism.html#12616" class="Bound">y</a> <a id="12618" class="Symbol">→</a> <a id="12620" href="plfa.part1.Isomorphism.html#12616" class="Bound">y</a><a id="12621" class="Symbol">}</a>
    <a id="12627" class="Symbol">;</a> <a id="12629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="12637" class="Symbol">=</a> <a id="12639" class="Symbol">λ{</a><a id="12641" href="plfa.part1.Isomorphism.html#12641" class="Bound">x</a> <a id="12643" class="Symbol">→</a> <a id="12645" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="12649" class="Symbol">}</a>
    <a id="12655" class="Symbol">}</a>

<a id="≲-trans"></a><a id="12658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12658" class="Function">≲-trans</a> <a id="12666" class="Symbol">:</a> <a id="12668" class="Symbol">∀</a> <a id="12670" class="Symbol">{</a><a id="12671" href="plfa.part1.Isomorphism.html#12671" class="Bound">A</a> <a id="12673" href="plfa.part1.Isomorphism.html#12673" class="Bound">B</a> <a id="12675" href="plfa.part1.Isomorphism.html#12675" class="Bound">C</a> <a id="12677" class="Symbol">:</a> <a id="12679" class="PrimitiveType">Set</a><a id="12682" class="Symbol">}</a> <a id="12684" class="Symbol">→</a> <a id="12686" href="plfa.part1.Isomorphism.html#12671" class="Bound">A</a> <a id="12688" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="12690" href="plfa.part1.Isomorphism.html#12673" class="Bound">B</a> <a id="12692" class="Symbol">→</a> <a id="12694" href="plfa.part1.Isomorphism.html#12673" class="Bound">B</a> <a id="12696" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="12698" href="plfa.part1.Isomorphism.html#12675" class="Bound">C</a> <a id="12700" class="Symbol">→</a> <a id="12702" href="plfa.part1.Isomorphism.html#12671" class="Bound">A</a> <a id="12704" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="12706" href="plfa.part1.Isomorphism.html#12675" class="Bound">C</a>
<a id="12708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12658" class="Function">≲-trans</a> <a id="12716" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12720" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12724" class="Symbol">=</a>
  <a id="12728" class="Keyword">record</a>
    <a id="12739" class="Symbol">{</a> <a id="12741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a>      <a id="12749" class="Symbol">=</a> <a id="12751" class="Symbol">λ{</a><a id="12753" href="plfa.part1.Isomorphism.html#12753" class="Bound">x</a> <a id="12755" class="Symbol">→</a> <a id="12757" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a>   <a id="12762" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12766" class="Symbol">(</a><a id="12767" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a>   <a id="12772" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12776" href="plfa.part1.Isomorphism.html#12753" class="Bound">x</a><a id="12777" class="Symbol">)}</a>
    <a id="12784" class="Symbol">;</a> <a id="12786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a>    <a id="12794" class="Symbol">=</a> <a id="12796" class="Symbol">λ{</a><a id="12798" href="plfa.part1.Isomorphism.html#12798" class="Bound">y</a> <a id="12800" class="Symbol">→</a> <a id="12802" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="12807" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12811" class="Symbol">(</a><a id="12812" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="12817" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12821" href="plfa.part1.Isomorphism.html#12798" class="Bound">y</a><a id="12822" class="Symbol">)}</a>
    <a id="12829" class="Symbol">;</a> <a id="12831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="12839" class="Symbol">=</a> <a id="12841" class="Symbol">λ{</a><a id="12843" href="plfa.part1.Isomorphism.html#12843" class="Bound">x</a> <a id="12845" class="Symbol">→</a>
        <a id="12855" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="12871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a> <a id="12876" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12880" class="Symbol">(</a><a id="12881" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="12886" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12890" class="Symbol">(</a><a id="12891" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="12894" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12898" class="Symbol">(</a><a id="12899" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="12902" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12906" href="plfa.part1.Isomorphism.html#12843" class="Bound">x</a><a id="12907" class="Symbol">)))</a>
        <a id="12919" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="12922" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="12927" class="Symbol">(</a><a id="12928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a> <a id="12933" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a><a id="12936" class="Symbol">)</a> <a id="12938" class="Symbol">(</a><a id="12939" href="plfa.part1.Isomorphism.html#12005" class="Field">from∘to</a> <a id="12947" href="plfa.part1.Isomorphism.html#12720" class="Bound">B≲C</a> <a id="12951" class="Symbol">(</a><a id="12952" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="12955" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12959" href="plfa.part1.Isomorphism.html#12843" class="Bound">x</a><a id="12960" class="Symbol">))</a> <a id="12963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="12975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a> <a id="12980" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12984" class="Symbol">(</a><a id="12985" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="12988" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="12992" href="plfa.part1.Isomorphism.html#12843" class="Bound">x</a><a id="12993" class="Symbol">)</a>
        <a id="13003" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="13014" href="plfa.part1.Isomorphism.html#12716" class="Bound">A≲B</a> <a id="13018" href="plfa.part1.Isomorphism.html#12843" class="Bound">x</a> <a id="13020" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12843" class="Bound">x</a>
        <a id="13042" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="13043" class="Symbol">}</a>
     <a id="13050" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
{:/}

显而易见的是，如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。这个一种反对称性的弱化形式：

{% raw %}<pre class="Agda"><a id="≲-antisym"></a><a id="13301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13301" class="Function">≲-antisym</a> <a id="13311" class="Symbol">:</a> <a id="13313" class="Symbol">∀</a> <a id="13315" class="Symbol">{</a><a id="13316" href="plfa.part1.Isomorphism.html#13316" class="Bound">A</a> <a id="13318" href="plfa.part1.Isomorphism.html#13318" class="Bound">B</a> <a id="13320" class="Symbol">:</a> <a id="13322" class="PrimitiveType">Set</a><a id="13325" class="Symbol">}</a>
  <a id="13329" class="Symbol">→</a> <a id="13331" class="Symbol">(</a><a id="13332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13332" class="Bound">A≲B</a> <a id="13336" class="Symbol">:</a> <a id="13338" href="plfa.part1.Isomorphism.html#13316" class="Bound">A</a> <a id="13340" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="13342" href="plfa.part1.Isomorphism.html#13318" class="Bound">B</a><a id="13343" class="Symbol">)</a>
  <a id="13347" class="Symbol">→</a> <a id="13349" class="Symbol">(</a><a id="13350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13350" class="Bound">B≲A</a> <a id="13354" class="Symbol">:</a> <a id="13356" href="plfa.part1.Isomorphism.html#13318" class="Bound">B</a> <a id="13358" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="13360" href="plfa.part1.Isomorphism.html#13316" class="Bound">A</a><a id="13361" class="Symbol">)</a>
  <a id="13365" class="Symbol">→</a> <a id="13367" class="Symbol">(</a><a id="13368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a> <a id="13371" href="plfa.part1.Isomorphism.html#13332" class="Bound">A≲B</a> <a id="13375" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13377" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="13382" href="plfa.part1.Isomorphism.html#13350" class="Bound">B≲A</a><a id="13385" class="Symbol">)</a>
  <a id="13389" class="Symbol">→</a> <a id="13391" class="Symbol">(</a><a id="13392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a> <a id="13397" href="plfa.part1.Isomorphism.html#13332" class="Bound">A≲B</a> <a id="13401" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13403" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="13406" href="plfa.part1.Isomorphism.html#13350" class="Bound">B≲A</a><a id="13409" class="Symbol">)</a>
    <a id="13415" class="Comment">-------------------</a>
  <a id="13437" class="Symbol">→</a> <a id="13439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13316" class="Bound">A</a> <a id="13441" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="13443" href="plfa.part1.Isomorphism.html#13318" class="Bound">B</a>
<a id="13445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13301" class="Function">≲-antisym</a> <a id="13455" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a> <a id="13459" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13463" href="plfa.part1.Isomorphism.html#13463" class="Bound">to≡from</a> <a id="13471" href="plfa.part1.Isomorphism.html#13471" class="Bound">from≡to</a> <a id="13479" class="Symbol">=</a>
  <a id="13483" class="Keyword">record</a>
    <a id="13494" class="Symbol">{</a> <a id="13496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="13504" class="Symbol">=</a> <a id="13506" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="13509" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a>
    <a id="13517" class="Symbol">;</a> <a id="13519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="13527" class="Symbol">=</a> <a id="13529" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="13534" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a>
    <a id="13542" class="Symbol">;</a> <a id="13544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="13552" class="Symbol">=</a> <a id="13554" href="plfa.part1.Isomorphism.html#12005" class="Field">from∘to</a> <a id="13562" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a>
    <a id="13570" class="Symbol">;</a> <a id="13572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="13580" class="Symbol">=</a> <a id="13582" class="Symbol">λ{</a><a id="13584" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a> <a id="13586" class="Symbol">→</a>
        <a id="13596" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="13612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a> <a id="13615" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a> <a id="13619" class="Symbol">(</a><a id="13620" href="plfa.part1.Isomorphism.html#11985" class="Field">from</a> <a id="13625" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a> <a id="13629" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a><a id="13630" class="Symbol">)</a>
        <a id="13640" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13643" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13648" class="Symbol">(</a><a id="13649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a> <a id="13652" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a><a id="13655" class="Symbol">)</a> <a id="13657" class="Symbol">(</a><a id="13658" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13667" href="plfa.part1.Isomorphism.html#13471" class="Bound">from≡to</a> <a id="13675" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a><a id="13676" class="Symbol">)</a> <a id="13678" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a> <a id="13693" href="plfa.part1.Isomorphism.html#13455" class="Bound">A≲B</a> <a id="13697" class="Symbol">(</a><a id="13698" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="13701" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13705" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a><a id="13706" class="Symbol">)</a>
        <a id="13716" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13719" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13463" class="Bound">to≡from</a> <a id="13736" class="Symbol">(</a><a id="13737" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="13740" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13744" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a><a id="13745" class="Symbol">)</a> <a id="13747" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a> <a id="13764" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13768" class="Symbol">(</a><a id="13769" href="plfa.part1.Isomorphism.html#11965" class="Field">to</a> <a id="13772" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13776" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a><a id="13777" class="Symbol">)</a>
        <a id="13787" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="13798" href="plfa.part1.Isomorphism.html#13459" class="Bound">B≲A</a> <a id="13802" href="plfa.part1.Isomorphism.html#13584" class="Bound">y</a> <a id="13804" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#13584" class="Bound">y</a>
        <a id="13826" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="13827" class="Symbol">}</a>
    <a id="13833" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.
{:/}

前三部分可以直接从嵌入中得来，最后一部分我们可以把 `B ≲ A` 中的左逆和两个嵌入中的 `to` 与 `from` 部分的相等性来获得同构中的右逆。


{::comment}
## Equational reasoning for embedding
{:/}

## 嵌入的相等性论证

{::comment}
We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:
{:/}

和同构类似，我们亦支持嵌入的相等性论证：

{% raw %}<pre class="Agda"><a id="14382" class="Keyword">module</a> <a id="≲-Reasoning"></a><a id="14389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14389" class="Module">≲-Reasoning</a> <a id="14401" class="Keyword">where</a>

  <a id="14410" class="Keyword">infix</a>  <a id="14417" class="Number">1</a> <a id="14419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14465" class="Function Operator">≲-begin_</a>
  <a id="14430" class="Keyword">infixr</a> <a id="14437" class="Number">2</a> <a id="14439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14549" class="Function Operator">_≲⟨_⟩_</a>
  <a id="14448" class="Keyword">infix</a>  <a id="14455" class="Number">3</a> <a id="14457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14668" class="Function Operator">_≲-∎</a>

  <a id="≲-Reasoning.≲-begin_"></a><a id="14465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14465" class="Function Operator">≲-begin_</a> <a id="14474" class="Symbol">:</a> <a id="14476" class="Symbol">∀</a> <a id="14478" class="Symbol">{</a><a id="14479" href="plfa.part1.Isomorphism.html#14479" class="Bound">A</a> <a id="14481" href="plfa.part1.Isomorphism.html#14481" class="Bound">B</a> <a id="14483" class="Symbol">:</a> <a id="14485" class="PrimitiveType">Set</a><a id="14488" class="Symbol">}</a>
    <a id="14494" class="Symbol">→</a> <a id="14496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14479" class="Bound">A</a> <a id="14498" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14500" href="plfa.part1.Isomorphism.html#14481" class="Bound">B</a>
      <a id="14508" class="Comment">-----</a>
    <a id="14518" class="Symbol">→</a> <a id="14520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14479" class="Bound">A</a> <a id="14522" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14524" href="plfa.part1.Isomorphism.html#14481" class="Bound">B</a>
  <a id="14528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14465" class="Function Operator">≲-begin</a> <a id="14536" href="plfa.part1.Isomorphism.html#14536" class="Bound">A≲B</a> <a id="14540" class="Symbol">=</a> <a id="14542" href="plfa.part1.Isomorphism.html#14536" class="Bound">A≲B</a>

  <a id="≲-Reasoning._≲⟨_⟩_"></a><a id="14549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14549" class="Function Operator">_≲⟨_⟩_</a> <a id="14556" class="Symbol">:</a> <a id="14558" class="Symbol">∀</a> <a id="14560" class="Symbol">(</a><a id="14561" href="plfa.part1.Isomorphism.html#14561" class="Bound">A</a> <a id="14563" class="Symbol">:</a> <a id="14565" class="PrimitiveType">Set</a><a id="14568" class="Symbol">)</a> <a id="14570" class="Symbol">{</a><a id="14571" href="plfa.part1.Isomorphism.html#14571" class="Bound">B</a> <a id="14573" href="plfa.part1.Isomorphism.html#14573" class="Bound">C</a> <a id="14575" class="Symbol">:</a> <a id="14577" class="PrimitiveType">Set</a><a id="14580" class="Symbol">}</a>
    <a id="14586" class="Symbol">→</a> <a id="14588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14561" class="Bound">A</a> <a id="14590" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14592" href="plfa.part1.Isomorphism.html#14571" class="Bound">B</a>
    <a id="14598" class="Symbol">→</a> <a id="14600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14571" class="Bound">B</a> <a id="14602" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14604" href="plfa.part1.Isomorphism.html#14573" class="Bound">C</a>
      <a id="14612" class="Comment">-----</a>
    <a id="14622" class="Symbol">→</a> <a id="14624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14561" class="Bound">A</a> <a id="14626" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14628" href="plfa.part1.Isomorphism.html#14573" class="Bound">C</a>
  <a id="14632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14632" class="Bound">A</a> <a id="14634" href="plfa.part1.Isomorphism.html#14549" class="Function Operator">≲⟨</a> <a id="14637" href="plfa.part1.Isomorphism.html#14637" class="Bound">A≲B</a> <a id="14641" href="plfa.part1.Isomorphism.html#14549" class="Function Operator">⟩</a> <a id="14643" href="plfa.part1.Isomorphism.html#14643" class="Bound">B≲C</a> <a id="14647" class="Symbol">=</a> <a id="14649" href="plfa.part1.Isomorphism.html#12658" class="Function">≲-trans</a> <a id="14657" href="plfa.part1.Isomorphism.html#14637" class="Bound">A≲B</a> <a id="14661" href="plfa.part1.Isomorphism.html#14643" class="Bound">B≲C</a>

  <a id="≲-Reasoning._≲-∎"></a><a id="14668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14668" class="Function Operator">_≲-∎</a> <a id="14673" class="Symbol">:</a> <a id="14675" class="Symbol">∀</a> <a id="14677" class="Symbol">(</a><a id="14678" href="plfa.part1.Isomorphism.html#14678" class="Bound">A</a> <a id="14680" class="Symbol">:</a> <a id="14682" class="PrimitiveType">Set</a><a id="14685" class="Symbol">)</a>
      <a id="14693" class="Comment">-----</a>
    <a id="14703" class="Symbol">→</a> <a id="14705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14678" class="Bound">A</a> <a id="14707" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14709" href="plfa.part1.Isomorphism.html#14678" class="Bound">A</a>
  <a id="14713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14713" class="Bound">A</a> <a id="14715" href="plfa.part1.Isomorphism.html#14668" class="Function Operator">≲-∎</a> <a id="14719" class="Symbol">=</a> <a id="14721" href="plfa.part1.Isomorphism.html#12526" class="Function">≲-refl</a>

<a id="14729" class="Keyword">open</a> <a id="14734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14389" class="Module">≲-Reasoning</a>
</pre>{% endraw %}
{::comment}
#### Exercise `≃-implies-≲` (practice)
{:/}

#### 练习 `≃-implies-≲`（实践）

{::comment}
Show that every isomorphism implies an embedding.
{:/}

证明每个同构蕴涵了一个嵌入。

{% raw %}<pre class="Agda"><a id="14923" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="14935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14935" class="Postulate">≃-implies-≲</a> <a id="14947" class="Symbol">:</a> <a id="14949" class="Symbol">∀</a> <a id="14951" class="Symbol">{</a><a id="14952" href="plfa.part1.Isomorphism.html#14952" class="Bound">A</a> <a id="14954" href="plfa.part1.Isomorphism.html#14954" class="Bound">B</a> <a id="14956" class="Symbol">:</a> <a id="14958" class="PrimitiveType">Set</a><a id="14961" class="Symbol">}</a>
    <a id="14967" class="Symbol">→</a> <a id="14969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14952" class="Bound">A</a> <a id="14971" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">≃</a> <a id="14973" href="plfa.part1.Isomorphism.html#14954" class="Bound">B</a>
      <a id="14981" class="Comment">-----</a>
    <a id="14991" class="Symbol">→</a> <a id="14993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#14952" class="Bound">A</a> <a id="14995" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">≲</a> <a id="14997" href="plfa.part1.Isomorphism.html#14954" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="15020" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15057" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_⇔_` (practice) {#iff}
{:/}

#### 练习 `_⇔_`（实践） {#iff}

{::comment}
Define equivalence of propositions (also known as "if and only if") as follows:
{:/}

按下列形式定义命题的等价性（又名“当且仅当“）：

{% raw %}<pre class="Agda"><a id="15285" class="Keyword">record</a> <a id="_⇔_"></a><a id="15292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#15292" class="Record Operator">_⇔_</a> <a id="15296" class="Symbol">(</a><a id="15297" href="plfa.part1.Isomorphism.html#15297" class="Bound">A</a> <a id="15299" href="plfa.part1.Isomorphism.html#15299" class="Bound">B</a> <a id="15301" class="Symbol">:</a> <a id="15303" class="PrimitiveType">Set</a><a id="15306" class="Symbol">)</a> <a id="15308" class="Symbol">:</a> <a id="15310" class="PrimitiveType">Set</a> <a id="15314" class="Keyword">where</a>
  <a id="15322" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="15332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#15332" class="Field">to</a>   <a id="15337" class="Symbol">:</a> <a id="15339" href="plfa.part1.Isomorphism.html#15297" class="Bound">A</a> <a id="15341" class="Symbol">→</a> <a id="15343" href="plfa.part1.Isomorphism.html#15299" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="15349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#15349" class="Field">from</a> <a id="15354" class="Symbol">:</a> <a id="15356" href="plfa.part1.Isomorphism.html#15299" class="Bound">B</a> <a id="15358" class="Symbol">→</a> <a id="15360" href="plfa.part1.Isomorphism.html#15297" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Show that equivalence is reflexive, symmetric, and transitive.
{:/}

证明等价性是自反、对称和传递的。

{::comment}
{% raw %}<pre class="Agda"><a id="15482" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15519" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}
{:/}

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin) and
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:
{:/}

回忆练习 [Bin]({{ site.baseurl }}/Naturals/#Bin) 和
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)，我们定义了比特串数据类型 `Bin` 来表示自然数，并要求你来定义下列函数：


    to : ℕ → Bin
    from : Bin → ℕ

{::comment}
which satisfy the following property:
{:/}

它们满足如下性质：

    from (to n) ≡ n

{::comment}
Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{:/}

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。

{::comment}
{% raw %}<pre class="Agda"><a id="16330" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="16367" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Why do `to` and `from` not form an isomorphism?
{:/}

为什么 `to` 和 `from` 不能构造一个同构？


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="16653" class="Keyword">import</a> <a id="16660" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="16669" class="Keyword">using</a> <a id="16675" class="Symbol">(</a><a id="16676" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="16679" class="Symbol">)</a>
<a id="16681" class="Keyword">import</a> <a id="16688" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html" class="Module">Function.Inverse</a> <a id="16705" class="Keyword">using</a> <a id="16711" class="Symbol">(</a><a id="16712" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html#2229" class="Function Operator">_↔_</a><a id="16715" class="Symbol">)</a>
<a id="16717" class="Keyword">import</a> <a id="16724" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html" class="Module">Function.LeftInverse</a> <a id="16745" class="Keyword">using</a> <a id="16751" class="Symbol">(</a><a id="16752" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html#2682" class="Function Operator">_↞_</a><a id="16755" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.
{:/}

标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，并可以由任何相等性的记法来参数化。


## Unicode

{::comment}
This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用了如下 Unicode：

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
