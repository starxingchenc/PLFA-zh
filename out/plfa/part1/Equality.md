---
src       : "src/plfa/part1/Equality.lagda.md"
title     : "Equality: 相等性与等式推理"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="183" class="Keyword">module</a> <a id="190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}" class="Module">plfa.part1.Equality</a> <a id="210" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
{:/}

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，我们将相等性作为一个基础运算，而现在我们来说明如果将其定义为一个归纳的数据类型。


{::comment}
## Imports
{:/}

## 导入

{::comment}
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
{:/}

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。我们在此定义相等性，导入其他内容将会产生冲突。


{::comment}
## Equality
{:/}

## 相等性

{::comment}
We declare equality as follows:
{:/}

我们如下定义相等性：

{% raw %}<pre class="Agda"><a id="1054" class="Keyword">data</a> <a id="_≡_"></a><a id="1059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1059" class="Datatype Operator">_≡_</a> <a id="1063" class="Symbol">{</a><a id="1064" href="plfa.part1.Equality.html#1064" class="Bound">A</a> <a id="1066" class="Symbol">:</a> <a id="1068" class="PrimitiveType">Set</a><a id="1071" class="Symbol">}</a> <a id="1073" class="Symbol">(</a><a id="1074" href="plfa.part1.Equality.html#1074" class="Bound">x</a> <a id="1076" class="Symbol">:</a> <a id="1078" href="plfa.part1.Equality.html#1064" class="Bound">A</a><a id="1079" class="Symbol">)</a> <a id="1081" class="Symbol">:</a> <a id="1083" href="plfa.part1.Equality.html#1064" class="Bound">A</a> <a id="1085" class="Symbol">→</a> <a id="1087" class="PrimitiveType">Set</a> <a id="1091" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="1099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1099" class="InductiveConstructor">refl</a> <a id="1104" class="Symbol">:</a> <a id="1106" href="plfa.part1.Equality.html#1074" class="Bound">x</a> <a id="1108" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="1110" href="plfa.part1.Equality.html#1074" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
{:/}

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造子 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，而第二个参数（Argument）则是由 `A → Set` 的索引给出。这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，这样它才可以等用于第一个。

{::comment}
We declare the precedence of equality as follows:
{:/}

我们如下定义相等性的优先级：

{% raw %}<pre class="Agda"><a id="2112" class="Keyword">infix</a> <a id="2118" class="Number">4</a> <a id="2120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1059" class="Datatype Operator">_≡_</a>
</pre>{% endraw %}
{::comment}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
{:/}

我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以其它算术运算符的结合都比它紧密。由于它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。


{::comment}
## Equality is an equivalence relation
{:/}

## 相等性是一个等价关系（Equivalence Relation）

{::comment}
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{:/}

一个等价关系是自反、对称和传递的。其中自反性可以通过构造子 `refl` 直接从相等性的定义中得来。我们可以直接地证明其对称性：

{% raw %}<pre class="Agda"><a id="sym"></a><a id="2823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#2823" class="Function">sym</a> <a id="2827" class="Symbol">:</a> <a id="2829" class="Symbol">∀</a> <a id="2831" class="Symbol">{</a><a id="2832" href="plfa.part1.Equality.html#2832" class="Bound">A</a> <a id="2834" class="Symbol">:</a> <a id="2836" class="PrimitiveType">Set</a><a id="2839" class="Symbol">}</a> <a id="2841" class="Symbol">{</a><a id="2842" href="plfa.part1.Equality.html#2842" class="Bound">x</a> <a id="2844" href="plfa.part1.Equality.html#2844" class="Bound">y</a> <a id="2846" class="Symbol">:</a> <a id="2848" href="plfa.part1.Equality.html#2832" class="Bound">A</a><a id="2849" class="Symbol">}</a>
  <a id="2853" class="Symbol">→</a> <a id="2855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#2842" class="Bound">x</a> <a id="2857" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="2859" href="plfa.part1.Equality.html#2844" class="Bound">y</a>
    <a id="2865" class="Comment">-----</a>
  <a id="2873" class="Symbol">→</a> <a id="2875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#2844" class="Bound">y</a> <a id="2877" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="2879" href="plfa.part1.Equality.html#2842" class="Bound">x</a>
<a id="2881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#2823" class="Function">sym</a> <a id="2885" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a> <a id="2890" class="Symbol">=</a> <a id="2892" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
{:/}

这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。

{::comment}
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
{:/}

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

{::comment}
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
{:/}

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为所有可能的构造子。此处只有一个构造子：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

{::comment}
This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
{:/}

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。

{::comment}
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
{:/}

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造子实例。

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

{::comment}
This completes the definition as given above.
{:/}

我们至此完成了与之前给出证明相同的证明。

{::comment}
Transitivity is equally straightforward:
{:/}

传递性亦是很直接：

{% raw %}<pre class="Agda"><a id="trans"></a><a id="5160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5160" class="Function">trans</a> <a id="5166" class="Symbol">:</a> <a id="5168" class="Symbol">∀</a> <a id="5170" class="Symbol">{</a><a id="5171" href="plfa.part1.Equality.html#5171" class="Bound">A</a> <a id="5173" class="Symbol">:</a> <a id="5175" class="PrimitiveType">Set</a><a id="5178" class="Symbol">}</a> <a id="5180" class="Symbol">{</a><a id="5181" href="plfa.part1.Equality.html#5181" class="Bound">x</a> <a id="5183" href="plfa.part1.Equality.html#5183" class="Bound">y</a> <a id="5185" href="plfa.part1.Equality.html#5185" class="Bound">z</a> <a id="5187" class="Symbol">:</a> <a id="5189" href="plfa.part1.Equality.html#5171" class="Bound">A</a><a id="5190" class="Symbol">}</a>
  <a id="5194" class="Symbol">→</a> <a id="5196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5181" class="Bound">x</a> <a id="5198" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="5200" href="plfa.part1.Equality.html#5183" class="Bound">y</a>
  <a id="5204" class="Symbol">→</a> <a id="5206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5183" class="Bound">y</a> <a id="5208" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="5210" href="plfa.part1.Equality.html#5185" class="Bound">z</a>
    <a id="5216" class="Comment">-----</a>
  <a id="5224" class="Symbol">→</a> <a id="5226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5181" class="Bound">x</a> <a id="5228" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="5230" href="plfa.part1.Equality.html#5185" class="Bound">z</a>
<a id="5232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5160" class="Function">trans</a> <a id="5238" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a> <a id="5243" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>  <a id="5249" class="Symbol">=</a>  <a id="5252" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
{:/}

同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。


{::comment}
## Congruence and substitution {#cong}
{:/}

## 合同性和替换性 {#cong}

{::comment}
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{:/}

相等性满足 *合同性*（Congurence）。如果两个项相等，那么对它们使用相同的函数，其结果仍然相等：

{% raw %}<pre class="Agda"><a id="cong"></a><a id="5760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5760" class="Function">cong</a> <a id="5765" class="Symbol">:</a> <a id="5767" class="Symbol">∀</a> <a id="5769" class="Symbol">{</a><a id="5770" href="plfa.part1.Equality.html#5770" class="Bound">A</a> <a id="5772" href="plfa.part1.Equality.html#5772" class="Bound">B</a> <a id="5774" class="Symbol">:</a> <a id="5776" class="PrimitiveType">Set</a><a id="5779" class="Symbol">}</a> <a id="5781" class="Symbol">(</a><a id="5782" href="plfa.part1.Equality.html#5782" class="Bound">f</a> <a id="5784" class="Symbol">:</a> <a id="5786" href="plfa.part1.Equality.html#5770" class="Bound">A</a> <a id="5788" class="Symbol">→</a> <a id="5790" href="plfa.part1.Equality.html#5772" class="Bound">B</a><a id="5791" class="Symbol">)</a> <a id="5793" class="Symbol">{</a><a id="5794" href="plfa.part1.Equality.html#5794" class="Bound">x</a> <a id="5796" href="plfa.part1.Equality.html#5796" class="Bound">y</a> <a id="5798" class="Symbol">:</a> <a id="5800" href="plfa.part1.Equality.html#5770" class="Bound">A</a><a id="5801" class="Symbol">}</a>
  <a id="5805" class="Symbol">→</a> <a id="5807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5794" class="Bound">x</a> <a id="5809" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="5811" href="plfa.part1.Equality.html#5796" class="Bound">y</a>
    <a id="5817" class="Comment">---------</a>
  <a id="5829" class="Symbol">→</a> <a id="5831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5782" class="Bound">f</a> <a id="5833" href="plfa.part1.Equality.html#5794" class="Bound">x</a> <a id="5835" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="5837" href="plfa.part1.Equality.html#5782" class="Bound">f</a> <a id="5839" href="plfa.part1.Equality.html#5796" class="Bound">y</a>
<a id="5841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5760" class="Function">cong</a> <a id="5846" href="plfa.part1.Equality.html#5846" class="Bound">f</a> <a id="5848" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>  <a id="5854" class="Symbol">=</a>  <a id="5857" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Congruence of functions with two arguments is similar:
{:/}

两个参数的函数也满足合同性：

{% raw %}<pre class="Agda"><a id="cong₂"></a><a id="5960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5960" class="Function">cong₂</a> <a id="5966" class="Symbol">:</a> <a id="5968" class="Symbol">∀</a> <a id="5970" class="Symbol">{</a><a id="5971" href="plfa.part1.Equality.html#5971" class="Bound">A</a> <a id="5973" href="plfa.part1.Equality.html#5973" class="Bound">B</a> <a id="5975" href="plfa.part1.Equality.html#5975" class="Bound">C</a> <a id="5977" class="Symbol">:</a> <a id="5979" class="PrimitiveType">Set</a><a id="5982" class="Symbol">}</a> <a id="5984" class="Symbol">(</a><a id="5985" href="plfa.part1.Equality.html#5985" class="Bound">f</a> <a id="5987" class="Symbol">:</a> <a id="5989" href="plfa.part1.Equality.html#5971" class="Bound">A</a> <a id="5991" class="Symbol">→</a> <a id="5993" href="plfa.part1.Equality.html#5973" class="Bound">B</a> <a id="5995" class="Symbol">→</a> <a id="5997" href="plfa.part1.Equality.html#5975" class="Bound">C</a><a id="5998" class="Symbol">)</a> <a id="6000" class="Symbol">{</a><a id="6001" href="plfa.part1.Equality.html#6001" class="Bound">u</a> <a id="6003" href="plfa.part1.Equality.html#6003" class="Bound">x</a> <a id="6005" class="Symbol">:</a> <a id="6007" href="plfa.part1.Equality.html#5971" class="Bound">A</a><a id="6008" class="Symbol">}</a> <a id="6010" class="Symbol">{</a><a id="6011" href="plfa.part1.Equality.html#6011" class="Bound">v</a> <a id="6013" href="plfa.part1.Equality.html#6013" class="Bound">y</a> <a id="6015" class="Symbol">:</a> <a id="6017" href="plfa.part1.Equality.html#5973" class="Bound">B</a><a id="6018" class="Symbol">}</a>
  <a id="6022" class="Symbol">→</a> <a id="6024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6001" class="Bound">u</a> <a id="6026" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6028" href="plfa.part1.Equality.html#6003" class="Bound">x</a>
  <a id="6032" class="Symbol">→</a> <a id="6034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6011" class="Bound">v</a> <a id="6036" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6038" href="plfa.part1.Equality.html#6013" class="Bound">y</a>
    <a id="6044" class="Comment">-------------</a>
  <a id="6060" class="Symbol">→</a> <a id="6062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5985" class="Bound">f</a> <a id="6064" href="plfa.part1.Equality.html#6001" class="Bound">u</a> <a id="6066" href="plfa.part1.Equality.html#6011" class="Bound">v</a> <a id="6068" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6070" href="plfa.part1.Equality.html#5985" class="Bound">f</a> <a id="6072" href="plfa.part1.Equality.html#6003" class="Bound">x</a> <a id="6074" href="plfa.part1.Equality.html#6013" class="Bound">y</a>
<a id="6076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5960" class="Function">cong₂</a> <a id="6082" href="plfa.part1.Equality.html#6082" class="Bound">f</a> <a id="6084" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a> <a id="6089" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>  <a id="6095" class="Symbol">=</a>  <a id="6098" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{:/}

在函数上的等价性也满足合同性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：

{% raw %}<pre class="Agda"><a id="cong-app"></a><a id="6335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6335" class="Function">cong-app</a> <a id="6344" class="Symbol">:</a> <a id="6346" class="Symbol">∀</a> <a id="6348" class="Symbol">{</a><a id="6349" href="plfa.part1.Equality.html#6349" class="Bound">A</a> <a id="6351" href="plfa.part1.Equality.html#6351" class="Bound">B</a> <a id="6353" class="Symbol">:</a> <a id="6355" class="PrimitiveType">Set</a><a id="6358" class="Symbol">}</a> <a id="6360" class="Symbol">{</a><a id="6361" href="plfa.part1.Equality.html#6361" class="Bound">f</a> <a id="6363" href="plfa.part1.Equality.html#6363" class="Bound">g</a> <a id="6365" class="Symbol">:</a> <a id="6367" href="plfa.part1.Equality.html#6349" class="Bound">A</a> <a id="6369" class="Symbol">→</a> <a id="6371" href="plfa.part1.Equality.html#6351" class="Bound">B</a><a id="6372" class="Symbol">}</a>
  <a id="6376" class="Symbol">→</a> <a id="6378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6361" class="Bound">f</a> <a id="6380" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6382" href="plfa.part1.Equality.html#6363" class="Bound">g</a>
    <a id="6388" class="Comment">---------------------</a>
  <a id="6412" class="Symbol">→</a> <a id="6414" class="Symbol">∀</a> <a id="6416" class="Symbol">(</a><a id="6417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6417" class="Bound">x</a> <a id="6419" class="Symbol">:</a> <a id="6421" href="plfa.part1.Equality.html#6349" class="Bound">A</a><a id="6422" class="Symbol">)</a> <a id="6424" class="Symbol">→</a> <a id="6426" href="plfa.part1.Equality.html#6361" class="Bound">f</a> <a id="6428" href="plfa.part1.Equality.html#6417" class="Bound">x</a> <a id="6430" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6432" href="plfa.part1.Equality.html#6363" class="Bound">g</a> <a id="6434" href="plfa.part1.Equality.html#6417" class="Bound">x</a>
<a id="6436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6335" class="Function">cong-app</a> <a id="6445" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a> <a id="6450" href="plfa.part1.Equality.html#6450" class="Bound">x</a> <a id="6452" class="Symbol">=</a> <a id="6454" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{:/}

相等性也满足*替换性*（Substitution）。如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。

{% raw %}<pre class="Agda"><a id="subst"></a><a id="6678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6678" class="Function">subst</a> <a id="6684" class="Symbol">:</a> <a id="6686" class="Symbol">∀</a> <a id="6688" class="Symbol">{</a><a id="6689" href="plfa.part1.Equality.html#6689" class="Bound">A</a> <a id="6691" class="Symbol">:</a> <a id="6693" class="PrimitiveType">Set</a><a id="6696" class="Symbol">}</a> <a id="6698" class="Symbol">{</a><a id="6699" href="plfa.part1.Equality.html#6699" class="Bound">x</a> <a id="6701" href="plfa.part1.Equality.html#6701" class="Bound">y</a> <a id="6703" class="Symbol">:</a> <a id="6705" href="plfa.part1.Equality.html#6689" class="Bound">A</a><a id="6706" class="Symbol">}</a> <a id="6708" class="Symbol">(</a><a id="6709" href="plfa.part1.Equality.html#6709" class="Bound">P</a> <a id="6711" class="Symbol">:</a> <a id="6713" href="plfa.part1.Equality.html#6689" class="Bound">A</a> <a id="6715" class="Symbol">→</a> <a id="6717" class="PrimitiveType">Set</a><a id="6720" class="Symbol">)</a>
  <a id="6724" class="Symbol">→</a> <a id="6726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6699" class="Bound">x</a> <a id="6728" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="6730" href="plfa.part1.Equality.html#6701" class="Bound">y</a>
    <a id="6736" class="Comment">---------</a>
  <a id="6748" class="Symbol">→</a> <a id="6750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6709" class="Bound">P</a> <a id="6752" href="plfa.part1.Equality.html#6699" class="Bound">x</a> <a id="6754" class="Symbol">→</a> <a id="6756" href="plfa.part1.Equality.html#6709" class="Bound">P</a> <a id="6758" href="plfa.part1.Equality.html#6701" class="Bound">y</a>
<a id="6760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6678" class="Function">subst</a> <a id="6766" href="plfa.part1.Equality.html#6766" class="Bound">P</a> <a id="6768" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a> <a id="6773" href="plfa.part1.Equality.html#6773" class="Bound">px</a> <a id="6776" class="Symbol">=</a> <a id="6778" href="plfa.part1.Equality.html#6773" class="Bound">px</a>
</pre>{% endraw %}

{::comment}
## Chains of equations
{:/}

## 等式串

{::comment}
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{:/}

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们讲声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。

{% raw %}<pre class="Agda"><a id="7149" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="7156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7156" class="Module">≡-Reasoning</a> <a id="7168" class="Symbol">{</a><a id="7169" href="plfa.part1.Equality.html#7169" class="Bound">A</a> <a id="7171" class="Symbol">:</a> <a id="7173" class="PrimitiveType">Set</a><a id="7176" class="Symbol">}</a> <a id="7178" class="Keyword">where</a>

  <a id="7187" class="Keyword">infix</a>  <a id="7194" class="Number">1</a> <a id="7196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin_</a>
  <a id="7205" class="Keyword">infixr</a> <a id="7212" class="Number">2</a> <a id="7214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7324" class="Function Operator">_≡⟨⟩_</a> <a id="7220" href="plfa.part1.Equality.html#7409" class="Function Operator">_≡⟨_⟩_</a>
  <a id="7229" class="Keyword">infix</a>  <a id="7236" class="Number">3</a> <a id="7238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7524" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="7244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin_</a> <a id="7251" class="Symbol">:</a> <a id="7253" class="Symbol">∀</a> <a id="7255" class="Symbol">{</a><a id="7256" href="plfa.part1.Equality.html#7256" class="Bound">x</a> <a id="7258" href="plfa.part1.Equality.html#7258" class="Bound">y</a> <a id="7260" class="Symbol">:</a> <a id="7262" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7263" class="Symbol">}</a>
    <a id="7269" class="Symbol">→</a> <a id="7271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7256" class="Bound">x</a> <a id="7273" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7275" href="plfa.part1.Equality.html#7258" class="Bound">y</a>
      <a id="7283" class="Comment">-----</a>
    <a id="7293" class="Symbol">→</a> <a id="7295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7256" class="Bound">x</a> <a id="7297" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7299" href="plfa.part1.Equality.html#7258" class="Bound">y</a>
  <a id="7303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin</a> <a id="7309" href="plfa.part1.Equality.html#7309" class="Bound">x≡y</a>  <a id="7314" class="Symbol">=</a>  <a id="7317" href="plfa.part1.Equality.html#7309" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="7324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7324" class="Function Operator">_≡⟨⟩_</a> <a id="7330" class="Symbol">:</a> <a id="7332" class="Symbol">∀</a> <a id="7334" class="Symbol">(</a><a id="7335" href="plfa.part1.Equality.html#7335" class="Bound">x</a> <a id="7337" class="Symbol">:</a> <a id="7339" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7340" class="Symbol">)</a> <a id="7342" class="Symbol">{</a><a id="7343" href="plfa.part1.Equality.html#7343" class="Bound">y</a> <a id="7345" class="Symbol">:</a> <a id="7347" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7348" class="Symbol">}</a>
    <a id="7354" class="Symbol">→</a> <a id="7356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7335" class="Bound">x</a> <a id="7358" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7360" href="plfa.part1.Equality.html#7343" class="Bound">y</a>
      <a id="7368" class="Comment">-----</a>
    <a id="7378" class="Symbol">→</a> <a id="7380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7335" class="Bound">x</a> <a id="7382" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7384" href="plfa.part1.Equality.html#7343" class="Bound">y</a>
  <a id="7388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7388" class="Bound">x</a> <a id="7390" href="plfa.part1.Equality.html#7324" class="Function Operator">≡⟨⟩</a> <a id="7394" href="plfa.part1.Equality.html#7394" class="Bound">x≡y</a>  <a id="7399" class="Symbol">=</a>  <a id="7402" href="plfa.part1.Equality.html#7394" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="7409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">_≡⟨_⟩_</a> <a id="7416" class="Symbol">:</a> <a id="7418" class="Symbol">∀</a> <a id="7420" class="Symbol">(</a><a id="7421" href="plfa.part1.Equality.html#7421" class="Bound">x</a> <a id="7423" class="Symbol">:</a> <a id="7425" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7426" class="Symbol">)</a> <a id="7428" class="Symbol">{</a><a id="7429" href="plfa.part1.Equality.html#7429" class="Bound">y</a> <a id="7431" href="plfa.part1.Equality.html#7431" class="Bound">z</a> <a id="7433" class="Symbol">:</a> <a id="7435" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7436" class="Symbol">}</a>
    <a id="7442" class="Symbol">→</a> <a id="7444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7421" class="Bound">x</a> <a id="7446" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7448" href="plfa.part1.Equality.html#7429" class="Bound">y</a>
    <a id="7454" class="Symbol">→</a> <a id="7456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7429" class="Bound">y</a> <a id="7458" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7460" href="plfa.part1.Equality.html#7431" class="Bound">z</a>
      <a id="7468" class="Comment">-----</a>
    <a id="7478" class="Symbol">→</a> <a id="7480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7421" class="Bound">x</a> <a id="7482" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7484" href="plfa.part1.Equality.html#7431" class="Bound">z</a>
  <a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7488" class="Bound">x</a> <a id="7490" href="plfa.part1.Equality.html#7409" class="Function Operator">≡⟨</a> <a id="7493" href="plfa.part1.Equality.html#7493" class="Bound">x≡y</a> <a id="7497" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a> <a id="7499" href="plfa.part1.Equality.html#7499" class="Bound">y≡z</a>  <a id="7504" class="Symbol">=</a>  <a id="7507" href="plfa.part1.Equality.html#5160" class="Function">trans</a> <a id="7513" href="plfa.part1.Equality.html#7493" class="Bound">x≡y</a> <a id="7517" href="plfa.part1.Equality.html#7499" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="7524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7524" class="Function Operator">_∎</a> <a id="7527" class="Symbol">:</a> <a id="7529" class="Symbol">∀</a> <a id="7531" class="Symbol">(</a><a id="7532" href="plfa.part1.Equality.html#7532" class="Bound">x</a> <a id="7534" class="Symbol">:</a> <a id="7536" href="plfa.part1.Equality.html#7169" class="Bound">A</a><a id="7537" class="Symbol">)</a>
      <a id="7545" class="Comment">-----</a>
    <a id="7555" class="Symbol">→</a> <a id="7557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7532" class="Bound">x</a> <a id="7559" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="7561" href="plfa.part1.Equality.html#7532" class="Bound">x</a>
  <a id="7565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7565" class="Bound">x</a> <a id="7567" href="plfa.part1.Equality.html#7524" class="Function Operator">∎</a>  <a id="7570" class="Symbol">=</a>  <a id="7573" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>

<a id="7579" class="Keyword">open</a> <a id="7584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7156" class="Module">≡-Reasoning</a>
</pre>{% endraw %}
{::comment}
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
{:/}

这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。打开（Open）一个模块会把模块内的所有定义导入进当前的环境中。

{::comment}
As an example, let's look at a proof of transitivity
as a chain of equations:
{:/}

举个例子，我们来看看如何用等式串证明传递性：

{% raw %}<pre class="Agda"><a id="trans′"></a><a id="8445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8445" class="Function">trans′</a> <a id="8452" class="Symbol">:</a> <a id="8454" class="Symbol">∀</a> <a id="8456" class="Symbol">{</a><a id="8457" href="plfa.part1.Equality.html#8457" class="Bound">A</a> <a id="8459" class="Symbol">:</a> <a id="8461" class="PrimitiveType">Set</a><a id="8464" class="Symbol">}</a> <a id="8466" class="Symbol">{</a><a id="8467" href="plfa.part1.Equality.html#8467" class="Bound">x</a> <a id="8469" href="plfa.part1.Equality.html#8469" class="Bound">y</a> <a id="8471" href="plfa.part1.Equality.html#8471" class="Bound">z</a> <a id="8473" class="Symbol">:</a> <a id="8475" href="plfa.part1.Equality.html#8457" class="Bound">A</a><a id="8476" class="Symbol">}</a>
  <a id="8480" class="Symbol">→</a> <a id="8482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8467" class="Bound">x</a> <a id="8484" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="8486" href="plfa.part1.Equality.html#8469" class="Bound">y</a>
  <a id="8490" class="Symbol">→</a> <a id="8492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8469" class="Bound">y</a> <a id="8494" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="8496" href="plfa.part1.Equality.html#8471" class="Bound">z</a>
    <a id="8502" class="Comment">-----</a>
  <a id="8510" class="Symbol">→</a> <a id="8512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8467" class="Bound">x</a> <a id="8514" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="8516" href="plfa.part1.Equality.html#8471" class="Bound">z</a>
<a id="8518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8445" class="Function">trans′</a> <a id="8525" class="Symbol">{</a><a id="8526" href="plfa.part1.Equality.html#8526" class="Bound">A</a><a id="8527" class="Symbol">}</a> <a id="8529" class="Symbol">{</a><a id="8530" href="plfa.part1.Equality.html#8530" class="Bound">x</a><a id="8531" class="Symbol">}</a> <a id="8533" class="Symbol">{</a><a id="8534" href="plfa.part1.Equality.html#8534" class="Bound">y</a><a id="8535" class="Symbol">}</a> <a id="8537" class="Symbol">{</a><a id="8538" href="plfa.part1.Equality.html#8538" class="Bound">z</a><a id="8539" class="Symbol">}</a> <a id="8541" href="plfa.part1.Equality.html#8541" class="Bound">x≡y</a> <a id="8545" href="plfa.part1.Equality.html#8545" class="Bound">y≡z</a> <a id="8549" class="Symbol">=</a>
  <a id="8553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin</a>
    <a id="8563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8530" class="Bound">x</a>
  <a id="8567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">≡⟨</a> <a id="8570" href="plfa.part1.Equality.html#8541" class="Bound">x≡y</a> <a id="8574" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a>
    <a id="8580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8534" class="Bound">y</a>
  <a id="8584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">≡⟨</a> <a id="8587" href="plfa.part1.Equality.html#8545" class="Bound">y≡z</a> <a id="8591" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a>
    <a id="8597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8538" class="Bound">z</a>
  <a id="8601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7524" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
According to the fixity declarations, the body parses as follows:
{:/}

根据其定义，等式右边会被解析成如下：

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

{::comment}
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
{:/}

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：

    trans x≡y (trans y≡z refl)

{::comment}
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
{:/}

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。


{::comment}
## Chains of equations, another example
{:/}

## 等式串的另外一个例子

{::comment}
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{:/}

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：

{% raw %}<pre class="Agda"><a id="11008" class="Keyword">data</a> <a id="ℕ"></a><a id="11013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11013" class="Datatype">ℕ</a> <a id="11015" class="Symbol">:</a> <a id="11017" class="PrimitiveType">Set</a> <a id="11021" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="11029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11029" class="InductiveConstructor">zero</a> <a id="11034" class="Symbol">:</a> <a id="11036" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="11040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11040" class="InductiveConstructor">suc</a>  <a id="11045" class="Symbol">:</a> <a id="11047" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a> <a id="11049" class="Symbol">→</a> <a id="11051" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="11054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11054" class="Function Operator">_+_</a> <a id="11058" class="Symbol">:</a> <a id="11060" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a> <a id="11062" class="Symbol">→</a> <a id="11064" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a> <a id="11066" class="Symbol">→</a> <a id="11068" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a>
<a id="11070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11029" class="InductiveConstructor">zero</a>    <a id="11078" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11080" href="plfa.part1.Equality.html#11080" class="Bound">n</a>  <a id="11083" class="Symbol">=</a>  <a id="11086" href="plfa.part1.Equality.html#11080" class="Bound">n</a>
<a id="11088" class="Symbol">(</a><a id="11089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11040" class="InductiveConstructor">suc</a> <a id="11093" href="plfa.part1.Equality.html#11093" class="Bound">m</a><a id="11094" class="Symbol">)</a> <a id="11096" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11098" href="plfa.part1.Equality.html#11098" class="Bound">n</a>  <a id="11101" class="Symbol">=</a>  <a id="11104" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="11108" class="Symbol">(</a><a id="11109" href="plfa.part1.Equality.html#11093" class="Bound">m</a> <a id="11111" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11113" href="plfa.part1.Equality.html#11098" class="Bound">n</a><a id="11114" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
To save space we postulate (rather than prove in full) two lemmas:
{:/}

为了节约空间，我们假设两条引理（而不是证明它们）：

{% raw %}<pre class="Agda"><a id="11237" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="11249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11249" class="Postulate">+-identity</a> <a id="11260" class="Symbol">:</a> <a id="11262" class="Symbol">∀</a> <a id="11264" class="Symbol">(</a><a id="11265" href="plfa.part1.Equality.html#11265" class="Bound">m</a> <a id="11267" class="Symbol">:</a> <a id="11269" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="11270" class="Symbol">)</a> <a id="11272" class="Symbol">→</a> <a id="11274" href="plfa.part1.Equality.html#11265" class="Bound">m</a> <a id="11276" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11278" href="plfa.part1.Equality.html#11029" class="InductiveConstructor">zero</a> <a id="11283" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="11285" href="plfa.part1.Equality.html#11265" class="Bound">m</a>
  <a id="+-suc"></a><a id="11289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11289" class="Postulate">+-suc</a> <a id="11295" class="Symbol">:</a> <a id="11297" class="Symbol">∀</a> <a id="11299" class="Symbol">(</a><a id="11300" href="plfa.part1.Equality.html#11300" class="Bound">m</a> <a id="11302" href="plfa.part1.Equality.html#11302" class="Bound">n</a> <a id="11304" class="Symbol">:</a> <a id="11306" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="11307" class="Symbol">)</a> <a id="11309" class="Symbol">→</a> <a id="11311" href="plfa.part1.Equality.html#11300" class="Bound">m</a> <a id="11313" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11315" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="11319" href="plfa.part1.Equality.html#11302" class="Bound">n</a> <a id="11321" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="11323" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="11327" class="Symbol">(</a><a id="11328" href="plfa.part1.Equality.html#11300" class="Bound">m</a> <a id="11330" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11332" href="plfa.part1.Equality.html#11302" class="Bound">n</a><a id="11333" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
{:/}

这是我们第一次使用*假设*（Postulate）。假设为一个标识符指定一个签名，但是不提供定义。我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，那么我们可以证明出任何东西。

{::comment}
We then repeat the proof of commutativity:
{:/}

我们接下来重复交换律的证明：

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="11846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11846" class="Function">+-comm</a> <a id="11853" class="Symbol">:</a> <a id="11855" class="Symbol">∀</a> <a id="11857" class="Symbol">(</a><a id="11858" href="plfa.part1.Equality.html#11858" class="Bound">m</a> <a id="11860" href="plfa.part1.Equality.html#11860" class="Bound">n</a> <a id="11862" class="Symbol">:</a> <a id="11864" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="11865" class="Symbol">)</a> <a id="11867" class="Symbol">→</a> <a id="11869" href="plfa.part1.Equality.html#11858" class="Bound">m</a> <a id="11871" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11873" href="plfa.part1.Equality.html#11860" class="Bound">n</a> <a id="11875" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="11877" href="plfa.part1.Equality.html#11860" class="Bound">n</a> <a id="11879" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11881" href="plfa.part1.Equality.html#11858" class="Bound">m</a>
<a id="11883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11846" class="Function">+-comm</a> <a id="11890" href="plfa.part1.Equality.html#11890" class="Bound">m</a> <a id="11892" href="plfa.part1.Equality.html#11029" class="InductiveConstructor">zero</a> <a id="11897" class="Symbol">=</a>
  <a id="11901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin</a>
    <a id="11911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11890" class="Bound">m</a> <a id="11913" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11915" href="plfa.part1.Equality.html#11029" class="InductiveConstructor">zero</a>
  <a id="11922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">≡⟨</a> <a id="11925" href="plfa.part1.Equality.html#11249" class="Postulate">+-identity</a> <a id="11936" href="plfa.part1.Equality.html#11890" class="Bound">m</a> <a id="11938" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a>
    <a id="11944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11890" class="Bound">m</a>
  <a id="11948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7324" class="Function Operator">≡⟨⟩</a>
    <a id="11956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11029" class="InductiveConstructor">zero</a> <a id="11961" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="11963" href="plfa.part1.Equality.html#11890" class="Bound">m</a>
  <a id="11967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7524" class="Function Operator">∎</a>
<a id="11969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11846" class="Function">+-comm</a> <a id="11976" href="plfa.part1.Equality.html#11976" class="Bound">m</a> <a id="11978" class="Symbol">(</a><a id="11979" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="11983" href="plfa.part1.Equality.html#11983" class="Bound">n</a><a id="11984" class="Symbol">)</a> <a id="11986" class="Symbol">=</a>
  <a id="11990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7244" class="Function Operator">begin</a>
    <a id="12000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11976" class="Bound">m</a> <a id="12002" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="12004" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="12008" href="plfa.part1.Equality.html#11983" class="Bound">n</a>
  <a id="12012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">≡⟨</a> <a id="12015" href="plfa.part1.Equality.html#11289" class="Postulate">+-suc</a> <a id="12021" href="plfa.part1.Equality.html#11976" class="Bound">m</a> <a id="12023" href="plfa.part1.Equality.html#11983" class="Bound">n</a> <a id="12025" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a>
    <a id="12031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11040" class="InductiveConstructor">suc</a> <a id="12035" class="Symbol">(</a><a id="12036" href="plfa.part1.Equality.html#11976" class="Bound">m</a> <a id="12038" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="12040" href="plfa.part1.Equality.html#11983" class="Bound">n</a><a id="12041" class="Symbol">)</a>
  <a id="12045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7409" class="Function Operator">≡⟨</a> <a id="12048" href="plfa.part1.Equality.html#5760" class="Function">cong</a> <a id="12053" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="12057" class="Symbol">(</a><a id="12058" href="plfa.part1.Equality.html#11846" class="Function">+-comm</a> <a id="12065" href="plfa.part1.Equality.html#11976" class="Bound">m</a> <a id="12067" href="plfa.part1.Equality.html#11983" class="Bound">n</a><a id="12068" class="Symbol">)</a> <a id="12070" href="plfa.part1.Equality.html#7409" class="Function Operator">⟩</a>
    <a id="12076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11040" class="InductiveConstructor">suc</a> <a id="12080" class="Symbol">(</a><a id="12081" href="plfa.part1.Equality.html#11983" class="Bound">n</a> <a id="12083" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="12085" href="plfa.part1.Equality.html#11976" class="Bound">m</a><a id="12086" class="Symbol">)</a>
  <a id="12090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7324" class="Function Operator">≡⟨⟩</a>
    <a id="12098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11040" class="InductiveConstructor">suc</a> <a id="12102" href="plfa.part1.Equality.html#11983" class="Bound">n</a> <a id="12104" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="12106" href="plfa.part1.Equality.html#11976" class="Bound">m</a>
  <a id="12110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#7524" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
{:/}

论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。

{::comment}
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
{:/}

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出

      suc (n + m)
    ≡⟨⟩
      suc n + m

{::comment}
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
{:/}

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出

      suc n + m
    ≡⟨⟩
      suc (n + m)

{::comment}
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
{:/}

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。而书写的顺序合不合理则是由我们自行决定。


{::comment}
#### Exercise `≤-Reasoning` (stretch)
{:/}

#### 练习 `≤-Reasoning` (延伸)

{::comment}
The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.
{:/}

[Relations]({{ site.baseurl }}/Relations/) 章节中的单调性证明亦可以用相似于 `≡-Reasoning` 的，更易于理解的形式给出。相似地来定义 `≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤`、`+-monoʳ-≤`
和 `+-mono-≤`。

{::comment}
{% raw %}<pre class="Agda"><a id="13715" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="13752" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Rewriting
{:/}

## 重写

{::comment}
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{:/}

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：

{% raw %}<pre class="Agda"><a id="13960" class="Keyword">data</a> <a id="even"></a><a id="13965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="13970" class="Symbol">:</a> <a id="13972" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a> <a id="13974" class="Symbol">→</a> <a id="13976" class="PrimitiveType">Set</a>
<a id="13980" class="Keyword">data</a> <a id="odd"></a><a id="13985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13985" class="Datatype">odd</a>  <a id="13990" class="Symbol">:</a> <a id="13992" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a> <a id="13994" class="Symbol">→</a> <a id="13996" class="PrimitiveType">Set</a>

<a id="14001" class="Keyword">data</a> <a id="14006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="14011" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="14020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14020" class="InductiveConstructor">even-zero</a> <a id="14030" class="Symbol">:</a> <a id="14032" href="plfa.part1.Equality.html#13965" class="Datatype">even</a> <a id="14037" href="plfa.part1.Equality.html#11029" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="14045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14045" class="InductiveConstructor">even-suc</a> <a id="14054" class="Symbol">:</a> <a id="14056" class="Symbol">∀</a> <a id="14058" class="Symbol">{</a><a id="14059" href="plfa.part1.Equality.html#14059" class="Bound">n</a> <a id="14061" class="Symbol">:</a> <a id="14063" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="14064" class="Symbol">}</a>
    <a id="14070" class="Symbol">→</a> <a id="14072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13985" class="Datatype">odd</a> <a id="14076" href="plfa.part1.Equality.html#14059" class="Bound">n</a>
      <a id="14084" class="Comment">------------</a>
    <a id="14101" class="Symbol">→</a> <a id="14103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="14108" class="Symbol">(</a><a id="14109" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="14113" href="plfa.part1.Equality.html#14059" class="Bound">n</a><a id="14114" class="Symbol">)</a>

<a id="14117" class="Keyword">data</a> <a id="14122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13985" class="Datatype">odd</a> <a id="14126" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14134" class="InductiveConstructor">odd-suc</a> <a id="14142" class="Symbol">:</a> <a id="14144" class="Symbol">∀</a> <a id="14146" class="Symbol">{</a><a id="14147" href="plfa.part1.Equality.html#14147" class="Bound">n</a> <a id="14149" class="Symbol">:</a> <a id="14151" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="14152" class="Symbol">}</a>
    <a id="14158" class="Symbol">→</a> <a id="14160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="14165" href="plfa.part1.Equality.html#14147" class="Bound">n</a>
      <a id="14173" class="Comment">-----------</a>
    <a id="14189" class="Symbol">→</a> <a id="14191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13985" class="Datatype">odd</a> <a id="14195" class="Symbol">(</a><a id="14196" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="14200" href="plfa.part1.Equality.html#14147" class="Bound">n</a><a id="14201" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
{:/}

在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。

{::comment}
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{:/}

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，我们只用编译程序指令来告诉 Agda 什么类型对应相等性：

{% raw %}<pre class="Agda"><a id="14796" class="Symbol">{-#</a> <a id="14800" class="Keyword">BUILTIN</a> <a id="14808" class="Pragma">EQUALITY</a> <a id="14817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1059" class="Datatype Operator">_≡_</a> <a id="14821" class="Symbol">#-}</a>
</pre>{% endraw %}
{::comment}
We can then prove the desired property as follows:
{:/}

我们然后就可以如下证明求证的性质：

{% raw %}<pre class="Agda"><a id="even-comm"></a><a id="14922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14922" class="Function">even-comm</a> <a id="14932" class="Symbol">:</a> <a id="14934" class="Symbol">∀</a> <a id="14936" class="Symbol">(</a><a id="14937" href="plfa.part1.Equality.html#14937" class="Bound">m</a> <a id="14939" href="plfa.part1.Equality.html#14939" class="Bound">n</a> <a id="14941" class="Symbol">:</a> <a id="14943" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="14944" class="Symbol">)</a>
  <a id="14948" class="Symbol">→</a> <a id="14950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="14955" class="Symbol">(</a><a id="14956" href="plfa.part1.Equality.html#14937" class="Bound">m</a> <a id="14958" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="14960" href="plfa.part1.Equality.html#14939" class="Bound">n</a><a id="14961" class="Symbol">)</a>
    <a id="14967" class="Comment">------------</a>
  <a id="14982" class="Symbol">→</a> <a id="14984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="14989" class="Symbol">(</a><a id="14990" href="plfa.part1.Equality.html#14939" class="Bound">n</a> <a id="14992" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="14994" href="plfa.part1.Equality.html#14937" class="Bound">m</a><a id="14995" class="Symbol">)</a>
<a id="14997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14922" class="Function">even-comm</a> <a id="15007" href="plfa.part1.Equality.html#15007" class="Bound">m</a> <a id="15009" href="plfa.part1.Equality.html#15009" class="Bound">n</a> <a id="15011" href="plfa.part1.Equality.html#15011" class="Bound">ev</a>  <a id="15015" class="Keyword">rewrite</a> <a id="15023" href="plfa.part1.Equality.html#11846" class="Function">+-comm</a> <a id="15030" href="plfa.part1.Equality.html#15009" class="Bound">n</a> <a id="15032" href="plfa.part1.Equality.html#15007" class="Bound">m</a>  <a id="15035" class="Symbol">=</a>  <a id="15038" href="plfa.part1.Equality.html#15011" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
{:/}

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

{::comment}
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
{:/}

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
Now we add the rewrite:
{:/}

现在我们加入重写：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
{:/}

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。


{::comment}
## Multiple rewrites
{:/}

## 多重重写

{::comment}
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{:/}

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：

{% raw %}<pre class="Agda"><a id="+-comm′"></a><a id="17259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17259" class="Function">+-comm′</a> <a id="17267" class="Symbol">:</a> <a id="17269" class="Symbol">∀</a> <a id="17271" class="Symbol">(</a><a id="17272" href="plfa.part1.Equality.html#17272" class="Bound">m</a> <a id="17274" href="plfa.part1.Equality.html#17274" class="Bound">n</a> <a id="17276" class="Symbol">:</a> <a id="17278" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="17279" class="Symbol">)</a> <a id="17281" class="Symbol">→</a> <a id="17283" href="plfa.part1.Equality.html#17272" class="Bound">m</a> <a id="17285" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="17287" href="plfa.part1.Equality.html#17274" class="Bound">n</a> <a id="17289" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="17291" href="plfa.part1.Equality.html#17274" class="Bound">n</a> <a id="17293" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="17295" href="plfa.part1.Equality.html#17272" class="Bound">m</a>
<a id="17297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17259" class="Function">+-comm′</a> <a id="17305" href="plfa.part1.Equality.html#11029" class="InductiveConstructor">zero</a>    <a id="17313" href="plfa.part1.Equality.html#17313" class="Bound">n</a>  <a id="17316" class="Keyword">rewrite</a> <a id="17324" href="plfa.part1.Equality.html#11249" class="Postulate">+-identity</a> <a id="17335" href="plfa.part1.Equality.html#17313" class="Bound">n</a>             <a id="17349" class="Symbol">=</a>  <a id="17352" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
<a id="17357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17259" class="Function">+-comm′</a> <a id="17365" class="Symbol">(</a><a id="17366" href="plfa.part1.Equality.html#11040" class="InductiveConstructor">suc</a> <a id="17370" href="plfa.part1.Equality.html#17370" class="Bound">m</a><a id="17371" class="Symbol">)</a> <a id="17373" href="plfa.part1.Equality.html#17373" class="Bound">n</a>  <a id="17376" class="Keyword">rewrite</a> <a id="17384" href="plfa.part1.Equality.html#11289" class="Postulate">+-suc</a> <a id="17390" href="plfa.part1.Equality.html#17373" class="Bound">n</a> <a id="17392" href="plfa.part1.Equality.html#17370" class="Bound">m</a> <a id="17394" class="Symbol">|</a> <a id="17396" href="plfa.part1.Equality.html#17259" class="Function">+-comm′</a> <a id="17404" href="plfa.part1.Equality.html#17370" class="Bound">m</a> <a id="17406" href="plfa.part1.Equality.html#17373" class="Bound">n</a>  <a id="17409" class="Symbol">=</a>  <a id="17412" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
{:/}

这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将合同性考虑在其中。尽管使用重写的证明更加的简短，使用等式串的证明能容易理解，我们将尽可能的使用后者。


{::comment}
## Rewriting expanded
{:/}

## 深入重写

{::comment}
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{:/}

`rewrite` 记法实际上是 `with` 抽象的一种应用：

{% raw %}<pre class="Agda"><a id="even-comm′"></a><a id="18200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18200" class="Function">even-comm′</a> <a id="18211" class="Symbol">:</a> <a id="18213" class="Symbol">∀</a> <a id="18215" class="Symbol">(</a><a id="18216" href="plfa.part1.Equality.html#18216" class="Bound">m</a> <a id="18218" href="plfa.part1.Equality.html#18218" class="Bound">n</a> <a id="18220" class="Symbol">:</a> <a id="18222" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="18223" class="Symbol">)</a>
  <a id="18227" class="Symbol">→</a> <a id="18229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="18234" class="Symbol">(</a><a id="18235" href="plfa.part1.Equality.html#18216" class="Bound">m</a> <a id="18237" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="18239" href="plfa.part1.Equality.html#18218" class="Bound">n</a><a id="18240" class="Symbol">)</a>
    <a id="18246" class="Comment">------------</a>
  <a id="18261" class="Symbol">→</a> <a id="18263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="18268" class="Symbol">(</a><a id="18269" href="plfa.part1.Equality.html#18218" class="Bound">n</a> <a id="18271" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="18273" href="plfa.part1.Equality.html#18216" class="Bound">m</a><a id="18274" class="Symbol">)</a>
<a id="18276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18200" class="Function">even-comm′</a> <a id="18287" href="plfa.part1.Equality.html#18287" class="Bound">m</a> <a id="18289" href="plfa.part1.Equality.html#18289" class="Bound">n</a> <a id="18291" href="plfa.part1.Equality.html#18291" class="Bound">ev</a> <a id="18294" class="Keyword">with</a>   <a id="18301" href="plfa.part1.Equality.html#18287" class="Bound">m</a> <a id="18303" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="18305" href="plfa.part1.Equality.html#18289" class="Bound">n</a>  <a id="18308" class="Symbol">|</a> <a id="18310" href="plfa.part1.Equality.html#11846" class="Function">+-comm</a> <a id="18317" href="plfa.part1.Equality.html#18287" class="Bound">m</a> <a id="18319" href="plfa.part1.Equality.html#18289" class="Bound">n</a>
<a id="18321" class="Symbol">...</a>                  <a id="18342" class="Symbol">|</a> <a id="18344" class="DottedPattern Symbol">.(</a><a id="18346" class="DottedPattern Bound">n</a> <a id="18348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#11054" class="DottedPattern Function Operator">+</a> <a id="18350" class="DottedPattern Bound">m</a><a id="18351" class="DottedPattern Symbol">)</a> <a id="18353" class="Symbol">|</a> <a id="18355" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>       <a id="18366" class="Symbol">=</a> <a id="18368" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
{:/}

总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。注意在这里使用的*点模式*（Dot Pattern），`.(n + m)`。点模式由一个点和一个表达式组成，在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴涵了需要的信息。但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）

{::comment}
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{:/}

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：

{% raw %}<pre class="Agda"><a id="even-comm″"></a><a id="19937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#19937" class="Function">even-comm″</a> <a id="19948" class="Symbol">:</a> <a id="19950" class="Symbol">∀</a> <a id="19952" class="Symbol">(</a><a id="19953" href="plfa.part1.Equality.html#19953" class="Bound">m</a> <a id="19955" href="plfa.part1.Equality.html#19955" class="Bound">n</a> <a id="19957" class="Symbol">:</a> <a id="19959" href="plfa.part1.Equality.html#11013" class="Datatype">ℕ</a><a id="19960" class="Symbol">)</a>
  <a id="19964" class="Symbol">→</a> <a id="19966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="19971" class="Symbol">(</a><a id="19972" href="plfa.part1.Equality.html#19953" class="Bound">m</a> <a id="19974" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="19976" href="plfa.part1.Equality.html#19955" class="Bound">n</a><a id="19977" class="Symbol">)</a>
    <a id="19983" class="Comment">------------</a>
  <a id="19998" class="Symbol">→</a> <a id="20000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13965" class="Datatype">even</a> <a id="20005" class="Symbol">(</a><a id="20006" href="plfa.part1.Equality.html#19955" class="Bound">n</a> <a id="20008" href="plfa.part1.Equality.html#11054" class="Function Operator">+</a> <a id="20010" href="plfa.part1.Equality.html#19953" class="Bound">m</a><a id="20011" class="Symbol">)</a>
<a id="20013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#19937" class="Function">even-comm″</a> <a id="20024" href="plfa.part1.Equality.html#20024" class="Bound">m</a> <a id="20026" href="plfa.part1.Equality.html#20026" class="Bound">n</a>  <a id="20029" class="Symbol">=</a>  <a id="20032" href="plfa.part1.Equality.html#6678" class="Function">subst</a> <a id="20038" href="plfa.part1.Equality.html#13965" class="Datatype">even</a> <a id="20043" class="Symbol">(</a><a id="20044" href="plfa.part1.Equality.html#11846" class="Function">+-comm</a> <a id="20051" href="plfa.part1.Equality.html#20024" class="Bound">m</a> <a id="20053" href="plfa.part1.Equality.html#20026" class="Bound">n</a><a id="20054" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
{:/}

尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。


{::comment}
## Leibniz equality
{:/}

## 莱布尼兹（Leibniz）相等性

{::comment}
The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.
{:/}

我们使用的相等性断言的形式源于 Martin Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，于 1686 年发表。莱布尼兹断言的相等性表示*不可分辨的实体*（Identity of Indiscernibles）：两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），与史波克定律紧密相关：“一个不造成区别的区别不是区别”。我们在这里定义莱布尼兹相等性，并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin Löf 相等性。

{::comment}
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
{:/}

莱布尼兹不等式一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。

{::comment}
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{:/}

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，我们有 `P x` 蕴涵了 `P y`：

{% raw %}<pre class="Agda"><a id="_≐_"></a><a id="21797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21797" class="Function Operator">_≐_</a> <a id="21801" class="Symbol">:</a> <a id="21803" class="Symbol">∀</a> <a id="21805" class="Symbol">{</a><a id="21806" href="plfa.part1.Equality.html#21806" class="Bound">A</a> <a id="21808" class="Symbol">:</a> <a id="21810" class="PrimitiveType">Set</a><a id="21813" class="Symbol">}</a> <a id="21815" class="Symbol">(</a><a id="21816" href="plfa.part1.Equality.html#21816" class="Bound">x</a> <a id="21818" href="plfa.part1.Equality.html#21818" class="Bound">y</a> <a id="21820" class="Symbol">:</a> <a id="21822" href="plfa.part1.Equality.html#21806" class="Bound">A</a><a id="21823" class="Symbol">)</a> <a id="21825" class="Symbol">→</a> <a id="21827" class="PrimitiveType">Set₁</a>
<a id="21832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21797" class="Function Operator">_≐_</a> <a id="21836" class="Symbol">{</a><a id="21837" href="plfa.part1.Equality.html#21837" class="Bound">A</a><a id="21838" class="Symbol">}</a> <a id="21840" href="plfa.part1.Equality.html#21840" class="Bound">x</a> <a id="21842" href="plfa.part1.Equality.html#21842" class="Bound">y</a> <a id="21844" class="Symbol">=</a> <a id="21846" class="Symbol">∀</a> <a id="21848" class="Symbol">(</a><a id="21849" href="plfa.part1.Equality.html#21849" class="Bound">P</a> <a id="21851" class="Symbol">:</a> <a id="21853" href="plfa.part1.Equality.html#21837" class="Bound">A</a> <a id="21855" class="Symbol">→</a> <a id="21857" class="PrimitiveType">Set</a><a id="21860" class="Symbol">)</a> <a id="21862" class="Symbol">→</a> <a id="21864" href="plfa.part1.Equality.html#21849" class="Bound">P</a> <a id="21866" href="plfa.part1.Equality.html#21840" class="Bound">x</a> <a id="21868" class="Symbol">→</a> <a id="21870" href="plfa.part1.Equality.html#21849" class="Bound">P</a> <a id="21872" href="plfa.part1.Equality.html#21842" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
{:/}

我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。

{::comment}
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
{:/}

这是我们第一次使用*等级*（Levels）。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。

{::comment}
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{:/}

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：

{% raw %}<pre class="Agda"><a id="refl-≐"></a><a id="23096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23096" class="Function">refl-≐</a> <a id="23103" class="Symbol">:</a> <a id="23105" class="Symbol">∀</a> <a id="23107" class="Symbol">{</a><a id="23108" href="plfa.part1.Equality.html#23108" class="Bound">A</a> <a id="23110" class="Symbol">:</a> <a id="23112" class="PrimitiveType">Set</a><a id="23115" class="Symbol">}</a> <a id="23117" class="Symbol">{</a><a id="23118" href="plfa.part1.Equality.html#23118" class="Bound">x</a> <a id="23120" class="Symbol">:</a> <a id="23122" href="plfa.part1.Equality.html#23108" class="Bound">A</a><a id="23123" class="Symbol">}</a>
  <a id="23127" class="Symbol">→</a> <a id="23129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23118" class="Bound">x</a> <a id="23131" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23133" href="plfa.part1.Equality.html#23118" class="Bound">x</a>
<a id="23135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23096" class="Function">refl-≐</a> <a id="23142" href="plfa.part1.Equality.html#23142" class="Bound">P</a> <a id="23144" href="plfa.part1.Equality.html#23144" class="Bound">Px</a>  <a id="23148" class="Symbol">=</a>  <a id="23151" href="plfa.part1.Equality.html#23144" class="Bound">Px</a>

<a id="trans-≐"></a><a id="23155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23155" class="Function">trans-≐</a> <a id="23163" class="Symbol">:</a> <a id="23165" class="Symbol">∀</a> <a id="23167" class="Symbol">{</a><a id="23168" href="plfa.part1.Equality.html#23168" class="Bound">A</a> <a id="23170" class="Symbol">:</a> <a id="23172" class="PrimitiveType">Set</a><a id="23175" class="Symbol">}</a> <a id="23177" class="Symbol">{</a><a id="23178" href="plfa.part1.Equality.html#23178" class="Bound">x</a> <a id="23180" href="plfa.part1.Equality.html#23180" class="Bound">y</a> <a id="23182" href="plfa.part1.Equality.html#23182" class="Bound">z</a> <a id="23184" class="Symbol">:</a> <a id="23186" href="plfa.part1.Equality.html#23168" class="Bound">A</a><a id="23187" class="Symbol">}</a>
  <a id="23191" class="Symbol">→</a> <a id="23193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23178" class="Bound">x</a> <a id="23195" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23197" href="plfa.part1.Equality.html#23180" class="Bound">y</a>
  <a id="23201" class="Symbol">→</a> <a id="23203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23180" class="Bound">y</a> <a id="23205" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23207" href="plfa.part1.Equality.html#23182" class="Bound">z</a>
    <a id="23213" class="Comment">-----</a>
  <a id="23221" class="Symbol">→</a> <a id="23223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23178" class="Bound">x</a> <a id="23225" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23227" href="plfa.part1.Equality.html#23182" class="Bound">z</a>
<a id="23229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23155" class="Function">trans-≐</a> <a id="23237" href="plfa.part1.Equality.html#23237" class="Bound">x≐y</a> <a id="23241" href="plfa.part1.Equality.html#23241" class="Bound">y≐z</a> <a id="23245" href="plfa.part1.Equality.html#23245" class="Bound">P</a> <a id="23247" href="plfa.part1.Equality.html#23247" class="Bound">Px</a>  <a id="23251" class="Symbol">=</a>  <a id="23254" href="plfa.part1.Equality.html#23241" class="Bound">y≐z</a> <a id="23258" href="plfa.part1.Equality.html#23245" class="Bound">P</a> <a id="23260" class="Symbol">(</a><a id="23261" href="plfa.part1.Equality.html#23237" class="Bound">x≐y</a> <a id="23265" href="plfa.part1.Equality.html#23245" class="Bound">P</a> <a id="23267" href="plfa.part1.Equality.html#23247" class="Bound">Px</a><a id="23269" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{:/}

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴涵 `P y`，那么反方向的蕴涵也成立。

{% raw %}<pre class="Agda"><a id="sym-≐"></a><a id="23510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23510" class="Function">sym-≐</a> <a id="23516" class="Symbol">:</a> <a id="23518" class="Symbol">∀</a> <a id="23520" class="Symbol">{</a><a id="23521" href="plfa.part1.Equality.html#23521" class="Bound">A</a> <a id="23523" class="Symbol">:</a> <a id="23525" class="PrimitiveType">Set</a><a id="23528" class="Symbol">}</a> <a id="23530" class="Symbol">{</a><a id="23531" href="plfa.part1.Equality.html#23531" class="Bound">x</a> <a id="23533" href="plfa.part1.Equality.html#23533" class="Bound">y</a> <a id="23535" class="Symbol">:</a> <a id="23537" href="plfa.part1.Equality.html#23521" class="Bound">A</a><a id="23538" class="Symbol">}</a>
  <a id="23542" class="Symbol">→</a> <a id="23544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23531" class="Bound">x</a> <a id="23546" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23548" href="plfa.part1.Equality.html#23533" class="Bound">y</a>
    <a id="23554" class="Comment">-----</a>
  <a id="23562" class="Symbol">→</a> <a id="23564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23533" class="Bound">y</a> <a id="23566" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="23568" href="plfa.part1.Equality.html#23531" class="Bound">x</a>
<a id="23570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23510" class="Function">sym-≐</a> <a id="23576" class="Symbol">{</a><a id="23577" href="plfa.part1.Equality.html#23577" class="Bound">A</a><a id="23578" class="Symbol">}</a> <a id="23580" class="Symbol">{</a><a id="23581" href="plfa.part1.Equality.html#23581" class="Bound">x</a><a id="23582" class="Symbol">}</a> <a id="23584" class="Symbol">{</a><a id="23585" href="plfa.part1.Equality.html#23585" class="Bound">y</a><a id="23586" class="Symbol">}</a> <a id="23588" href="plfa.part1.Equality.html#23588" class="Bound">x≐y</a> <a id="23592" href="plfa.part1.Equality.html#23592" class="Bound">P</a>  <a id="23595" class="Symbol">=</a>  <a id="23598" href="plfa.part1.Equality.html#23680" class="Function">Qy</a>
  <a id="23603" class="Keyword">where</a>
    <a id="23613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23613" class="Function">Q</a> <a id="23615" class="Symbol">:</a> <a id="23617" href="plfa.part1.Equality.html#23577" class="Bound">A</a> <a id="23619" class="Symbol">→</a> <a id="23621" class="PrimitiveType">Set</a>
    <a id="23629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23613" class="Function">Q</a> <a id="23631" href="plfa.part1.Equality.html#23631" class="Bound">z</a> <a id="23633" class="Symbol">=</a> <a id="23635" href="plfa.part1.Equality.html#23592" class="Bound">P</a> <a id="23637" href="plfa.part1.Equality.html#23631" class="Bound">z</a> <a id="23639" class="Symbol">→</a> <a id="23641" href="plfa.part1.Equality.html#23592" class="Bound">P</a> <a id="23643" href="plfa.part1.Equality.html#23581" class="Bound">x</a>
    <a id="23649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23649" class="Function">Qx</a> <a id="23652" class="Symbol">:</a> <a id="23654" href="plfa.part1.Equality.html#23613" class="Function">Q</a> <a id="23656" href="plfa.part1.Equality.html#23581" class="Bound">x</a>
    <a id="23662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23649" class="Function">Qx</a> <a id="23665" class="Symbol">=</a> <a id="23667" href="plfa.part1.Equality.html#23096" class="Function">refl-≐</a> <a id="23674" href="plfa.part1.Equality.html#23592" class="Bound">P</a>
    <a id="23680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23680" class="Function">Qy</a> <a id="23683" class="Symbol">:</a> <a id="23685" href="plfa.part1.Equality.html#23613" class="Function">Q</a> <a id="23687" href="plfa.part1.Equality.html#23585" class="Bound">y</a>
    <a id="23693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#23680" class="Function">Qy</a> <a id="23696" class="Symbol">=</a> <a id="23698" href="plfa.part1.Equality.html#23588" class="Bound">x≐y</a> <a id="23702" href="plfa.part1.Equality.html#23613" class="Function">Q</a> <a id="23704" href="plfa.part1.Equality.html#23649" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.
{:/}

给定 `x ≐ y` 和一个特定的 `P`，我们需要构造一个 `P y` 蕴涵 `P x` 的证明。我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴涵 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，由此通过 `x ≐ y` 就能推出 `Q y` 成立。而 `Q y`
正是我们需要的证明，即 `P y` 蕴涵 `P x`。

{::comment}
We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{:/}

我们现在来证明 Martin Löf 相等性蕴涵了莱布尼兹相等性，以及其逆命题。在正方向上，如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。

{% raw %}<pre class="Agda"><a id="≡-implies-≐"></a><a id="24753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#24753" class="Function">≡-implies-≐</a> <a id="24765" class="Symbol">:</a> <a id="24767" class="Symbol">∀</a> <a id="24769" class="Symbol">{</a><a id="24770" href="plfa.part1.Equality.html#24770" class="Bound">A</a> <a id="24772" class="Symbol">:</a> <a id="24774" class="PrimitiveType">Set</a><a id="24777" class="Symbol">}</a> <a id="24779" class="Symbol">{</a><a id="24780" href="plfa.part1.Equality.html#24780" class="Bound">x</a> <a id="24782" href="plfa.part1.Equality.html#24782" class="Bound">y</a> <a id="24784" class="Symbol">:</a> <a id="24786" href="plfa.part1.Equality.html#24770" class="Bound">A</a><a id="24787" class="Symbol">}</a>
  <a id="24791" class="Symbol">→</a> <a id="24793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#24780" class="Bound">x</a> <a id="24795" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="24797" href="plfa.part1.Equality.html#24782" class="Bound">y</a>
    <a id="24803" class="Comment">-----</a>
  <a id="24811" class="Symbol">→</a> <a id="24813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#24780" class="Bound">x</a> <a id="24815" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="24817" href="plfa.part1.Equality.html#24782" class="Bound">y</a>
<a id="24819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#24753" class="Function">≡-implies-≐</a> <a id="24831" href="plfa.part1.Equality.html#24831" class="Bound">x≡y</a> <a id="24835" href="plfa.part1.Equality.html#24835" class="Bound">P</a>  <a id="24838" class="Symbol">=</a>  <a id="24841" href="plfa.part1.Equality.html#6678" class="Function">subst</a> <a id="24847" href="plfa.part1.Equality.html#24835" class="Bound">P</a> <a id="24849" href="plfa.part1.Equality.html#24831" class="Bound">x≡y</a>
</pre>{% endraw %}
{::comment}
This direction follows from substitution, which we showed earlier.
{:/}

因为这个方向由替换性可以得来，如之前证明的那样。

{::comment}
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{:/}

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，我们需要证明 `x ≡ y`：

{% raw %}<pre class="Agda"><a id="≐-implies-≡"></a><a id="25180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25180" class="Function">≐-implies-≡</a> <a id="25192" class="Symbol">:</a> <a id="25194" class="Symbol">∀</a> <a id="25196" class="Symbol">{</a><a id="25197" href="plfa.part1.Equality.html#25197" class="Bound">A</a> <a id="25199" class="Symbol">:</a> <a id="25201" class="PrimitiveType">Set</a><a id="25204" class="Symbol">}</a> <a id="25206" class="Symbol">{</a><a id="25207" href="plfa.part1.Equality.html#25207" class="Bound">x</a> <a id="25209" href="plfa.part1.Equality.html#25209" class="Bound">y</a> <a id="25211" class="Symbol">:</a> <a id="25213" href="plfa.part1.Equality.html#25197" class="Bound">A</a><a id="25214" class="Symbol">}</a>
  <a id="25218" class="Symbol">→</a> <a id="25220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25207" class="Bound">x</a> <a id="25222" href="plfa.part1.Equality.html#21797" class="Function Operator">≐</a> <a id="25224" href="plfa.part1.Equality.html#25209" class="Bound">y</a>
    <a id="25230" class="Comment">-----</a>
  <a id="25238" class="Symbol">→</a> <a id="25240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25207" class="Bound">x</a> <a id="25242" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="25244" href="plfa.part1.Equality.html#25209" class="Bound">y</a>
<a id="25246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25180" class="Function">≐-implies-≡</a> <a id="25258" class="Symbol">{</a><a id="25259" href="plfa.part1.Equality.html#25259" class="Bound">A</a><a id="25260" class="Symbol">}</a> <a id="25262" class="Symbol">{</a><a id="25263" href="plfa.part1.Equality.html#25263" class="Bound">x</a><a id="25264" class="Symbol">}</a> <a id="25266" class="Symbol">{</a><a id="25267" href="plfa.part1.Equality.html#25267" class="Bound">y</a><a id="25268" class="Symbol">}</a> <a id="25270" href="plfa.part1.Equality.html#25270" class="Bound">x≐y</a>  <a id="25275" class="Symbol">=</a>  <a id="25278" href="plfa.part1.Equality.html#25352" class="Function">Qy</a>
  <a id="25283" class="Keyword">where</a>
    <a id="25293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25293" class="Function">Q</a> <a id="25295" class="Symbol">:</a> <a id="25297" href="plfa.part1.Equality.html#25259" class="Bound">A</a> <a id="25299" class="Symbol">→</a> <a id="25301" class="PrimitiveType">Set</a>
    <a id="25309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25293" class="Function">Q</a> <a id="25311" href="plfa.part1.Equality.html#25311" class="Bound">z</a> <a id="25313" class="Symbol">=</a> <a id="25315" href="plfa.part1.Equality.html#25263" class="Bound">x</a> <a id="25317" href="plfa.part1.Equality.html#1059" class="Datatype Operator">≡</a> <a id="25319" href="plfa.part1.Equality.html#25311" class="Bound">z</a>
    <a id="25325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25325" class="Function">Qx</a> <a id="25328" class="Symbol">:</a> <a id="25330" href="plfa.part1.Equality.html#25293" class="Function">Q</a> <a id="25332" href="plfa.part1.Equality.html#25263" class="Bound">x</a>
    <a id="25338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25325" class="Function">Qx</a> <a id="25341" class="Symbol">=</a> <a id="25343" href="plfa.part1.Equality.html#1099" class="InductiveConstructor">refl</a>
    <a id="25352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25352" class="Function">Qy</a> <a id="25355" class="Symbol">:</a> <a id="25357" href="plfa.part1.Equality.html#25293" class="Function">Q</a> <a id="25359" href="plfa.part1.Equality.html#25267" class="Bound">y</a>
    <a id="25365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#25352" class="Function">Qy</a> <a id="25368" class="Symbol">=</a> <a id="25370" href="plfa.part1.Equality.html#25270" class="Bound">x≐y</a> <a id="25374" href="plfa.part1.Equality.html#25293" class="Function">Q</a> <a id="25376" href="plfa.part1.Equality.html#25325" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
{:/}

此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。

{::comment}
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
{:/}

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，草稿，2017）


{::comment}
## Universe polymorphism {#unipoly}
{:/}

## 全体多态 {#unipoly}

{::comment}
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
{:/}

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？

{::comment}
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{:/}

答案是*全体多态*（Universe Polymorphism），一个定义可以根据任何等级 `ℓ` 来做出。为了使用等级，我们首先导入下列内容：

{% raw %}<pre class="Agda"><a id="27255" class="Keyword">open</a> <a id="27260" class="Keyword">import</a> <a id="27267" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="27273" class="Keyword">using</a> <a id="27279" class="Symbol">(</a><a id="27280" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="27285" class="Symbol">;</a> <a id="27287" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="27290" class="Symbol">)</a> <a id="27292" class="Keyword">renaming</a> <a id="27301" class="Symbol">(</a><a id="27302" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="27307" class="Symbol">to</a> <a id="27310" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="27315" class="Symbol">;</a> <a id="27317" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="27321" class="Symbol">to</a> <a id="27324" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="27328" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
{:/}

我们将构造子 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。

{::comment}
Levels are isomorphic to natural numbers, and have similar constructors:
{:/}

等级与自然数是同构的，有相似的构造子：

    lzero : Level
    lsuc  : Level → Level

{::comment}
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
{:/}

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

{::comment}
and so on. There is also an operator
{:/}

以此类推。我们还有一个运算符：

    _⊔_ : Level → Level → Level

{::comment}
that given two levels returns the larger of the two.
{:/}

给定两个等级，返回两者中较大的那个。

{::comment}
Here is the definition of equality, generalised to an arbitrary level:
{:/}

下面是相等性的定义，推广到任意等级：

{% raw %}<pre class="Agda"><a id="28174" class="Keyword">data</a> <a id="_≡′_"></a><a id="28179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28179" class="Datatype Operator">_≡′_</a> <a id="28184" class="Symbol">{</a><a id="28185" href="plfa.part1.Equality.html#28185" class="Bound">ℓ</a> <a id="28187" class="Symbol">:</a> <a id="28189" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28194" class="Symbol">}</a> <a id="28196" class="Symbol">{</a><a id="28197" href="plfa.part1.Equality.html#28197" class="Bound">A</a> <a id="28199" class="Symbol">:</a> <a id="28201" class="PrimitiveType">Set</a> <a id="28205" href="plfa.part1.Equality.html#28185" class="Bound">ℓ</a><a id="28206" class="Symbol">}</a> <a id="28208" class="Symbol">(</a><a id="28209" href="plfa.part1.Equality.html#28209" class="Bound">x</a> <a id="28211" class="Symbol">:</a> <a id="28213" href="plfa.part1.Equality.html#28197" class="Bound">A</a><a id="28214" class="Symbol">)</a> <a id="28216" class="Symbol">:</a> <a id="28218" href="plfa.part1.Equality.html#28197" class="Bound">A</a> <a id="28220" class="Symbol">→</a> <a id="28222" class="PrimitiveType">Set</a> <a id="28226" href="plfa.part1.Equality.html#28185" class="Bound">ℓ</a> <a id="28228" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="28236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28236" class="InductiveConstructor">refl′</a> <a id="28242" class="Symbol">:</a> <a id="28244" href="plfa.part1.Equality.html#28209" class="Bound">x</a> <a id="28246" href="plfa.part1.Equality.html#28179" class="Datatype Operator">≡′</a> <a id="28249" href="plfa.part1.Equality.html#28209" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Similarly, here is the generalised definition of symmetry:
{:/}

相似的，下面是对称性的推广定义：

{% raw %}<pre class="Agda"><a id="sym′"></a><a id="28355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28355" class="Function">sym′</a> <a id="28360" class="Symbol">:</a> <a id="28362" class="Symbol">∀</a> <a id="28364" class="Symbol">{</a><a id="28365" href="plfa.part1.Equality.html#28365" class="Bound">ℓ</a> <a id="28367" class="Symbol">:</a> <a id="28369" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28374" class="Symbol">}</a> <a id="28376" class="Symbol">{</a><a id="28377" href="plfa.part1.Equality.html#28377" class="Bound">A</a> <a id="28379" class="Symbol">:</a> <a id="28381" class="PrimitiveType">Set</a> <a id="28385" href="plfa.part1.Equality.html#28365" class="Bound">ℓ</a><a id="28386" class="Symbol">}</a> <a id="28388" class="Symbol">{</a><a id="28389" href="plfa.part1.Equality.html#28389" class="Bound">x</a> <a id="28391" href="plfa.part1.Equality.html#28391" class="Bound">y</a> <a id="28393" class="Symbol">:</a> <a id="28395" href="plfa.part1.Equality.html#28377" class="Bound">A</a><a id="28396" class="Symbol">}</a>
  <a id="28400" class="Symbol">→</a> <a id="28402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28389" class="Bound">x</a> <a id="28404" href="plfa.part1.Equality.html#28179" class="Datatype Operator">≡′</a> <a id="28407" href="plfa.part1.Equality.html#28391" class="Bound">y</a>
    <a id="28413" class="Comment">------</a>
  <a id="28422" class="Symbol">→</a> <a id="28424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28391" class="Bound">y</a> <a id="28426" href="plfa.part1.Equality.html#28179" class="Datatype Operator">≡′</a> <a id="28429" href="plfa.part1.Equality.html#28389" class="Bound">x</a>
<a id="28431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28355" class="Function">sym′</a> <a id="28436" href="plfa.part1.Equality.html#28236" class="InductiveConstructor">refl′</a> <a id="28442" class="Symbol">=</a> <a id="28444" href="plfa.part1.Equality.html#28236" class="InductiveConstructor">refl′</a>
</pre>{% endraw %}
{::comment}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
{:/}

为了简介，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，包括相等性的定义，都推广到了任意等级，如上所示。

{::comment}
Here is the generalised definition of Leibniz equality:
{:/}

下面是莱布尼兹相等性的推广定义：

{% raw %}<pre class="Agda"><a id="_≐′_"></a><a id="28842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28842" class="Function Operator">_≐′_</a> <a id="28847" class="Symbol">:</a> <a id="28849" class="Symbol">∀</a> <a id="28851" class="Symbol">{</a><a id="28852" href="plfa.part1.Equality.html#28852" class="Bound">ℓ</a> <a id="28854" class="Symbol">:</a> <a id="28856" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28861" class="Symbol">}</a> <a id="28863" class="Symbol">{</a><a id="28864" href="plfa.part1.Equality.html#28864" class="Bound">A</a> <a id="28866" class="Symbol">:</a> <a id="28868" class="PrimitiveType">Set</a> <a id="28872" href="plfa.part1.Equality.html#28852" class="Bound">ℓ</a><a id="28873" class="Symbol">}</a> <a id="28875" class="Symbol">(</a><a id="28876" href="plfa.part1.Equality.html#28876" class="Bound">x</a> <a id="28878" href="plfa.part1.Equality.html#28878" class="Bound">y</a> <a id="28880" class="Symbol">:</a> <a id="28882" href="plfa.part1.Equality.html#28864" class="Bound">A</a><a id="28883" class="Symbol">)</a> <a id="28885" class="Symbol">→</a> <a id="28887" class="PrimitiveType">Set</a> <a id="28891" class="Symbol">(</a><a id="28892" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="28897" href="plfa.part1.Equality.html#28852" class="Bound">ℓ</a><a id="28898" class="Symbol">)</a>
<a id="28900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#28842" class="Function Operator">_≐′_</a> <a id="28905" class="Symbol">{</a><a id="28906" href="plfa.part1.Equality.html#28906" class="Bound">ℓ</a><a id="28907" class="Symbol">}</a> <a id="28909" class="Symbol">{</a><a id="28910" href="plfa.part1.Equality.html#28910" class="Bound">A</a><a id="28911" class="Symbol">}</a> <a id="28913" href="plfa.part1.Equality.html#28913" class="Bound">x</a> <a id="28915" href="plfa.part1.Equality.html#28915" class="Bound">y</a> <a id="28917" class="Symbol">=</a> <a id="28919" class="Symbol">∀</a> <a id="28921" class="Symbol">(</a><a id="28922" href="plfa.part1.Equality.html#28922" class="Bound">P</a> <a id="28924" class="Symbol">:</a> <a id="28926" href="plfa.part1.Equality.html#28910" class="Bound">A</a> <a id="28928" class="Symbol">→</a> <a id="28930" class="PrimitiveType">Set</a> <a id="28934" href="plfa.part1.Equality.html#28906" class="Bound">ℓ</a><a id="28935" class="Symbol">)</a> <a id="28937" class="Symbol">→</a> <a id="28939" href="plfa.part1.Equality.html#28922" class="Bound">P</a> <a id="28941" href="plfa.part1.Equality.html#28913" class="Bound">x</a> <a id="28943" class="Symbol">→</a> <a id="28945" href="plfa.part1.Equality.html#28922" class="Bound">P</a> <a id="28947" href="plfa.part1.Equality.html#28915" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
{:/}

之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。

{::comment}
Most other functions in the standard library are also generalised to
arbitrary levels. For instance, here is the definition of composition.
{:/}

标准库中的大部分函数都泛化到了任意层级。例如，以下是复合的定义。

{% raw %}<pre class="Agda"><a id="_∘_"></a><a id="29421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#29421" class="Function Operator">_∘_</a> <a id="29425" class="Symbol">:</a> <a id="29427" class="Symbol">∀</a> <a id="29429" class="Symbol">{</a><a id="29430" href="plfa.part1.Equality.html#29430" class="Bound">ℓ₁</a> <a id="29433" href="plfa.part1.Equality.html#29433" class="Bound">ℓ₂</a> <a id="29436" href="plfa.part1.Equality.html#29436" class="Bound">ℓ₃</a> <a id="29439" class="Symbol">:</a> <a id="29441" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="29446" class="Symbol">}</a> <a id="29448" class="Symbol">{</a><a id="29449" href="plfa.part1.Equality.html#29449" class="Bound">A</a> <a id="29451" class="Symbol">:</a> <a id="29453" class="PrimitiveType">Set</a> <a id="29457" href="plfa.part1.Equality.html#29430" class="Bound">ℓ₁</a><a id="29459" class="Symbol">}</a> <a id="29461" class="Symbol">{</a><a id="29462" href="plfa.part1.Equality.html#29462" class="Bound">B</a> <a id="29464" class="Symbol">:</a> <a id="29466" class="PrimitiveType">Set</a> <a id="29470" href="plfa.part1.Equality.html#29433" class="Bound">ℓ₂</a><a id="29472" class="Symbol">}</a> <a id="29474" class="Symbol">{</a><a id="29475" href="plfa.part1.Equality.html#29475" class="Bound">C</a> <a id="29477" class="Symbol">:</a> <a id="29479" class="PrimitiveType">Set</a> <a id="29483" href="plfa.part1.Equality.html#29436" class="Bound">ℓ₃</a><a id="29485" class="Symbol">}</a>
  <a id="29489" class="Symbol">→</a> <a id="29491" class="Symbol">(</a><a id="29492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#29462" class="Bound">B</a> <a id="29494" class="Symbol">→</a> <a id="29496" href="plfa.part1.Equality.html#29475" class="Bound">C</a><a id="29497" class="Symbol">)</a> <a id="29499" class="Symbol">→</a> <a id="29501" class="Symbol">(</a><a id="29502" href="plfa.part1.Equality.html#29449" class="Bound">A</a> <a id="29504" class="Symbol">→</a> <a id="29506" href="plfa.part1.Equality.html#29462" class="Bound">B</a><a id="29507" class="Symbol">)</a> <a id="29509" class="Symbol">→</a> <a id="29511" href="plfa.part1.Equality.html#29449" class="Bound">A</a> <a id="29513" class="Symbol">→</a> <a id="29515" href="plfa.part1.Equality.html#29475" class="Bound">C</a>
<a id="29517" class="Symbol">(</a><a id="29518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#29518" class="Bound">g</a> <a id="29520" href="plfa.part1.Equality.html#29421" class="Function Operator">∘</a> <a id="29522" href="plfa.part1.Equality.html#29522" class="Bound">f</a><a id="29523" class="Symbol">)</a> <a id="29525" href="plfa.part1.Equality.html#29525" class="Bound">x</a>  <a id="29528" class="Symbol">=</a>  <a id="29531" href="plfa.part1.Equality.html#29518" class="Bound">g</a> <a id="29533" class="Symbol">(</a><a id="29534" href="plfa.part1.Equality.html#29522" class="Bound">f</a> <a id="29536" href="plfa.part1.Equality.html#29525" class="Bound">x</a><a id="29537" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Further information on levels can be found in the [Agda Wiki][wiki].
{:/}

更多的关于等级的信息可以从[Agda 维基（英文）][wiki]中查询。

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the
standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="29937" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="29991" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="30055" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>
</pre>{% endraw %}
{::comment}
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
{:/}

这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
{:/}

本章节使用下列 Unicode：

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  接近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
