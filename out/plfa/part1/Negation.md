---
src       : "src/plfa/part1/Negation.lagda.md"
title     : "Negation: 直觉逻辑与命题逻辑中的否定"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
translators : ["Oling Cat"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="188" class="Keyword">module</a> <a id="195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}" class="Module">plfa.part1.Negation</a> <a id="215" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This chapter introduces negation, and discusses intuitionistic
and classical logic.
{:/}

本章介绍了否定的性质，讨论了直觉逻辑和经典逻辑。

## Imports

{% raw %}<pre class="Agda"><a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="420" class="Keyword">using</a> <a id="426" class="Symbol">(</a><a id="427" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="430" class="Symbol">;</a> <a id="432" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="436" class="Symbol">)</a>
<a id="438" class="Keyword">open</a> <a id="443" class="Keyword">import</a> <a id="450" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="459" class="Keyword">using</a> <a id="465" class="Symbol">(</a><a id="466" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="467" class="Symbol">;</a> <a id="469" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="473" class="Symbol">;</a> <a id="475" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="478" class="Symbol">)</a>
<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a><a id="510" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="511" class="Symbol">;</a> <a id="513" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="519" class="Symbol">)</a>
<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="542" class="Keyword">using</a> <a id="548" class="Symbol">(</a><a id="549" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="552" class="Symbol">;</a> <a id="554" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="558" class="Symbol">;</a> <a id="560" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="564" class="Symbol">)</a>
<a id="566" class="Keyword">open</a> <a id="571" class="Keyword">import</a> <a id="578" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="591" class="Keyword">using</a> <a id="597" class="Symbol">(</a><a id="598" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="601" class="Symbol">)</a>
<a id="603" class="Keyword">open</a> <a id="608" class="Keyword">import</a> <a id="615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="638" class="Keyword">using</a> <a id="644" class="Symbol">(</a><a id="645" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="648" class="Symbol">;</a> <a id="650" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="664" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Negation
{:/}

## 否定

{::comment}
Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
{:/}

给定命题 `A`，当 `A` 不成立时，它的否定形式 `¬ A` 成立。我们将否定阐述为「蕴涵假」来形式化此概念。

{% raw %}<pre class="Agda"><a id="¬_"></a><a id="946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬_</a> <a id="949" class="Symbol">:</a> <a id="951" class="PrimitiveType">Set</a> <a id="955" class="Symbol">→</a> <a id="957" class="PrimitiveType">Set</a>
<a id="961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="963" href="plfa.part1.Negation.html#963" class="Bound">A</a> <a id="965" class="Symbol">=</a> <a id="967" href="plfa.part1.Negation.html#963" class="Bound">A</a> <a id="969" class="Symbol">→</a> <a id="971" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}
{::comment}
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.
{:/}

这是一种**反证法（Proof by Contradiction）**的形式：若从 `A` 可得出结论 `⊥`（即矛盾），则 `¬ A` 必定成立。

{::comment}
Evidence that `¬ A` holds is of the form
{:/}

`¬ A` 成立的证据的形式为：

    λ{ x → N }

{::comment}
where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.
{:/}

其中 `N` 是类型为 `⊥` 的项，它包含类型为 `A` 的自由变量 `x`。换言之，`¬ A` 成立的证据是一个函数，该函数将 `A` 成立的证据转换为 `⊥` 成立的证据。

{::comment}
Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
{:/}

给定 `¬ A` 和 `A` 均成立的证据，我们可以得出 `⊥` 成立。换言之，若 `¬ A` 和 `A` 均成立，那么我们就得到了矛盾：

{% raw %}<pre class="Agda"><a id="¬-elim"></a><a id="1856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1856" class="Function">¬-elim</a> <a id="1863" class="Symbol">:</a> <a id="1865" class="Symbol">∀</a> <a id="1867" class="Symbol">{</a><a id="1868" href="plfa.part1.Negation.html#1868" class="Bound">A</a> <a id="1870" class="Symbol">:</a> <a id="1872" class="PrimitiveType">Set</a><a id="1875" class="Symbol">}</a>
  <a id="1879" class="Symbol">→</a> <a id="1881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="1883" href="plfa.part1.Negation.html#1868" class="Bound">A</a>
  <a id="1887" class="Symbol">→</a> <a id="1889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1868" class="Bound">A</a>
    <a id="1895" class="Comment">---</a>
  <a id="1901" class="Symbol">→</a> <a id="1903" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="1905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1856" class="Function">¬-elim</a> <a id="1912" href="plfa.part1.Negation.html#1912" class="Bound">¬x</a> <a id="1915" href="plfa.part1.Negation.html#1915" class="Bound">x</a> <a id="1917" class="Symbol">=</a> <a id="1919" href="plfa.part1.Negation.html#1912" class="Bound">¬x</a> <a id="1922" href="plfa.part1.Negation.html#1915" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.
{:/}

在这里，我们将 `¬ A` 的证据写作 `¬x`，将 `A` 的证据写作 `x`。这表示 `¬x` 必须是类型为 `A → ⊥`
的函数，因此应用 `¬x x` 得到的类型必为 `⊥`。注意此规则只是 `→-elim` 的一个特例。

{::comment}
We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
{:/}

我们将否定的优先级设定为高于析取和合取，但低于其它运算：

{% raw %}<pre class="Agda"><a id="2491" class="Keyword">infix</a> <a id="2497" class="Number">3</a> <a id="2499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬_</a>
</pre>{% endraw %}
{::comment}
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.
{:/}

因此，`¬ A × ¬ B` 会解析为 `(¬ A) × (¬ B)`，而 `¬ m ≡ n` 会解析为 `¬ (m ≡ n)`。

{::comment}
In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
{:/}

在**经典逻辑**中，`A` 等价于 `¬ ¬ A`。而如前文所述，Agda 中使用了**直觉逻辑**，因此我们只有该等价关系的一半，即 `A` 蕴涵 `¬ ¬ A`：

{% raw %}<pre class="Agda"><a id="¬¬-intro"></a><a id="2978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2978" class="Function">¬¬-intro</a> <a id="2987" class="Symbol">:</a> <a id="2989" class="Symbol">∀</a> <a id="2991" class="Symbol">{</a><a id="2992" href="plfa.part1.Negation.html#2992" class="Bound">A</a> <a id="2994" class="Symbol">:</a> <a id="2996" class="PrimitiveType">Set</a><a id="2999" class="Symbol">}</a>
  <a id="3003" class="Symbol">→</a> <a id="3005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2992" class="Bound">A</a>
    <a id="3011" class="Comment">-----</a>
  <a id="3019" class="Symbol">→</a> <a id="3021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="3023" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="3025" href="plfa.part1.Negation.html#2992" class="Bound">A</a>
<a id="3027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2978" class="Function">¬¬-intro</a> <a id="3036" href="plfa.part1.Negation.html#3036" class="Bound">x</a>  <a id="3039" class="Symbol">=</a>  <a id="3042" class="Symbol">λ{</a><a id="3044" href="plfa.part1.Negation.html#3044" class="Bound">¬x</a> <a id="3047" class="Symbol">→</a> <a id="3049" href="plfa.part1.Negation.html#3044" class="Bound">¬x</a> <a id="3052" href="plfa.part1.Negation.html#3036" class="Bound">x</a><a id="3053" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.
{:/}

令 `x` 为 `A` 的证据。我们要证明若假定 `¬ A` 成立，则会导出矛盾，因此 `¬ ¬ A`
必定成立。令 `¬x` 为 `¬ A` 的证据。那么以 `¬x x` 为证据，从 `A` 和 `¬ A` 可以导出矛盾。这样我们就证明了 `¬ ¬ A`。

{::comment}
An equivalent way to write the above is as follows:
{:/}

以上描述的等价写法如下：

{% raw %}<pre class="Agda"><a id="¬¬-intro′"></a><a id="3542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3542" class="Function">¬¬-intro′</a> <a id="3552" class="Symbol">:</a> <a id="3554" class="Symbol">∀</a> <a id="3556" class="Symbol">{</a><a id="3557" href="plfa.part1.Negation.html#3557" class="Bound">A</a> <a id="3559" class="Symbol">:</a> <a id="3561" class="PrimitiveType">Set</a><a id="3564" class="Symbol">}</a>
  <a id="3568" class="Symbol">→</a> <a id="3570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3557" class="Bound">A</a>
    <a id="3576" class="Comment">-----</a>
  <a id="3584" class="Symbol">→</a> <a id="3586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="3588" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="3590" href="plfa.part1.Negation.html#3557" class="Bound">A</a>
<a id="3592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3542" class="Function">¬¬-intro′</a> <a id="3602" href="plfa.part1.Negation.html#3602" class="Bound">x</a> <a id="3604" href="plfa.part1.Negation.html#3604" class="Bound">¬x</a> <a id="3607" class="Symbol">=</a> <a id="3609" href="plfa.part1.Negation.html#3604" class="Bound">¬x</a> <a id="3612" href="plfa.part1.Negation.html#3602" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.
{:/}

在这里我们简单地将 λ-项的参数转换成了该函数的额外参数。我们通常会使用后面这种形式，因为它更加紧凑。

{::comment}
We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
{:/}

我们无法证明 `¬ ¬ A` 蕴涵 `A`，但可以证明 `¬ ¬ ¬ A` 蕴涵 `¬ A`：

{% raw %}<pre class="Agda"><a id="¬¬¬-elim"></a><a id="4017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4017" class="Function">¬¬¬-elim</a> <a id="4026" class="Symbol">:</a> <a id="4028" class="Symbol">∀</a> <a id="4030" class="Symbol">{</a><a id="4031" href="plfa.part1.Negation.html#4031" class="Bound">A</a> <a id="4033" class="Symbol">:</a> <a id="4035" class="PrimitiveType">Set</a><a id="4038" class="Symbol">}</a>
  <a id="4042" class="Symbol">→</a> <a id="4044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="4046" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="4048" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="4050" href="plfa.part1.Negation.html#4031" class="Bound">A</a>
    <a id="4056" class="Comment">-------</a>
  <a id="4066" class="Symbol">→</a> <a id="4068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="4070" href="plfa.part1.Negation.html#4031" class="Bound">A</a>
<a id="4072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4017" class="Function">¬¬¬-elim</a> <a id="4081" href="plfa.part1.Negation.html#4081" class="Bound">¬¬¬x</a>  <a id="4087" class="Symbol">=</a>  <a id="4090" class="Symbol">λ</a> <a id="4092" href="plfa.part1.Negation.html#4092" class="Bound">x</a> <a id="4094" class="Symbol">→</a> <a id="4096" href="plfa.part1.Negation.html#4081" class="Bound">¬¬¬x</a> <a id="4101" class="Symbol">(</a><a id="4102" href="plfa.part1.Negation.html#2978" class="Function">¬¬-intro</a> <a id="4111" href="plfa.part1.Negation.html#4092" class="Bound">x</a><a id="4112" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.
{:/}

令 `¬¬¬x` 为 `¬ ¬ ¬ A` 的证据。我们要证明若假定 `A` 成立就会导出矛盾，因此 `¬ A` 必定成立。令 `x` 为 `A` 的证据。根据前面的结果，以 `¬¬-intro x`
为证据可得出结论 `¬ ¬ A`。根据 `¬¬¬x (¬¬-intro x)`，我们可从
`¬ ¬ ¬ A` 和 `¬ ¬ A` 导出矛盾。这样我们就证明了 `¬ A`。

{::comment}
Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
{:/}

另一个逻辑规则是**换质换位律（contraposition）**，它陈述了若 `A` 蕴涵 `B`，则 `¬ B` 蕴涵 `¬ A`：

{% raw %}<pre class="Agda"><a id="contraposition"></a><a id="4869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4869" class="Function">contraposition</a> <a id="4884" class="Symbol">:</a> <a id="4886" class="Symbol">∀</a> <a id="4888" class="Symbol">{</a><a id="4889" href="plfa.part1.Negation.html#4889" class="Bound">A</a> <a id="4891" href="plfa.part1.Negation.html#4891" class="Bound">B</a> <a id="4893" class="Symbol">:</a> <a id="4895" class="PrimitiveType">Set</a><a id="4898" class="Symbol">}</a>
  <a id="4902" class="Symbol">→</a> <a id="4904" class="Symbol">(</a><a id="4905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4889" class="Bound">A</a> <a id="4907" class="Symbol">→</a> <a id="4909" href="plfa.part1.Negation.html#4891" class="Bound">B</a><a id="4910" class="Symbol">)</a>
    <a id="4916" class="Comment">-----------</a>
  <a id="4930" class="Symbol">→</a> <a id="4932" class="Symbol">(</a><a id="4933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#946" class="Function Operator">¬</a> <a id="4935" href="plfa.part1.Negation.html#4891" class="Bound">B</a> <a id="4937" class="Symbol">→</a> <a id="4939" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="4941" href="plfa.part1.Negation.html#4889" class="Bound">A</a><a id="4942" class="Symbol">)</a>
<a id="4944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4869" class="Function">contraposition</a> <a id="4959" href="plfa.part1.Negation.html#4959" class="Bound">f</a> <a id="4961" href="plfa.part1.Negation.html#4961" class="Bound">¬y</a> <a id="4964" href="plfa.part1.Negation.html#4964" class="Bound">x</a> <a id="4966" class="Symbol">=</a> <a id="4968" href="plfa.part1.Negation.html#4961" class="Bound">¬y</a> <a id="4971" class="Symbol">(</a><a id="4972" href="plfa.part1.Negation.html#4959" class="Bound">f</a> <a id="4974" href="plfa.part1.Negation.html#4964" class="Bound">x</a><a id="4975" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.
{:/}

令 `f` 为 `A → B` 的证据，`¬y` 为 `¬ B` 的证据。我们要证明，若假定 `A`
成立就会导出矛盾，因此 `¬ A` 必定成立。令 `x` 为 `A` 的证据。根据 `f x`，我们可从 `A → B` 和 `A` 我们可得出结论 `B`。而根据 `¬y (f x)`，可从
`B` 和 `¬ B` 得出结论 `⊥`。这样，我们就证明了 `¬ A`。

{::comment}
Using negation, it is straightforward to define inequality:
{:/}

利用否定可直接定义不等性：


{% raw %}<pre class="Agda"><a id="_≢_"></a><a id="5631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5631" class="Function Operator">_≢_</a> <a id="5635" class="Symbol">:</a> <a id="5637" class="Symbol">∀</a> <a id="5639" class="Symbol">{</a><a id="5640" href="plfa.part1.Negation.html#5640" class="Bound">A</a> <a id="5642" class="Symbol">:</a> <a id="5644" class="PrimitiveType">Set</a><a id="5647" class="Symbol">}</a> <a id="5649" class="Symbol">→</a> <a id="5651" href="plfa.part1.Negation.html#5640" class="Bound">A</a> <a id="5653" class="Symbol">→</a> <a id="5655" href="plfa.part1.Negation.html#5640" class="Bound">A</a> <a id="5657" class="Symbol">→</a> <a id="5659" class="PrimitiveType">Set</a>
<a id="5663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5663" class="Bound">x</a> <a id="5665" href="plfa.part1.Negation.html#5631" class="Function Operator">≢</a> <a id="5667" href="plfa.part1.Negation.html#5667" class="Bound">y</a>  <a id="5670" class="Symbol">=</a>  <a id="5673" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="5675" class="Symbol">(</a><a id="5676" href="plfa.part1.Negation.html#5663" class="Bound">x</a> <a id="5678" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5680" href="plfa.part1.Negation.html#5667" class="Bound">y</a><a id="5681" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
It is trivial to show distinct numbers are not equal:
{:/}

要证明不同的数不相等很简单：

{% raw %}<pre class="Agda"><a id="5780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5780" class="Function">_</a> <a id="5782" class="Symbol">:</a> <a id="5784" class="Number">1</a> <a id="5786" href="plfa.part1.Negation.html#5631" class="Function Operator">≢</a> <a id="5788" class="Number">2</a>
<a id="5790" class="Symbol">_</a> <a id="5792" class="Symbol">=</a> <a id="5794" class="Symbol">λ()</a>
</pre>{% endraw %}
{::comment}
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
{:/}

这是我们第一次在 λ-表达式中使用谬模式（Absurd Pattern）。类型 `M ≡ N`
只有在 `M` 和 `N` 可被化简为相同的项时才能居留。由于 `1` 和 `2`
会化简为不同的正规形式，因此 Agda 判定没有证据可证明 `1 ≡ 2`。第二个例子是，很容易验证皮亚诺公理中「零不是任何数的后继数」的假设：

{% raw %}<pre class="Agda"><a id="peano"></a><a id="6371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#6371" class="Function">peano</a> <a id="6377" class="Symbol">:</a> <a id="6379" class="Symbol">∀</a> <a id="6381" class="Symbol">{</a><a id="6382" href="plfa.part1.Negation.html#6382" class="Bound">m</a> <a id="6384" class="Symbol">:</a> <a id="6386" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="6387" class="Symbol">}</a> <a id="6389" class="Symbol">→</a> <a id="6391" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="6396" href="plfa.part1.Negation.html#5631" class="Function Operator">≢</a> <a id="6398" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6402" href="plfa.part1.Negation.html#6382" class="Bound">m</a>
<a id="6404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#6371" class="Function">peano</a> <a id="6410" class="Symbol">=</a> <a id="6412" class="Symbol">λ()</a>
</pre>{% endraw %}
{::comment}
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.
{:/}

它们的证明基本上相同，因为谬模式会匹配所有类型为 `zero ≡ suc m` 的可能的证据。

{::comment}
Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where
{:/}

鉴于蕴涵和幂运算之间的对应关系，以及没有成员的类型为假，我们可以将否定看作零的幂。它确实对应于我们所知的算术运算，即

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

{::comment}
Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
{:/}

确实，只有一个 `⊥ → ⊥` 的证明。我们可以用两种方式写出此证明：

{% raw %}<pre class="Agda"><a id="id"></a><a id="7098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7098" class="Function">id</a> <a id="7101" class="Symbol">:</a> <a id="7103" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="7105" class="Symbol">→</a> <a id="7107" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="7109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7098" class="Function">id</a> <a id="7112" href="plfa.part1.Negation.html#7112" class="Bound">x</a> <a id="7114" class="Symbol">=</a> <a id="7116" href="plfa.part1.Negation.html#7112" class="Bound">x</a>

<a id="id′"></a><a id="7119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7119" class="Function">id′</a> <a id="7123" class="Symbol">:</a> <a id="7125" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="7127" class="Symbol">→</a> <a id="7129" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="7131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7119" class="Function">id′</a> <a id="7135" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
But, using extensionality, we can prove these equal:
{:/}

不过使用外延性，我们可以证明二者相等：

{% raw %}<pre class="Agda"><a id="id≡id′"></a><a id="7239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7239" class="Function">id≡id′</a> <a id="7246" class="Symbol">:</a> <a id="7248" href="plfa.part1.Negation.html#7098" class="Function">id</a> <a id="7251" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7253" href="plfa.part1.Negation.html#7119" class="Function">id′</a>
<a id="7257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7239" class="Function">id≡id′</a> <a id="7264" class="Symbol">=</a> <a id="7266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3764" class="Postulate">extensionality</a> <a id="7281" class="Symbol">(λ())</a>
</pre>{% endraw %}
{::comment}
By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.
{:/}

根据外延性，对于任何在二者定义域中的 `x`，都有 `id x ≡ id′ x`，则 `id ≡ id′` 成立。不过没有 `x` 在它们的定义域中，因此其相等性平凡成立。

{::comment}
Indeed, we can show any two proofs of a negation are equal:
{:/}

实际上，我们可以证明任意两个否定的证明都是相等的：

{% raw %}<pre class="Agda"><a id="assimilation"></a><a id="7671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7671" class="Function">assimilation</a> <a id="7684" class="Symbol">:</a> <a id="7686" class="Symbol">∀</a> <a id="7688" class="Symbol">{</a><a id="7689" href="plfa.part1.Negation.html#7689" class="Bound">A</a> <a id="7691" class="Symbol">:</a> <a id="7693" class="PrimitiveType">Set</a><a id="7696" class="Symbol">}</a> <a id="7698" class="Symbol">(</a><a id="7699" href="plfa.part1.Negation.html#7699" class="Bound">¬x</a> <a id="7702" href="plfa.part1.Negation.html#7702" class="Bound">¬x′</a> <a id="7706" class="Symbol">:</a> <a id="7708" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="7710" href="plfa.part1.Negation.html#7689" class="Bound">A</a><a id="7711" class="Symbol">)</a> <a id="7713" class="Symbol">→</a> <a id="7715" href="plfa.part1.Negation.html#7699" class="Bound">¬x</a> <a id="7718" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7720" href="plfa.part1.Negation.html#7702" class="Bound">¬x′</a>
<a id="7724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#7671" class="Function">assimilation</a> <a id="7737" href="plfa.part1.Negation.html#7737" class="Bound">¬x</a> <a id="7740" href="plfa.part1.Negation.html#7740" class="Bound">¬x′</a> <a id="7744" class="Symbol">=</a> <a id="7746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#3764" class="Postulate">extensionality</a> <a id="7761" class="Symbol">(λ</a> <a id="7764" href="plfa.part1.Negation.html#7764" class="Bound">x</a> <a id="7766" class="Symbol">→</a> <a id="7768" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7775" class="Symbol">(</a><a id="7776" href="plfa.part1.Negation.html#7737" class="Bound">¬x</a> <a id="7779" href="plfa.part1.Negation.html#7764" class="Bound">x</a><a id="7780" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.
{:/}

`¬ A` 的证据蕴涵任何 `A` 的证据都可直接得出矛盾。但由于外延性全称量化了使
`A` 成立的 `x`，因此任何这样的 `x` 都会直接导出矛盾，同样其相等性平凡成立。


{::comment}
#### Exercise `<-irreflexive` (recommended)
{:/}

#### 练习 `<-irreflexive`（推荐）

{::comment}
Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.
{:/}

利用否定证明[严格不等性]({{ site.baseurl }}/Relations/#strict-inequality)满足非自反性，即 `n < n` 对于任何 `n` 都不成立。

{::comment}
{% raw %}<pre class="Agda"><a id="8521" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="8558" class="Comment">-- 请将代码写在此处</a>
</pre>{% endraw %}
{::comment}
#### Exercise `trichotomy` (practice)
{:/}

#### 练习 `trichotomy`（实践）

{::comment}
Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:
{:/}

请证明严格不等性满足[三分律]({{ site.baseurl }}/Relations/#trichotomy)，即对于任何自然数 `m` 和 `n`，以下三条刚好只有一条成立：

* `m < n`
* `m ≡ n`
* `m > n`

{::comment}
Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.
{:/}

「刚好只有一条」的意思是，三者中不仅有一条成立，而且当其中一条成立时，其它二者的否定也必定成立。

{::comment}
{% raw %}<pre class="Agda"><a id="9189" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="9226" class="Comment">-- 请将代码写在此处</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊎-dual-×` (recommended)
{:/}

#### 练习 `⊎-dual-×`（推荐）

{::comment}
Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.
{:/}

请证明合取、析取和否定可通过以下版本的德摩根定律（De Morgan's Law）关联在一起。

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

{::comment}
This result is an easy consequence of something we've proved previously.
{:/}

此结果是我们之前证明的定理的简单推论。

{::comment}
{% raw %}<pre class="Agda"><a id="9644" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="9681" class="Comment">-- 请将代码写在此处</a>
</pre>{% endraw %}
{::comment}
Do we also have the following?
{:/}

以下命题也成立吗？

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

{::comment}
If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?
{:/}

若成立，请证明；若不成立，你能给出一个比同构更弱的关系将两边关联起来吗？


{::comment}
## Intuitive and Classical logic
{:/}

## 直觉逻辑与经典逻辑

{::comment}
In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."
{:/}

在 Gilbert 和 Sullivan 的电影《船夫》（_The Gondoliers_）中，
Casilda 被告知她还是个婴儿时，就被许配给了巴塔维亚国王的继承人。但由于一场动乱，没人知道她被许配给了两位继承人 Marco 和 Giuseppe
中的哪一位。她惊慌地哀嚎道：「那么你的意思是说我嫁给了两位船夫中的一位，但却无法确定是谁？」对此的回答是：「虽然不知道是谁，但这件事却是毫无疑问的。」

{::comment}
Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.
{:/}

逻辑学有很多变种，而**经典逻辑**和**直觉逻辑**之间有一个区别。直觉主义者关注于某些逻辑学家对无限性本质的假设，坚持真理的构造主义的概念。具体来说，它们坚持认为 `A ⊎ B` 的证明必须确定 `A` 或 `B` 中的**哪一个**成立，因此它们会解决宣称 Casilda 嫁给了 Marco 或者 Giuseppe，直到其中一个被确定为她的丈夫为止。或许 Gilbert 和 Sullivan 期待直觉主义，因为在故事的结局中，继承人是第三个人 Luiz，他和 Casilda 已经顺利地相爱了。

{::comment}
Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.
{:/}

直觉主义者也拒绝排中律（Law of the Excluded Middle）————该定律断言，对于所有的
`A`，`A ⊎ ¬ A` 必定成立————因为该定律没有给出 `A` 和 `¬ A` 中的哪一个成立。海廷（Heyting）形式化了希尔伯特（Hilbert）经典逻辑的一个变种，抓住了直觉主义中可证明性的概念。具体来说，排中律在希尔伯特逻辑中是可证明的，但在海廷逻辑中却不可证明。进一步来说，如果排中律作为一条公理添加到海廷逻辑中，那么它会等价于希尔伯特逻辑。柯尔莫哥洛夫（Kolmogorov）证明了两种逻辑紧密相关：他给出了双重否定翻译，即一个式子在经典逻辑中可证，当且仅当它的双重否定式在直觉逻辑中可证。

{::comment}
Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.
{:/}

「命题即类型」最初是为直觉逻辑而制定的。这是一种完美的契合，因为在直觉主义的解释中，式子 `A ⊎ B` 刚好可以在给出 `A` 或 `B` 之一的证明时得证，因此对应于析取的类型是一个不交和（Disjoint Sum）。

{::comment}
(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

（以上内容部分取自 "Propositions as Types", Philip Wadler,
_Communications of the ACM_，2015 年 12 月。）

{::comment}
## Excluded middle is irrefutable
{:/}

## 排中律是不可辩驳的

{::comment}
The law of the excluded middle can be formulated as follows:
{:/}

排中律可形式化如下：

{% raw %}<pre class="Agda"><a id="13455" class="Keyword">postulate</a>
  <a id="em"></a><a id="13467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13467" class="Postulate">em</a> <a id="13470" class="Symbol">:</a> <a id="13472" class="Symbol">∀</a> <a id="13474" class="Symbol">{</a><a id="13475" href="plfa.part1.Negation.html#13475" class="Bound">A</a> <a id="13477" class="Symbol">:</a> <a id="13479" class="PrimitiveType">Set</a><a id="13482" class="Symbol">}</a> <a id="13484" class="Symbol">→</a> <a id="13486" href="plfa.part1.Negation.html#13475" class="Bound">A</a> <a id="13488" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="13490" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="13492" href="plfa.part1.Negation.html#13475" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
{:/}

如之前所言，排中律在直觉逻辑中并不成立。然而，我们可以证明它是
**不可辩驳（Irrefutable）**的，即其否定的否定是可证明的（因而其否定式不可证明）：

{% raw %}<pre class="Agda"><a id="em-irrefutable"></a><a id="13837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13837" class="Function">em-irrefutable</a> <a id="13852" class="Symbol">:</a> <a id="13854" class="Symbol">∀</a> <a id="13856" class="Symbol">{</a><a id="13857" href="plfa.part1.Negation.html#13857" class="Bound">A</a> <a id="13859" class="Symbol">:</a> <a id="13861" class="PrimitiveType">Set</a><a id="13864" class="Symbol">}</a> <a id="13866" class="Symbol">→</a> <a id="13868" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="13870" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="13872" class="Symbol">(</a><a id="13873" href="plfa.part1.Negation.html#13857" class="Bound">A</a> <a id="13875" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="13877" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="13879" href="plfa.part1.Negation.html#13857" class="Bound">A</a><a id="13880" class="Symbol">)</a>
<a id="13882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13837" class="Function">em-irrefutable</a> <a id="13897" class="Symbol">=</a> <a id="13899" class="Symbol">λ</a> <a id="13901" href="plfa.part1.Negation.html#13901" class="Bound">k</a> <a id="13903" class="Symbol">→</a> <a id="13905" href="plfa.part1.Negation.html#13901" class="Bound">k</a> <a id="13907" class="Symbol">(</a><a id="13908" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="13913" class="Symbol">(λ</a> <a id="13916" href="plfa.part1.Negation.html#13916" class="Bound">x</a> <a id="13918" class="Symbol">→</a> <a id="13920" href="plfa.part1.Negation.html#13901" class="Bound">k</a> <a id="13922" class="Symbol">(</a><a id="13923" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="13928" href="plfa.part1.Negation.html#13916" class="Bound">x</a><a id="13929" class="Symbol">)))</a>
</pre>{% endraw %}
{::comment}
The best way to explain this code is to develop it interactively:
{:/}

解释此代码的最佳方式是交互式地推导它：

    em-irrefutable k = ?

{::comment}
Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:
{:/}

给定 `¬ (A ⊎ ¬ A)` 的证据 `k`，即一个函数，它接受一个类型为 `A ⊎ ¬ A` 的值，返回一个空类型的值，我们必须在 `?` 处填上一个返回空类型的项。得到空类型值的唯一方式就是应用 `k` 本身，于是我们据此展开此洞：

    em-irrefutable k = k ?

{::comment}
We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:
{:/}

我们需要用类型为 `A ⊎ ¬ A` 的值填上这个新的洞。由于目前我们并没有类型为 `A` 的值，因此先处理第二个析取：

    em-irrefutable k = k (inj₂ λ{ x → ? })

{::comment}
The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:
{:/}

第二个析取接受 `¬ A` 的证据，即一个函数，它接受类型为 `A` 的值，返回空类型的值。我们将 `x` 绑定到类型为 `A` 的值，现在我们需要在洞中填入空类型的值。同样，得到空类型的值的唯一方法就是将 `k` 应用到其自身，于是我们展开此洞：

    em-irrefutable k = k (inj₂ λ{ x → k ? })

{::comment}
This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:
{:/}

这次我们就有一个类型为 `A` 的值了，其名为 `x`，于是我们可以处理第一个析取：

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

{::comment}
There are no holes left! This completes the proof.
{:/}

现在没有洞了！这样就完成了证明。

{::comment}
The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)
{:/}

下面的故事说明了我们创建的项的行为。
（向 Peter Selinger 道歉，他讲的是个关于国王，巫师和贤者之石的类似的故事。）

{::comment}
Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."
{:/}

曾经有一个恶魔向一个男人提议：「要么 (a) 我给你 10 亿美元，要么 (b) 如果你付给我
10 亿美元，我可以实现你的任何一个愿望。当然，得是我决定提供 (a) 还是 (b)。」

{::comment}
The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.
{:/}

男人很谨慎。他需要付出他的灵魂吗？恶魔说不用，他只要接受这个提议就行。

{::comment}
The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?
{:/}

于是男人思索着，如果恶魔向他提供 (b)，那么他不太可能付得起这个愿望。不过倘若真是如此的话，能有什么坏处吗？

{::comment}
"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."
{:/}

「我接受」，男人回答道，「我能得到 (a) 还是 (b)？」

恶魔顿了顿。「我提供 (b)。」

{::comment}
The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.
{:/}

男人很失望，但并不惊讶。「果然是这样」，他想。但是这个提议折磨着他。想想他都能用这个愿望做些什么！多年以后，男人开始积累钱财。为了得到这笔钱，他有时会做坏事，而且他隐约意识到这一定是魔鬼所想到的。最后他攒够了 10 亿美元，恶魔再次出现了。

{::comment}
"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"
{:/}

「这是 10 亿美元」，男人说着，交出一个手提箱。「实现我的愿望吧！」

{::comment}
The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."
{:/}

恶魔接过了手提箱。然后他说道，「哦？我之前说的是 (b) 吗？抱歉，我说的是 (a)。很高兴能给你 10 亿美元。」

{::comment}
And the devil handed back to the man the same valise that the man had
just handed to him.
{:/}

于是恶魔将那个手提箱又还给了他。

{::comment}
(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)
{:/}

（以上内容部分取自 "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003 年。）


{::comment}
#### Exercise `Classical` (stretch)
{:/}

#### 练习 `Classical`（延伸）

{::comment}
Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.
{:/}

考虑以下定律：

  * 排中律：对于所有 `A`，`A ⊎ ¬ A`。
  * 双重否定消去：对于所有的 `A`，`¬ ¬ A → A`。
  * 皮尔士定律：对于所有的 `A` 和 `B`，`((A → B) → A) → A`。
  * 蕴涵表示为析取：对于所有的 `A` 和 `B`，`(A → B) → ¬ A ⊎ B`。
  * 德摩根定律：对于所有的 `A` 和 `B`，`¬ (¬ A × ¬ B) → A ⊎ B`。

{::comment}
Show that each of these implies all the others.
{:/}

请证明其中任意一条定律都蕴涵其它所有定律。

{::comment}
{% raw %}<pre class="Agda"><a id="18997" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="19034" class="Comment">-- 请将代码写在此处</a>
</pre>{% endraw %}

{::comment}
#### Exercise `Stable` (stretch)
{:/}

#### 联系 `Stable`（延伸）

{::comment}
Say that a formula is _stable_ if double negation elimination holds for it:
{:/}

若双重否定消去对某个式子成立，我们就说它是**稳定（Stable）**的：

{% raw %}<pre class="Agda"><a id="Stable"></a><a id="19262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#19262" class="Function">Stable</a> <a id="19269" class="Symbol">:</a> <a id="19271" class="PrimitiveType">Set</a> <a id="19275" class="Symbol">→</a> <a id="19277" class="PrimitiveType">Set</a>
<a id="19281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#19262" class="Function">Stable</a> <a id="19288" href="plfa.part1.Negation.html#19288" class="Bound">A</a> <a id="19290" class="Symbol">=</a> <a id="19292" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="19294" href="plfa.part1.Negation.html#946" class="Function Operator">¬</a> <a id="19296" href="plfa.part1.Negation.html#19288" class="Bound">A</a> <a id="19298" class="Symbol">→</a> <a id="19300" href="plfa.part1.Negation.html#19288" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.
{:/}

请证明任何否定式都是稳定的，并且两个稳定式的合取也是稳定的。

{::comment}
{% raw %}<pre class="Agda"><a id="19473" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="19510" class="Comment">-- 请将代码写在此处</a>
</pre>{% endraw %}
{::comment}
## Standard Prelude
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中的类似定义可在标准库中找到：

{% raw %}<pre class="Agda"><a id="19697" class="Keyword">import</a> <a id="19704" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="19721" class="Keyword">using</a> <a id="19727" class="Symbol">(</a><a id="19728" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="19730" class="Symbol">)</a>
<a id="19732" class="Keyword">import</a> <a id="19739" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="19765" class="Keyword">using</a> <a id="19771" class="Symbol">(</a><a id="19772" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="19786" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

本章使用了以下 Unicode：

{::comment}
    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
{:/}


    ¬  U+00AC  否定符号 (\neg)
    ≢  U+2262  不等价于 (\==n)
