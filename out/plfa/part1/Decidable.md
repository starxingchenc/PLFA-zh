---
src       : "src/plfa/part1/Decidable.lagda.md"
title     : "Decidable: 布尔值与判定过程"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="181" class="Keyword">module</a> <a id="188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}" class="Module">plfa.part1.Decidable</a> <a id="209" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.
{:/}

我们有两种不同的方式来表示关系：一是表示为由关系成立的*证明*（Evidence）所构成的数据类型；二是表示为一个*计算*（Compute）关系是否成立的函数。在本章中，我们将探讨这两种方式之间的关系。我们首先研究大家熟悉的*布尔值*（Boolean）记法，但是之后我们会发现，相较布尔值记法，使用一种新的*可判定性*（Decidable）记法将会是更好的选择。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="834" class="Keyword">import</a> <a id="841" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="879" class="Symbol">as</a> <a id="882" class="Module">Eq</a>
<a id="885" class="Keyword">open</a> <a id="890" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="893" class="Keyword">using</a> <a id="899" class="Symbol">(</a><a id="900" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="903" class="Symbol">;</a> <a id="905" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="909" class="Symbol">)</a>
<a id="911" class="Keyword">open</a> <a id="916" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="931" class="Keyword">open</a> <a id="936" class="Keyword">import</a> <a id="943" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="952" class="Keyword">using</a> <a id="958" class="Symbol">(</a><a id="959" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="960" class="Symbol">;</a> <a id="962" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="966" class="Symbol">;</a> <a id="968" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="971" class="Symbol">)</a>
<a id="973" class="Keyword">open</a> <a id="978" class="Keyword">import</a> <a id="985" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="998" class="Keyword">using</a> <a id="1004" class="Symbol">(</a><a id="1005" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1008" class="Symbol">)</a> <a id="1010" class="Keyword">renaming</a> <a id="1019" class="Symbol">(</a><a id="1020" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1024" class="Symbol">to</a> <a id="1027" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1032" class="Symbol">)</a>
<a id="1034" class="Keyword">open</a> <a id="1039" class="Keyword">import</a> <a id="1046" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1055" class="Keyword">using</a> <a id="1061" class="Symbol">(</a><a id="1062" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1065" class="Symbol">;</a> <a id="1067" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1071" class="Symbol">;</a> <a id="1073" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1077" class="Symbol">)</a>
<a id="1079" class="Keyword">open</a> <a id="1084" class="Keyword">import</a> <a id="1091" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1108" class="Keyword">using</a> <a id="1114" class="Symbol">(</a><a id="1115" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1117" class="Symbol">)</a>
<a id="1119" class="Keyword">open</a> <a id="1124" class="Keyword">import</a> <a id="1131" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1157" class="Keyword">using</a> <a id="1163" class="Symbol">()</a>
  <a id="1168" class="Keyword">renaming</a> <a id="1177" class="Symbol">(</a><a id="1178" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">contradiction</a> <a id="1192" class="Symbol">to</a> <a id="1195" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a><a id="1203" class="Symbol">)</a>
<a id="1205" class="Keyword">open</a> <a id="1210" class="Keyword">import</a> <a id="1217" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1227" class="Keyword">using</a> <a id="1233" class="Symbol">(</a><a id="1234" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1235" class="Symbol">;</a> <a id="1237" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1239" class="Symbol">)</a>
<a id="1241" class="Keyword">open</a> <a id="1246" class="Keyword">import</a> <a id="1253" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1264" class="Keyword">using</a> <a id="1270" class="Symbol">(</a><a id="1271" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1272" class="Symbol">;</a> <a id="1274" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1280" class="Symbol">)</a>
<a id="1282" class="Keyword">open</a> <a id="1287" class="Keyword">import</a> <a id="1294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1315" class="Keyword">using</a> <a id="1321" class="Symbol">(</a><a id="1322" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="1325" class="Symbol">;</a> <a id="1327" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="1330" class="Symbol">;</a> <a id="1332" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="1335" class="Symbol">)</a>
<a id="1337" class="Keyword">open</a> <a id="1342" class="Keyword">import</a> <a id="1349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1372" class="Keyword">using</a> <a id="1378" class="Symbol">(</a><a id="1379" href="plfa.part1.Isomorphism.html#15292" class="Record Operator">_⇔_</a><a id="1382" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Evidence vs Computation
{:/}

## 证据 vs 计算

{::comment}
Recall that Chapter [Relations]({{ site.baseurl }}/Relations/)
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
{:/}

回忆我们在 [Relations]({{ site.baseurl }}/Relations/)
章节中将比较定义为一个归纳数据类型，其提供了一个数小于或等于另外一个数的证明：

{% raw %}<pre class="Agda"><a id="1743" class="Keyword">infix</a> <a id="1749" class="Number">4</a> <a id="1751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1761" class="Datatype Operator">_≤_</a>

<a id="1756" class="Keyword">data</a> <a id="_≤_"></a><a id="1761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1761" class="Datatype Operator">_≤_</a> <a id="1765" class="Symbol">:</a> <a id="1767" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1769" class="Symbol">→</a> <a id="1771" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1773" class="Symbol">→</a> <a id="1775" class="PrimitiveType">Set</a> <a id="1779" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1788" class="InductiveConstructor">z≤n</a> <a id="1792" class="Symbol">:</a> <a id="1794" class="Symbol">∀</a> <a id="1796" class="Symbol">{</a><a id="1797" href="plfa.part1.Decidable.html#1797" class="Bound">n</a> <a id="1799" class="Symbol">:</a> <a id="1801" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1802" class="Symbol">}</a>
      <a id="1810" class="Comment">--------</a>
    <a id="1823" class="Symbol">→</a> <a id="1825" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1761" class="Datatype Operator">≤</a> <a id="1832" href="plfa.part1.Decidable.html#1797" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1837" class="InductiveConstructor">s≤s</a> <a id="1841" class="Symbol">:</a> <a id="1843" class="Symbol">∀</a> <a id="1845" class="Symbol">{</a><a id="1846" href="plfa.part1.Decidable.html#1846" class="Bound">m</a> <a id="1848" href="plfa.part1.Decidable.html#1848" class="Bound">n</a> <a id="1850" class="Symbol">:</a> <a id="1852" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1853" class="Symbol">}</a>
    <a id="1859" class="Symbol">→</a> <a id="1861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1846" class="Bound">m</a> <a id="1863" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="1865" href="plfa.part1.Decidable.html#1848" class="Bound">n</a>
      <a id="1873" class="Comment">-------------</a>
    <a id="1891" class="Symbol">→</a> <a id="1893" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#1846" class="Bound">m</a> <a id="1899" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="1901" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1905" href="plfa.part1.Decidable.html#1848" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
{:/}

举例来说，我们提供 `2 ≤ 4` 成立的证明，也可以证明没有 `4 ≤ 2` 成立的证明。

{% raw %}<pre class="Agda"><a id="2≤4"></a><a id="2086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2086" class="Function">2≤4</a> <a id="2090" class="Symbol">:</a> <a id="2092" class="Number">2</a> <a id="2094" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="2096" class="Number">4</a>
<a id="2098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2086" class="Function">2≤4</a> <a id="2102" class="Symbol">=</a> <a id="2104" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="2108" class="Symbol">(</a><a id="2109" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="2113" href="plfa.part1.Decidable.html#1788" class="InductiveConstructor">z≤n</a><a id="2116" class="Symbol">)</a>

<a id="¬4≤2"></a><a id="2119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2119" class="Function">¬4≤2</a> <a id="2124" class="Symbol">:</a> <a id="2126" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="2128" class="Symbol">(</a><a id="2129" class="Number">4</a> <a id="2131" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="2133" class="Number">2</a><a id="2134" class="Symbol">)</a>
<a id="2136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2119" class="Function">¬4≤2</a> <a id="2141" class="Symbol">(</a><a id="2142" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="2146" class="Symbol">(</a><a id="2147" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="2151" class="Symbol">()))</a>
</pre>{% endraw %}
{::comment}
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).
{:/}

`()` 的出现表明了没有 `2 ≤ 0` 成立的证明：`z≤n` 不能匹配（因为 `2` 不是
`zero`），`s≤s` 也不能匹配（因为 `0` 不能匹配 `suc n`）。

{::comment}
An alternative, which may seem more familiar, is to define a
type of booleans:
{:/}

作为替代的定义，我们可以定义一个大家可能比较熟悉的布尔类型：

{% raw %}<pre class="Agda"><a id="2607" class="Keyword">data</a> <a id="Bool"></a><a id="2612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2612" class="Datatype">Bool</a> <a id="2617" class="Symbol">:</a> <a id="2619" class="PrimitiveType">Set</a> <a id="2623" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="2631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>  <a id="2637" class="Symbol">:</a> <a id="2639" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="2646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="InductiveConstructor">false</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
</pre>{% endraw %}
{::comment}
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
{:/}

给定了布尔类型，我们可以定义一个两个数的函数在比较关系成立时来*计算*出 `true`，否则计算出 `false`：

{% raw %}<pre class="Agda"><a id="2879" class="Keyword">infix</a> <a id="2885" class="Number">4</a> <a id="2887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">_≤ᵇ_</a>

<a id="_≤ᵇ_"></a><a id="2893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">_≤ᵇ_</a> <a id="2898" class="Symbol">:</a> <a id="2900" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2902" class="Symbol">→</a> <a id="2904" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2906" class="Symbol">→</a> <a id="2908" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="2913" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="2918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="2921" href="plfa.part1.Decidable.html#2921" class="Bound">n</a>       <a id="2929" class="Symbol">=</a>  <a id="2932" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="2937" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2941" class="Bound">m</a> <a id="2943" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="2946" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>   <a id="2953" class="Symbol">=</a>  <a id="2956" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
<a id="2962" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2966" class="Bound">m</a> <a id="2968" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="2971" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2975" href="plfa.part1.Decidable.html#2975" class="Bound">n</a>  <a id="2978" class="Symbol">=</a>  <a id="2981" href="plfa.part1.Decidable.html#2966" class="Bound">m</a> <a id="2983" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="2986" href="plfa.part1.Decidable.html#2975" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ᵇ 4` holds,
and we can compute that `4 ≤ᵇ 2` does not hold:
{:/}

定义中的第一条与最后一条与归纳数据类型中的两个构造子相对应。因为对于任意的 `m`，不可能出现
`suc m ≤ zero` 的证明，我们使用中间一条定义来表示。举个例子，我们可以计算 `2 ≤ᵇ 4` 成立，也可以计算 `4 ≤ᵇ 2` 不成立：

{% raw %}<pre class="Agda"><a id="3458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#3458" class="Function">_</a> <a id="3460" class="Symbol">:</a> <a id="3462" class="Symbol">(</a><a id="3463" class="Number">2</a> <a id="3465" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="3468" class="Number">4</a><a id="3469" class="Symbol">)</a> <a id="3471" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3473" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="3478" class="Symbol">_</a> <a id="3480" class="Symbol">=</a>
  <a id="3484" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3494" class="Number">2</a> <a id="3496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3499" class="Number">4</a>
  <a id="3503" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3511" class="Number">1</a> <a id="3513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3516" class="Number">3</a>
  <a id="3520" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3528" class="Number">0</a> <a id="3530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3533" class="Number">2</a>
  <a id="3537" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>
  <a id="3552" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>

<a id="3555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#3555" class="Function">_</a> <a id="3557" class="Symbol">:</a> <a id="3559" class="Symbol">(</a><a id="3560" class="Number">4</a> <a id="3562" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="3565" class="Number">2</a><a id="3566" class="Symbol">)</a> <a id="3568" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3570" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
<a id="3576" class="Symbol">_</a> <a id="3578" class="Symbol">=</a>
  <a id="3582" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3592" class="Number">4</a> <a id="3594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3597" class="Number">2</a>
  <a id="3601" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3609" class="Number">3</a> <a id="3611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3614" class="Number">1</a>
  <a id="3618" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3626" class="Number">2</a> <a id="3628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2893" class="Function Operator">≤ᵇ</a> <a id="3631" class="Number">0</a>
  <a id="3635" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="InductiveConstructor">false</a>
  <a id="3651" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.
{:/}

在第一种情况中，我们需要两步来将第一个参数降低到 0，再用一步来计算出真，这对应着我们需要使用两次 `s≤s` 和一次 `z≤n` 来证明 `2 ≤ 4`。在第二种情况中，我们需要两步来将第二个参数降低到 0，再用一步来计算出假，这对应着我们需要使用两次 `s≤s` 和一次 `()` 来说明没有 `4 ≤ 2` 的证明。

{::comment}
## Relating evidence and computation
{:/}

## 将证明与计算相联系

{::comment}
We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
{:/}

我们希望能够证明这两种方法是有联系的，而我们的确可以。首先，我们定义一个函数来把计算世界映射到证明世界：

{% raw %}<pre class="Agda"><a id="T"></a><a id="4612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#4612" class="Function">T</a> <a id="4614" class="Symbol">:</a> <a id="4616" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="4621" class="Symbol">→</a> <a id="4623" class="PrimitiveType">Set</a>
<a id="4627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#4612" class="Function">T</a> <a id="4629" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>   <a id="4636" class="Symbol">=</a>  <a id="4639" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a>
<a id="4641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#4612" class="Function">T</a> <a id="4643" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>  <a id="4650" class="Symbol">=</a>  <a id="4653" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}
{::comment}
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.
{:/}

回忆到 `⊤` 是只有一个元素 `tt` 的单元类型，`⊥` 是没有值的空类型。（注意 `T` 是大写字母 `t`，与 `⊤` 不同。）如果 `b` 是 `Bool` 类型的，那么如果 `b` 为真，`tt` 可以提供 `T b` 成立的证明；如果 `b` 为假，则不可能有 `T b` 成立的证明。

{::comment}
Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
{:/}

换句话说，`T b` 当且仅当 `b ≡ true` 成立时成立。在向前的方向，我们需要针对 `b` 进行情况分析：

{% raw %}<pre class="Agda"><a id="T→≡"></a><a id="5434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#5434" class="Function">T→≡</a> <a id="5438" class="Symbol">:</a> <a id="5440" class="Symbol">∀</a> <a id="5442" class="Symbol">(</a><a id="5443" href="plfa.part1.Decidable.html#5443" class="Bound">b</a> <a id="5445" class="Symbol">:</a> <a id="5447" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a><a id="5451" class="Symbol">)</a> <a id="5453" class="Symbol">→</a> <a id="5455" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="5457" href="plfa.part1.Decidable.html#5443" class="Bound">b</a> <a id="5459" class="Symbol">→</a> <a id="5461" href="plfa.part1.Decidable.html#5443" class="Bound">b</a> <a id="5463" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5465" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="5470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#5434" class="Function">T→≡</a> <a id="5474" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a> <a id="5479" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>   <a id="5484" class="Symbol">=</a>  <a id="5487" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="5492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#5434" class="Function">T→≡</a> <a id="5496" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a> <a id="5502" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.
{:/}

如果 `b` 为真，那么 `T b` 由 `tt` 证明，`b ≡ true` 由 `refl` 证明。当 `b` 为假，那么 `T b` 无法证明。

{::comment}
In the reverse direction, there is no need for a case analysis on the boolean `b`:
{:/}

在向后的方向，不需要针对布尔值 `b` 的情况分析：

{% raw %}<pre class="Agda"><a id="≡→T"></a><a id="5874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#5874" class="Function">≡→T</a> <a id="5878" class="Symbol">:</a> <a id="5880" class="Symbol">∀</a> <a id="5882" class="Symbol">{</a><a id="5883" href="plfa.part1.Decidable.html#5883" class="Bound">b</a> <a id="5885" class="Symbol">:</a> <a id="5887" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a><a id="5891" class="Symbol">}</a> <a id="5893" class="Symbol">→</a> <a id="5895" href="plfa.part1.Decidable.html#5883" class="Bound">b</a> <a id="5897" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5899" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a> <a id="5904" class="Symbol">→</a> <a id="5906" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="5908" href="plfa.part1.Decidable.html#5883" class="Bound">b</a>
<a id="5910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#5874" class="Function">≡→T</a> <a id="5914" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>  <a id="5920" class="Symbol">=</a>  <a id="5923" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
</pre>{% endraw %}
{::comment}
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.
{:/}

如果 `b ≡ true` 由 `refl` 证明，我们知道 `b` 是 `true`，因此 `T b` 由 `tt` 证明。

{::comment}
Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.
{:/}

现在我们可以证明 `T (m ≤ᵇ n)` 当且仅当 `m ≤ n` 成立时成立。

{::comment}
In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
{:/}

在向前的方向，我们考虑 `_≤ᵇ_` 定义中的三条语句：

{% raw %}<pre class="Agda"><a id="≤ᵇ→≤"></a><a id="6396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#6396" class="Function">≤ᵇ→≤</a> <a id="6401" class="Symbol">:</a> <a id="6403" class="Symbol">∀</a> <a id="6405" class="Symbol">(</a><a id="6406" href="plfa.part1.Decidable.html#6406" class="Bound">m</a> <a id="6408" href="plfa.part1.Decidable.html#6408" class="Bound">n</a> <a id="6410" class="Symbol">:</a> <a id="6412" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="6413" class="Symbol">)</a> <a id="6415" class="Symbol">→</a> <a id="6417" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="6419" class="Symbol">(</a><a id="6420" href="plfa.part1.Decidable.html#6406" class="Bound">m</a> <a id="6422" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="6425" href="plfa.part1.Decidable.html#6408" class="Bound">n</a><a id="6426" class="Symbol">)</a> <a id="6428" class="Symbol">→</a> <a id="6430" href="plfa.part1.Decidable.html#6406" class="Bound">m</a> <a id="6432" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="6434" href="plfa.part1.Decidable.html#6408" class="Bound">n</a>
<a id="6436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#6396" class="Function">≤ᵇ→≤</a> <a id="6441" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6449" href="plfa.part1.Decidable.html#6449" class="Bound">n</a>       <a id="6457" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="6461" class="Symbol">=</a>  <a id="6464" href="plfa.part1.Decidable.html#1788" class="InductiveConstructor">z≤n</a>
<a id="6468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#6396" class="Function">≤ᵇ→≤</a> <a id="6473" class="Symbol">(</a><a id="6474" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6478" href="plfa.part1.Decidable.html#6478" class="Bound">m</a><a id="6479" class="Symbol">)</a> <a id="6481" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6489" class="Symbol">()</a>
<a id="6492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#6396" class="Function">≤ᵇ→≤</a> <a id="6497" class="Symbol">(</a><a id="6498" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6502" href="plfa.part1.Decidable.html#6502" class="Bound">m</a><a id="6503" class="Symbol">)</a> <a id="6505" class="Symbol">(</a><a id="6506" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6510" href="plfa.part1.Decidable.html#6510" class="Bound">n</a><a id="6511" class="Symbol">)</a> <a id="6513" href="plfa.part1.Decidable.html#6513" class="Bound">t</a>   <a id="6517" class="Symbol">=</a>  <a id="6520" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="6524" class="Symbol">(</a><a id="6525" href="plfa.part1.Decidable.html#6396" class="Function">≤ᵇ→≤</a> <a id="6530" href="plfa.part1.Decidable.html#6502" class="Bound">m</a> <a id="6532" href="plfa.part1.Decidable.html#6510" class="Bound">n</a> <a id="6534" href="plfa.part1.Decidable.html#6513" class="Bound">t</a><a id="6535" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have that `suc m ≤ᵇ suc n` recurses
to `m ≤ᵇ n`.  We let `t` be the evidence of `T (suc m ≤ᵇ suc n)` if it exists,
which, by definition of `_≤ᵇ_`, will also be evidence of `T (m ≤ᵇ n)`.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.
{:/}

第一条语句中，我们立即可以得出 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 而得，相对应地 `m ≤ n` 由 `z≤n` 而证明。在中间的语句中，我们立刻得出 `suc m ≤ᵇ zero` 为假，则
`T (m ≤ᵇ n)` 为空，因此我们无需证明 `m ≤ n`，同时也不存在这样的证明。在最后的语句中，我们对于
`suc m ≤ᵇ suc n` 递归至 `m ≤ᵇ n`。令 `t` 为 `T (suc m ≤ᵇ suc n)` 的证明，如果其存在。根据 `_≤ᵇ_` 的定义，这也是 `T (m ≤ᵇ n)` 的证明。我们递归地应用函数来获得 `m ≤ n` 的证明，再使用
`s≤s` 将其转换成为 `suc m ≤ suc n` 的证明。

{::comment}
In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
{:/}

在向后的方向，我们考虑 `m ≤ n` 成立证明的可能形式：

{% raw %}<pre class="Agda"><a id="≤→≤ᵇ"></a><a id="7736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#7736" class="Function">≤→≤ᵇ</a> <a id="7741" class="Symbol">:</a> <a id="7743" class="Symbol">∀</a> <a id="7745" class="Symbol">{</a><a id="7746" href="plfa.part1.Decidable.html#7746" class="Bound">m</a> <a id="7748" href="plfa.part1.Decidable.html#7748" class="Bound">n</a> <a id="7750" class="Symbol">:</a> <a id="7752" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7753" class="Symbol">}</a> <a id="7755" class="Symbol">→</a> <a id="7757" href="plfa.part1.Decidable.html#7746" class="Bound">m</a> <a id="7759" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="7761" href="plfa.part1.Decidable.html#7748" class="Bound">n</a> <a id="7763" class="Symbol">→</a> <a id="7765" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="7767" class="Symbol">(</a><a id="7768" href="plfa.part1.Decidable.html#7746" class="Bound">m</a> <a id="7770" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="7773" href="plfa.part1.Decidable.html#7748" class="Bound">n</a><a id="7774" class="Symbol">)</a>
<a id="7776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#7736" class="Function">≤→≤ᵇ</a> <a id="7781" href="plfa.part1.Decidable.html#1788" class="InductiveConstructor">z≤n</a>        <a id="7792" class="Symbol">=</a>  <a id="7795" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="7798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#7736" class="Function">≤→≤ᵇ</a> <a id="7803" class="Symbol">(</a><a id="7804" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="7808" href="plfa.part1.Decidable.html#7808" class="Bound">m≤n</a><a id="7811" class="Symbol">)</a>  <a id="7814" class="Symbol">=</a>  <a id="7817" href="plfa.part1.Decidable.html#7736" class="Function">≤→≤ᵇ</a> <a id="7822" href="plfa.part1.Decidable.html#7808" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.
{:/}

如果证明是 `z≤n`，我们立即可以得到 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 证明。如果证明是 `s≤s` 作用于 `m≤n`，那么 `suc m ≤ᵇ suc n` 规约到 `m ≤ᵇ n`，我们可以递归地使用函数来获得 `T (m ≤ᵇ n)` 的证明。

{::comment}
The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.
{:/}

向前方向的证明比向后方向的证明多一条语句，因为在向前方向的证明中我们需要考虑比较结果为真和假的语句，而向后方向的证明只需要考虑比较成立的语句。这也是为什么我们比起计算的形式，更加偏爱证明的形式，因为这样让我们做更少的工作：我们只需要考虑关系成立时的情况，而可以忽略不成立的情况。

{::comment}
On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.
{:/}

从另一个角度来说，有时计算的性质可能正是我们所需要的。面对一个大数值上的非显然关系，使用电脑来计算出答案可能会更加方便。幸运的是，比起在*证明*或*计算*之中犹豫，我们有一种更好的方法来兼取其优。

{::comment}
## The best of both worlds
{:/}

## 取二者之精华

{::comment}
A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
{:/}

一个返回布尔值的函数提供恰好一比特的信息：这个关系成立或是不成立。相反地，证明的形式告诉我们为什么这个关系成立，但却需要我们自行完成这个证明。不过，我们其实可以简单地定义一个类型来取二者之精华。我们把它叫做：`Dec A`，其中 `Dec` 是*可判定的*（Decidable）的意思。

{% raw %}<pre class="Agda"><a id="10019" class="Keyword">data</a> <a id="Dec"></a><a id="10024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10024" class="Datatype">Dec</a> <a id="10028" class="Symbol">(</a><a id="10029" href="plfa.part1.Decidable.html#10029" class="Bound">A</a> <a id="10031" class="Symbol">:</a> <a id="10033" class="PrimitiveType">Set</a><a id="10036" class="Symbol">)</a> <a id="10038" class="Symbol">:</a> <a id="10040" class="PrimitiveType">Set</a> <a id="10044" class="Keyword">where</a>
  <a id="Dec.yes"></a><a id="10052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10052" class="InductiveConstructor">yes</a> <a id="10056" class="Symbol">:</a>   <a id="10060" href="plfa.part1.Decidable.html#10029" class="Bound">A</a> <a id="10062" class="Symbol">→</a> <a id="10064" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="10068" href="plfa.part1.Decidable.html#10029" class="Bound">A</a>
  <a id="Dec.no"></a><a id="10072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10072" class="InductiveConstructor">no</a>  <a id="10076" class="Symbol">:</a> <a id="10078" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10080" href="plfa.part1.Decidable.html#10029" class="Bound">A</a> <a id="10082" class="Symbol">→</a> <a id="10084" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="10088" href="plfa.part1.Decidable.html#10029" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).
{:/}

正如布尔值，这个类型有两个构造子。一个 `Dec A` 类型的值要么是以 `yes x` 的形式，其中 `x` 提供 `A`
成立的证明，或者是以 `no ¬x` 的形式，其中 `x` 提供了 `A` 无法成立的证明。（也就是说，`¬x` 是一个给定
`A` 成立的证据，返回矛盾的函数）

{::comment}
For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.
{:/}

比如说，我们定义一个函数 `_≤?_`，给定两个数，判定是否一个数小于等于另一个，并提供证明来说明结论。

{::comment}
First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
{:/}

首先，我们使用两个有用的函数，用于构造不等式不成立的证明：

{% raw %}<pre class="Agda"><a id="¬s≤z"></a><a id="10957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10957" class="Function">¬s≤z</a> <a id="10962" class="Symbol">:</a> <a id="10964" class="Symbol">∀</a> <a id="10966" class="Symbol">{</a><a id="10967" href="plfa.part1.Decidable.html#10967" class="Bound">m</a> <a id="10969" class="Symbol">:</a> <a id="10971" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10972" class="Symbol">}</a> <a id="10974" class="Symbol">→</a> <a id="10976" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10978" class="Symbol">(</a><a id="10979" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10983" href="plfa.part1.Decidable.html#10967" class="Bound">m</a> <a id="10985" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="10987" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="10991" class="Symbol">)</a>
<a id="10993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10957" class="Function">¬s≤z</a> <a id="10998" class="Symbol">()</a>

<a id="¬s≤s"></a><a id="11002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#11002" class="Function">¬s≤s</a> <a id="11007" class="Symbol">:</a> <a id="11009" class="Symbol">∀</a> <a id="11011" class="Symbol">{</a><a id="11012" href="plfa.part1.Decidable.html#11012" class="Bound">m</a> <a id="11014" href="plfa.part1.Decidable.html#11014" class="Bound">n</a> <a id="11016" class="Symbol">:</a> <a id="11018" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11019" class="Symbol">}</a> <a id="11021" class="Symbol">→</a> <a id="11023" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="11025" class="Symbol">(</a><a id="11026" href="plfa.part1.Decidable.html#11012" class="Bound">m</a> <a id="11028" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="11030" href="plfa.part1.Decidable.html#11014" class="Bound">n</a><a id="11031" class="Symbol">)</a> <a id="11033" class="Symbol">→</a> <a id="11035" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="11037" class="Symbol">(</a><a id="11038" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11042" href="plfa.part1.Decidable.html#11012" class="Bound">m</a> <a id="11044" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="11046" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11050" href="plfa.part1.Decidable.html#11014" class="Bound">n</a><a id="11051" class="Symbol">)</a>
<a id="11053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#11002" class="Function">¬s≤s</a> <a id="11058" href="plfa.part1.Decidable.html#11058" class="Bound">¬m≤n</a> <a id="11063" class="Symbol">(</a><a id="11064" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="11068" href="plfa.part1.Decidable.html#11068" class="Bound">m≤n</a><a id="11071" class="Symbol">)</a> <a id="11073" class="Symbol">=</a> <a id="11075" href="plfa.part1.Decidable.html#11058" class="Bound">¬m≤n</a> <a id="11080" href="plfa.part1.Decidable.html#11068" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.
{:/}

第一个函数断言了 `¬ (suc m ≤ zero)`，由荒谬可得。因为每个不等式的成立证明必须是
`zero ≤ n` 或者 `suc m ≤ suc n` 的形式，两者都无法匹配 `suc m ≤ zero`。第二个函数取 `¬ (m ≤ n)` 的证明 `¬m≤n`，返回 `¬ (suc m ≤ suc n)` 的证明。所有形如 `suc m ≤ suc n` 的证明必须是以 `s≤s m≤n` 的形式给出。因此我们可以构造一个矛盾，以 `¬m≤n m≤n` 来证明。

{::comment}
Using these, it is straightforward to decide an inequality:
{:/}

使用这些，我们可以直接的判定不等关系：

{% raw %}<pre class="Agda"><a id="_≤?_"></a><a id="11907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#11907" class="Function Operator">_≤?_</a> <a id="11912" class="Symbol">:</a> <a id="11914" class="Symbol">∀</a> <a id="11916" class="Symbol">(</a><a id="11917" href="plfa.part1.Decidable.html#11917" class="Bound">m</a> <a id="11919" href="plfa.part1.Decidable.html#11919" class="Bound">n</a> <a id="11921" class="Symbol">:</a> <a id="11923" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11924" class="Symbol">)</a> <a id="11926" class="Symbol">→</a> <a id="11928" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="11932" class="Symbol">(</a><a id="11933" href="plfa.part1.Decidable.html#11917" class="Bound">m</a> <a id="11935" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="11937" href="plfa.part1.Decidable.html#11919" class="Bound">n</a><a id="11938" class="Symbol">)</a>
<a id="11940" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="11946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#11907" class="Function Operator">≤?</a> <a id="11949" href="plfa.part1.Decidable.html#11949" class="Bound">n</a>                   <a id="11969" class="Symbol">=</a>  <a id="11972" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="11976" href="plfa.part1.Decidable.html#1788" class="InductiveConstructor">z≤n</a>
<a id="11980" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#11984" class="Bound">m</a> <a id="11986" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="11989" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                <a id="12009" class="Symbol">=</a>  <a id="12012" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="12015" href="plfa.part1.Decidable.html#10957" class="Function">¬s≤z</a>
<a id="12020" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#12024" class="Bound">m</a> <a id="12026" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="12029" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12033" href="plfa.part1.Decidable.html#12033" class="Bound">n</a> <a id="12035" class="Keyword">with</a> <a id="12040" href="plfa.part1.Decidable.html#12024" class="Bound">m</a> <a id="12042" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="12045" href="plfa.part1.Decidable.html#12033" class="Bound">n</a>
<a id="12047" class="Symbol">...</a>               <a id="12065" class="Symbol">|</a> <a id="12067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10052" class="InductiveConstructor">yes</a> <a id="12071" href="plfa.part1.Decidable.html#12071" class="Bound">m≤n</a>  <a id="12076" class="Symbol">=</a>  <a id="12079" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="12083" class="Symbol">(</a><a id="12084" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="12088" href="plfa.part1.Decidable.html#12071" class="Bound">m≤n</a><a id="12091" class="Symbol">)</a>
<a id="12093" class="Symbol">...</a>               <a id="12111" class="Symbol">|</a> <a id="12113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10072" class="InductiveConstructor">no</a> <a id="12116" href="plfa.part1.Decidable.html#12116" class="Bound">¬m≤n</a>  <a id="12122" class="Symbol">=</a>  <a id="12125" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="12128" class="Symbol">(</a><a id="12129" href="plfa.part1.Decidable.html#11002" class="Function">¬s≤s</a> <a id="12134" href="plfa.part1.Decidable.html#12116" class="Bound">¬m≤n</a><a id="12138" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ zero` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.
{:/}

与 `_≤ᵇ_` 一样，定义有三条语句。第一条语句中，`zero ≤ n` 立即成立，由 `z≤n` 证明。第二条语句中，`suc m ≤ zero` 立即不成立，由 `¬s≤z` 证明。第三条语句中，我们需要递归地应用 `m ≤? n`。有两种可能性，在 `yes` 的情况中，它会返回
`m ≤ n` 的证明 `m≤n`，所以 `s≤s m≤n` 即可作为 `suc m ≤ suc n` 的证明；在 `no` 的情况中，它会返回 `¬ (m ≤ n)` 的证明 `¬m≤n`，所以 `¬s≤s ¬m≤n` 即可作为 `¬ (suc m ≤ suc n)` 的证明。

{::comment}
When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.
{:/}

当我们写 `_≤ᵇ_` 时，我们必须写两个其他的函数 `≤ᵇ→≤` 和 `≤→≤ᵇ` 来证明其正确性。作为对比，`_≤?_` 的定义自身就证明了其正确性，由类型即可得知。`_≤?_` 的代码也比
`_≤ᵇ_`、`≤ᵇ→≤` 和 `≤→≤ᵇ` 加起来要简洁的多。我们稍后将会证明，如果我们需要后三者，我们亦可简单地从 `_≤?_` 中派生出来。

{::comment}
We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
{:/}

我们可以使用我们新的函数来*计算*出我们之前需要自己想出来的*证明*。

{% raw %}<pre class="Agda"><a id="13809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#13809" class="Function">_</a> <a id="13811" class="Symbol">:</a> <a id="13813" class="Number">2</a> <a id="13815" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="13818" class="Number">4</a> <a id="13820" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13822" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="13826" class="Symbol">(</a><a id="13827" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="13831" class="Symbol">(</a><a id="13832" href="plfa.part1.Decidable.html#1837" class="InductiveConstructor">s≤s</a> <a id="13836" href="plfa.part1.Decidable.html#1788" class="InductiveConstructor">z≤n</a><a id="13839" class="Symbol">))</a>
<a id="13842" class="Symbol">_</a> <a id="13844" class="Symbol">=</a> <a id="13846" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="13852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#13852" class="Function">_</a> <a id="13854" class="Symbol">:</a> <a id="13856" class="Number">4</a> <a id="13858" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="13861" class="Number">2</a> <a id="13863" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13865" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="13868" class="Symbol">(</a><a id="13869" href="plfa.part1.Decidable.html#11002" class="Function">¬s≤s</a> <a id="13874" class="Symbol">(</a><a id="13875" href="plfa.part1.Decidable.html#11002" class="Function">¬s≤s</a> <a id="13880" href="plfa.part1.Decidable.html#10957" class="Function">¬s≤z</a><a id="13884" class="Symbol">))</a>
<a id="13887" class="Symbol">_</a> <a id="13889" class="Symbol">=</a> <a id="13891" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.
{:/}

你可以验证 Agda 的确计算出了这些值。输入 `C-c C-n` 并给出 `2 ≤? 4` 或者 `4 ≤? 2` 作为需要的表达式，Agda 会输出如上的值。

{::comment}
(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)
{:/}

（小细节：如果我们不把 `¬s≤z` 和 `¬s≤s` 作为顶层函数来定义，而是使用内嵌的匿名函数，
Agda 可能会在规范化否定的证明中出现问题。）


{::comment}
#### Exercise `_<?_` (recommended)
{:/}

#### 练习 `_<?_` （推荐）

{::comment}
Analogous to the function above, define a function to decide strict inequality:
{:/}

与上面的函数相似，定义一个判定严格不等性的函数：

{% raw %}<pre class="Agda"><a id="14665" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="14677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#14677" class="Postulate Operator">_&lt;?_</a> <a id="14682" class="Symbol">:</a> <a id="14684" class="Symbol">∀</a> <a id="14686" class="Symbol">(</a><a id="14687" href="plfa.part1.Decidable.html#14687" class="Bound">m</a> <a id="14689" href="plfa.part1.Decidable.html#14689" class="Bound">n</a> <a id="14691" class="Symbol">:</a> <a id="14693" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14694" class="Symbol">)</a> <a id="14696" class="Symbol">→</a> <a id="14698" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="14702" class="Symbol">(</a><a id="14703" href="plfa.part1.Decidable.html#14687" class="Bound">m</a> <a id="14705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#26539" class="Datatype Operator">&lt;</a> <a id="14707" href="plfa.part1.Decidable.html#14689" class="Bound">n</a><a id="14708" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14731" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="14768" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_≡ℕ?_` (practice)
{:/}

#### 练习 `_≡ℕ?_`（实践）

{::comment}
Define a function to decide whether two naturals are equal:
{:/}

定义一个函数来判定两个自然数是否相等。

{% raw %}<pre class="Agda"><a id="14961" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="14973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#14973" class="Postulate Operator">_≡ℕ?_</a> <a id="14979" class="Symbol">:</a> <a id="14981" class="Symbol">∀</a> <a id="14983" class="Symbol">(</a><a id="14984" href="plfa.part1.Decidable.html#14984" class="Bound">m</a> <a id="14986" href="plfa.part1.Decidable.html#14986" class="Bound">n</a> <a id="14988" class="Symbol">:</a> <a id="14990" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14991" class="Symbol">)</a> <a id="14993" class="Symbol">→</a> <a id="14995" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="14999" class="Symbol">(</a><a id="15000" href="plfa.part1.Decidable.html#14984" class="Bound">m</a> <a id="15002" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15004" href="plfa.part1.Decidable.html#14986" class="Bound">n</a><a id="15005" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="15028" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15065" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Decidables from booleans, and booleans from decidables
{:/}

## 从可判定的值到布尔值，从布尔值到可判定的值

{::comment}
Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
{:/}

好奇的读者可能会思考能不能重用 `m ≤ᵇ n` 的定义，加上它与 `m ≤ n` 等价的证明，来证明可判定性。的确，我们是可以做到的：

{% raw %}<pre class="Agda"><a id="_≤?′_"></a><a id="15469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#15469" class="Function Operator">_≤?′_</a> <a id="15475" class="Symbol">:</a> <a id="15477" class="Symbol">∀</a> <a id="15479" class="Symbol">(</a><a id="15480" href="plfa.part1.Decidable.html#15480" class="Bound">m</a> <a id="15482" href="plfa.part1.Decidable.html#15482" class="Bound">n</a> <a id="15484" class="Symbol">:</a> <a id="15486" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15487" class="Symbol">)</a> <a id="15489" class="Symbol">→</a> <a id="15491" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="15495" class="Symbol">(</a><a id="15496" href="plfa.part1.Decidable.html#15480" class="Bound">m</a> <a id="15498" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="15500" href="plfa.part1.Decidable.html#15482" class="Bound">n</a><a id="15501" class="Symbol">)</a>
<a id="15503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#15503" class="Bound">m</a> <a id="15505" href="plfa.part1.Decidable.html#15469" class="Function Operator">≤?′</a> <a id="15509" href="plfa.part1.Decidable.html#15509" class="Bound">n</a> <a id="15511" class="Keyword">with</a> <a id="15516" href="plfa.part1.Decidable.html#15503" class="Bound">m</a> <a id="15518" href="plfa.part1.Decidable.html#2893" class="Function Operator">≤ᵇ</a> <a id="15521" href="plfa.part1.Decidable.html#15509" class="Bound">n</a> <a id="15523" class="Symbol">|</a> <a id="15525" href="plfa.part1.Decidable.html#6396" class="Function">≤ᵇ→≤</a> <a id="15530" href="plfa.part1.Decidable.html#15503" class="Bound">m</a> <a id="15532" href="plfa.part1.Decidable.html#15509" class="Bound">n</a> <a id="15534" class="Symbol">|</a> <a id="15536" href="plfa.part1.Decidable.html#7736" class="Function">≤→≤ᵇ</a> <a id="15541" class="Symbol">{</a><a id="15542" href="plfa.part1.Decidable.html#15503" class="Bound">m</a><a id="15543" class="Symbol">}</a> <a id="15545" class="Symbol">{</a><a id="15546" href="plfa.part1.Decidable.html#15509" class="Bound">n</a><a id="15547" class="Symbol">}</a>
<a id="15549" class="Symbol">...</a>        <a id="15560" class="Symbol">|</a> <a id="15562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>   <a id="15569" class="Symbol">|</a> <a id="15571" href="plfa.part1.Decidable.html#15571" class="Bound">p</a>        <a id="15580" class="Symbol">|</a> <a id="15582" class="Symbol">_</a>            <a id="15595" class="Symbol">=</a> <a id="15597" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="15601" class="Symbol">(</a><a id="15602" href="plfa.part1.Decidable.html#15571" class="Bound">p</a> <a id="15604" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="15606" class="Symbol">)</a>
<a id="15608" class="Symbol">...</a>        <a id="15619" class="Symbol">|</a> <a id="15621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="InductiveConstructor">false</a>  <a id="15628" class="Symbol">|</a> <a id="15630" class="Symbol">_</a>        <a id="15639" class="Symbol">|</a> <a id="15641" href="plfa.part1.Decidable.html#15641" class="Bound">¬p</a>           <a id="15654" class="Symbol">=</a> <a id="15656" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="15659" href="plfa.part1.Decidable.html#15641" class="Bound">¬p</a>
</pre>{% endraw %}
{::comment}
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.
{:/}

如果 `m ≤ᵇ n` 为真，那么 `≤ᵇ→≤` 会返回一个 `m ≤ n` 成立的证明。如果 `m ≤ᵇ n` 为假，那么 `≤→≤ᵇ` 会取一个 `m ≤ n` 成立的证明，将其转换为一个矛盾。

{::comment}
The triple binding of the `with` clause in this proof is essential.
If instead we wrote:
{:/}

在这个证明中，`with` 语句的三重约束是必须的。如果我们取而代之的写：

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

{::comment}
then Agda would make two complaints, one for each clause:
{:/}

那么 Agda 对于每条语句会有一个抱怨：

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

{::comment}
Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.
{:/}

将表达式放在 `with` 语句中能让 Agda 利用下列事实：当 `m ≤ᵇ n` 为真时，`T (m ≤ᵇ n)` 是
`⊤`；当 `m ≤ᵇ n` 为假时，`T (m ≤ᵇ n)` 是 `⊥`。

{::comment}
However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.
{:/}

然而，总体来说还是直接定义 `_≤?_` 比较方便，正如之前部分中那样。如果有人真的很需要 `_≤ᵇ_`，那么它和它的性质可以简单地从 `_≤?_` 中派生出来，正如我们接下来要展示的一样。

{::comment}
Erasure takes a decidable value to a boolean:
{:/}

擦除（Erasure）将一个可判定的值转换为一个布尔值：

{% raw %}<pre class="Agda"><a id="⌊_⌋"></a><a id="17240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17240" class="Function Operator">⌊_⌋</a> <a id="17244" class="Symbol">:</a> <a id="17246" class="Symbol">∀</a> <a id="17248" class="Symbol">{</a><a id="17249" href="plfa.part1.Decidable.html#17249" class="Bound">A</a> <a id="17251" class="Symbol">:</a> <a id="17253" class="PrimitiveType">Set</a><a id="17256" class="Symbol">}</a> <a id="17258" class="Symbol">→</a> <a id="17260" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="17264" href="plfa.part1.Decidable.html#17249" class="Bound">A</a> <a id="17266" class="Symbol">→</a> <a id="17268" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="17273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17240" class="Function Operator">⌊</a> <a id="17275" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="17279" href="plfa.part1.Decidable.html#17279" class="Bound">x</a> <a id="17281" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>  <a id="17284" class="Symbol">=</a>  <a id="17287" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="17292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17240" class="Function Operator">⌊</a> <a id="17294" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="17297" href="plfa.part1.Decidable.html#17297" class="Bound">¬x</a> <a id="17300" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>  <a id="17303" class="Symbol">=</a>  <a id="17306" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
{:/}

使用擦除，我们可以简单地从 `_≤?_` 中派生出 `_≤ᵇ_`：

{% raw %}<pre class="Agda"><a id="_≤ᵇ′_"></a><a id="17430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17430" class="Function Operator">_≤ᵇ′_</a> <a id="17436" class="Symbol">:</a> <a id="17438" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17440" class="Symbol">→</a> <a id="17442" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17444" class="Symbol">→</a> <a id="17446" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="17451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17451" class="Bound">m</a> <a id="17453" href="plfa.part1.Decidable.html#17430" class="Function Operator">≤ᵇ′</a> <a id="17457" href="plfa.part1.Decidable.html#17457" class="Bound">n</a>  <a id="17460" class="Symbol">=</a>  <a id="17463" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="17465" href="plfa.part1.Decidable.html#17451" class="Bound">m</a> <a id="17467" href="plfa.part1.Decidable.html#11907" class="Function Operator">≤?</a> <a id="17470" href="plfa.part1.Decidable.html#17457" class="Bound">n</a> <a id="17472" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
{:/}

更进一步来说，如果 `D` 是一个类型为 `Dec A` 的值，那么 `T ⌊ D ⌋`
当且仅当 `A` 成立时成立：
{% raw %}<pre class="Agda"><a id="toWitness"></a><a id="17665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17665" class="Function">toWitness</a> <a id="17675" class="Symbol">:</a> <a id="17677" class="Symbol">∀</a> <a id="17679" class="Symbol">{</a><a id="17680" href="plfa.part1.Decidable.html#17680" class="Bound">A</a> <a id="17682" class="Symbol">:</a> <a id="17684" class="PrimitiveType">Set</a><a id="17687" class="Symbol">}</a> <a id="17689" class="Symbol">{</a><a id="17690" href="plfa.part1.Decidable.html#17690" class="Bound">D</a> <a id="17692" class="Symbol">:</a> <a id="17694" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="17698" href="plfa.part1.Decidable.html#17680" class="Bound">A</a><a id="17699" class="Symbol">}</a> <a id="17701" class="Symbol">→</a> <a id="17703" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="17705" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="17707" href="plfa.part1.Decidable.html#17690" class="Bound">D</a> <a id="17709" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="17711" class="Symbol">→</a> <a id="17713" href="plfa.part1.Decidable.html#17680" class="Bound">A</a>
<a id="17715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17665" class="Function">toWitness</a> <a id="17725" class="Symbol">{</a><a id="17726" href="plfa.part1.Decidable.html#17726" class="Bound">A</a><a id="17727" class="Symbol">}</a> <a id="17729" class="Symbol">{</a><a id="17730" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="17734" href="plfa.part1.Decidable.html#17734" class="Bound">x</a><a id="17735" class="Symbol">}</a> <a id="17737" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="17741" class="Symbol">=</a>  <a id="17744" href="plfa.part1.Decidable.html#17734" class="Bound">x</a>
<a id="17746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17665" class="Function">toWitness</a> <a id="17756" class="Symbol">{</a><a id="17757" href="plfa.part1.Decidable.html#17757" class="Bound">A</a><a id="17758" class="Symbol">}</a> <a id="17760" class="Symbol">{</a><a id="17761" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="17764" href="plfa.part1.Decidable.html#17764" class="Bound">¬x</a><a id="17766" class="Symbol">}</a> <a id="17768" class="Symbol">()</a>

<a id="fromWitness"></a><a id="17772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17772" class="Function">fromWitness</a> <a id="17784" class="Symbol">:</a> <a id="17786" class="Symbol">∀</a> <a id="17788" class="Symbol">{</a><a id="17789" href="plfa.part1.Decidable.html#17789" class="Bound">A</a> <a id="17791" class="Symbol">:</a> <a id="17793" class="PrimitiveType">Set</a><a id="17796" class="Symbol">}</a> <a id="17798" class="Symbol">{</a><a id="17799" href="plfa.part1.Decidable.html#17799" class="Bound">D</a> <a id="17801" class="Symbol">:</a> <a id="17803" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="17807" href="plfa.part1.Decidable.html#17789" class="Bound">A</a><a id="17808" class="Symbol">}</a> <a id="17810" class="Symbol">→</a> <a id="17812" href="plfa.part1.Decidable.html#17789" class="Bound">A</a> <a id="17814" class="Symbol">→</a> <a id="17816" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="17818" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="17820" href="plfa.part1.Decidable.html#17799" class="Bound">D</a> <a id="17822" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
<a id="17824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17772" class="Function">fromWitness</a> <a id="17836" class="Symbol">{</a><a id="17837" href="plfa.part1.Decidable.html#17837" class="Bound">A</a><a id="17838" class="Symbol">}</a> <a id="17840" class="Symbol">{</a><a id="17841" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="17845" href="plfa.part1.Decidable.html#17845" class="Bound">x</a><a id="17846" class="Symbol">}</a> <a id="17848" class="Symbol">_</a>  <a id="17851" class="Symbol">=</a>  <a id="17854" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="17857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#17772" class="Function">fromWitness</a> <a id="17869" class="Symbol">{</a><a id="17870" href="plfa.part1.Decidable.html#17870" class="Bound">A</a><a id="17871" class="Symbol">}</a> <a id="17873" class="Symbol">{</a><a id="17874" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="17877" href="plfa.part1.Decidable.html#17877" class="Bound">¬x</a><a id="17879" class="Symbol">}</a> <a id="17881" href="plfa.part1.Decidable.html#17881" class="Bound">x</a>  <a id="17884" class="Symbol">=</a>  <a id="17887" href="plfa.part1.Decidable.html#17877" class="Bound">¬x</a> <a id="17890" href="plfa.part1.Decidable.html#17881" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
{:/}

使用这些，我们可以简单地派生出 `T (m ≤ᵇ′ n)` 当且仅当 `m ≤ n` 成立时成立。

{% raw %}<pre class="Agda"><a id="≤ᵇ′→≤"></a><a id="18071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18071" class="Function">≤ᵇ′→≤</a> <a id="18077" class="Symbol">:</a> <a id="18079" class="Symbol">∀</a> <a id="18081" class="Symbol">{</a><a id="18082" href="plfa.part1.Decidable.html#18082" class="Bound">m</a> <a id="18084" href="plfa.part1.Decidable.html#18084" class="Bound">n</a> <a id="18086" class="Symbol">:</a> <a id="18088" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18089" class="Symbol">}</a> <a id="18091" class="Symbol">→</a> <a id="18093" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="18095" class="Symbol">(</a><a id="18096" href="plfa.part1.Decidable.html#18082" class="Bound">m</a> <a id="18098" href="plfa.part1.Decidable.html#17430" class="Function Operator">≤ᵇ′</a> <a id="18102" href="plfa.part1.Decidable.html#18084" class="Bound">n</a><a id="18103" class="Symbol">)</a> <a id="18105" class="Symbol">→</a> <a id="18107" href="plfa.part1.Decidable.html#18082" class="Bound">m</a> <a id="18109" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="18111" href="plfa.part1.Decidable.html#18084" class="Bound">n</a>
<a id="18113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18071" class="Function">≤ᵇ′→≤</a>  <a id="18120" class="Symbol">=</a>  <a id="18123" href="plfa.part1.Decidable.html#17665" class="Function">toWitness</a>

<a id="≤→≤ᵇ′"></a><a id="18134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18134" class="Function">≤→≤ᵇ′</a> <a id="18140" class="Symbol">:</a> <a id="18142" class="Symbol">∀</a> <a id="18144" class="Symbol">{</a><a id="18145" href="plfa.part1.Decidable.html#18145" class="Bound">m</a> <a id="18147" href="plfa.part1.Decidable.html#18147" class="Bound">n</a> <a id="18149" class="Symbol">:</a> <a id="18151" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18152" class="Symbol">}</a> <a id="18154" class="Symbol">→</a> <a id="18156" href="plfa.part1.Decidable.html#18145" class="Bound">m</a> <a id="18158" href="plfa.part1.Decidable.html#1761" class="Datatype Operator">≤</a> <a id="18160" href="plfa.part1.Decidable.html#18147" class="Bound">n</a> <a id="18162" class="Symbol">→</a> <a id="18164" href="plfa.part1.Decidable.html#4612" class="Function">T</a> <a id="18166" class="Symbol">(</a><a id="18167" href="plfa.part1.Decidable.html#18145" class="Bound">m</a> <a id="18169" href="plfa.part1.Decidable.html#17430" class="Function Operator">≤ᵇ′</a> <a id="18173" href="plfa.part1.Decidable.html#18147" class="Bound">n</a><a id="18174" class="Symbol">)</a>
<a id="18176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18134" class="Function">≤→≤ᵇ′</a>  <a id="18183" class="Symbol">=</a>  <a id="18186" href="plfa.part1.Decidable.html#17772" class="Function">fromWitness</a>
</pre>{% endraw %}
{::comment}
In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.
{:/}

总结来说，最好避免直接使用布尔值，而使用可判定的值。如果有需要布尔值的时候，它们和它们的性质可以简单地从对应的可判定的值中派生而来。


{::comment}
## Logical connectives
{:/}

{::comment}
Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.
{:/}

大多数读者对于布尔值的逻辑运算符很熟悉了。每个逻辑运算符都可以被延伸至可判定的值。

{::comment}
The conjunction of two booleans is true if both are true,
and false if either is false:
{:/}

两个布尔值的合取当两者都为真时为真，当任一为假时为假：

{% raw %}<pre class="Agda"><a id="18818" class="Keyword">infixr</a> <a id="18825" class="Number">6</a> <a id="18827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18832" class="Function Operator">_∧_</a>

<a id="_∧_"></a><a id="18832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18832" class="Function Operator">_∧_</a> <a id="18836" class="Symbol">:</a> <a id="18838" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="18843" class="Symbol">→</a> <a id="18845" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="18850" class="Symbol">→</a> <a id="18852" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="18857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>  <a id="18863" href="plfa.part1.Decidable.html#18832" class="Function Operator">∧</a> <a id="18865" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>  <a id="18871" class="Symbol">=</a> <a id="18873" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="18878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="InductiveConstructor">false</a> <a id="18884" href="plfa.part1.Decidable.html#18832" class="Function Operator">∧</a> <a id="18886" class="Symbol">_</a>     <a id="18892" class="Symbol">=</a> <a id="18894" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
<a id="18900" class="CatchallClause Symbol">_</a><a id="18901" class="CatchallClause">     </a><a id="18906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#18832" class="CatchallClause Function Operator">∧</a><a id="18907" class="CatchallClause"> </a><a id="18908" href="plfa.part1.Decidable.html#2646" class="CatchallClause InductiveConstructor">false</a> <a id="18914" class="Symbol">=</a> <a id="18916" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第三个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第二条还是第三条会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their conjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的合取：

{% raw %}<pre class="Agda"><a id="19388" class="Keyword">infixr</a> <a id="19395" class="Number">6</a> <a id="19397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#19406" class="Function Operator">_×-dec_</a>

<a id="_×-dec_"></a><a id="19406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#19406" class="Function Operator">_×-dec_</a> <a id="19414" class="Symbol">:</a> <a id="19416" class="Symbol">∀</a> <a id="19418" class="Symbol">{</a><a id="19419" href="plfa.part1.Decidable.html#19419" class="Bound">A</a> <a id="19421" href="plfa.part1.Decidable.html#19421" class="Bound">B</a> <a id="19423" class="Symbol">:</a> <a id="19425" class="PrimitiveType">Set</a><a id="19428" class="Symbol">}</a> <a id="19430" class="Symbol">→</a> <a id="19432" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="19436" href="plfa.part1.Decidable.html#19419" class="Bound">A</a> <a id="19438" class="Symbol">→</a> <a id="19440" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="19444" href="plfa.part1.Decidable.html#19421" class="Bound">B</a> <a id="19446" class="Symbol">→</a> <a id="19448" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="19452" class="Symbol">(</a><a id="19453" href="plfa.part1.Decidable.html#19419" class="Bound">A</a> <a id="19455" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="19457" href="plfa.part1.Decidable.html#19421" class="Bound">B</a><a id="19458" class="Symbol">)</a>
<a id="19460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10052" class="InductiveConstructor">yes</a> <a id="19464" href="plfa.part1.Decidable.html#19464" class="Bound">x</a> <a id="19466" href="plfa.part1.Decidable.html#19406" class="Function Operator">×-dec</a> <a id="19472" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="19476" href="plfa.part1.Decidable.html#19476" class="Bound">y</a> <a id="19478" class="Symbol">=</a> <a id="19480" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="19484" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19486" href="plfa.part1.Decidable.html#19464" class="Bound">x</a> <a id="19488" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19490" href="plfa.part1.Decidable.html#19476" class="Bound">y</a> <a id="19492" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a>
<a id="19494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10072" class="InductiveConstructor">no</a> <a id="19497" href="plfa.part1.Decidable.html#19497" class="Bound">¬x</a> <a id="19500" href="plfa.part1.Decidable.html#19406" class="Function Operator">×-dec</a> <a id="19506" class="Symbol">_</a>     <a id="19512" class="Symbol">=</a> <a id="19514" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="19517" class="Symbol">λ{</a> <a id="19520" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19522" href="plfa.part1.Decidable.html#19522" class="Bound">x</a> <a id="19524" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19526" href="plfa.part1.Decidable.html#19526" class="Bound">y</a> <a id="19528" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19530" class="Symbol">→</a> <a id="19532" href="plfa.part1.Decidable.html#19497" class="Bound">¬x</a> <a id="19535" href="plfa.part1.Decidable.html#19522" class="Bound">x</a> <a id="19537" class="Symbol">}</a>
<a id="19539" class="CatchallClause Symbol">_</a><a id="19540" class="CatchallClause">     </a><a id="19545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#19406" class="CatchallClause Function Operator">×-dec</a><a id="19550" class="CatchallClause"> </a><a id="19551" href="plfa.part1.Decidable.html#10072" class="CatchallClause InductiveConstructor">no</a><a id="19553" class="CatchallClause"> </a><a id="19554" href="plfa.part1.Decidable.html#19554" class="CatchallClause Bound">¬y</a> <a id="19557" class="Symbol">=</a> <a id="19559" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="19562" class="Symbol">λ{</a> <a id="19565" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19567" href="plfa.part1.Decidable.html#19567" class="Bound">x</a> <a id="19569" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19571" href="plfa.part1.Decidable.html#19571" class="Bound">y</a> <a id="19573" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19575" class="Symbol">→</a> <a id="19577" href="plfa.part1.Decidable.html#19554" class="Bound">¬y</a> <a id="19580" href="plfa.part1.Decidable.html#19571" class="Bound">y</a> <a id="19582" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.
{:/}

两个命题的合取当两者都成立时成立，其否定则当任意一者否定成立时成立。如果两个都成立，我们将每一证明放入数据对中，作为合取的证明。如果任意一者的否定成立，假设整个合取将会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第三条等式在左手边以灰色显示，说明等式的顺序决定了第二条还是第三条会被匹配。这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都不成立，我们选择第一个来构造矛盾，但选择第二个也是同样正确的。

{::comment}
The disjunction of two booleans is true if either is true,
and false if both are false:
{:/}

两个布尔值的析取当任意为真时为真，当两者为假时为假：

{% raw %}<pre class="Agda"><a id="20629" class="Keyword">infixr</a> <a id="20636" class="Number">5</a> <a id="20638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#20643" class="Function Operator">_∨_</a>

<a id="_∨_"></a><a id="20643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#20643" class="Function Operator">_∨_</a> <a id="20647" class="Symbol">:</a> <a id="20649" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="20654" class="Symbol">→</a> <a id="20656" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="20661" class="Symbol">→</a> <a id="20663" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="20668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>  <a id="20674" href="plfa.part1.Decidable.html#20643" class="Function Operator">∨</a> <a id="20676" class="Symbol">_</a>      <a id="20683" class="Symbol">=</a> <a id="20685" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="20690" class="CatchallClause Symbol">_</a><a id="20691" class="CatchallClause">     </a><a id="20696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#20643" class="CatchallClause Function Operator">∨</a><a id="20697" class="CatchallClause"> </a><a id="20698" href="plfa.part1.Decidable.html#2631" class="CatchallClause InductiveConstructor">true</a>   <a id="20705" class="Symbol">=</a> <a id="20707" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="20712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="InductiveConstructor">false</a> <a id="20718" href="plfa.part1.Decidable.html#20643" class="Function Operator">∨</a> <a id="20720" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>  <a id="20727" class="Symbol">=</a> <a id="20729" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their disjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="21202" class="Keyword">infixr</a> <a id="21209" class="Number">5</a> <a id="21211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#21220" class="Function Operator">_⊎-dec_</a>

<a id="_⊎-dec_"></a><a id="21220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#21220" class="Function Operator">_⊎-dec_</a> <a id="21228" class="Symbol">:</a> <a id="21230" class="Symbol">∀</a> <a id="21232" class="Symbol">{</a><a id="21233" href="plfa.part1.Decidable.html#21233" class="Bound">A</a> <a id="21235" href="plfa.part1.Decidable.html#21235" class="Bound">B</a> <a id="21237" class="Symbol">:</a> <a id="21239" class="PrimitiveType">Set</a><a id="21242" class="Symbol">}</a> <a id="21244" class="Symbol">→</a> <a id="21246" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="21250" href="plfa.part1.Decidable.html#21233" class="Bound">A</a> <a id="21252" class="Symbol">→</a> <a id="21254" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="21258" href="plfa.part1.Decidable.html#21235" class="Bound">B</a> <a id="21260" class="Symbol">→</a> <a id="21262" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="21266" class="Symbol">(</a><a id="21267" href="plfa.part1.Decidable.html#21233" class="Bound">A</a> <a id="21269" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="21271" href="plfa.part1.Decidable.html#21235" class="Bound">B</a><a id="21272" class="Symbol">)</a>
<a id="21274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10052" class="InductiveConstructor">yes</a> <a id="21278" href="plfa.part1.Decidable.html#21278" class="Bound">x</a> <a id="21280" href="plfa.part1.Decidable.html#21220" class="Function Operator">⊎-dec</a> <a id="21286" class="Symbol">_</a>     <a id="21292" class="Symbol">=</a> <a id="21294" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="21298" class="Symbol">(</a><a id="21299" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21304" href="plfa.part1.Decidable.html#21278" class="Bound">x</a><a id="21305" class="Symbol">)</a>
<a id="21307" class="CatchallClause Symbol">_</a><a id="21308" class="CatchallClause">     </a><a id="21313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#21220" class="CatchallClause Function Operator">⊎-dec</a><a id="21318" class="CatchallClause"> </a><a id="21319" href="plfa.part1.Decidable.html#10052" class="CatchallClause InductiveConstructor">yes</a><a id="21322" class="CatchallClause"> </a><a id="21323" href="plfa.part1.Decidable.html#21323" class="CatchallClause Bound">y</a> <a id="21325" class="Symbol">=</a> <a id="21327" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="21331" class="Symbol">(</a><a id="21332" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21337" href="plfa.part1.Decidable.html#21323" class="Bound">y</a><a id="21338" class="Symbol">)</a>
<a id="21340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10072" class="InductiveConstructor">no</a> <a id="21343" href="plfa.part1.Decidable.html#21343" class="Bound">¬x</a> <a id="21346" href="plfa.part1.Decidable.html#21220" class="Function Operator">⊎-dec</a> <a id="21352" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="21355" href="plfa.part1.Decidable.html#21355" class="Bound">¬y</a> <a id="21358" class="Symbol">=</a> <a id="21360" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="21363" class="Symbol">λ{</a> <a id="21366" class="Symbol">(</a><a id="21367" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21372" href="plfa.part1.Decidable.html#21372" class="Bound">x</a><a id="21373" class="Symbol">)</a> <a id="21375" class="Symbol">→</a> <a id="21377" href="plfa.part1.Decidable.html#21343" class="Bound">¬x</a> <a id="21380" href="plfa.part1.Decidable.html#21372" class="Bound">x</a> <a id="21382" class="Symbol">;</a> <a id="21384" class="Symbol">(</a><a id="21385" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21390" href="plfa.part1.Decidable.html#21390" class="Bound">y</a><a id="21391" class="Symbol">)</a> <a id="21393" class="Symbol">→</a> <a id="21395" href="plfa.part1.Decidable.html#21355" class="Bound">¬y</a> <a id="21398" href="plfa.part1.Decidable.html#21390" class="Bound">y</a> <a id="21400" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.
{:/}

两个命题的析取当任意一者成立时成立，其否定则当两者的否定成立时成立。如果任意一者成立，我们使用其证明来作为析取的证明。如果两个的否定都成立，假设任意一者都会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都成立，我们选择第一个来构造析取，但选择第二个也是同样正确的。

{::comment}
The negation of a boolean is false if its argument is true,
and vice versa:
{:/}

一个布尔值的否定当值为真时为假，反之亦然：

{% raw %}<pre class="Agda"><a id="not"></a><a id="22375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22375" class="Function">not</a> <a id="22379" class="Symbol">:</a> <a id="22381" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="22386" class="Symbol">→</a> <a id="22388" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="22393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22375" class="Function">not</a> <a id="22397" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>  <a id="22403" class="Symbol">=</a> <a id="22405" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
<a id="22411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22375" class="Function">not</a> <a id="22415" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a> <a id="22421" class="Symbol">=</a> <a id="22423" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
</pre>{% endraw %}
{::comment}
Correspondingly, given a decidable proposition, we
can decide its negation:
{:/}

相应地，给定一个可判定的命题，我们可以判定它的否定：

{% raw %}<pre class="Agda"><a id="¬?"></a><a id="22559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22559" class="Function">¬?</a> <a id="22562" class="Symbol">:</a> <a id="22564" class="Symbol">∀</a> <a id="22566" class="Symbol">{</a><a id="22567" href="plfa.part1.Decidable.html#22567" class="Bound">A</a> <a id="22569" class="Symbol">:</a> <a id="22571" class="PrimitiveType">Set</a><a id="22574" class="Symbol">}</a> <a id="22576" class="Symbol">→</a> <a id="22578" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="22582" href="plfa.part1.Decidable.html#22567" class="Bound">A</a> <a id="22584" class="Symbol">→</a> <a id="22586" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="22590" class="Symbol">(</a><a id="22591" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="22593" href="plfa.part1.Decidable.html#22567" class="Bound">A</a><a id="22594" class="Symbol">)</a>
<a id="22596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22559" class="Function">¬?</a> <a id="22599" class="Symbol">(</a><a id="22600" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="22604" href="plfa.part1.Decidable.html#22604" class="Bound">x</a><a id="22605" class="Symbol">)</a>  <a id="22608" class="Symbol">=</a>  <a id="22611" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="22614" class="Symbol">(</a><a id="22615" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a> <a id="22624" href="plfa.part1.Decidable.html#22604" class="Bound">x</a><a id="22625" class="Symbol">)</a>
<a id="22627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#22559" class="Function">¬?</a> <a id="22630" class="Symbol">(</a><a id="22631" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="22634" href="plfa.part1.Decidable.html#22634" class="Bound">¬x</a><a id="22636" class="Symbol">)</a>  <a id="22639" class="Symbol">=</a>  <a id="22642" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="22646" href="plfa.part1.Decidable.html#22634" class="Bound">¬x</a>
</pre>{% endraw %}
{::comment}
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.
{:/}

我们直接把 yes 和 no 交换。在第一个等式中，右手边断言了 `¬ A` 的否定成立，也就是说
`¬ ¬ A` 成立——这是一个 `A` 成立时可以简单得到的推论。

{::comment}
There is also a slightly less familiar connective,
corresponding to implication:
{:/}

还有一个与蕴涵相对应，但是稍微不那么知名的运算符：

{% raw %}<pre class="Agda"><a id="_⊃_"></a><a id="23094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#23094" class="Function Operator">_⊃_</a> <a id="23098" class="Symbol">:</a> <a id="23100" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="23105" class="Symbol">→</a> <a id="23107" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="23112" class="Symbol">→</a> <a id="23114" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
<a id="23119" class="Symbol">_</a>     <a id="23125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#23094" class="Function Operator">⊃</a> <a id="23127" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>   <a id="23134" class="Symbol">=</a>  <a id="23137" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="23142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2646" class="CatchallClause InductiveConstructor">false</a><a id="23147" class="CatchallClause"> </a><a id="23148" href="plfa.part1.Decidable.html#23094" class="CatchallClause Function Operator">⊃</a><a id="23149" class="CatchallClause"> </a><a id="23150" class="CatchallClause Symbol">_</a>      <a id="23157" class="Symbol">=</a>  <a id="23160" href="plfa.part1.Decidable.html#2631" class="InductiveConstructor">true</a>
<a id="23165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#2631" class="InductiveConstructor">true</a>  <a id="23171" href="plfa.part1.Decidable.html#23094" class="Function Operator">⊃</a> <a id="23173" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>  <a id="23180" class="Symbol">=</a>  <a id="23183" href="plfa.part1.Decidable.html#2646" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

当任何一个布尔值为真的时候，另一个布尔值恒为真，我们成为第一个布尔值蕴涵第二个布尔值。因此，两者的蕴涵在第二个为真或者第一个为假时为真，在第一个为真而第二个为假时为假。在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="_→-dec_"></a><a id="23987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#23987" class="Function Operator">_→-dec_</a> <a id="23995" class="Symbol">:</a> <a id="23997" class="Symbol">∀</a> <a id="23999" class="Symbol">{</a><a id="24000" href="plfa.part1.Decidable.html#24000" class="Bound">A</a> <a id="24002" href="plfa.part1.Decidable.html#24002" class="Bound">B</a> <a id="24004" class="Symbol">:</a> <a id="24006" class="PrimitiveType">Set</a><a id="24009" class="Symbol">}</a> <a id="24011" class="Symbol">→</a> <a id="24013" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="24017" href="plfa.part1.Decidable.html#24000" class="Bound">A</a> <a id="24019" class="Symbol">→</a> <a id="24021" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="24025" href="plfa.part1.Decidable.html#24002" class="Bound">B</a> <a id="24027" class="Symbol">→</a> <a id="24029" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="24033" class="Symbol">(</a><a id="24034" href="plfa.part1.Decidable.html#24000" class="Bound">A</a> <a id="24036" class="Symbol">→</a> <a id="24038" href="plfa.part1.Decidable.html#24002" class="Bound">B</a><a id="24039" class="Symbol">)</a>
<a id="24041" class="Symbol">_</a>     <a id="24047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#23987" class="Function Operator">→-dec</a> <a id="24053" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="24057" href="plfa.part1.Decidable.html#24057" class="Bound">y</a>  <a id="24060" class="Symbol">=</a>  <a id="24063" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="24067" class="Symbol">(λ</a> <a id="24070" href="plfa.part1.Decidable.html#24070" class="Bound">_</a> <a id="24072" class="Symbol">→</a> <a id="24074" href="plfa.part1.Decidable.html#24057" class="Bound">y</a><a id="24075" class="Symbol">)</a>
<a id="24077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10072" class="CatchallClause InductiveConstructor">no</a><a id="24079" class="CatchallClause"> </a><a id="24080" href="plfa.part1.Decidable.html#24080" class="CatchallClause Bound">¬x</a><a id="24082" class="CatchallClause"> </a><a id="24083" href="plfa.part1.Decidable.html#23987" class="CatchallClause Function Operator">→-dec</a><a id="24088" class="CatchallClause"> </a><a id="24089" class="CatchallClause Symbol">_</a>      <a id="24096" class="Symbol">=</a>  <a id="24099" href="plfa.part1.Decidable.html#10052" class="InductiveConstructor">yes</a> <a id="24103" class="Symbol">(λ</a> <a id="24106" href="plfa.part1.Decidable.html#24106" class="Bound">x</a> <a id="24108" class="Symbol">→</a> <a id="24110" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="24117" class="Symbol">(</a><a id="24118" href="plfa.part1.Decidable.html#24080" class="Bound">¬x</a> <a id="24121" href="plfa.part1.Decidable.html#24106" class="Bound">x</a><a id="24122" class="Symbol">))</a>
<a id="24125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#10052" class="InductiveConstructor">yes</a> <a id="24129" href="plfa.part1.Decidable.html#24129" class="Bound">x</a> <a id="24131" href="plfa.part1.Decidable.html#23987" class="Function Operator">→-dec</a> <a id="24137" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="24140" href="plfa.part1.Decidable.html#24140" class="Bound">¬y</a>  <a id="24144" class="Symbol">=</a>  <a id="24147" href="plfa.part1.Decidable.html#10072" class="InductiveConstructor">no</a> <a id="24150" class="Symbol">(λ</a> <a id="24153" href="plfa.part1.Decidable.html#24153" class="Bound">f</a> <a id="24155" class="Symbol">→</a> <a id="24157" href="plfa.part1.Decidable.html#24140" class="Bound">¬y</a> <a id="24160" class="Symbol">(</a><a id="24161" href="plfa.part1.Decidable.html#24153" class="Bound">f</a> <a id="24163" href="plfa.part1.Decidable.html#24129" class="Bound">x</a><a id="24164" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
The implication holds if either the second holds or
the negation of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.
{:/}

两者的蕴涵在第二者成立或者第一者的否定成立时成立，其否定在第一者成立而第二者否定成立时成立。蕴涵成立的证明是一个从第一者成立的证明到第二者成立的证明的函数。如果第二者成立，那么这个函数直接返回第二者的证明。如果第一者的否定成立，那么使用第一者成立的证明，构造一个矛盾。如果第一者成立，第二者不成立，给定蕴涵成立的证明，我们必须构造一个矛盾：我们将成立的证明 `f`
应用于第一者成立的证明 `x`，再加以第二者否定成立的证明 `¬y` 来构造矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。这一次，我们给出的结果会因为是哪一条被匹配而不一样，但两者都是同样正确的。

#### Exercise `erasure` (practice)

#### 练习 `erasure`（实践）

{::comment}
Show that erasure relates corresponding boolean and decidable operations:
{:/}

证明擦除将对应的布尔值和可判定的值的操作联系了起来：

{% raw %}<pre class="Agda"><a id="25694" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="25706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#25706" class="Postulate">∧-×</a> <a id="25710" class="Symbol">:</a> <a id="25712" class="Symbol">∀</a> <a id="25714" class="Symbol">{</a><a id="25715" href="plfa.part1.Decidable.html#25715" class="Bound">A</a> <a id="25717" href="plfa.part1.Decidable.html#25717" class="Bound">B</a> <a id="25719" class="Symbol">:</a> <a id="25721" class="PrimitiveType">Set</a><a id="25724" class="Symbol">}</a> <a id="25726" class="Symbol">(</a><a id="25727" href="plfa.part1.Decidable.html#25727" class="Bound">x</a> <a id="25729" class="Symbol">:</a> <a id="25731" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="25735" href="plfa.part1.Decidable.html#25715" class="Bound">A</a><a id="25736" class="Symbol">)</a> <a id="25738" class="Symbol">(</a><a id="25739" href="plfa.part1.Decidable.html#25739" class="Bound">y</a> <a id="25741" class="Symbol">:</a> <a id="25743" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="25747" href="plfa.part1.Decidable.html#25717" class="Bound">B</a><a id="25748" class="Symbol">)</a> <a id="25750" class="Symbol">→</a> <a id="25752" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25754" href="plfa.part1.Decidable.html#25727" class="Bound">x</a> <a id="25756" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="25758" href="plfa.part1.Decidable.html#18832" class="Function Operator">∧</a> <a id="25760" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25762" href="plfa.part1.Decidable.html#25739" class="Bound">y</a> <a id="25764" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="25766" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25768" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25770" href="plfa.part1.Decidable.html#25727" class="Bound">x</a> <a id="25772" href="plfa.part1.Decidable.html#19406" class="Function Operator">×-dec</a> <a id="25778" href="plfa.part1.Decidable.html#25739" class="Bound">y</a> <a id="25780" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
  <a id="∨-⊎"></a><a id="25784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#25784" class="Postulate">∨-⊎</a> <a id="25788" class="Symbol">:</a> <a id="25790" class="Symbol">∀</a> <a id="25792" class="Symbol">{</a><a id="25793" href="plfa.part1.Decidable.html#25793" class="Bound">A</a> <a id="25795" href="plfa.part1.Decidable.html#25795" class="Bound">B</a> <a id="25797" class="Symbol">:</a> <a id="25799" class="PrimitiveType">Set</a><a id="25802" class="Symbol">}</a> <a id="25804" class="Symbol">(</a><a id="25805" href="plfa.part1.Decidable.html#25805" class="Bound">x</a> <a id="25807" class="Symbol">:</a> <a id="25809" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="25813" href="plfa.part1.Decidable.html#25793" class="Bound">A</a><a id="25814" class="Symbol">)</a> <a id="25816" class="Symbol">(</a><a id="25817" href="plfa.part1.Decidable.html#25817" class="Bound">y</a> <a id="25819" class="Symbol">:</a> <a id="25821" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="25825" href="plfa.part1.Decidable.html#25795" class="Bound">B</a><a id="25826" class="Symbol">)</a> <a id="25828" class="Symbol">→</a> <a id="25830" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25832" href="plfa.part1.Decidable.html#25805" class="Bound">x</a> <a id="25834" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="25836" href="plfa.part1.Decidable.html#20643" class="Function Operator">∨</a> <a id="25838" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25840" href="plfa.part1.Decidable.html#25817" class="Bound">y</a> <a id="25842" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="25844" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25846" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25848" href="plfa.part1.Decidable.html#25805" class="Bound">x</a> <a id="25850" href="plfa.part1.Decidable.html#21220" class="Function Operator">⊎-dec</a> <a id="25856" href="plfa.part1.Decidable.html#25817" class="Bound">y</a> <a id="25858" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="25862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#25862" class="Postulate">not-¬</a> <a id="25868" class="Symbol">:</a> <a id="25870" class="Symbol">∀</a> <a id="25872" class="Symbol">{</a><a id="25873" href="plfa.part1.Decidable.html#25873" class="Bound">A</a> <a id="25875" class="Symbol">:</a> <a id="25877" class="PrimitiveType">Set</a><a id="25880" class="Symbol">}</a> <a id="25882" class="Symbol">(</a><a id="25883" href="plfa.part1.Decidable.html#25883" class="Bound">x</a> <a id="25885" class="Symbol">:</a> <a id="25887" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="25891" href="plfa.part1.Decidable.html#25873" class="Bound">A</a><a id="25892" class="Symbol">)</a> <a id="25894" class="Symbol">→</a> <a id="25896" href="plfa.part1.Decidable.html#22375" class="Function">not</a> <a id="25900" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25902" href="plfa.part1.Decidable.html#25883" class="Bound">x</a> <a id="25904" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="25906" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25908" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="25910" href="plfa.part1.Decidable.html#22559" class="Function">¬?</a> <a id="25913" href="plfa.part1.Decidable.html#25883" class="Bound">x</a> <a id="25915" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
#### Exercise `iff-erasure` (recommended)
{:/}

#### 练习 `iff-erasure` （推荐）

{::comment}
Give analogues of the `_⇔_` operation from
Chapter [Isomorphism]({{ site.baseurl }}/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
{:/}

给出与 [Isomorphism][plfa.Isomorphism#iff] 章节中 `_↔_` 相对应的布尔值与可判定的值的操作，并证明其对应的擦除：

{% raw %}<pre class="Agda"><a id="26294" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="26306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#26306" class="Postulate Operator">_iff_</a> <a id="26312" class="Symbol">:</a> <a id="26314" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="26319" class="Symbol">→</a> <a id="26321" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a> <a id="26326" class="Symbol">→</a> <a id="26328" href="plfa.part1.Decidable.html#2612" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="26335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#26335" class="Postulate Operator">_⇔-dec_</a> <a id="26343" class="Symbol">:</a> <a id="26345" class="Symbol">∀</a> <a id="26347" class="Symbol">{</a><a id="26348" href="plfa.part1.Decidable.html#26348" class="Bound">A</a> <a id="26350" href="plfa.part1.Decidable.html#26350" class="Bound">B</a> <a id="26352" class="Symbol">:</a> <a id="26354" class="PrimitiveType">Set</a><a id="26357" class="Symbol">}</a> <a id="26359" class="Symbol">→</a> <a id="26361" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="26365" href="plfa.part1.Decidable.html#26348" class="Bound">A</a> <a id="26367" class="Symbol">→</a> <a id="26369" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="26373" href="plfa.part1.Decidable.html#26350" class="Bound">B</a> <a id="26375" class="Symbol">→</a> <a id="26377" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="26381" class="Symbol">(</a><a id="26382" href="plfa.part1.Decidable.html#26348" class="Bound">A</a> <a id="26384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#15292" class="Record Operator">⇔</a> <a id="26386" href="plfa.part1.Decidable.html#26350" class="Bound">B</a><a id="26387" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="26391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Decidable.md %}{% raw %}#26391" class="Postulate">iff-⇔</a> <a id="26397" class="Symbol">:</a> <a id="26399" class="Symbol">∀</a> <a id="26401" class="Symbol">{</a><a id="26402" href="plfa.part1.Decidable.html#26402" class="Bound">A</a> <a id="26404" href="plfa.part1.Decidable.html#26404" class="Bound">B</a> <a id="26406" class="Symbol">:</a> <a id="26408" class="PrimitiveType">Set</a><a id="26411" class="Symbol">}</a> <a id="26413" class="Symbol">(</a><a id="26414" href="plfa.part1.Decidable.html#26414" class="Bound">x</a> <a id="26416" class="Symbol">:</a> <a id="26418" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="26422" href="plfa.part1.Decidable.html#26402" class="Bound">A</a><a id="26423" class="Symbol">)</a> <a id="26425" class="Symbol">(</a><a id="26426" href="plfa.part1.Decidable.html#26426" class="Bound">y</a> <a id="26428" class="Symbol">:</a> <a id="26430" href="plfa.part1.Decidable.html#10024" class="Datatype">Dec</a> <a id="26434" href="plfa.part1.Decidable.html#26404" class="Bound">B</a><a id="26435" class="Symbol">)</a> <a id="26437" class="Symbol">→</a> <a id="26439" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="26441" href="plfa.part1.Decidable.html#26414" class="Bound">x</a> <a id="26443" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="26445" href="plfa.part1.Decidable.html#26306" class="Postulate Operator">iff</a> <a id="26449" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="26451" href="plfa.part1.Decidable.html#26426" class="Bound">y</a> <a id="26453" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a> <a id="26455" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="26457" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌊</a> <a id="26459" href="plfa.part1.Decidable.html#26414" class="Bound">x</a> <a id="26461" href="plfa.part1.Decidable.html#26335" class="Postulate Operator">⇔-dec</a> <a id="26467" href="plfa.part1.Decidable.html#26426" class="Bound">y</a> <a id="26469" href="plfa.part1.Decidable.html#17240" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="26492" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="26529" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard Library
{:/}

## 标准库

{% raw %}<pre class="Agda"><a id="26597" class="Keyword">import</a> <a id="26604" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="26619" class="Keyword">using</a> <a id="26625" class="Symbol">(</a><a id="26626" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="26630" class="Symbol">;</a> <a id="26632" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="26636" class="Symbol">;</a> <a id="26638" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="26643" class="Symbol">;</a> <a id="26645" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="26646" class="Symbol">;</a> <a id="26648" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="26651" class="Symbol">;</a> <a id="26653" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="26656" class="Symbol">;</a> <a id="26658" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="26661" class="Symbol">)</a>
<a id="26663" class="Keyword">import</a> <a id="26670" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="26679" class="Keyword">using</a> <a id="26685" class="Symbol">(</a><a id="26686" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#4585" class="Function Operator">_≤?_</a><a id="26690" class="Symbol">)</a>
<a id="26692" class="Keyword">import</a> <a id="26699" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="26716" class="Keyword">using</a> <a id="26722" class="Symbol">(</a><a id="26723" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="26726" class="Symbol">;</a> <a id="26728" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="26731" class="Symbol">;</a> <a id="26733" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="26735" class="Symbol">)</a>
<a id="26737" class="Keyword">import</a> <a id="26744" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="26771" class="Keyword">using</a> <a id="26777" class="Symbol">(</a><a id="26778" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="26781" class="Symbol">;</a> <a id="26783" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="26792" class="Symbol">;</a> <a id="26794" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="26805" class="Symbol">)</a>
<a id="26807" class="Keyword">import</a> <a id="26814" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="26840" class="Keyword">using</a> <a id="26846" class="Symbol">(</a><a id="26847" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="26849" class="Symbol">)</a>
<a id="26851" class="Keyword">import</a> <a id="26858" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="26883" class="Keyword">using</a> <a id="26889" class="Symbol">(</a><a id="26890" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="26897" class="Symbol">)</a>
<a id="26899" class="Keyword">import</a> <a id="26906" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="26927" class="Keyword">using</a> <a id="26933" class="Symbol">(</a><a id="26934" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="26941" class="Symbol">)</a>
<a id="26943" class="Keyword">import</a> <a id="26950" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.html" class="Module">Relation.Binary</a> <a id="26966" class="Keyword">using</a> <a id="26972" class="Symbol">(</a><a id="26973" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.Core.html#5557" class="Function">Decidable</a><a id="26982" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\cll)
    ⌋  U+230B  RIGHT FLOOR (\clr)
{:/}

    ∧  U+2227  逻辑和 (\and, \wedge)
    ∨  U+2228  逻辑或 (\or, \vee)
    ⊃  U+2283  超集 (\sup)
    ᵇ  U+1D47  修饰符小写 B  (\^b)
    ⌊  U+230A  左向下取整 (\cll)
    ⌋  U+230B  右向下取整 (\clr)
