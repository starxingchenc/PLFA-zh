---
src       : "src/plfa/part1/Connectives.lagda.md"
title     : "Connectives: 合取、析取与蕴涵"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="188" class="Keyword">module</a> <a id="195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}" class="Module">plfa.part1.Connectives</a> <a id="218" class="Keyword">where</a>
</pre>{% endraw %}
<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

{::comment}
This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:
{:/}

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，即*命题即类型*原理（Propositions as Types）。

{::comment}
  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.
{:/}

  * *合取*（Conjunction）即是*积*（Product）
  * *析取*（Disjunction）即是*和*（Sum）
  * *真*（True）即是*单元类型*（Unit Type）
  * *假*（False）即是*空类型*（Empty Type）
  * *蕴涵*（Implication）即是*函数空间*（Function Space）

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="1146" class="Keyword">import</a> <a id="1153" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1191" class="Symbol">as</a> <a id="1194" class="Module">Eq</a>
<a id="1197" class="Keyword">open</a> <a id="1202" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1205" class="Keyword">using</a> <a id="1211" class="Symbol">(</a><a id="1212" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1215" class="Symbol">;</a> <a id="1217" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1221" class="Symbol">)</a>
<a id="1223" class="Keyword">open</a> <a id="1228" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="1243" class="Keyword">open</a> <a id="1248" class="Keyword">import</a> <a id="1255" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1264" class="Keyword">using</a> <a id="1270" class="Symbol">(</a><a id="1271" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1272" class="Symbol">)</a>
<a id="1274" class="Keyword">open</a> <a id="1279" class="Keyword">import</a> <a id="1286" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1295" class="Keyword">using</a> <a id="1301" class="Symbol">(</a><a id="1302" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1305" class="Symbol">)</a>
<a id="1307" class="Keyword">open</a> <a id="1312" class="Keyword">import</a> <a id="1319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1342" class="Keyword">using</a> <a id="1348" class="Symbol">(</a><a id="1349" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="1352" class="Symbol">;</a> <a id="1354" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">_≲_</a><a id="1357" class="Symbol">;</a> <a id="1359" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="1373" class="Symbol">)</a>
<a id="1375" class="Keyword">open</a> <a id="1380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Conjunction is product
{:/}

## 合取即是积

{::comment}
Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，其合取 `A × B` 成立当 `A` 成立和 `B` 成立。我们将这样的概念形式化，使用如下的归纳类型：

{% raw %}<pre class="Agda"><a id="1733" class="Keyword">data</a> <a id="_×_"></a><a id="1738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1738" class="Datatype Operator">_×_</a> <a id="1742" class="Symbol">(</a><a id="1743" href="plfa.part1.Connectives.html#1743" class="Bound">A</a> <a id="1745" href="plfa.part1.Connectives.html#1745" class="Bound">B</a> <a id="1747" class="Symbol">:</a> <a id="1749" class="PrimitiveType">Set</a><a id="1752" class="Symbol">)</a> <a id="1754" class="Symbol">:</a> <a id="1756" class="PrimitiveType">Set</a> <a id="1760" class="Keyword">where</a>

  <a id="_×_.⟨_,_⟩"></a><a id="1769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="1775" class="Symbol">:</a>
      <a id="1783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1743" class="Bound">A</a>
    <a id="1789" class="Symbol">→</a> <a id="1791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1745" class="Bound">B</a>
      <a id="1799" class="Comment">-----</a>
    <a id="1809" class="Symbol">→</a> <a id="1811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1743" class="Bound">A</a> <a id="1813" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="1815" href="plfa.part1.Connectives.html#1745" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.
{:/}

`A × B` 成立的证明由 `⟨ M , N ⟩` 的形式表现，其中 `M` 是 `A` 成立的证明，
`N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{:/}

给定 `A × B` 成立的证明，我们可以得出 `A` 成立或者 `B` 成立。

{% raw %}<pre class="Agda"><a id="proj₁"></a><a id="2203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2203" class="Function">proj₁</a> <a id="2209" class="Symbol">:</a> <a id="2211" class="Symbol">∀</a> <a id="2213" class="Symbol">{</a><a id="2214" href="plfa.part1.Connectives.html#2214" class="Bound">A</a> <a id="2216" href="plfa.part1.Connectives.html#2216" class="Bound">B</a> <a id="2218" class="Symbol">:</a> <a id="2220" class="PrimitiveType">Set</a><a id="2223" class="Symbol">}</a>
  <a id="2227" class="Symbol">→</a> <a id="2229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2214" class="Bound">A</a> <a id="2231" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="2233" href="plfa.part1.Connectives.html#2216" class="Bound">B</a>
    <a id="2239" class="Comment">-----</a>
  <a id="2247" class="Symbol">→</a> <a id="2249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2214" class="Bound">A</a>
<a id="2251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2203" class="Function">proj₁</a> <a id="2257" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="2259" href="plfa.part1.Connectives.html#2259" class="Bound">x</a> <a id="2261" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="2263" href="plfa.part1.Connectives.html#2263" class="Bound">y</a> <a id="2265" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="2267" class="Symbol">=</a> <a id="2269" href="plfa.part1.Connectives.html#2259" class="Bound">x</a>

<a id="proj₂"></a><a id="2272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2272" class="Function">proj₂</a> <a id="2278" class="Symbol">:</a> <a id="2280" class="Symbol">∀</a> <a id="2282" class="Symbol">{</a><a id="2283" href="plfa.part1.Connectives.html#2283" class="Bound">A</a> <a id="2285" href="plfa.part1.Connectives.html#2285" class="Bound">B</a> <a id="2287" class="Symbol">:</a> <a id="2289" class="PrimitiveType">Set</a><a id="2292" class="Symbol">}</a>
  <a id="2296" class="Symbol">→</a> <a id="2298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2283" class="Bound">A</a> <a id="2300" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="2302" href="plfa.part1.Connectives.html#2285" class="Bound">B</a>
    <a id="2308" class="Comment">-----</a>
  <a id="2316" class="Symbol">→</a> <a id="2318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2285" class="Bound">B</a>
<a id="2320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2272" class="Function">proj₂</a> <a id="2326" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="2328" href="plfa.part1.Connectives.html#2328" class="Bound">x</a> <a id="2330" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="2332" href="plfa.part1.Connectives.html#2332" class="Bound">y</a> <a id="2334" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="2336" class="Symbol">=</a> <a id="2338" href="plfa.part1.Connectives.html#2332" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.
{:/}

如果 `L` 是 `A × B` 成立的证据, 那么 `proj₁ L` 是 `A` 成立的证据，
`proj₂ L` 是 `B` 成立的证据。

{::comment}
Equivalently, we could also declare conjunction as a record type:
{:/}

等价地，我们亦可以将合取定义为一个记录类型：

{% raw %}<pre class="Agda"><a id="2691" class="Keyword">record</a> <a id="_×′_"></a><a id="2698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2698" class="Record Operator">_×′_</a> <a id="2703" class="Symbol">(</a><a id="2704" href="plfa.part1.Connectives.html#2704" class="Bound">A</a> <a id="2706" href="plfa.part1.Connectives.html#2706" class="Bound">B</a> <a id="2708" class="Symbol">:</a> <a id="2710" class="PrimitiveType">Set</a><a id="2713" class="Symbol">)</a> <a id="2715" class="Symbol">:</a> <a id="2717" class="PrimitiveType">Set</a> <a id="2721" class="Keyword">where</a>
  <a id="2729" class="Keyword">field</a>
    <a id="_×′_.proj₁′"></a><a id="2739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2739" class="Field">proj₁′</a> <a id="2746" class="Symbol">:</a> <a id="2748" href="plfa.part1.Connectives.html#2704" class="Bound">A</a>
    <a id="_×′_.proj₂′"></a><a id="2754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2754" class="Field">proj₂′</a> <a id="2761" class="Symbol">:</a> <a id="2763" href="plfa.part1.Connectives.html#2706" class="Bound">B</a>
<a id="2765" class="Keyword">open</a> <a id="2770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2698" class="Module Operator">_×′_</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

在这里，记录的构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B`.
{:/}

其中 `M` 是 `A` 类型的项，`N` 是 `B` 类型的项。

{::comment}
When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.
{:/}

当 `⟨_,_⟩` 在等式右手边的项中出现的时候，我们将其称作*构造子*（Constructor），当它出现在等式左边时，我们将其称作*析构器*（Destructor）。我们亦可将 `proj₁` 和 `proj₂`
称作析构器，因为它们起到相似的效果。

{::comment}
Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.
{:/}

其他的术语将 `⟨_,_⟩` 称作*引入*（Introduce）合取，将 `proj₁` 和 `proj₂` 称作*消去*（Eliminate）合取。前者亦记作 `×-I`，后者 `×-E₁` 和 `×-E₂`。如果我们从上到下来阅读这些规则，引入和消去正如其名字所说的那样：第一条*引入*一个运算符，所以运算符出现在结论中，而不是假设中；第二条*消去*一个带有运算符的式子，而运算符出现在假设中，而不是结论中。引入规则描述了运算符在什么情况下成立——即怎么样*定义*一个运算符。消去规则描述了运算符成立时，可以得出什么样的结论——即怎么样*使用*一个运算符。

{::comment}
(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

（上面一段内容由此处改编得来：*Propositions as Types*，作者：Philip Wadler，发表于 《ACM 通讯》，2015 年 9 月）

{::comment}
In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{:/}

在这样的情况下，先使用析构器，再使用构造子将结果重组，得到还是原来的积。

{% raw %}<pre class="Agda"><a id="η-×"></a><a id="4997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4997" class="Function">η-×</a> <a id="5001" class="Symbol">:</a> <a id="5003" class="Symbol">∀</a> <a id="5005" class="Symbol">{</a><a id="5006" href="plfa.part1.Connectives.html#5006" class="Bound">A</a> <a id="5008" href="plfa.part1.Connectives.html#5008" class="Bound">B</a> <a id="5010" class="Symbol">:</a> <a id="5012" class="PrimitiveType">Set</a><a id="5015" class="Symbol">}</a> <a id="5017" class="Symbol">(</a><a id="5018" href="plfa.part1.Connectives.html#5018" class="Bound">w</a> <a id="5020" class="Symbol">:</a> <a id="5022" href="plfa.part1.Connectives.html#5006" class="Bound">A</a> <a id="5024" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="5026" href="plfa.part1.Connectives.html#5008" class="Bound">B</a><a id="5027" class="Symbol">)</a> <a id="5029" class="Symbol">→</a> <a id="5031" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="5033" href="plfa.part1.Connectives.html#2203" class="Function">proj₁</a> <a id="5039" href="plfa.part1.Connectives.html#5018" class="Bound">w</a> <a id="5041" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="5043" href="plfa.part1.Connectives.html#2272" class="Function">proj₂</a> <a id="5049" href="plfa.part1.Connectives.html#5018" class="Bound">w</a> <a id="5051" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="5053" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5055" href="plfa.part1.Connectives.html#5018" class="Bound">w</a>
<a id="5057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4997" class="Function">η-×</a> <a id="5061" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="5063" href="plfa.part1.Connectives.html#5063" class="Bound">x</a> <a id="5065" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="5067" href="plfa.part1.Connectives.html#5067" class="Bound">y</a> <a id="5069" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="5071" class="Symbol">=</a> <a id="5073" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.
{:/}

左手边的模式匹配是必要的。用 `⟨ x , y ⟩` 来替换 `w` 让等式的两边可以化简成相同的项。

{::comment}
We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{:/}

我们设置合取的优先级，使它与除了析取之外结合的都不紧密：

{% raw %}<pre class="Agda"><a id="5475" class="Keyword">infixr</a> <a id="5482" class="Number">2</a> <a id="5484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1738" class="Datatype Operator">_×_</a>
</pre>{% endraw %}
{::comment}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.
{:/}

因此，`m ≤ n × n ≤ p` 解析为 `(m ≤ n) × (n ≤ p)`。

{::comment}
Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A × B` 称为 `A` 与 `B` 的*积*。在集合论中它也被称作*笛卡尔积*（Cartesian Product），在计算机科学中它对应*记录*类型。如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，那么类型 `A × B` 有 `m * n` 个不同的成员。这也是它被称为积的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型：

{% raw %}<pre class="Agda"><a id="6344" class="Keyword">data</a> <a id="Bool"></a><a id="6349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6349" class="Datatype">Bool</a> <a id="6354" class="Symbol">:</a> <a id="6356" class="PrimitiveType">Set</a> <a id="6360" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6368" class="InductiveConstructor">true</a>  <a id="6374" class="Symbol">:</a> <a id="6376" href="plfa.part1.Connectives.html#6349" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="6383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6383" class="InductiveConstructor">false</a> <a id="6389" class="Symbol">:</a> <a id="6391" href="plfa.part1.Connectives.html#6349" class="Datatype">Bool</a>

<a id="6397" class="Keyword">data</a> <a id="Tri"></a><a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6402" class="Datatype">Tri</a> <a id="6406" class="Symbol">:</a> <a id="6408" class="PrimitiveType">Set</a> <a id="6412" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="6420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6420" class="InductiveConstructor">aa</a> <a id="6423" class="Symbol">:</a> <a id="6425" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="6431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6431" class="InductiveConstructor">bb</a> <a id="6434" class="Symbol">:</a> <a id="6436" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="6442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6442" class="InductiveConstructor">cc</a> <a id="6445" class="Symbol">:</a> <a id="6447" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Then the type `Bool × Tri` has six members:
{:/}

那么，`Bool × Tri` 类型有如下的六个成员：

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：

{% raw %}<pre class="Agda"><a id="×-count"></a><a id="6805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6813" class="Symbol">:</a> <a id="6815" href="plfa.part1.Connectives.html#6349" class="Datatype">Bool</a> <a id="6820" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="6822" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a> <a id="6826" class="Symbol">→</a> <a id="6828" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="6830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6838" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6840" href="plfa.part1.Connectives.html#6368" class="InductiveConstructor">true</a>  <a id="6846" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6848" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a> <a id="6851" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6854" class="Symbol">=</a>  <a id="6857" class="Number">1</a>
<a id="6859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6867" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6869" href="plfa.part1.Connectives.html#6368" class="InductiveConstructor">true</a>  <a id="6875" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6877" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a> <a id="6880" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6883" class="Symbol">=</a>  <a id="6886" class="Number">2</a>
<a id="6888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6896" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6898" href="plfa.part1.Connectives.html#6368" class="InductiveConstructor">true</a>  <a id="6904" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6906" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a> <a id="6909" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6912" class="Symbol">=</a>  <a id="6915" class="Number">3</a>
<a id="6917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6925" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6927" href="plfa.part1.Connectives.html#6383" class="InductiveConstructor">false</a> <a id="6933" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6935" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a> <a id="6938" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6941" class="Symbol">=</a>  <a id="6944" class="Number">4</a>
<a id="6946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6954" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6956" href="plfa.part1.Connectives.html#6383" class="InductiveConstructor">false</a> <a id="6962" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6964" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a> <a id="6967" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6970" class="Symbol">=</a>  <a id="6973" class="Number">5</a>
<a id="6975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6805" class="Function">×-count</a> <a id="6983" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="6985" href="plfa.part1.Connectives.html#6383" class="InductiveConstructor">false</a> <a id="6991" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="6993" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a> <a id="6996" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>  <a id="6999" class="Symbol">=</a>  <a id="7002" class="Number">6</a>
</pre>{% endraw %}
{::comment}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.
{:/}

类型上的积与数的积有相似的性质——它们满足交换律和结合律。更确切地说，积在*在同构意义下*满足交换律和结合率。

{::comment}
For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{:/}

对于交换律，`to` 函数将有序对交换，将 `⟨ x , y ⟩` 变为 `⟨ y , x ⟩`，`from`
函数亦是如此（忽略命名）。在 `from∘to` 和 `to∘from` 中正确地实例化要匹配的模式是很重要的。使用 `λ w → refl` 作为 `from∘to` 的定义是不可行的，`to∘from` 同理。

{% raw %}<pre class="Agda"><a id="×-comm"></a><a id="7801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7801" class="Function">×-comm</a> <a id="7808" class="Symbol">:</a> <a id="7810" class="Symbol">∀</a> <a id="7812" class="Symbol">{</a><a id="7813" href="plfa.part1.Connectives.html#7813" class="Bound">A</a> <a id="7815" href="plfa.part1.Connectives.html#7815" class="Bound">B</a> <a id="7817" class="Symbol">:</a> <a id="7819" class="PrimitiveType">Set</a><a id="7822" class="Symbol">}</a> <a id="7824" class="Symbol">→</a> <a id="7826" href="plfa.part1.Connectives.html#7813" class="Bound">A</a> <a id="7828" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="7830" href="plfa.part1.Connectives.html#7815" class="Bound">B</a> <a id="7832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="7834" href="plfa.part1.Connectives.html#7815" class="Bound">B</a> <a id="7836" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="7838" href="plfa.part1.Connectives.html#7813" class="Bound">A</a>
<a id="7840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7801" class="Function">×-comm</a> <a id="7847" class="Symbol">=</a>
  <a id="7851" class="Keyword">record</a>
    <a id="7862" class="Symbol">{</a> <a id="7864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>       <a id="7873" class="Symbol">=</a>  <a id="7876" class="Symbol">λ{</a> <a id="7879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="7881" href="plfa.part1.Connectives.html#7881" class="Bound">x</a> <a id="7883" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="7885" href="plfa.part1.Connectives.html#7885" class="Bound">y</a> <a id="7887" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="7889" class="Symbol">→</a> <a id="7891" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="7893" href="plfa.part1.Connectives.html#7885" class="Bound">y</a> <a id="7895" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="7897" href="plfa.part1.Connectives.html#7881" class="Bound">x</a> <a id="7899" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="7901" class="Symbol">}</a>
    <a id="7907" class="Symbol">;</a> <a id="7909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>     <a id="7918" class="Symbol">=</a>  <a id="7921" class="Symbol">λ{</a> <a id="7924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="7926" href="plfa.part1.Connectives.html#7926" class="Bound">y</a> <a id="7928" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="7930" href="plfa.part1.Connectives.html#7930" class="Bound">x</a> <a id="7932" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="7934" class="Symbol">→</a> <a id="7936" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="7938" href="plfa.part1.Connectives.html#7930" class="Bound">x</a> <a id="7940" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="7942" href="plfa.part1.Connectives.html#7926" class="Bound">y</a> <a id="7944" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="7946" class="Symbol">}</a>
    <a id="7952" class="Symbol">;</a> <a id="7954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a>  <a id="7963" class="Symbol">=</a>  <a id="7966" class="Symbol">λ{</a> <a id="7969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="7971" href="plfa.part1.Connectives.html#7971" class="Bound">x</a> <a id="7973" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="7975" href="plfa.part1.Connectives.html#7975" class="Bound">y</a> <a id="7977" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="7979" class="Symbol">→</a> <a id="7981" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="7986" class="Symbol">}</a>
    <a id="7992" class="Symbol">;</a> <a id="7994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a>  <a id="8003" class="Symbol">=</a>  <a id="8006" class="Symbol">λ{</a> <a id="8009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="8011" href="plfa.part1.Connectives.html#8011" class="Bound">y</a> <a id="8013" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="8015" href="plfa.part1.Connectives.html#8015" class="Bound">x</a> <a id="8017" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="8019" class="Symbol">→</a> <a id="8021" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8026" class="Symbol">}</a>
    <a id="8032" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:
{:/}

满足*交换律*和*在同构意义下满足交换律*是不一样的。比较下列两个命题：

    m * n ≡ n * m
    A × B ≃ B × A

{::comment}
In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.
{:/}

在第一个情况下，我们可能有 `m` 是 `2`、`n` 是 `3`，那么 `m * n` 和 `n * m` 都是 `6`。在第二个情况下，我们可能有 `A` 是 `Bool` 和 `B` 是 `Tri`，但是 `Bool × Tri` 和
`Tri × Bool` *不是*一样的。但是存在一个两者之间的同构。例如：`⟨ true , aa ⟩` 是前者的成员，其对应后者的成员 `⟨ aa , true ⟩`。

{::comment}
For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于结合律来说，`to` 函数将两个有序对进行重组：将 `⟨ ⟨ x , y ⟩ , z ⟩` 转换为 `⟨ x , ⟨ y , z ⟩ ⟩`，
`from` 函数则为其逆。同样，左逆和右逆的证明需要在一个合适的模式来匹配，从而可以直接化简：

{% raw %}<pre class="Agda"><a id="×-assoc"></a><a id="9312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9312" class="Function">×-assoc</a> <a id="9320" class="Symbol">:</a> <a id="9322" class="Symbol">∀</a> <a id="9324" class="Symbol">{</a><a id="9325" href="plfa.part1.Connectives.html#9325" class="Bound">A</a> <a id="9327" href="plfa.part1.Connectives.html#9327" class="Bound">B</a> <a id="9329" href="plfa.part1.Connectives.html#9329" class="Bound">C</a> <a id="9331" class="Symbol">:</a> <a id="9333" class="PrimitiveType">Set</a><a id="9336" class="Symbol">}</a> <a id="9338" class="Symbol">→</a> <a id="9340" class="Symbol">(</a><a id="9341" href="plfa.part1.Connectives.html#9325" class="Bound">A</a> <a id="9343" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="9345" href="plfa.part1.Connectives.html#9327" class="Bound">B</a><a id="9346" class="Symbol">)</a> <a id="9348" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="9350" href="plfa.part1.Connectives.html#9329" class="Bound">C</a> <a id="9352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="9354" href="plfa.part1.Connectives.html#9325" class="Bound">A</a> <a id="9356" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="9358" class="Symbol">(</a><a id="9359" href="plfa.part1.Connectives.html#9327" class="Bound">B</a> <a id="9361" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="9363" href="plfa.part1.Connectives.html#9329" class="Bound">C</a><a id="9364" class="Symbol">)</a>
<a id="9366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9312" class="Function">×-assoc</a> <a id="9374" class="Symbol">=</a>
  <a id="9378" class="Keyword">record</a>
    <a id="9389" class="Symbol">{</a> <a id="9391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="9399" class="Symbol">=</a> <a id="9401" class="Symbol">λ{</a> <a id="9404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="9406" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9408" href="plfa.part1.Connectives.html#9408" class="Bound">x</a> <a id="9410" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9412" href="plfa.part1.Connectives.html#9412" class="Bound">y</a> <a id="9414" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9416" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9418" href="plfa.part1.Connectives.html#9418" class="Bound">z</a> <a id="9420" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9422" class="Symbol">→</a> <a id="9424" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9426" href="plfa.part1.Connectives.html#9408" class="Bound">x</a> <a id="9428" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9430" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9432" href="plfa.part1.Connectives.html#9412" class="Bound">y</a> <a id="9434" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9436" href="plfa.part1.Connectives.html#9418" class="Bound">z</a> <a id="9438" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9440" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9442" class="Symbol">}</a>
    <a id="9448" class="Symbol">;</a> <a id="9450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="9458" class="Symbol">=</a> <a id="9460" class="Symbol">λ{</a> <a id="9463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="9465" href="plfa.part1.Connectives.html#9465" class="Bound">x</a> <a id="9467" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9469" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9471" href="plfa.part1.Connectives.html#9471" class="Bound">y</a> <a id="9473" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9475" href="plfa.part1.Connectives.html#9475" class="Bound">z</a> <a id="9477" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9479" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9481" class="Symbol">→</a> <a id="9483" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9485" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9487" href="plfa.part1.Connectives.html#9465" class="Bound">x</a> <a id="9489" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9491" href="plfa.part1.Connectives.html#9471" class="Bound">y</a> <a id="9493" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9495" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9497" href="plfa.part1.Connectives.html#9475" class="Bound">z</a> <a id="9499" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9501" class="Symbol">}</a>
    <a id="9507" class="Symbol">;</a> <a id="9509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="9517" class="Symbol">=</a> <a id="9519" class="Symbol">λ{</a> <a id="9522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="9524" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9526" href="plfa.part1.Connectives.html#9526" class="Bound">x</a> <a id="9528" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9530" href="plfa.part1.Connectives.html#9530" class="Bound">y</a> <a id="9532" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9534" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9536" href="plfa.part1.Connectives.html#9536" class="Bound">z</a> <a id="9538" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9540" class="Symbol">→</a> <a id="9542" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9547" class="Symbol">}</a>
    <a id="9553" class="Symbol">;</a> <a id="9555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="9563" class="Symbol">=</a> <a id="9565" class="Symbol">λ{</a> <a id="9568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="9570" href="plfa.part1.Connectives.html#9570" class="Bound">x</a> <a id="9572" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9574" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="9576" href="plfa.part1.Connectives.html#9576" class="Bound">y</a> <a id="9578" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="9580" href="plfa.part1.Connectives.html#9580" class="Bound">z</a> <a id="9582" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9584" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="9586" class="Symbol">→</a> <a id="9588" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9593" class="Symbol">}</a>
    <a id="9599" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:
{:/}

满足*结合律*和*在同构意义下满足结合律*是不一样的。比较下列两个命题：

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

{::comment}
For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.
{:/}

举个例子，`(ℕ × Bool) × Tri` 与 `ℕ × (Bool × Tri)` *不同*，但是两个类型之间存在同构。例如 `⟨ ⟨ 1 , true ⟩ , aa ⟩`，一个前者的成员，与 `⟨ 1 , ⟨ true , aa ⟩ ⟩`，一个后者的成员，相对应。

{::comment}
#### Exercise `⇔≃×` (recommended)
{:/}

#### 练习 `⇔≃×` （推荐）

{::comment}
Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.
{:/}

证明[之前]({{ site.baseurl }}/Isomorphism/#iff)定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。

{::comment}
{% raw %}<pre class="Agda"><a id="10567" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10604" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Truth is unit
{:/}

## 真即是单元类型

{::comment}
Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{:/}

恒真 `⊤` 恒成立。我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="10811" class="Keyword">data</a> <a id="⊤"></a><a id="10816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10816" class="Datatype">⊤</a> <a id="10818" class="Symbol">:</a> <a id="10820" class="PrimitiveType">Set</a> <a id="10824" class="Keyword">where</a>

  <a id="⊤.tt"></a><a id="10833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10833" class="InductiveConstructor">tt</a> <a id="10836" class="Symbol">:</a>
    <a id="10842" class="Comment">--</a>
    <a id="10849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10816" class="Datatype">⊤</a>
</pre>{% endraw %}
{::comment}
Evidence that `⊤` holds is of the form `tt`.
{:/}

`⊤` 成立的证明由 `tt` 的形式构成。

{::comment}
There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.
{:/}

恒真有引入规则，但没有消去规则。给定一个 `⊤` 成立的证明，我们不能得出任何有趣的结论。因为恒真恒成立，知道恒真成立不会给我们带来新的知识。

{::comment}
The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{:/}

`η-×` 的 零元形式是 `η-⊤`，其断言了任何 `⊤` 类型的值一定等于 `tt`：

{% raw %}<pre class="Agda"><a id="η-⊤"></a><a id="11413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11413" class="Function">η-⊤</a> <a id="11417" class="Symbol">:</a> <a id="11419" class="Symbol">∀</a> <a id="11421" class="Symbol">(</a><a id="11422" href="plfa.part1.Connectives.html#11422" class="Bound">w</a> <a id="11424" class="Symbol">:</a> <a id="11426" href="plfa.part1.Connectives.html#10816" class="Datatype">⊤</a><a id="11427" class="Symbol">)</a> <a id="11429" class="Symbol">→</a> <a id="11431" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="11434" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11436" href="plfa.part1.Connectives.html#11422" class="Bound">w</a>
<a id="11438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11413" class="Function">η-⊤</a> <a id="11442" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="11445" class="Symbol">=</a> <a id="11447" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.
{:/}

左手边的模式匹配是必要的。将 `w` 替换为 `tt` 让等式两边可以化简为相同的值。

{::comment}
We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:

我们将 `⊤` 称为*单元*类型（Unit Type）。实际上，`⊤` 类型只有一个成员 `tt`。例如，下面的函数枚举了所有 `⊤` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊤-count"></a><a id="11949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11949" class="Function">⊤-count</a> <a id="11957" class="Symbol">:</a> <a id="11959" href="plfa.part1.Connectives.html#10816" class="Datatype">⊤</a> <a id="11961" class="Symbol">→</a> <a id="11963" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="11965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11949" class="Function">⊤-count</a> <a id="11973" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="11976" class="Symbol">=</a> <a id="11978" class="Number">1</a>
</pre>{% endraw %}
{::comment}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于数来说，1 是乘法的幺元。对应地，单元是积的幺元（*在同构意义下*）。对于左幺元来说，
`to` 函数将 `⟨ tt , x ⟩` 转换成 `x`， `from` 函数则是其反函数。左逆的证明需要匹配一个合适的模式来化简：

{% raw %}<pre class="Agda"><a id="⊤-identityˡ"></a><a id="12453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12453" class="Function">⊤-identityˡ</a> <a id="12465" class="Symbol">:</a> <a id="12467" class="Symbol">∀</a> <a id="12469" class="Symbol">{</a><a id="12470" href="plfa.part1.Connectives.html#12470" class="Bound">A</a> <a id="12472" class="Symbol">:</a> <a id="12474" class="PrimitiveType">Set</a><a id="12477" class="Symbol">}</a> <a id="12479" class="Symbol">→</a> <a id="12481" href="plfa.part1.Connectives.html#10816" class="Datatype">⊤</a> <a id="12483" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="12485" href="plfa.part1.Connectives.html#12470" class="Bound">A</a> <a id="12487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="12489" href="plfa.part1.Connectives.html#12470" class="Bound">A</a>
<a id="12491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12453" class="Function">⊤-identityˡ</a> <a id="12503" class="Symbol">=</a>
  <a id="12507" class="Keyword">record</a>
    <a id="12518" class="Symbol">{</a> <a id="12520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="12528" class="Symbol">=</a> <a id="12530" class="Symbol">λ{</a> <a id="12533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="12535" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="12538" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="12540" href="plfa.part1.Connectives.html#12540" class="Bound">x</a> <a id="12542" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="12544" class="Symbol">→</a> <a id="12546" href="plfa.part1.Connectives.html#12540" class="Bound">x</a> <a id="12548" class="Symbol">}</a>
    <a id="12554" class="Symbol">;</a> <a id="12556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="12564" class="Symbol">=</a> <a id="12566" class="Symbol">λ{</a> <a id="12569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12569" class="Bound">x</a> <a id="12571" class="Symbol">→</a> <a id="12573" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="12575" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="12578" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="12580" href="plfa.part1.Connectives.html#12569" class="Bound">x</a> <a id="12582" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="12584" class="Symbol">}</a>
    <a id="12590" class="Symbol">;</a> <a id="12592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="12600" class="Symbol">=</a> <a id="12602" class="Symbol">λ{</a> <a id="12605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="12607" href="plfa.part1.Connectives.html#10833" class="InductiveConstructor">tt</a> <a id="12610" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="12612" href="plfa.part1.Connectives.html#12612" class="Bound">x</a> <a id="12614" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="12616" class="Symbol">→</a> <a id="12618" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12623" class="Symbol">}</a>
    <a id="12629" class="Symbol">;</a> <a id="12631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="12639" class="Symbol">=</a> <a id="12641" class="Symbol">λ{</a> <a id="12644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12644" class="Bound">x</a> <a id="12646" class="Symbol">→</a> <a id="12648" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12653" class="Symbol">}</a>
    <a id="12659" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:
{:/}

*幺元*和*在同构意义下的幺元*是不一样的。比较下列两个命题：

    1 * m ≡ m
    ⊤ × A ≃ A

{::comment}
In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.
{:/}

在第一种情况下，我们可能有 `m` 是 `2`，那么 `1 * m` 和 `m` 都为 `2`。在第二种情况下，我们可能有 `A` 是 `Bool`，但是 `⊤ × Bool` 和 `Bool` 是不同的。例如：`⟨ tt , true ⟩` 是前者的成员，其对应后者的成员 `true`。

{::comment}
Right identity follows from commutativity of product and left identity:
{:/}

右幺元可以由积的交换律得来：

{% raw %}<pre class="Agda"><a id="⊤-identityʳ"></a><a id="13495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13495" class="Function">⊤-identityʳ</a> <a id="13507" class="Symbol">:</a> <a id="13509" class="Symbol">∀</a> <a id="13511" class="Symbol">{</a><a id="13512" href="plfa.part1.Connectives.html#13512" class="Bound">A</a> <a id="13514" class="Symbol">:</a> <a id="13516" class="PrimitiveType">Set</a><a id="13519" class="Symbol">}</a> <a id="13521" class="Symbol">→</a> <a id="13523" class="Symbol">(</a><a id="13524" href="plfa.part1.Connectives.html#13512" class="Bound">A</a> <a id="13526" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="13528" href="plfa.part1.Connectives.html#10816" class="Datatype">⊤</a><a id="13529" class="Symbol">)</a> <a id="13531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="13533" href="plfa.part1.Connectives.html#13512" class="Bound">A</a>
<a id="13535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13495" class="Function">⊤-identityʳ</a> <a id="13547" class="Symbol">{</a><a id="13548" href="plfa.part1.Connectives.html#13548" class="Bound">A</a><a id="13549" class="Symbol">}</a> <a id="13551" class="Symbol">=</a>
  <a id="13555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11069" class="Function Operator">≃-begin</a>
    <a id="13567" class="Symbol">(</a><a id="13568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13548" class="Bound">A</a> <a id="13570" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="13572" href="plfa.part1.Connectives.html#10816" class="Datatype">⊤</a><a id="13573" class="Symbol">)</a>
  <a id="13577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11153" class="Function Operator">≃⟨</a> <a id="13580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7801" class="Function">×-comm</a> <a id="13587" href="plfa.part1.Isomorphism.html#11153" class="Function Operator">⟩</a>
    <a id="13593" class="Symbol">(</a><a id="13594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10816" class="Datatype">⊤</a> <a id="13596" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="13598" href="plfa.part1.Connectives.html#13548" class="Bound">A</a><a id="13599" class="Symbol">)</a>
  <a id="13603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11153" class="Function Operator">≃⟨</a> <a id="13606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12453" class="Function">⊤-identityˡ</a> <a id="13618" href="plfa.part1.Isomorphism.html#11153" class="Function Operator">⟩</a>
    <a id="13624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13548" class="Bound">A</a>
  <a id="13628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11272" class="Function Operator">≃-∎</a>
</pre>{% endraw %}
{::comment}
Here we have used a chain of isomorphisms, analogous to that used for
equality.
{:/}

我们在此使用了同构链，与等式链相似。

{::comment}
## Disjunction is sum
{:/}

## 析取即是和

{::comment}
Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，析取 `A ⊎ B` 在 `A` 成立或者 `B` 成立时成立。我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="14063" class="Keyword">data</a> <a id="_⊎_"></a><a id="14068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14068" class="Datatype Operator">_⊎_</a> <a id="14072" class="Symbol">(</a><a id="14073" href="plfa.part1.Connectives.html#14073" class="Bound">A</a> <a id="14075" href="plfa.part1.Connectives.html#14075" class="Bound">B</a> <a id="14077" class="Symbol">:</a> <a id="14079" class="PrimitiveType">Set</a><a id="14082" class="Symbol">)</a> <a id="14084" class="Symbol">:</a> <a id="14086" class="PrimitiveType">Set</a> <a id="14090" class="Keyword">where</a>

  <a id="_⊎_.inj₁"></a><a id="14099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14099" class="InductiveConstructor">inj₁</a> <a id="14104" class="Symbol">:</a>
      <a id="14112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14073" class="Bound">A</a>
      <a id="14120" class="Comment">-----</a>
    <a id="14130" class="Symbol">→</a> <a id="14132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14073" class="Bound">A</a> <a id="14134" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="14136" href="plfa.part1.Connectives.html#14075" class="Bound">B</a>

  <a id="_⊎_.inj₂"></a><a id="14141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14141" class="InductiveConstructor">inj₂</a> <a id="14146" class="Symbol">:</a>
      <a id="14154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14075" class="Bound">B</a>
      <a id="14162" class="Comment">-----</a>
    <a id="14172" class="Symbol">→</a> <a id="14174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14073" class="Bound">A</a> <a id="14176" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="14178" href="plfa.part1.Connectives.html#14075" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.
{:/}

`A ⊎ B` 成立的证明有两个形式： `inj₁ M`，其中 `M` 是 `A` 成立的证明，或者
`inj₂ N`，其中 `N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
{:/}

给定 `A → C` 和 `B → C` 成立的证明，那么给定一个 `A ⊎ B` 的证明，我们可以得出 `C` 成立：

{% raw %}<pre class="Agda"><a id="case-⊎"></a><a id="14651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14651" class="Function">case-⊎</a> <a id="14658" class="Symbol">:</a> <a id="14660" class="Symbol">∀</a> <a id="14662" class="Symbol">{</a><a id="14663" href="plfa.part1.Connectives.html#14663" class="Bound">A</a> <a id="14665" href="plfa.part1.Connectives.html#14665" class="Bound">B</a> <a id="14667" href="plfa.part1.Connectives.html#14667" class="Bound">C</a> <a id="14669" class="Symbol">:</a> <a id="14671" class="PrimitiveType">Set</a><a id="14674" class="Symbol">}</a>
  <a id="14678" class="Symbol">→</a> <a id="14680" class="Symbol">(</a><a id="14681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14663" class="Bound">A</a> <a id="14683" class="Symbol">→</a> <a id="14685" href="plfa.part1.Connectives.html#14667" class="Bound">C</a><a id="14686" class="Symbol">)</a>
  <a id="14690" class="Symbol">→</a> <a id="14692" class="Symbol">(</a><a id="14693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14665" class="Bound">B</a> <a id="14695" class="Symbol">→</a> <a id="14697" href="plfa.part1.Connectives.html#14667" class="Bound">C</a><a id="14698" class="Symbol">)</a>
  <a id="14702" class="Symbol">→</a> <a id="14704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14663" class="Bound">A</a> <a id="14706" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="14708" href="plfa.part1.Connectives.html#14665" class="Bound">B</a>
    <a id="14714" class="Comment">-----------</a>
  <a id="14728" class="Symbol">→</a> <a id="14730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14667" class="Bound">C</a>
<a id="14732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14651" class="Function">case-⊎</a> <a id="14739" href="plfa.part1.Connectives.html#14739" class="Bound">f</a> <a id="14741" href="plfa.part1.Connectives.html#14741" class="Bound">g</a> <a id="14743" class="Symbol">(</a><a id="14744" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="14749" href="plfa.part1.Connectives.html#14749" class="Bound">x</a><a id="14750" class="Symbol">)</a> <a id="14752" class="Symbol">=</a> <a id="14754" href="plfa.part1.Connectives.html#14739" class="Bound">f</a> <a id="14756" href="plfa.part1.Connectives.html#14749" class="Bound">x</a>
<a id="14758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14651" class="Function">case-⊎</a> <a id="14765" href="plfa.part1.Connectives.html#14765" class="Bound">f</a> <a id="14767" href="plfa.part1.Connectives.html#14767" class="Bound">g</a> <a id="14769" class="Symbol">(</a><a id="14770" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="14775" href="plfa.part1.Connectives.html#14775" class="Bound">y</a><a id="14776" class="Symbol">)</a> <a id="14778" class="Symbol">=</a> <a id="14780" href="plfa.part1.Connectives.html#14767" class="Bound">g</a> <a id="14782" href="plfa.part1.Connectives.html#14775" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.
{:/}

对 `inj₁` 和 `inj₂` 进行模式匹配，是我们使用析取成立的证明的常见方法。

{::comment}
When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.
{:/}

当 `inj₁` 和 `inj₂` 在等式右手边出现的时候，我们将其称作*构造子*，当它出现在等式左边时，我们将其称作*析构器*。我们亦可将 `case-⊎`
称作析构器，因为它们起到相似的效果。其他术语将 `inj₁` 和 `inj₂` 称为*引入*析取，将 `case-⊎` 称为*消去*析取。前者亦被称为 `⊎-I₁` 和 `⊎-I₂`，后者 `⊎-E`。

{::comment}
Applying the destructor to each of the constructors is the identity:
{:/}

对每个构造子使用析构器得到的是原来的值：

{% raw %}<pre class="Agda"><a id="η-⊎"></a><a id="15756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15756" class="Function">η-⊎</a> <a id="15760" class="Symbol">:</a> <a id="15762" class="Symbol">∀</a> <a id="15764" class="Symbol">{</a><a id="15765" href="plfa.part1.Connectives.html#15765" class="Bound">A</a> <a id="15767" href="plfa.part1.Connectives.html#15767" class="Bound">B</a> <a id="15769" class="Symbol">:</a> <a id="15771" class="PrimitiveType">Set</a><a id="15774" class="Symbol">}</a> <a id="15776" class="Symbol">(</a><a id="15777" href="plfa.part1.Connectives.html#15777" class="Bound">w</a> <a id="15779" class="Symbol">:</a> <a id="15781" href="plfa.part1.Connectives.html#15765" class="Bound">A</a> <a id="15783" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="15785" href="plfa.part1.Connectives.html#15767" class="Bound">B</a><a id="15786" class="Symbol">)</a> <a id="15788" class="Symbol">→</a> <a id="15790" href="plfa.part1.Connectives.html#14651" class="Function">case-⊎</a> <a id="15797" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="15802" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="15807" href="plfa.part1.Connectives.html#15777" class="Bound">w</a> <a id="15809" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15811" href="plfa.part1.Connectives.html#15777" class="Bound">w</a>
<a id="15813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15756" class="Function">η-⊎</a> <a id="15817" class="Symbol">(</a><a id="15818" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="15823" href="plfa.part1.Connectives.html#15823" class="Bound">x</a><a id="15824" class="Symbol">)</a> <a id="15826" class="Symbol">=</a> <a id="15828" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="15833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15756" class="Function">η-⊎</a> <a id="15837" class="Symbol">(</a><a id="15838" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="15843" href="plfa.part1.Connectives.html#15843" class="Bound">y</a><a id="15844" class="Symbol">)</a> <a id="15846" class="Symbol">=</a> <a id="15848" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
More generally, we can also throw in an arbitrary function from a disjunction:
{:/}

更普遍地来说，我们亦可对于析取使用一个任意的函数：

{% raw %}<pre class="Agda"><a id="uniq-⊎"></a><a id="15986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15986" class="Function">uniq-⊎</a> <a id="15993" class="Symbol">:</a> <a id="15995" class="Symbol">∀</a> <a id="15997" class="Symbol">{</a><a id="15998" href="plfa.part1.Connectives.html#15998" class="Bound">A</a> <a id="16000" href="plfa.part1.Connectives.html#16000" class="Bound">B</a> <a id="16002" href="plfa.part1.Connectives.html#16002" class="Bound">C</a> <a id="16004" class="Symbol">:</a> <a id="16006" class="PrimitiveType">Set</a><a id="16009" class="Symbol">}</a> <a id="16011" class="Symbol">(</a><a id="16012" href="plfa.part1.Connectives.html#16012" class="Bound">h</a> <a id="16014" class="Symbol">:</a> <a id="16016" href="plfa.part1.Connectives.html#15998" class="Bound">A</a> <a id="16018" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="16020" href="plfa.part1.Connectives.html#16000" class="Bound">B</a> <a id="16022" class="Symbol">→</a> <a id="16024" href="plfa.part1.Connectives.html#16002" class="Bound">C</a><a id="16025" class="Symbol">)</a> <a id="16027" class="Symbol">(</a><a id="16028" href="plfa.part1.Connectives.html#16028" class="Bound">w</a> <a id="16030" class="Symbol">:</a> <a id="16032" href="plfa.part1.Connectives.html#15998" class="Bound">A</a> <a id="16034" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="16036" href="plfa.part1.Connectives.html#16000" class="Bound">B</a><a id="16037" class="Symbol">)</a> <a id="16039" class="Symbol">→</a>
  <a id="16043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14651" class="Function">case-⊎</a> <a id="16050" class="Symbol">(</a><a id="16051" href="plfa.part1.Connectives.html#16012" class="Bound">h</a> <a id="16053" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16055" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a><a id="16059" class="Symbol">)</a> <a id="16061" class="Symbol">(</a><a id="16062" href="plfa.part1.Connectives.html#16012" class="Bound">h</a> <a id="16064" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16066" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a><a id="16070" class="Symbol">)</a> <a id="16072" href="plfa.part1.Connectives.html#16028" class="Bound">w</a> <a id="16074" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16076" href="plfa.part1.Connectives.html#16012" class="Bound">h</a> <a id="16078" href="plfa.part1.Connectives.html#16028" class="Bound">w</a>
<a id="16080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15986" class="Function">uniq-⊎</a> <a id="16087" href="plfa.part1.Connectives.html#16087" class="Bound">h</a> <a id="16089" class="Symbol">(</a><a id="16090" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="16095" href="plfa.part1.Connectives.html#16095" class="Bound">x</a><a id="16096" class="Symbol">)</a> <a id="16098" class="Symbol">=</a> <a id="16100" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="16105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15986" class="Function">uniq-⊎</a> <a id="16112" href="plfa.part1.Connectives.html#16112" class="Bound">h</a> <a id="16114" class="Symbol">(</a><a id="16115" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="16120" href="plfa.part1.Connectives.html#16120" class="Bound">y</a><a id="16121" class="Symbol">)</a> <a id="16123" class="Symbol">=</a> <a id="16125" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.
{:/}

左手边的模式匹配是必要的。用 `inj₁ x` 来替换 `w` 让等式的两边可以化简成相同的项，
`inj₂ y` 同理。

{::comment}
We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
{:/}

我们设置析取的优先级，使它与任何已经定义的运算符都结合的不紧密：

{% raw %}<pre class="Agda"><a id="16563" class="Keyword">infixr</a> <a id="16570" class="Number">1</a> <a id="16572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14068" class="Datatype Operator">_⊎_</a>
</pre>{% endraw %}
{::comment}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.
{:/}

因此 `A × C ⊎ B × C` 解析为 `(A × C) ⊎ (B × C)`。

{::comment}
Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A ⊎ B` 称为 `A` 与 `B` 的*和*。在集合论中它也被称作*不交并*（Disjoint Union），在计算机科学中它对应*变体记录*类型。如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，那么类型 `A ⊎ B` 有 `m + n` 个不同的成员。这也是它被称为和的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，如之前的定义。那么，`Bool ⊎ Tri` 类型有如下的五个成员：

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool ⊎ Tri` 的参数：

{% raw %}<pre class="Agda"><a id="⊎-count"></a><a id="17749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17757" class="Symbol">:</a> <a id="17759" href="plfa.part1.Connectives.html#6349" class="Datatype">Bool</a> <a id="17764" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="17766" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a> <a id="17770" class="Symbol">→</a> <a id="17772" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="17774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17782" class="Symbol">(</a><a id="17783" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="17788" href="plfa.part1.Connectives.html#6368" class="InductiveConstructor">true</a><a id="17792" class="Symbol">)</a>   <a id="17796" class="Symbol">=</a>  <a id="17799" class="Number">1</a>
<a id="17801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17809" class="Symbol">(</a><a id="17810" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="17815" href="plfa.part1.Connectives.html#6383" class="InductiveConstructor">false</a><a id="17820" class="Symbol">)</a>  <a id="17823" class="Symbol">=</a>  <a id="17826" class="Number">2</a>
<a id="17828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17836" class="Symbol">(</a><a id="17837" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="17842" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a><a id="17844" class="Symbol">)</a>     <a id="17850" class="Symbol">=</a>  <a id="17853" class="Number">3</a>
<a id="17855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17863" class="Symbol">(</a><a id="17864" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="17869" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a><a id="17871" class="Symbol">)</a>     <a id="17877" class="Symbol">=</a>  <a id="17880" class="Number">4</a>
<a id="17882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17749" class="Function">⊎-count</a> <a id="17890" class="Symbol">(</a><a id="17891" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="17896" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a><a id="17898" class="Symbol">)</a>     <a id="17904" class="Symbol">=</a>  <a id="17907" class="Number">5</a>
</pre>{% endraw %}
{::comment}
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.
{:/}

类型上的和与数的和有相似的性质——它们满足交换律和结合律。更确切地说，和在*在同构意义下*是交换和结合的。

{::comment}
#### Exercise `⊎-comm` (recommended)
{:/}

#### 练习 `⊎-comm` （推荐）

{::comment}
Show sum is commutative up to isomorphism.
{:/}

证明和类型在同构意义下满足交换律。

{::comment}
{% raw %}<pre class="Agda"><a id="18281" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18318" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊎-assoc` (practice)
{:/}

#### 练习 `⊎-assoc`（实践）

{::comment}
Show sum is associative up to isomorphism.
{:/}

证明和类型在同构意义下满足结合律。

{::comment}
{% raw %}<pre class="Agda"><a id="18508" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18545" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## False is empty
{:/}

## 假即是空类型

{::comment}
False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
{:/}

恒假 `⊥` 从不成立。我们将这个概念用合适的归纳类型来形式化：

{::comment}
FIXME: the code block is removed to make Agda not recognise this as code.
data ⊥ : Set where
  -- no clauses!
{:/}

{% raw %}<pre class="Agda"><a id="18881" class="Keyword">data</a> <a id="⊥"></a><a id="18886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18886" class="Datatype">⊥</a> <a id="18888" class="Symbol">:</a> <a id="18890" class="PrimitiveType">Set</a> <a id="18894" class="Keyword">where</a>
  <a id="18902" class="Comment">-- 没有语句！</a>
</pre>{% endraw %}
{::comment}
There is no possible evidence that `⊥` holds.
{:/}

没有 `⊥` 成立的证明。

{::comment}
Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
{:/}

与 `⊤` 相对偶，`⊥` 没有引入规则，但是有消去规则。因为恒假从不成立，如果它一旦成立，我们就进入了矛盾之中。给定 `⊥` 成立的证明，我们可以得出任何结论！这是逻辑学的基本原理，又由中世纪的拉丁文词组 _ex falso_ 为名。小孩子也由诸如
“如果猪有翅膀，那我就是示巴女王”的词组中知晓。我们如下将它形式化：

{% raw %}<pre class="Agda"><a id="⊥-elim"></a><a id="19629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19629" class="Function">⊥-elim</a> <a id="19636" class="Symbol">:</a> <a id="19638" class="Symbol">∀</a> <a id="19640" class="Symbol">{</a><a id="19641" href="plfa.part1.Connectives.html#19641" class="Bound">A</a> <a id="19643" class="Symbol">:</a> <a id="19645" class="PrimitiveType">Set</a><a id="19648" class="Symbol">}</a>
  <a id="19652" class="Symbol">→</a> <a id="19654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18886" class="Datatype">⊥</a>
    <a id="19660" class="Comment">--</a>
  <a id="19665" class="Symbol">→</a> <a id="19667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19641" class="Bound">A</a>
<a id="19669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19629" class="Function">⊥-elim</a> <a id="19676" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.
{:/}

这是我们第一次使用*荒谬模式*（Absurd Pattern） `()`。在这里，因为 `⊥`
是一个没有成员的类型，我们用 `()` 模式来指明这里不可能匹配任何这个类型的值。

{::comment}
The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.
{:/}

`case-⊎` 的零元形式是 `⊥-elim`。类比的来说，它应该叫做 `case-⊥`，但是我们在此使用标准库中使用的名字。

{::comment}
The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
{:/}

`uniq-⊎` 的零元形式是 `uniq-⊥`，其断言了 `⊥-elim` 和任何取 `⊥` 的函数是等价的。

{% raw %}<pre class="Agda"><a id="uniq-⊥"></a><a id="20419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20419" class="Function">uniq-⊥</a> <a id="20426" class="Symbol">:</a> <a id="20428" class="Symbol">∀</a> <a id="20430" class="Symbol">{</a><a id="20431" href="plfa.part1.Connectives.html#20431" class="Bound">C</a> <a id="20433" class="Symbol">:</a> <a id="20435" class="PrimitiveType">Set</a><a id="20438" class="Symbol">}</a> <a id="20440" class="Symbol">(</a><a id="20441" href="plfa.part1.Connectives.html#20441" class="Bound">h</a> <a id="20443" class="Symbol">:</a> <a id="20445" href="plfa.part1.Connectives.html#18886" class="Datatype">⊥</a> <a id="20447" class="Symbol">→</a> <a id="20449" href="plfa.part1.Connectives.html#20431" class="Bound">C</a><a id="20450" class="Symbol">)</a> <a id="20452" class="Symbol">(</a><a id="20453" href="plfa.part1.Connectives.html#20453" class="Bound">w</a> <a id="20455" class="Symbol">:</a> <a id="20457" href="plfa.part1.Connectives.html#18886" class="Datatype">⊥</a><a id="20458" class="Symbol">)</a> <a id="20460" class="Symbol">→</a> <a id="20462" href="plfa.part1.Connectives.html#19629" class="Function">⊥-elim</a> <a id="20469" href="plfa.part1.Connectives.html#20453" class="Bound">w</a> <a id="20471" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="20473" href="plfa.part1.Connectives.html#20441" class="Bound">h</a> <a id="20475" href="plfa.part1.Connectives.html#20453" class="Bound">w</a>
<a id="20477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20419" class="Function">uniq-⊥</a> <a id="20484" href="plfa.part1.Connectives.html#20484" class="Bound">h</a> <a id="20486" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.
{:/}

使用荒谬模式断言了 `w` 没有任何可能的值，因此等式显然成立。

{::comment}
We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:

我们将 `⊥` 成为*空*类型（Empty Type）。实际上，`⊥` 类型没有成员。例如，下面的函数枚举了所有 `⊥` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊥-count"></a><a id="20900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20900" class="Function">⊥-count</a> <a id="20908" class="Symbol">:</a> <a id="20910" href="plfa.part1.Connectives.html#18886" class="Datatype">⊥</a> <a id="20912" class="Symbol">→</a> <a id="20914" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="20916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20900" class="Function">⊥-count</a> <a id="20924" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.
{:/}

同样，荒谬模式告诉我们没有值可以来匹配类型 `⊥`。

{::comment}
For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.
{:/}

对于数来说，0 是加法的幺元。对应地，空是和的幺元（*在同构意义下*）。

{::comment}
#### Exercise `⊥-identityˡ` (recommended)
{:/}

#### 练习 `⊥-identityˡ` （推荐）

{::comment}
Show empty is the left identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的左幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21427" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21464" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
#### Exercise `⊥-identityʳ` (practice)

#### 练习 `⊥-identityʳ`（实践）

{::comment}
Show empty is the right identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的右幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21661" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21698" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Implication is function {#implication}
{:/}

## 蕴涵即是函数 {#implication}

{::comment}
Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.
{:/}

给定两个命题 `A` 和 `B`，其蕴涵 `A → B` 在任何 `A` 成立的时候，`B` 也成立时成立。我们用函数类型来形式化蕴涵，如本书中通篇出现的那样。


{::comment}
Evidence that `A → B` holds is of the form
{:/}

`A → B` 成立的证据由下面的形式组成：

    λ (x : A) → N

{::comment}
where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.
{:/}

其中 `N` 是一个类型为 `B` 的项，其包括了一个类型为 `A` 的自由变量 `x`。给定一个 `A → B` 成立的证明 `L`，和一个 `A` 成立的证明 `M`，那么 `L M` 是 `B` 成立的证明。也就是说，`A → B` 成立的证明是一个函数，将 `A` 成立的证明转换成 `B` 成立的证明。

{::comment}
Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
{:/}

换句话说，如果知道 `A → B` 和 `A` 同时成立，那么我们可以推出 `B` 成立：

{% raw %}<pre class="Agda"><a id="→-elim"></a><a id="22918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22918" class="Function">→-elim</a> <a id="22925" class="Symbol">:</a> <a id="22927" class="Symbol">∀</a> <a id="22929" class="Symbol">{</a><a id="22930" href="plfa.part1.Connectives.html#22930" class="Bound">A</a> <a id="22932" href="plfa.part1.Connectives.html#22932" class="Bound">B</a> <a id="22934" class="Symbol">:</a> <a id="22936" class="PrimitiveType">Set</a><a id="22939" class="Symbol">}</a>
  <a id="22943" class="Symbol">→</a> <a id="22945" class="Symbol">(</a><a id="22946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22930" class="Bound">A</a> <a id="22948" class="Symbol">→</a> <a id="22950" href="plfa.part1.Connectives.html#22932" class="Bound">B</a><a id="22951" class="Symbol">)</a>
  <a id="22955" class="Symbol">→</a> <a id="22957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22930" class="Bound">A</a>
    <a id="22963" class="Comment">-------</a>
  <a id="22973" class="Symbol">→</a> <a id="22975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22932" class="Bound">B</a>
<a id="22977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22918" class="Function">→-elim</a> <a id="22984" href="plfa.part1.Connectives.html#22984" class="Bound">L</a> <a id="22986" href="plfa.part1.Connectives.html#22986" class="Bound">M</a> <a id="22988" class="Symbol">=</a> <a id="22990" href="plfa.part1.Connectives.html#22984" class="Bound">L</a> <a id="22992" href="plfa.part1.Connectives.html#22986" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.
{:/}

在中世纪，这条规则被叫做 _modus ponens_，它与函数应用相对应。

{::comment}
Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.
{:/}

定义一个函数，不管是带名字的定义或是使用 Lambda 抽象，被称为*引入*一个函数，使用一个函数被称为*消去*一个函数。

{::comment}
Elimination followed by introduction is the identity:
{:/}

引入后接着消去，得到的还是原来的值：

{% raw %}<pre class="Agda"><a id="η-→"></a><a id="23528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#23528" class="Function">η-→</a> <a id="23532" class="Symbol">:</a> <a id="23534" class="Symbol">∀</a> <a id="23536" class="Symbol">{</a><a id="23537" href="plfa.part1.Connectives.html#23537" class="Bound">A</a> <a id="23539" href="plfa.part1.Connectives.html#23539" class="Bound">B</a> <a id="23541" class="Symbol">:</a> <a id="23543" class="PrimitiveType">Set</a><a id="23546" class="Symbol">}</a> <a id="23548" class="Symbol">(</a><a id="23549" href="plfa.part1.Connectives.html#23549" class="Bound">f</a> <a id="23551" class="Symbol">:</a> <a id="23553" href="plfa.part1.Connectives.html#23537" class="Bound">A</a> <a id="23555" class="Symbol">→</a> <a id="23557" href="plfa.part1.Connectives.html#23539" class="Bound">B</a><a id="23558" class="Symbol">)</a> <a id="23560" class="Symbol">→</a> <a id="23562" class="Symbol">(λ</a> <a id="23565" class="Symbol">(</a><a id="23566" href="plfa.part1.Connectives.html#23566" class="Bound">x</a> <a id="23568" class="Symbol">:</a> <a id="23570" href="plfa.part1.Connectives.html#23537" class="Bound">A</a><a id="23571" class="Symbol">)</a> <a id="23573" class="Symbol">→</a> <a id="23575" href="plfa.part1.Connectives.html#23549" class="Bound">f</a> <a id="23577" href="plfa.part1.Connectives.html#23566" class="Bound">x</a><a id="23578" class="Symbol">)</a> <a id="23580" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23582" href="plfa.part1.Connectives.html#23549" class="Bound">f</a>
<a id="23584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#23528" class="Function">η-→</a> <a id="23588" href="plfa.part1.Connectives.html#23588" class="Bound">f</a> <a id="23590" class="Symbol">=</a> <a id="23592" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.
{:/}

蕴涵比其他的运算符结合得都不紧密。因此 `A ⊎ B → B ⊎ A` 被解析为 `(A ⊎ B) → (B ⊎ A)`。

{::comment}
Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A → B` 称为从 `A` 到 `B` 的*函数*空间。它有时也被称作以 `B` 为底，`A` 为次数的*幂*。如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，那么类型 `A → B` 有 `nᵐ` 个不同的成员。这也是它被称为幂的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，如之前的定义。那么，`Bool → Tri` 类型有如下的九个成员（三的平方）：

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

{::comment}
For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool → Tri` 的参数：

{% raw %}<pre class="Agda"><a id="→-count"></a><a id="24995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#24995" class="Function">→-count</a> <a id="25003" class="Symbol">:</a> <a id="25005" class="Symbol">(</a><a id="25006" href="plfa.part1.Connectives.html#6349" class="Datatype">Bool</a> <a id="25011" class="Symbol">→</a> <a id="25013" href="plfa.part1.Connectives.html#6402" class="Datatype">Tri</a><a id="25016" class="Symbol">)</a> <a id="25018" class="Symbol">→</a> <a id="25020" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="25022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#24995" class="Function">→-count</a> <a id="25030" href="plfa.part1.Connectives.html#25030" class="Bound">f</a> <a id="25032" class="Keyword">with</a> <a id="25037" href="plfa.part1.Connectives.html#25030" class="Bound">f</a> <a id="25039" href="plfa.part1.Connectives.html#6368" class="InductiveConstructor">true</a> <a id="25044" class="Symbol">|</a> <a id="25046" href="plfa.part1.Connectives.html#25030" class="Bound">f</a> <a id="25048" href="plfa.part1.Connectives.html#6383" class="InductiveConstructor">false</a>
<a id="25054" class="Symbol">...</a>          <a id="25067" class="Symbol">|</a> <a id="25069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6420" class="InductiveConstructor">aa</a>     <a id="25076" class="Symbol">|</a> <a id="25078" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a>      <a id="25086" class="Symbol">=</a>   <a id="25090" class="Number">1</a>
<a id="25092" class="Symbol">...</a>          <a id="25105" class="Symbol">|</a> <a id="25107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6420" class="InductiveConstructor">aa</a>     <a id="25114" class="Symbol">|</a> <a id="25116" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a>      <a id="25124" class="Symbol">=</a>   <a id="25128" class="Number">2</a>
<a id="25130" class="Symbol">...</a>          <a id="25143" class="Symbol">|</a> <a id="25145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6420" class="InductiveConstructor">aa</a>     <a id="25152" class="Symbol">|</a> <a id="25154" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a>      <a id="25162" class="Symbol">=</a>   <a id="25166" class="Number">3</a>
<a id="25168" class="Symbol">...</a>          <a id="25181" class="Symbol">|</a> <a id="25183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6431" class="InductiveConstructor">bb</a>     <a id="25190" class="Symbol">|</a> <a id="25192" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a>      <a id="25200" class="Symbol">=</a>   <a id="25204" class="Number">4</a>
<a id="25206" class="Symbol">...</a>          <a id="25219" class="Symbol">|</a> <a id="25221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6431" class="InductiveConstructor">bb</a>     <a id="25228" class="Symbol">|</a> <a id="25230" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a>      <a id="25238" class="Symbol">=</a>   <a id="25242" class="Number">5</a>
<a id="25244" class="Symbol">...</a>          <a id="25257" class="Symbol">|</a> <a id="25259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6431" class="InductiveConstructor">bb</a>     <a id="25266" class="Symbol">|</a> <a id="25268" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a>      <a id="25276" class="Symbol">=</a>   <a id="25280" class="Number">6</a>
<a id="25282" class="Symbol">...</a>          <a id="25295" class="Symbol">|</a> <a id="25297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6442" class="InductiveConstructor">cc</a>     <a id="25304" class="Symbol">|</a> <a id="25306" href="plfa.part1.Connectives.html#6420" class="InductiveConstructor">aa</a>      <a id="25314" class="Symbol">=</a>   <a id="25318" class="Number">7</a>
<a id="25320" class="Symbol">...</a>          <a id="25333" class="Symbol">|</a> <a id="25335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6442" class="InductiveConstructor">cc</a>     <a id="25342" class="Symbol">|</a> <a id="25344" href="plfa.part1.Connectives.html#6431" class="InductiveConstructor">bb</a>      <a id="25352" class="Symbol">=</a>   <a id="25356" class="Number">8</a>
<a id="25358" class="Symbol">...</a>          <a id="25371" class="Symbol">|</a> <a id="25373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6442" class="InductiveConstructor">cc</a>     <a id="25380" class="Symbol">|</a> <a id="25382" href="plfa.part1.Connectives.html#6442" class="InductiveConstructor">cc</a>      <a id="25390" class="Symbol">=</a>   <a id="25394" class="Number">9</a>
</pre>{% endraw %}
{::comment}
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.
{:/}

类型上的幂与数的幂有相似的性质，很多数上成立的关系式也可以在类型上成立。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p ^ n) ^ m  ≡  p ^ (n * m)

{::comment}
we have the isomorphism
{:/}

我们有如下的同构：

    A → (B → C)  ≃  (A × B) → C

{::comment}
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
{:/}

两个类型可以被看作给定 `A` 成立的证据和 `B` 成立的证据，返回 `C` 成立的证据。这个同构有时也被称作*柯里化*（Currying）。右逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="currying"></a><a id="26134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26134" class="Function">currying</a> <a id="26143" class="Symbol">:</a> <a id="26145" class="Symbol">∀</a> <a id="26147" class="Symbol">{</a><a id="26148" href="plfa.part1.Connectives.html#26148" class="Bound">A</a> <a id="26150" href="plfa.part1.Connectives.html#26150" class="Bound">B</a> <a id="26152" href="plfa.part1.Connectives.html#26152" class="Bound">C</a> <a id="26154" class="Symbol">:</a> <a id="26156" class="PrimitiveType">Set</a><a id="26159" class="Symbol">}</a> <a id="26161" class="Symbol">→</a> <a id="26163" class="Symbol">(</a><a id="26164" href="plfa.part1.Connectives.html#26148" class="Bound">A</a> <a id="26166" class="Symbol">→</a> <a id="26168" href="plfa.part1.Connectives.html#26150" class="Bound">B</a> <a id="26170" class="Symbol">→</a> <a id="26172" href="plfa.part1.Connectives.html#26152" class="Bound">C</a><a id="26173" class="Symbol">)</a> <a id="26175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="26177" class="Symbol">(</a><a id="26178" href="plfa.part1.Connectives.html#26148" class="Bound">A</a> <a id="26180" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="26182" href="plfa.part1.Connectives.html#26150" class="Bound">B</a> <a id="26184" class="Symbol">→</a> <a id="26186" href="plfa.part1.Connectives.html#26152" class="Bound">C</a><a id="26187" class="Symbol">)</a>
<a id="26189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26134" class="Function">currying</a> <a id="26198" class="Symbol">=</a>
  <a id="26202" class="Keyword">record</a>
    <a id="26213" class="Symbol">{</a> <a id="26215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="26223" class="Symbol">=</a>  <a id="26226" class="Symbol">λ{</a> <a id="26229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26229" class="Bound">f</a> <a id="26231" class="Symbol">→</a> <a id="26233" class="Symbol">λ{</a> <a id="26236" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="26238" href="plfa.part1.Connectives.html#26238" class="Bound">x</a> <a id="26240" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="26242" href="plfa.part1.Connectives.html#26242" class="Bound">y</a> <a id="26244" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="26246" class="Symbol">→</a> <a id="26248" href="plfa.part1.Connectives.html#26229" class="Bound">f</a> <a id="26250" href="plfa.part1.Connectives.html#26238" class="Bound">x</a> <a id="26252" href="plfa.part1.Connectives.html#26242" class="Bound">y</a> <a id="26254" class="Symbol">}}</a>
    <a id="26261" class="Symbol">;</a> <a id="26263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="26271" class="Symbol">=</a>  <a id="26274" class="Symbol">λ{</a> <a id="26277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26277" class="Bound">g</a> <a id="26279" class="Symbol">→</a> <a id="26281" class="Symbol">λ{</a> <a id="26284" href="plfa.part1.Connectives.html#26284" class="Bound">x</a> <a id="26286" class="Symbol">→</a> <a id="26288" class="Symbol">λ{</a> <a id="26291" href="plfa.part1.Connectives.html#26291" class="Bound">y</a> <a id="26293" class="Symbol">→</a> <a id="26295" href="plfa.part1.Connectives.html#26277" class="Bound">g</a> <a id="26297" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="26299" href="plfa.part1.Connectives.html#26284" class="Bound">x</a> <a id="26301" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="26303" href="plfa.part1.Connectives.html#26291" class="Bound">y</a> <a id="26305" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="26307" class="Symbol">}}}</a>
    <a id="26315" class="Symbol">;</a> <a id="26317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="26325" class="Symbol">=</a>  <a id="26328" class="Symbol">λ{</a> <a id="26331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26331" class="Bound">f</a> <a id="26333" class="Symbol">→</a> <a id="26335" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26340" class="Symbol">}</a>
    <a id="26346" class="Symbol">;</a> <a id="26348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="26356" class="Symbol">=</a>  <a id="26359" class="Symbol">λ{</a> <a id="26362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#26362" class="Bound">g</a> <a id="26364" class="Symbol">→</a> <a id="26366" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="26381" class="Symbol">λ{</a> <a id="26384" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="26386" href="plfa.part1.Connectives.html#26386" class="Bound">x</a> <a id="26388" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="26390" href="plfa.part1.Connectives.html#26390" class="Bound">y</a> <a id="26392" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="26394" class="Symbol">→</a> <a id="26396" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26401" class="Symbol">}}</a>
    <a id="26408" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition
{:/}

柯里化告诉我们，如果一个函数有取一个数据对作为参数，那么我们可以构造一个函数，取第一个参数，返回一个取第二个参数，返回最终结果的函数。因此，举例来说，下面表示加法的形式：

    _+_ : ℕ → ℕ → ℕ

{::comment}
is isomorphic to a function that accepts a pair of arguments:
{:/}

和下面的一个带有一个数据对作为参数的函数是同构的：

    _+′_ : (ℕ × ℕ) → ℕ

{::comment}
Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.
{:/}

Agda 对柯里化进行了优化，因此 `2 + 3` 是 `_+_ 2 3` 的简写。在一个对有序对进行优化的语言里，
`2 +′ 3` 可能是 `_+′_ ⟨ 2 , 3 ⟩` 的简写。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    p ^ (n + m) = (p ^ n) * (p ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

{::comment}
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
{:/}

命题如果 `A` 成立或者 `B` 成立，那么 `C` 成立，和命题如果 `A` 成立，那么 `C` 成立以及如果 `B` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="→-distrib-⊎"></a><a id="27724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#27724" class="Function">→-distrib-⊎</a> <a id="27736" class="Symbol">:</a> <a id="27738" class="Symbol">∀</a> <a id="27740" class="Symbol">{</a><a id="27741" href="plfa.part1.Connectives.html#27741" class="Bound">A</a> <a id="27743" href="plfa.part1.Connectives.html#27743" class="Bound">B</a> <a id="27745" href="plfa.part1.Connectives.html#27745" class="Bound">C</a> <a id="27747" class="Symbol">:</a> <a id="27749" class="PrimitiveType">Set</a><a id="27752" class="Symbol">}</a> <a id="27754" class="Symbol">→</a> <a id="27756" class="Symbol">(</a><a id="27757" href="plfa.part1.Connectives.html#27741" class="Bound">A</a> <a id="27759" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="27761" href="plfa.part1.Connectives.html#27743" class="Bound">B</a> <a id="27763" class="Symbol">→</a> <a id="27765" href="plfa.part1.Connectives.html#27745" class="Bound">C</a><a id="27766" class="Symbol">)</a> <a id="27768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="27770" class="Symbol">((</a><a id="27772" href="plfa.part1.Connectives.html#27741" class="Bound">A</a> <a id="27774" class="Symbol">→</a> <a id="27776" href="plfa.part1.Connectives.html#27745" class="Bound">C</a><a id="27777" class="Symbol">)</a> <a id="27779" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="27781" class="Symbol">(</a><a id="27782" href="plfa.part1.Connectives.html#27743" class="Bound">B</a> <a id="27784" class="Symbol">→</a> <a id="27786" href="plfa.part1.Connectives.html#27745" class="Bound">C</a><a id="27787" class="Symbol">))</a>
<a id="27790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#27724" class="Function">→-distrib-⊎</a> <a id="27802" class="Symbol">=</a>
  <a id="27806" class="Keyword">record</a>
    <a id="27817" class="Symbol">{</a> <a id="27819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="27827" class="Symbol">=</a> <a id="27829" class="Symbol">λ{</a> <a id="27832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#27832" class="Bound">f</a> <a id="27834" class="Symbol">→</a> <a id="27836" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="27838" href="plfa.part1.Connectives.html#27832" class="Bound">f</a> <a id="27840" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27842" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="27847" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="27849" href="plfa.part1.Connectives.html#27832" class="Bound">f</a> <a id="27851" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27853" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="27858" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="27860" class="Symbol">}</a>
    <a id="27866" class="Symbol">;</a> <a id="27868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="27876" class="Symbol">=</a> <a id="27878" class="Symbol">λ{</a> <a id="27881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="27883" href="plfa.part1.Connectives.html#27883" class="Bound">g</a> <a id="27885" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="27887" href="plfa.part1.Connectives.html#27887" class="Bound">h</a> <a id="27889" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="27891" class="Symbol">→</a> <a id="27893" class="Symbol">λ{</a> <a id="27896" class="Symbol">(</a><a id="27897" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="27902" href="plfa.part1.Connectives.html#27902" class="Bound">x</a><a id="27903" class="Symbol">)</a> <a id="27905" class="Symbol">→</a> <a id="27907" href="plfa.part1.Connectives.html#27883" class="Bound">g</a> <a id="27909" href="plfa.part1.Connectives.html#27902" class="Bound">x</a> <a id="27911" class="Symbol">;</a> <a id="27913" class="Symbol">(</a><a id="27914" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="27919" href="plfa.part1.Connectives.html#27919" class="Bound">y</a><a id="27920" class="Symbol">)</a> <a id="27922" class="Symbol">→</a> <a id="27924" href="plfa.part1.Connectives.html#27887" class="Bound">h</a> <a id="27926" href="plfa.part1.Connectives.html#27919" class="Bound">y</a> <a id="27928" class="Symbol">}</a> <a id="27930" class="Symbol">}</a>
    <a id="27936" class="Symbol">;</a> <a id="27938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="27946" class="Symbol">=</a> <a id="27948" class="Symbol">λ{</a> <a id="27951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#27951" class="Bound">f</a> <a id="27953" class="Symbol">→</a> <a id="27955" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="27970" class="Symbol">λ{</a> <a id="27973" class="Symbol">(</a><a id="27974" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="27979" href="plfa.part1.Connectives.html#27979" class="Bound">x</a><a id="27980" class="Symbol">)</a> <a id="27982" class="Symbol">→</a> <a id="27984" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27989" class="Symbol">;</a> <a id="27991" class="Symbol">(</a><a id="27992" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="27997" href="plfa.part1.Connectives.html#27997" class="Bound">y</a><a id="27998" class="Symbol">)</a> <a id="28000" class="Symbol">→</a> <a id="28002" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28007" class="Symbol">}</a> <a id="28009" class="Symbol">}</a>
    <a id="28015" class="Symbol">;</a> <a id="28017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="28025" class="Symbol">=</a> <a id="28027" class="Symbol">λ{</a> <a id="28030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="28032" href="plfa.part1.Connectives.html#28032" class="Bound">g</a> <a id="28034" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="28036" href="plfa.part1.Connectives.html#28036" class="Bound">h</a> <a id="28038" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="28040" class="Symbol">→</a> <a id="28042" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28047" class="Symbol">}</a>
    <a id="28053" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p * n) ^ m = (p ^ m) * (n ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    A → B × C  ≃  (A → B) × (A → C)

{::comment}
That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
{:/}

命题如果 `A` 成立，那么 `B` 成立和 `C` 成立，和命题如果 `A` 成立，那么 `B` 成立以及如果 `A` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性和积的 `η-×` 规则：

{% raw %}<pre class="Agda"><a id="→-distrib-×"></a><a id="28622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#28622" class="Function">→-distrib-×</a> <a id="28634" class="Symbol">:</a> <a id="28636" class="Symbol">∀</a> <a id="28638" class="Symbol">{</a><a id="28639" href="plfa.part1.Connectives.html#28639" class="Bound">A</a> <a id="28641" href="plfa.part1.Connectives.html#28641" class="Bound">B</a> <a id="28643" href="plfa.part1.Connectives.html#28643" class="Bound">C</a> <a id="28645" class="Symbol">:</a> <a id="28647" class="PrimitiveType">Set</a><a id="28650" class="Symbol">}</a> <a id="28652" class="Symbol">→</a> <a id="28654" class="Symbol">(</a><a id="28655" href="plfa.part1.Connectives.html#28639" class="Bound">A</a> <a id="28657" class="Symbol">→</a> <a id="28659" href="plfa.part1.Connectives.html#28641" class="Bound">B</a> <a id="28661" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="28663" href="plfa.part1.Connectives.html#28643" class="Bound">C</a><a id="28664" class="Symbol">)</a> <a id="28666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="28668" class="Symbol">(</a><a id="28669" href="plfa.part1.Connectives.html#28639" class="Bound">A</a> <a id="28671" class="Symbol">→</a> <a id="28673" href="plfa.part1.Connectives.html#28641" class="Bound">B</a><a id="28674" class="Symbol">)</a> <a id="28676" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="28678" class="Symbol">(</a><a id="28679" href="plfa.part1.Connectives.html#28639" class="Bound">A</a> <a id="28681" class="Symbol">→</a> <a id="28683" href="plfa.part1.Connectives.html#28643" class="Bound">C</a><a id="28684" class="Symbol">)</a>
<a id="28686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#28622" class="Function">→-distrib-×</a> <a id="28698" class="Symbol">=</a>
  <a id="28702" class="Keyword">record</a>
    <a id="28713" class="Symbol">{</a> <a id="28715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="28723" class="Symbol">=</a> <a id="28725" class="Symbol">λ{</a> <a id="28728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#28728" class="Bound">f</a> <a id="28730" class="Symbol">→</a> <a id="28732" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="28734" href="plfa.part1.Connectives.html#2203" class="Function">proj₁</a> <a id="28740" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28742" href="plfa.part1.Connectives.html#28728" class="Bound">f</a> <a id="28744" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="28746" href="plfa.part1.Connectives.html#2272" class="Function">proj₂</a> <a id="28752" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28754" href="plfa.part1.Connectives.html#28728" class="Bound">f</a> <a id="28756" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="28758" class="Symbol">}</a>
    <a id="28764" class="Symbol">;</a> <a id="28766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="28774" class="Symbol">=</a> <a id="28776" class="Symbol">λ{</a> <a id="28779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="28781" href="plfa.part1.Connectives.html#28781" class="Bound">g</a> <a id="28783" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="28785" href="plfa.part1.Connectives.html#28785" class="Bound">h</a> <a id="28787" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="28789" class="Symbol">→</a> <a id="28791" class="Symbol">λ</a> <a id="28793" href="plfa.part1.Connectives.html#28793" class="Bound">x</a> <a id="28795" class="Symbol">→</a> <a id="28797" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="28799" href="plfa.part1.Connectives.html#28781" class="Bound">g</a> <a id="28801" href="plfa.part1.Connectives.html#28793" class="Bound">x</a> <a id="28803" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="28805" href="plfa.part1.Connectives.html#28785" class="Bound">h</a> <a id="28807" href="plfa.part1.Connectives.html#28793" class="Bound">x</a> <a id="28809" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="28811" class="Symbol">}</a>
    <a id="28817" class="Symbol">;</a> <a id="28819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="28827" class="Symbol">=</a> <a id="28829" class="Symbol">λ{</a> <a id="28832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#28832" class="Bound">f</a> <a id="28834" class="Symbol">→</a> <a id="28836" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="28851" class="Symbol">λ{</a> <a id="28854" href="plfa.part1.Connectives.html#28854" class="Bound">x</a> <a id="28856" class="Symbol">→</a> <a id="28858" href="plfa.part1.Connectives.html#4997" class="Function">η-×</a> <a id="28862" class="Symbol">(</a><a id="28863" href="plfa.part1.Connectives.html#28832" class="Bound">f</a> <a id="28865" href="plfa.part1.Connectives.html#28854" class="Bound">x</a><a id="28866" class="Symbol">)</a> <a id="28868" class="Symbol">}</a> <a id="28870" class="Symbol">}</a>
    <a id="28876" class="Symbol">;</a> <a id="28878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="28886" class="Symbol">=</a> <a id="28888" class="Symbol">λ{</a> <a id="28891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="28893" href="plfa.part1.Connectives.html#28893" class="Bound">g</a> <a id="28895" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="28897" href="plfa.part1.Connectives.html#28897" class="Bound">h</a> <a id="28899" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="28901" class="Symbol">→</a> <a id="28903" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28908" class="Symbol">}</a>
    <a id="28914" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Distribution
{:/}

## 分配律

{::comment}
Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
{:/}

在同构意义下，积对于和满足分配律。验证这条形式的代码和之前的证明相似：

{% raw %}<pre class="Agda"><a id="×-distrib-⊎"></a><a id="29153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#29153" class="Function">×-distrib-⊎</a> <a id="29165" class="Symbol">:</a> <a id="29167" class="Symbol">∀</a> <a id="29169" class="Symbol">{</a><a id="29170" href="plfa.part1.Connectives.html#29170" class="Bound">A</a> <a id="29172" href="plfa.part1.Connectives.html#29172" class="Bound">B</a> <a id="29174" href="plfa.part1.Connectives.html#29174" class="Bound">C</a> <a id="29176" class="Symbol">:</a> <a id="29178" class="PrimitiveType">Set</a><a id="29181" class="Symbol">}</a> <a id="29183" class="Symbol">→</a> <a id="29185" class="Symbol">(</a><a id="29186" href="plfa.part1.Connectives.html#29170" class="Bound">A</a> <a id="29188" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="29190" href="plfa.part1.Connectives.html#29172" class="Bound">B</a><a id="29191" class="Symbol">)</a> <a id="29193" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="29195" href="plfa.part1.Connectives.html#29174" class="Bound">C</a> <a id="29197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="29199" class="Symbol">(</a><a id="29200" href="plfa.part1.Connectives.html#29170" class="Bound">A</a> <a id="29202" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="29204" href="plfa.part1.Connectives.html#29174" class="Bound">C</a><a id="29205" class="Symbol">)</a> <a id="29207" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="29209" class="Symbol">(</a><a id="29210" href="plfa.part1.Connectives.html#29172" class="Bound">B</a> <a id="29212" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="29214" href="plfa.part1.Connectives.html#29174" class="Bound">C</a><a id="29215" class="Symbol">)</a>
<a id="29217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#29153" class="Function">×-distrib-⊎</a> <a id="29229" class="Symbol">=</a>
  <a id="29233" class="Keyword">record</a>
    <a id="29244" class="Symbol">{</a> <a id="29246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="29254" class="Symbol">=</a> <a id="29256" class="Symbol">λ{</a> <a id="29259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="29261" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29266" href="plfa.part1.Connectives.html#29266" class="Bound">x</a> <a id="29268" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29270" href="plfa.part1.Connectives.html#29270" class="Bound">z</a> <a id="29272" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="29274" class="Symbol">→</a> <a id="29276" class="Symbol">(</a><a id="29277" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29282" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29284" href="plfa.part1.Connectives.html#29266" class="Bound">x</a> <a id="29286" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29288" href="plfa.part1.Connectives.html#29270" class="Bound">z</a> <a id="29290" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29291" class="Symbol">)</a>
                 <a id="29310" class="Symbol">;</a> <a id="29312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="29314" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="29319" href="plfa.part1.Connectives.html#29319" class="Bound">y</a> <a id="29321" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29323" href="plfa.part1.Connectives.html#29323" class="Bound">z</a> <a id="29325" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="29327" class="Symbol">→</a> <a id="29329" class="Symbol">(</a><a id="29330" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="29335" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29337" href="plfa.part1.Connectives.html#29319" class="Bound">y</a> <a id="29339" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29341" href="plfa.part1.Connectives.html#29323" class="Bound">z</a> <a id="29343" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29344" class="Symbol">)</a>
                 <a id="29363" class="Symbol">}</a>
    <a id="29369" class="Symbol">;</a> <a id="29371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="29379" class="Symbol">=</a> <a id="29381" class="Symbol">λ{</a> <a id="29384" class="Symbol">(</a><a id="29385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14099" class="InductiveConstructor">inj₁</a> <a id="29390" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29392" href="plfa.part1.Connectives.html#29392" class="Bound">x</a> <a id="29394" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29396" href="plfa.part1.Connectives.html#29396" class="Bound">z</a> <a id="29398" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29399" class="Symbol">)</a> <a id="29401" class="Symbol">→</a> <a id="29403" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29405" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29410" href="plfa.part1.Connectives.html#29392" class="Bound">x</a> <a id="29412" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29414" href="plfa.part1.Connectives.html#29396" class="Bound">z</a> <a id="29416" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>
                 <a id="29435" class="Symbol">;</a> <a id="29437" class="Symbol">(</a><a id="29438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14141" class="InductiveConstructor">inj₂</a> <a id="29443" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29445" href="plfa.part1.Connectives.html#29445" class="Bound">y</a> <a id="29447" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29449" href="plfa.part1.Connectives.html#29449" class="Bound">z</a> <a id="29451" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29452" class="Symbol">)</a> <a id="29454" class="Symbol">→</a> <a id="29456" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29458" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="29463" href="plfa.part1.Connectives.html#29445" class="Bound">y</a> <a id="29465" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29467" href="plfa.part1.Connectives.html#29449" class="Bound">z</a> <a id="29469" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>
                 <a id="29488" class="Symbol">}</a>
    <a id="29494" class="Symbol">;</a> <a id="29496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="29504" class="Symbol">=</a> <a id="29506" class="Symbol">λ{</a> <a id="29509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="29511" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29516" href="plfa.part1.Connectives.html#29516" class="Bound">x</a> <a id="29518" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29520" href="plfa.part1.Connectives.html#29520" class="Bound">z</a> <a id="29522" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="29524" class="Symbol">→</a> <a id="29526" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29548" class="Symbol">;</a> <a id="29550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="29552" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="29557" href="plfa.part1.Connectives.html#29557" class="Bound">y</a> <a id="29559" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29561" href="plfa.part1.Connectives.html#29561" class="Bound">z</a> <a id="29563" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="29565" class="Symbol">→</a> <a id="29567" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29589" class="Symbol">}</a>
    <a id="29595" class="Symbol">;</a> <a id="29597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="29605" class="Symbol">=</a> <a id="29607" class="Symbol">λ{</a> <a id="29610" class="Symbol">(</a><a id="29611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14099" class="InductiveConstructor">inj₁</a> <a id="29616" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29618" href="plfa.part1.Connectives.html#29618" class="Bound">x</a> <a id="29620" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29622" href="plfa.part1.Connectives.html#29622" class="Bound">z</a> <a id="29624" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29625" class="Symbol">)</a> <a id="29627" class="Symbol">→</a> <a id="29629" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29651" class="Symbol">;</a> <a id="29653" class="Symbol">(</a><a id="29654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14141" class="InductiveConstructor">inj₂</a> <a id="29659" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29661" href="plfa.part1.Connectives.html#29661" class="Bound">y</a> <a id="29663" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29665" href="plfa.part1.Connectives.html#29665" class="Bound">z</a> <a id="29667" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29668" class="Symbol">)</a> <a id="29670" class="Symbol">→</a> <a id="29672" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29694" class="Symbol">}</a>
    <a id="29700" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Sums do not distribute over products up to isomorphism, but it is an embedding:
{:/}

和对于积不满足分配律，但满足嵌入：

{% raw %}<pre class="Agda"><a id="⊎-distrib-×"></a><a id="29828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#29828" class="Function">⊎-distrib-×</a> <a id="29840" class="Symbol">:</a> <a id="29842" class="Symbol">∀</a> <a id="29844" class="Symbol">{</a><a id="29845" href="plfa.part1.Connectives.html#29845" class="Bound">A</a> <a id="29847" href="plfa.part1.Connectives.html#29847" class="Bound">B</a> <a id="29849" href="plfa.part1.Connectives.html#29849" class="Bound">C</a> <a id="29851" class="Symbol">:</a> <a id="29853" class="PrimitiveType">Set</a><a id="29856" class="Symbol">}</a> <a id="29858" class="Symbol">→</a> <a id="29860" class="Symbol">(</a><a id="29861" href="plfa.part1.Connectives.html#29845" class="Bound">A</a> <a id="29863" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="29865" href="plfa.part1.Connectives.html#29847" class="Bound">B</a><a id="29866" class="Symbol">)</a> <a id="29868" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="29870" href="plfa.part1.Connectives.html#29849" class="Bound">C</a> <a id="29872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">≲</a> <a id="29874" class="Symbol">(</a><a id="29875" href="plfa.part1.Connectives.html#29845" class="Bound">A</a> <a id="29877" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="29879" href="plfa.part1.Connectives.html#29849" class="Bound">C</a><a id="29880" class="Symbol">)</a> <a id="29882" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="29884" class="Symbol">(</a><a id="29885" href="plfa.part1.Connectives.html#29847" class="Bound">B</a> <a id="29887" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="29889" href="plfa.part1.Connectives.html#29849" class="Bound">C</a><a id="29890" class="Symbol">)</a>
<a id="29892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#29828" class="Function">⊎-distrib-×</a> <a id="29904" class="Symbol">=</a>
  <a id="29908" class="Keyword">record</a>
    <a id="29919" class="Symbol">{</a> <a id="29921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11965" class="Field">to</a>      <a id="29929" class="Symbol">=</a> <a id="29931" class="Symbol">λ{</a> <a id="29934" class="Symbol">(</a><a id="29935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14099" class="InductiveConstructor">inj₁</a> <a id="29940" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29942" href="plfa.part1.Connectives.html#29942" class="Bound">x</a> <a id="29944" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29946" href="plfa.part1.Connectives.html#29946" class="Bound">y</a> <a id="29948" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="29949" class="Symbol">)</a> <a id="29951" class="Symbol">→</a> <a id="29953" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="29955" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29960" href="plfa.part1.Connectives.html#29942" class="Bound">x</a> <a id="29962" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="29964" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="29969" href="plfa.part1.Connectives.html#29946" class="Bound">y</a> <a id="29971" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>
                 <a id="29990" class="Symbol">;</a> <a id="29992" class="Symbol">(</a><a id="29993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14141" class="InductiveConstructor">inj₂</a> <a id="29998" href="plfa.part1.Connectives.html#29998" class="Bound">z</a><a id="29999" class="Symbol">)</a>         <a id="30009" class="Symbol">→</a> <a id="30011" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="30013" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30018" href="plfa.part1.Connectives.html#29998" class="Bound">z</a> <a id="30020" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30022" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30027" href="plfa.part1.Connectives.html#29998" class="Bound">z</a> <a id="30029" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a>
                 <a id="30048" class="Symbol">}</a>
    <a id="30054" class="Symbol">;</a> <a id="30056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11985" class="Field">from</a>    <a id="30064" class="Symbol">=</a> <a id="30066" class="Symbol">λ{</a> <a id="30069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="30071" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="30076" href="plfa.part1.Connectives.html#30076" class="Bound">x</a> <a id="30078" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30080" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="30085" href="plfa.part1.Connectives.html#30085" class="Bound">y</a> <a id="30087" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="30089" class="Symbol">→</a> <a id="30091" class="Symbol">(</a><a id="30092" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="30097" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="30099" href="plfa.part1.Connectives.html#30076" class="Bound">x</a> <a id="30101" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30103" href="plfa.part1.Connectives.html#30085" class="Bound">y</a> <a id="30105" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="30106" class="Symbol">)</a>
                 <a id="30125" class="Symbol">;</a> <a id="30127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="30129" href="plfa.part1.Connectives.html#14099" class="InductiveConstructor">inj₁</a> <a id="30134" href="plfa.part1.Connectives.html#30134" class="Bound">x</a> <a id="30136" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30138" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30143" href="plfa.part1.Connectives.html#30143" class="Bound">z</a> <a id="30145" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="30147" class="Symbol">→</a> <a id="30149" class="Symbol">(</a><a id="30150" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30155" href="plfa.part1.Connectives.html#30143" class="Bound">z</a><a id="30156" class="Symbol">)</a>
                 <a id="30175" class="Symbol">;</a> <a id="30177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1769" class="InductiveConstructor Operator">⟨</a> <a id="30179" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30184" href="plfa.part1.Connectives.html#30184" class="Bound">z</a> <a id="30186" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30188" class="Symbol">_</a>      <a id="30195" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a> <a id="30197" class="Symbol">→</a> <a id="30199" class="Symbol">(</a><a id="30200" href="plfa.part1.Connectives.html#14141" class="InductiveConstructor">inj₂</a> <a id="30205" href="plfa.part1.Connectives.html#30184" class="Bound">z</a><a id="30206" class="Symbol">)</a>
                 <a id="30225" class="Symbol">}</a>
    <a id="30231" class="Symbol">;</a> <a id="30233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#12005" class="Field">from∘to</a> <a id="30241" class="Symbol">=</a> <a id="30243" class="Symbol">λ{</a> <a id="30246" class="Symbol">(</a><a id="30247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14099" class="InductiveConstructor">inj₁</a> <a id="30252" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟨</a> <a id="30254" href="plfa.part1.Connectives.html#30254" class="Bound">x</a> <a id="30256" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">,</a> <a id="30258" href="plfa.part1.Connectives.html#30258" class="Bound">y</a> <a id="30260" href="plfa.part1.Connectives.html#1769" class="InductiveConstructor Operator">⟩</a><a id="30261" class="Symbol">)</a> <a id="30263" class="Symbol">→</a> <a id="30265" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30287" class="Symbol">;</a> <a id="30289" class="Symbol">(</a><a id="30290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14141" class="InductiveConstructor">inj₂</a> <a id="30295" href="plfa.part1.Connectives.html#30295" class="Bound">z</a><a id="30296" class="Symbol">)</a>         <a id="30306" class="Symbol">→</a> <a id="30308" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30330" class="Symbol">}</a>
    <a id="30336" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.
{:/}

我们在定义 `from` 函数的时候可以有选择。给定的定义中，它将 `⟨ inj₂ z , inj₂ z′ ⟩`
转换为 `inj₂ z`，但我们也可以返回 `inj₂ z′` 作为嵌入证明的变种。我们在这里只能证明嵌入，而不能证明同构，因为 `from` 函数必须丢弃 `z` 或者 `z′` 其中的一个。

{::comment}
In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:
{:/}

在一般的逻辑学方法中，两条分配律都以等价的形式给出，每一边都蕴涵了另一边：

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

{::comment}
But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.
{:/}

但当我们考虑提供上述蕴涵证明的函数时，第一条对应同构而第二条只能对应嵌入，揭示了有些定理比另一个更加的”正确“。


{::comment}
#### Exercise `⊎-weak-×` (recommended)
{:/}

#### 练习 `⊎-weak-×` （推荐）

{::comment}
Show that the following property holds:
{:/}

证明如下性质成立：

{% raw %}<pre class="Agda"><a id="31567" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="31579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#31579" class="Postulate">⊎-weak-×</a> <a id="31588" class="Symbol">:</a> <a id="31590" class="Symbol">∀</a> <a id="31592" class="Symbol">{</a><a id="31593" href="plfa.part1.Connectives.html#31593" class="Bound">A</a> <a id="31595" href="plfa.part1.Connectives.html#31595" class="Bound">B</a> <a id="31597" href="plfa.part1.Connectives.html#31597" class="Bound">C</a> <a id="31599" class="Symbol">:</a> <a id="31601" class="PrimitiveType">Set</a><a id="31604" class="Symbol">}</a> <a id="31606" class="Symbol">→</a> <a id="31608" class="Symbol">(</a><a id="31609" href="plfa.part1.Connectives.html#31593" class="Bound">A</a> <a id="31611" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="31613" href="plfa.part1.Connectives.html#31595" class="Bound">B</a><a id="31614" class="Symbol">)</a> <a id="31616" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="31618" href="plfa.part1.Connectives.html#31597" class="Bound">C</a> <a id="31620" class="Symbol">→</a> <a id="31622" href="plfa.part1.Connectives.html#31593" class="Bound">A</a> <a id="31624" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="31626" class="Symbol">(</a><a id="31627" href="plfa.part1.Connectives.html#31595" class="Bound">B</a> <a id="31629" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="31631" href="plfa.part1.Connectives.html#31597" class="Bound">C</a><a id="31632" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.
{:/}

这被称为*弱分配律*。给出相对应的分配律，并解释分配律与弱分配律的关系。

{::comment}
{% raw %}<pre class="Agda"><a id="31842" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31879" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `⊎×-implies-×⊎` (practice)
{:/}

#### 练习 `⊎×-implies-×⊎`（实践）

{::comment}
Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{:/}

证明合取的析取蕴涵了析取的合取：

{% raw %}<pre class="Agda"><a id="32093" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="32105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#32105" class="Postulate">⊎×-implies-×⊎</a> <a id="32119" class="Symbol">:</a> <a id="32121" class="Symbol">∀</a> <a id="32123" class="Symbol">{</a><a id="32124" href="plfa.part1.Connectives.html#32124" class="Bound">A</a> <a id="32126" href="plfa.part1.Connectives.html#32126" class="Bound">B</a> <a id="32128" href="plfa.part1.Connectives.html#32128" class="Bound">C</a> <a id="32130" href="plfa.part1.Connectives.html#32130" class="Bound">D</a> <a id="32132" class="Symbol">:</a> <a id="32134" class="PrimitiveType">Set</a><a id="32137" class="Symbol">}</a> <a id="32139" class="Symbol">→</a> <a id="32141" class="Symbol">(</a><a id="32142" href="plfa.part1.Connectives.html#32124" class="Bound">A</a> <a id="32144" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="32146" href="plfa.part1.Connectives.html#32126" class="Bound">B</a><a id="32147" class="Symbol">)</a> <a id="32149" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="32151" class="Symbol">(</a><a id="32152" href="plfa.part1.Connectives.html#32128" class="Bound">C</a> <a id="32154" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="32156" href="plfa.part1.Connectives.html#32130" class="Bound">D</a><a id="32157" class="Symbol">)</a> <a id="32159" class="Symbol">→</a> <a id="32161" class="Symbol">(</a><a id="32162" href="plfa.part1.Connectives.html#32124" class="Bound">A</a> <a id="32164" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="32166" href="plfa.part1.Connectives.html#32128" class="Bound">C</a><a id="32167" class="Symbol">)</a> <a id="32169" href="plfa.part1.Connectives.html#1738" class="Datatype Operator">×</a> <a id="32171" class="Symbol">(</a><a id="32172" href="plfa.part1.Connectives.html#32126" class="Bound">B</a> <a id="32174" href="plfa.part1.Connectives.html#14068" class="Datatype Operator">⊎</a> <a id="32176" href="plfa.part1.Connectives.html#32130" class="Bound">D</a><a id="32177" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, give a counterexample.
{:/}

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

{::comment}
{% raw %}<pre class="Agda"><a id="32317" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="32354" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="32544" class="Keyword">import</a> <a id="32551" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="32564" class="Keyword">using</a> <a id="32570" class="Symbol">(</a><a id="32571" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="32574" class="Symbol">;</a> <a id="32576" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="32581" class="Symbol">;</a> <a id="32583" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="32588" class="Symbol">)</a> <a id="32590" class="Keyword">renaming</a> <a id="32599" class="Symbol">(</a><a id="32600" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="32604" class="Symbol">to</a> <a id="32607" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="32612" class="Symbol">)</a>
<a id="32614" class="Keyword">import</a> <a id="32621" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="32631" class="Keyword">using</a> <a id="32637" class="Symbol">(</a><a id="32638" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="32639" class="Symbol">;</a> <a id="32641" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="32643" class="Symbol">)</a>
<a id="32645" class="Keyword">import</a> <a id="32652" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="32661" class="Keyword">using</a> <a id="32667" class="Symbol">(</a><a id="32668" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="32671" class="Symbol">;</a> <a id="32673" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="32677" class="Symbol">;</a> <a id="32679" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="32683" class="Symbol">)</a> <a id="32685" class="Keyword">renaming</a> <a id="32694" class="Symbol">(</a><a id="32695" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="32701" class="Symbol">to</a> <a id="32704" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="32710" class="Symbol">)</a>
<a id="32712" class="Keyword">import</a> <a id="32719" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="32730" class="Keyword">using</a> <a id="32736" class="Symbol">(</a><a id="32737" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="32738" class="Symbol">;</a> <a id="32740" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="32746" class="Symbol">)</a>
<a id="32748" class="Keyword">import</a> <a id="32755" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html" class="Module">Function.Equivalence</a> <a id="32776" class="Keyword">using</a> <a id="32782" class="Symbol">(</a><a id="32783" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html#971" class="Function Operator">_⇔_</a><a id="32786" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists]({{ site.baseurl }}/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.
{:/}

标准库中使用 `_,_` 构造数据对，而我们使用 `⟨_,_⟩`。前者在从数据对构造三元对或者更大的元组时更加的方便，允许 `a , b , c` 作为 `(a, (b , c))` 的记法。但它与其他有用的记法相冲突，比如说 [Lists][plfa.Lists] 中的 `[_,_]` 记法表示两个元素的列表，或者 [DeBruijn][plfa.DeBruijn] 章节中的 `Γ , A` 来表示环境的扩展。标准库中的 `_⇔_` 和我们的相似，但使用起来比较不便，因为它可以根据任意的相等性定义进行参数化。

## Unicode

{::comment}
This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用下列 Unicode：

    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)
