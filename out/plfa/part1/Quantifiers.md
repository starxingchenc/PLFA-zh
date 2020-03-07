---
src       : "src/plfa/part1/Quantifiers.lagda.md"
title     : "Quantifiers: 全称量词与存在量词"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
translators: ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="186" class="Keyword">module</a> <a id="193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}" class="Module">plfa.part1.Quantifiers</a> <a id="216" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This chapter introduces universal and existential quantification.
{:/}

本章节介绍全称量化（Universal Quantification）和存在量化（Existential Quantification）。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="422" class="Keyword">import</a> <a id="429" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="467" class="Symbol">as</a> <a id="470" class="Module">Eq</a>
<a id="473" class="Keyword">open</a> <a id="478" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="481" class="Keyword">using</a> <a id="487" class="Symbol">(</a><a id="488" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="491" class="Symbol">;</a> <a id="493" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="497" class="Symbol">)</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="520" class="Keyword">using</a> <a id="526" class="Symbol">(</a><a id="527" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="528" class="Symbol">;</a> <a id="530" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="534" class="Symbol">;</a> <a id="536" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="539" class="Symbol">;</a> <a id="541" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="544" class="Symbol">;</a> <a id="546" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="549" class="Symbol">)</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="580" class="Keyword">using</a> <a id="586" class="Symbol">(</a><a id="587" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="589" class="Symbol">)</a>
<a id="591" class="Keyword">open</a> <a id="596" class="Keyword">import</a> <a id="603" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="616" class="Keyword">using</a> <a id="622" class="Symbol">(</a><a id="623" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="626" class="Symbol">;</a> <a id="628" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="633" class="Symbol">)</a> <a id="635" class="Keyword">renaming</a> <a id="644" class="Symbol">(</a><a id="645" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="649" class="Symbol">to</a> <a id="652" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="657" class="Symbol">)</a>
<a id="659" class="Keyword">open</a> <a id="664" class="Keyword">import</a> <a id="671" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="680" class="Keyword">using</a> <a id="686" class="Symbol">(</a><a id="687" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="690" class="Symbol">)</a>
<a id="692" class="Keyword">open</a> <a id="697" class="Keyword">import</a> <a id="704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="727" class="Keyword">using</a> <a id="733" class="Symbol">(</a><a id="734" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="737" class="Symbol">;</a> <a id="739" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="753" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Universals
{:/}

## 全称量化

{::comment}
We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associ<a id="992" class="Bound">a</a>tive<a id="997" class="Bound">:</a>
{:<a id="1001" class="Bound">/</a>}

我<a id="1006" class="Function">们用</a>依<a id="1009" class="Bound">赖</a>函<a id="1011" class="Function">数</a>类<a id="1013" class="Bound">型</a>（<a id="1015" class="Function">D</a>e<a id="1017" class="Bound">p</a>endent Function Type）来形式化全称量化，这样的形式在书中贯穿始终。例如，在归纳一章中，我们证明了加法满足结合律：

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.
{:/}

它断言对于所有的自然数 `m`、`n` 和 `p`，`(m + n) + p ≡ m + (n + p)` 成立。它是一个依赖函数，给出 `m`、`n` 和 `p` 的值，它会返回与该等式对应的证据。

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) <a id="1869" class="Bound">→</a> B <a id="1873" class="Bound">x</a>`.

<a id="1878" class="Function">通常</a>给<a id="1881" class="Bound">定</a>一<a id="1883" class="Function">个</a> <a id="1885" class="Bound">`</a>A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 后的命题。变量 `x` 在 `B x` 中以自由变量的形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

{::comment}
Evidence that `∀ (x : A) → B x` holds is of the form
{:/}

`∀ (x : A) → B x` 成立的证明由以下形式构成：

    λ (x : A) → N x

{::comment}
where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.
{:/}

其中 `N x` 是一个 `B x` 类型的项，`N x` 和 `B x` 都包含了一个 `A` 类型的自由变量 `x`。给定一个项 `L`， 其提供 `∀ (x : A) → B x` 成立的证明，和一个类型为 `A` 的项 `M`，
`L M` 这一项则是 `B M` 成立的证明。换句话说，`∀ (x : A) → B x` 成立的证明是一个函数，将类型为 `A` 的项 `M` 转换成 `B M` 成立的证明。

{::comment}
Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{:/}

再换句话说，如果我们知道 `∀ (x : A) → B x` 成立，又知道 `M` 是一个类型为 `A` 的项，那么我们可以推导出 `B M` 成立：

{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="3065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3065" class="Function">∀-elim</a> <a id="3072" class="Symbol">:</a> <a id="3074" class="Symbol">∀</a> <a id="3076" class="Symbol">{</a><a id="3077" href="plfa.part1.Quantifiers.html#3077" class="Bound">A</a> <a id="3079" class="Symbol">:</a> <a id="3081" class="PrimitiveType">Set</a><a id="3084" class="Symbol">}</a> <a id="3086" class="Symbol">{</a><a id="3087" href="plfa.part1.Quantifiers.html#3087" class="Bound">B</a> <a id="3089" class="Symbol">:</a> <a id="3091" href="plfa.part1.Quantifiers.html#3077" class="Bound">A</a> <a id="3093" class="Symbol">→</a> <a id="3095" class="PrimitiveType">Set</a><a id="3098" class="Symbol">}</a>
  <a id="3102" class="Symbol">→</a> <a id="3104" class="Symbol">(</a><a id="3105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3105" class="Bound">L</a> <a id="3107" class="Symbol">:</a> <a id="3109" class="Symbol">∀</a> <a id="3111" class="Symbol">(</a><a id="3112" href="plfa.part1.Quantifiers.html#3112" class="Bound">x</a> <a id="3114" class="Symbol">:</a> <a id="3116" href="plfa.part1.Quantifiers.html#3077" class="Bound">A</a><a id="3117" class="Symbol">)</a> <a id="3119" class="Symbol">→</a> <a id="3121" href="plfa.part1.Quantifiers.html#3087" class="Bound">B</a> <a id="3123" href="plfa.part1.Quantifiers.html#3112" class="Bound">x</a><a id="3124" class="Symbol">)</a>
  <a id="3128" class="Symbol">→</a> <a id="3130" class="Symbol">(</a><a id="3131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3131" class="Bound">M</a> <a id="3133" class="Symbol">:</a> <a id="3135" href="plfa.part1.Quantifiers.html#3077" class="Bound">A</a><a id="3136" class="Symbol">)</a>
    <a id="3142" class="Comment">-----------------</a>
  <a id="3162" class="Symbol">→</a> <a id="3164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3087" class="Bound">B</a> <a id="3166" href="plfa.part1.Quantifiers.html#3131" class="Bound">M</a>
<a id="3168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3065" class="Function">∀-elim</a> <a id="3175" href="plfa.part1.Quantifiers.html#3175" class="Bound">L</a> <a id="3177" href="plfa.part1.Quantifiers.html#3177" class="Bound">M</a> <a id="3179" class="Symbol">=</a> <a id="3181" href="plfa.part1.Quantifiers.html#3175" class="Bound">L</a> <a id="3183" href="plfa.part1.Quantifiers.html#3177" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
As with `→-elim`, the rule corresponds to function application.
{:/}

如 `→-elim` 那样，这条规则对应了函数应用。

{::comment}
Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.
{:/}

函数是依赖函数的一种特殊形式，其值域不取决于定义域中的变量。当一个函数被视为蕴涵的证明时，它的参数和结果都是证明，而当一个依赖函数被视为全称量词的证明时，它的参数被视为数据类型中的一个元素，而结果是一个依赖于参数的命题的证明。因为在
Agda 中，一个数据类型中的一个值和一个命题的证明是无法区别的，这样的区别很大程度上取决于如何来诠释。

{::comment}
Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.
{:/}

依赖函数类型也被叫做依赖积（Dependent Product），因为如果 `A` 是一个有限的数据类型，有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，那么 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。的确，`∀ (x : A) → B x` 的记法有时也被 `Π[ x ∈ A ] (B x)` 取代，其中 `Π` 代表积。然而，我们还是使用依赖函数这个名称，因为依赖积这个名称是有歧义的，我们后续会体会到歧义所在。

{::comment}
#### Exercise `∀-distrib-×` (recommended)
{:/}

#### 练习 `∀-distrib-×` （推荐）

{::comment}
Show that universals distribute over conjunction:
{:/}

证明全称量词对于合取满足分配律：

{% raw %}<pre class="Agda"><a id="5054" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="5066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5066" class="Postulate">∀-distrib-×</a> <a id="5078" class="Symbol">:</a> <a id="5080" class="Symbol">∀</a> <a id="5082" class="Symbol">{</a><a id="5083" href="plfa.part1.Quantifiers.html#5083" class="Bound">A</a> <a id="5085" class="Symbol">:</a> <a id="5087" class="PrimitiveType">Set</a><a id="5090" class="Symbol">}</a> <a id="5092" class="Symbol">{</a><a id="5093" href="plfa.part1.Quantifiers.html#5093" class="Bound">B</a> <a id="5095" href="plfa.part1.Quantifiers.html#5095" class="Bound">C</a> <a id="5097" class="Symbol">:</a> <a id="5099" href="plfa.part1.Quantifiers.html#5083" class="Bound">A</a> <a id="5101" class="Symbol">→</a> <a id="5103" class="PrimitiveType">Set</a><a id="5106" class="Symbol">}</a> <a id="5108" class="Symbol">→</a>
    <a id="5114" class="Symbol">(∀</a> <a id="5117" class="Symbol">(</a><a id="5118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5118" class="Bound">x</a> <a id="5120" class="Symbol">:</a> <a id="5122" href="plfa.part1.Quantifiers.html#5083" class="Bound">A</a><a id="5123" class="Symbol">)</a> <a id="5125" class="Symbol">→</a> <a id="5127" href="plfa.part1.Quantifiers.html#5093" class="Bound">B</a> <a id="5129" href="plfa.part1.Quantifiers.html#5118" class="Bound">x</a> <a id="5131" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5133" href="plfa.part1.Quantifiers.html#5095" class="Bound">C</a> <a id="5135" href="plfa.part1.Quantifiers.html#5118" class="Bound">x</a><a id="5136" class="Symbol">)</a> <a id="5138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="5140" class="Symbol">(∀</a> <a id="5143" class="Symbol">(</a><a id="5144" href="plfa.part1.Quantifiers.html#5144" class="Bound">x</a> <a id="5146" class="Symbol">:</a> <a id="5148" href="plfa.part1.Quantifiers.html#5083" class="Bound">A</a><a id="5149" class="Symbol">)</a> <a id="5151" class="Symbol">→</a> <a id="5153" href="plfa.part1.Quantifiers.html#5093" class="Bound">B</a> <a id="5155" href="plfa.part1.Quantifiers.html#5144" class="Bound">x</a><a id="5156" class="Symbol">)</a> <a id="5158" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5160" class="Symbol">(∀</a> <a id="5163" class="Symbol">(</a><a id="5164" href="plfa.part1.Quantifiers.html#5164" class="Bound">x</a> <a id="5166" class="Symbol">:</a> <a id="5168" href="plfa.part1.Quantifiers.html#5083" class="Bound">A</a><a id="5169" class="Symbol">)</a> <a id="5171" class="Symbol">→</a> <a id="5173" href="plfa.part1.Quantifiers.html#5095" class="Bound">C</a> <a id="5175" href="plfa.part1.Quantifiers.html#5164" class="Bound">x</a><a id="5176" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).
{:/

将这个结果与 [Connectives]({{ site.baseurl }}/Connectives/)
章节中的 (`→-distrib-×`) 结果对比。

{::comment}
#### Exercise `⊎∀-implies-∀⊎` (practice)
{:/}

#### 练习 `⊎∀-implies-∀⊎`（实践）

{::comment}
Show that a disjunction of universals implies a universal of disjunctions:
{:/}

证明全称命题的析取蕴涵了析取的全称命题：

{% raw %}<pre class="Agda"><a id="5593" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5605" class="Postulate">⊎∀-implies-∀⊎</a> <a id="5619" class="Symbol">:</a> <a id="5621" class="Symbol">∀</a> <a id="5623" class="Symbol">{</a><a id="5624" href="plfa.part1.Quantifiers.html#5624" class="Bound">A</a> <a id="5626" class="Symbol">:</a> <a id="5628" class="PrimitiveType">Set</a><a id="5631" class="Symbol">}</a> <a id="5633" class="Symbol">{</a><a id="5634" href="plfa.part1.Quantifiers.html#5634" class="Bound">B</a> <a id="5636" href="plfa.part1.Quantifiers.html#5636" class="Bound">C</a> <a id="5638" class="Symbol">:</a> <a id="5640" href="plfa.part1.Quantifiers.html#5624" class="Bound">A</a> <a id="5642" class="Symbol">→</a> <a id="5644" class="PrimitiveType">Set</a><a id="5647" class="Symbol">}</a> <a id="5649" class="Symbol">→</a>
    <a id="5655" class="Symbol">(∀</a> <a id="5658" class="Symbol">(</a><a id="5659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5659" class="Bound">x</a> <a id="5661" class="Symbol">:</a> <a id="5663" href="plfa.part1.Quantifiers.html#5624" class="Bound">A</a><a id="5664" class="Symbol">)</a> <a id="5666" class="Symbol">→</a> <a id="5668" href="plfa.part1.Quantifiers.html#5634" class="Bound">B</a> <a id="5670" href="plfa.part1.Quantifiers.html#5659" class="Bound">x</a><a id="5671" class="Symbol">)</a> <a id="5673" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5675" class="Symbol">(∀</a> <a id="5678" class="Symbol">(</a><a id="5679" href="plfa.part1.Quantifiers.html#5679" class="Bound">x</a> <a id="5681" class="Symbol">:</a> <a id="5683" href="plfa.part1.Quantifiers.html#5624" class="Bound">A</a><a id="5684" class="Symbol">)</a> <a id="5686" class="Symbol">→</a> <a id="5688" href="plfa.part1.Quantifiers.html#5636" class="Bound">C</a> <a id="5690" href="plfa.part1.Quantifiers.html#5679" class="Bound">x</a><a id="5691" class="Symbol">)</a>  <a id="5694" class="Symbol">→</a>  <a id="5697" class="Symbol">∀</a> <a id="5699" class="Symbol">(</a><a id="5700" href="plfa.part1.Quantifiers.html#5700" class="Bound">x</a> <a id="5702" class="Symbol">:</a> <a id="5704" href="plfa.part1.Quantifiers.html#5624" class="Bound">A</a><a id="5705" class="Symbol">)</a> <a id="5707" class="Symbol">→</a> <a id="5709" href="plfa.part1.Quantifiers.html#5634" class="Bound">B</a> <a id="5711" href="plfa.part1.Quantifiers.html#5700" class="Bound">x</a> <a id="5713" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5715" href="plfa.part1.Quantifiers.html#5636" class="Bound">C</a> <a id="5717" href="plfa.part1.Quantifiers.html#5700" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∀-×` (practice)
{:/}

#### 练习 `∀-×`（实践）

{::comment}
Consider the following type.
{:/}

参考下面的类型：

{% raw %}<pre class="Agda"><a id="5961" class="Keyword">data</a> <a id="Tri"></a><a id="5966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5966" class="Datatype">Tri</a> <a id="5970" class="Symbol">:</a> <a id="5972" class="PrimitiveType">Set</a> <a id="5976" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="5984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5984" class="InductiveConstructor">aa</a> <a id="5987" class="Symbol">:</a> <a id="5989" href="plfa.part1.Quantifiers.html#5966" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="5995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5995" class="InductiveConstructor">bb</a> <a id="5998" class="Symbol">:</a> <a id="6000" href="plfa.part1.Quantifiers.html#5966" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="6006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#6006" class="InductiveConstructor">cc</a> <a id="6009" class="Symbol">:</a> <a id="6011" href="plfa.part1.Quantifiers.html#5966" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。提示：你需要引入一个可应用于依赖函数的外延性公设。


{::comment}
## Existentials
{:/}

## 存在量化

{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，存在量化的命题 `Σ[ x ∈ A ] B x` 当对于一些类型为 `A` 的项 `M`，命题 `B M` 成立时成立。在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

{::comment}
We formalise existential quantification by declaring a suitable
inductive type:
{:/}

我们定义一个合适的归纳数据类型来形式化存在量化：

{% raw %}<pre class="Agda"><a id="7173" class="Keyword">data</a> <a id="Σ"></a><a id="7178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7178" class="Datatype">Σ</a> <a id="7180" class="Symbol">(</a><a id="7181" href="plfa.part1.Quantifiers.html#7181" class="Bound">A</a> <a id="7183" class="Symbol">:</a> <a id="7185" class="PrimitiveType">Set</a><a id="7188" class="Symbol">)</a> <a id="7190" class="Symbol">(</a><a id="7191" href="plfa.part1.Quantifiers.html#7191" class="Bound">B</a> <a id="7193" class="Symbol">:</a> <a id="7195" href="plfa.part1.Quantifiers.html#7181" class="Bound">A</a> <a id="7197" class="Symbol">→</a> <a id="7199" class="PrimitiveType">Set</a><a id="7202" class="Symbol">)</a> <a id="7204" class="Symbol">:</a> <a id="7206" class="PrimitiveType">Set</a> <a id="7210" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="7218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7218" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="7224" class="Symbol">:</a> <a id="7226" class="Symbol">(</a><a id="7227" href="plfa.part1.Quantifiers.html#7227" class="Bound">x</a> <a id="7229" class="Symbol">:</a> <a id="7231" href="plfa.part1.Quantifiers.html#7181" class="Bound">A</a><a id="7232" class="Symbol">)</a> <a id="7234" class="Symbol">→</a> <a id="7236" href="plfa.part1.Quantifiers.html#7191" class="Bound">B</a> <a id="7238" href="plfa.part1.Quantifiers.html#7227" class="Bound">x</a> <a id="7240" class="Symbol">→</a> <a id="7242" href="plfa.part1.Quantifiers.html#7178" class="Datatype">Σ</a> <a id="7244" href="plfa.part1.Quantifiers.html#7181" class="Bound">A</a> <a id="7246" href="plfa.part1.Quantifiers.html#7191" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="7353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7353" class="Function">Σ-syntax</a> <a id="7362" class="Symbol">=</a> <a id="7364" href="plfa.part1.Quantifiers.html#7178" class="Datatype">Σ</a>
<a id="7366" class="Keyword">infix</a> <a id="7372" class="Number">2</a> <a id="7374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7353" class="Function">Σ-syntax</a>
<a id="7383" class="Keyword">syntax</a> <a id="7390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7353" class="Function">Σ-syntax</a> <a id="7399" class="Bound">A</a> <a id="7401" class="Symbol">(λ</a> <a id="7404" class="Bound">x</a> <a id="7406" class="Symbol">→</a> <a id="7408" class="Bound">B</a><a id="7409" class="Symbol">)</a> <a id="7411" class="Symbol">=</a> <a id="7413" class="Function">Σ[</a> <a id="7416" class="Bound">x</a> <a id="7418" class="Function">∈</a> <a id="7420" class="Bound">A</a> <a id="7422" class="Function">]</a> <a id="7424" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.
{:/}

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

{::comment}
Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.
{:/}

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M` 是类型为 `A` 的项，
`N` 是 `B M` 成立的证明。


{::comment}
Equivalently, we could also declare existentials as a record type:
{:/}

我们也可以用记录类型来等价地定义存在量化。

{% raw %}<pre class="Agda"><a id="8078" class="Keyword">record</a> <a id="Σ′"></a><a id="8085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8085" class="Record">Σ′</a> <a id="8088" class="Symbol">(</a><a id="8089" href="plfa.part1.Quantifiers.html#8089" class="Bound">A</a> <a id="8091" class="Symbol">:</a> <a id="8093" class="PrimitiveType">Set</a><a id="8096" class="Symbol">)</a> <a id="8098" class="Symbol">(</a><a id="8099" href="plfa.part1.Quantifiers.html#8099" class="Bound">B</a> <a id="8101" class="Symbol">:</a> <a id="8103" href="plfa.part1.Quantifiers.html#8089" class="Bound">A</a> <a id="8105" class="Symbol">→</a> <a id="8107" class="PrimitiveType">Set</a><a id="8110" class="Symbol">)</a> <a id="8112" class="Symbol">:</a> <a id="8114" class="PrimitiveType">Set</a> <a id="8118" class="Keyword">where</a>
  <a id="8126" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="8136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8136" class="Field">proj₁′</a> <a id="8143" class="Symbol">:</a> <a id="8145" href="plfa.part1.Quantifiers.html#8089" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="8151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8151" class="Field">proj₂′</a> <a id="8158" class="Symbol">:</a> <a id="8160" href="plfa.part1.Quantifiers.html#8099" class="Bound">B</a> <a id="8162" href="plfa.part1.Quantifiers.html#8136" class="Field">proj₁′</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应了项

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B M`.
{:/}

其中 `M` 是类型为 `A` 的项，`N` 是类型为 `B M` 的项。

{::comment}
Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.
{:/}

积是依赖积的一种特殊形式，其第二分量不取决于第一分量中的变量。当一个积被视为合取的证明时，它的两个分量都是证明，而当一个依赖积被视为存在量词的证明时，它的第一分量被视为数据类型中的一个元素，而第二分量是一个依赖于第一分量的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上取决于如何来诠释。

{::comment}
Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.
{:/}

存在量化也被叫做依赖和（Dependent Sum），因为如果 `A` 是一个有限的数据类型，有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，那么 `Σ[ x ∈ A ] B x` 有 `m₁ + ⋯ + mₙ` 个成员，这也解释了选择使用这个记法的原因——
`Σ` 代表和。

{::comment}
Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.
{:/}

存在量化有时也被叫做依赖积（Dependent Product），因为积是其中的一种特殊形式。但是，这样的叫法非常让人困扰，因为全程量化也被叫做依赖积，而存在量化已经有依赖和的叫法。

{::comment}
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{:/}

存在量词的普通记法是 `∃` （与全程量词的 `∀` 记法相类似）。我们使用 Agda 标准库中的惯例，使用一种隐式申明约束变量定义域的记法。

{% raw %}<pre class="Agda"><a id="∃"></a><a id="10512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10512" class="Function">∃</a> <a id="10514" class="Symbol">:</a> <a id="10516" class="Symbol">∀</a> <a id="10518" class="Symbol">{</a><a id="10519" href="plfa.part1.Quantifiers.html#10519" class="Bound">A</a> <a id="10521" class="Symbol">:</a> <a id="10523" class="PrimitiveType">Set</a><a id="10526" class="Symbol">}</a> <a id="10528" class="Symbol">(</a><a id="10529" href="plfa.part1.Quantifiers.html#10529" class="Bound">B</a> <a id="10531" class="Symbol">:</a> <a id="10533" href="plfa.part1.Quantifiers.html#10519" class="Bound">A</a> <a id="10535" class="Symbol">→</a> <a id="10537" class="PrimitiveType">Set</a><a id="10540" class="Symbol">)</a> <a id="10542" class="Symbol">→</a> <a id="10544" class="PrimitiveType">Set</a>
<a id="10548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10512" class="Function">∃</a> <a id="10550" class="Symbol">{</a><a id="10551" href="plfa.part1.Quantifiers.html#10551" class="Bound">A</a><a id="10552" class="Symbol">}</a> <a id="10554" href="plfa.part1.Quantifiers.html#10554" class="Bound">B</a> <a id="10556" class="Symbol">=</a> <a id="10558" href="plfa.part1.Quantifiers.html#7178" class="Datatype">Σ</a> <a id="10560" href="plfa.part1.Quantifiers.html#10551" class="Bound">A</a> <a id="10562" href="plfa.part1.Quantifiers.html#10554" class="Bound">B</a>

<a id="∃-syntax"></a><a id="10565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃-syntax</a> <a id="10574" class="Symbol">=</a> <a id="10576" href="plfa.part1.Quantifiers.html#10512" class="Function">∃</a>
<a id="10578" class="Keyword">syntax</a> <a id="10585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃-syntax</a> <a id="10594" class="Symbol">(λ</a> <a id="10597" class="Bound">x</a> <a id="10599" class="Symbol">→</a> <a id="10601" class="Bound">B</a><a id="10602" class="Symbol">)</a> <a id="10604" class="Symbol">=</a> <a id="10606" class="Function">∃[</a> <a id="10609" class="Bound">x</a> <a id="10611" class="Function">]</a> <a id="10613" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.
{:/}

这种特殊的语法只有在 `∃-syntax` 标识符被导入时可用。我们将倾向于使用这种语法，因为它更短，而且看上去更熟悉。

{::comment}
Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{:/}

给定 `∀ x → B x → C` 成立的证明，其中 `C` 不包括自由变量 `x`，给定 `∃[ x ] B x` 成立的证明，我们可以推导出 `C` 成立。

{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="11130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11130" class="Function">∃-elim</a> <a id="11137" class="Symbol">:</a> <a id="11139" class="Symbol">∀</a> <a id="11141" class="Symbol">{</a><a id="11142" href="plfa.part1.Quantifiers.html#11142" class="Bound">A</a> <a id="11144" class="Symbol">:</a> <a id="11146" class="PrimitiveType">Set</a><a id="11149" class="Symbol">}</a> <a id="11151" class="Symbol">{</a><a id="11152" href="plfa.part1.Quantifiers.html#11152" class="Bound">B</a> <a id="11154" class="Symbol">:</a> <a id="11156" href="plfa.part1.Quantifiers.html#11142" class="Bound">A</a> <a id="11158" class="Symbol">→</a> <a id="11160" class="PrimitiveType">Set</a><a id="11163" class="Symbol">}</a> <a id="11165" class="Symbol">{</a><a id="11166" href="plfa.part1.Quantifiers.html#11166" class="Bound">C</a> <a id="11168" class="Symbol">:</a> <a id="11170" class="PrimitiveType">Set</a><a id="11173" class="Symbol">}</a>
  <a id="11177" class="Symbol">→</a> <a id="11179" class="Symbol">(∀</a> <a id="11182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11182" class="Bound">x</a> <a id="11184" class="Symbol">→</a> <a id="11186" href="plfa.part1.Quantifiers.html#11152" class="Bound">B</a> <a id="11188" href="plfa.part1.Quantifiers.html#11182" class="Bound">x</a> <a id="11190" class="Symbol">→</a> <a id="11192" href="plfa.part1.Quantifiers.html#11166" class="Bound">C</a><a id="11193" class="Symbol">)</a>
  <a id="11197" class="Symbol">→</a> <a id="11199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃[</a> <a id="11202" href="plfa.part1.Quantifiers.html#11202" class="Bound">x</a> <a id="11204" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="11206" href="plfa.part1.Quantifiers.html#11152" class="Bound">B</a> <a id="11208" href="plfa.part1.Quantifiers.html#11202" class="Bound">x</a>
    <a id="11214" class="Comment">---------------</a>
  <a id="11232" class="Symbol">→</a> <a id="11234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11166" class="Bound">C</a>
<a id="11236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11130" class="Function">∃-elim</a> <a id="11243" href="plfa.part1.Quantifiers.html#11243" class="Bound">f</a> <a id="11245" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="11247" href="plfa.part1.Quantifiers.html#11247" class="Bound">x</a> <a id="11249" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="11251" href="plfa.part1.Quantifiers.html#11251" class="Bound">y</a> <a id="11253" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="11255" class="Symbol">=</a> <a id="11257" href="plfa.part1.Quantifiers.html#11243" class="Bound">f</a> <a id="11259" href="plfa.part1.Quantifiers.html#11247" class="Bound">x</a> <a id="11261" href="plfa.part1.Quantifiers.html#11251" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.
{:/}

换句话说，如果我们知道对于任何 `A` 类型的 `x`，`B x` 蕴涵了 `C`，还知道对于某个类型
`A` 的 `x`，`B x` 成立，那么我们可以推导出 `C` 成立。这是因为我们可以先将 `∀ x → B x → C`
的证明对于 `A` 类型的 `x` 和 `B x` 类型的 `y` 实例化，而这样的值恰好可以由 `∃[ x ] B x`
的证明来提供。

{::comment}
Indeed, the converse also holds, and the two together form an isomorphism:
{:/}

的确，逆命题也成立，两者合起来构成一个同构：

{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="11957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11957" class="Function">∀∃-currying</a> <a id="11969" class="Symbol">:</a> <a id="11971" class="Symbol">∀</a> <a id="11973" class="Symbol">{</a><a id="11974" href="plfa.part1.Quantifiers.html#11974" class="Bound">A</a> <a id="11976" class="Symbol">:</a> <a id="11978" class="PrimitiveType">Set</a><a id="11981" class="Symbol">}</a> <a id="11983" class="Symbol">{</a><a id="11984" href="plfa.part1.Quantifiers.html#11984" class="Bound">B</a> <a id="11986" class="Symbol">:</a> <a id="11988" href="plfa.part1.Quantifiers.html#11974" class="Bound">A</a> <a id="11990" class="Symbol">→</a> <a id="11992" class="PrimitiveType">Set</a><a id="11995" class="Symbol">}</a> <a id="11997" class="Symbol">{</a><a id="11998" href="plfa.part1.Quantifiers.html#11998" class="Bound">C</a> <a id="12000" class="Symbol">:</a> <a id="12002" class="PrimitiveType">Set</a><a id="12005" class="Symbol">}</a>
  <a id="12009" class="Symbol">→</a> <a id="12011" class="Symbol">(∀</a> <a id="12014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12014" class="Bound">x</a> <a id="12016" class="Symbol">→</a> <a id="12018" href="plfa.part1.Quantifiers.html#11984" class="Bound">B</a> <a id="12020" href="plfa.part1.Quantifiers.html#12014" class="Bound">x</a> <a id="12022" class="Symbol">→</a> <a id="12024" href="plfa.part1.Quantifiers.html#11998" class="Bound">C</a><a id="12025" class="Symbol">)</a> <a id="12027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="12029" class="Symbol">(</a><a id="12030" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="12033" href="plfa.part1.Quantifiers.html#12033" class="Bound">x</a> <a id="12035" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="12037" href="plfa.part1.Quantifiers.html#11984" class="Bound">B</a> <a id="12039" href="plfa.part1.Quantifiers.html#12033" class="Bound">x</a> <a id="12041" class="Symbol">→</a> <a id="12043" href="plfa.part1.Quantifiers.html#11998" class="Bound">C</a><a id="12044" class="Symbol">)</a>
<a id="12046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11957" class="Function">∀∃-currying</a> <a id="12058" class="Symbol">=</a>
  <a id="12062" class="Keyword">record</a>
    <a id="12073" class="Symbol">{</a> <a id="12075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="12083" class="Symbol">=</a>  <a id="12086" class="Symbol">λ{</a> <a id="12089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12089" class="Bound">f</a> <a id="12091" class="Symbol">→</a> <a id="12093" class="Symbol">λ{</a> <a id="12096" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="12098" href="plfa.part1.Quantifiers.html#12098" class="Bound">x</a> <a id="12100" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="12102" href="plfa.part1.Quantifiers.html#12102" class="Bound">y</a> <a id="12104" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="12106" class="Symbol">→</a> <a id="12108" href="plfa.part1.Quantifiers.html#12089" class="Bound">f</a> <a id="12110" href="plfa.part1.Quantifiers.html#12098" class="Bound">x</a> <a id="12112" href="plfa.part1.Quantifiers.html#12102" class="Bound">y</a> <a id="12114" class="Symbol">}}</a>
    <a id="12121" class="Symbol">;</a> <a id="12123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="12131" class="Symbol">=</a>  <a id="12134" class="Symbol">λ{</a> <a id="12137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12137" class="Bound">g</a> <a id="12139" class="Symbol">→</a> <a id="12141" class="Symbol">λ{</a> <a id="12144" href="plfa.part1.Quantifiers.html#12144" class="Bound">x</a> <a id="12146" class="Symbol">→</a> <a id="12148" class="Symbol">λ{</a> <a id="12151" href="plfa.part1.Quantifiers.html#12151" class="Bound">y</a> <a id="12153" class="Symbol">→</a> <a id="12155" href="plfa.part1.Quantifiers.html#12137" class="Bound">g</a> <a id="12157" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="12159" href="plfa.part1.Quantifiers.html#12144" class="Bound">x</a> <a id="12161" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="12163" href="plfa.part1.Quantifiers.html#12151" class="Bound">y</a> <a id="12165" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="12167" class="Symbol">}}}</a>
    <a id="12175" class="Symbol">;</a> <a id="12177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="12185" class="Symbol">=</a>  <a id="12188" class="Symbol">λ{</a> <a id="12191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12191" class="Bound">f</a> <a id="12193" class="Symbol">→</a> <a id="12195" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12200" class="Symbol">}</a>
    <a id="12206" class="Symbol">;</a> <a id="12208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="12216" class="Symbol">=</a>  <a id="12219" class="Symbol">λ{</a> <a id="12222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12222" class="Bound">g</a> <a id="12224" class="Symbol">→</a> <a id="12226" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="12241" class="Symbol">λ{</a> <a id="12244" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="12246" href="plfa.part1.Quantifiers.html#12246" class="Bound">x</a> <a id="12248" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="12250" href="plfa.part1.Quantifiers.html#12250" class="Bound">y</a> <a id="12252" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="12254" class="Symbol">→</a> <a id="12256" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12261" class="Symbol">}}</a>
    <a id="12268" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).
{:/}

这可以被看做是将柯里化推广的结果。的确，建立这两者同构的证明与之前我们讨论
[蕴涵]({{ site.baseurl }}/Connectives/#implication)时给出的证明是一样的。

{::comment}
#### Exercise `∃-distrib-⊎` (recommended)
{:/}

#### 练习 `∃-distrib-⊎` （推荐）

{::comment}
Show that existentials distribute over disjunction:
{:/}

证明存在量词对于析取满足分配律：

{% raw %}<pre class="Agda"><a id="12784" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="12796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12796" class="Postulate">∃-distrib-⊎</a> <a id="12808" class="Symbol">:</a> <a id="12810" class="Symbol">∀</a> <a id="12812" class="Symbol">{</a><a id="12813" href="plfa.part1.Quantifiers.html#12813" class="Bound">A</a> <a id="12815" class="Symbol">:</a> <a id="12817" class="PrimitiveType">Set</a><a id="12820" class="Symbol">}</a> <a id="12822" class="Symbol">{</a><a id="12823" href="plfa.part1.Quantifiers.html#12823" class="Bound">B</a> <a id="12825" href="plfa.part1.Quantifiers.html#12825" class="Bound">C</a> <a id="12827" class="Symbol">:</a> <a id="12829" href="plfa.part1.Quantifiers.html#12813" class="Bound">A</a> <a id="12831" class="Symbol">→</a> <a id="12833" class="PrimitiveType">Set</a><a id="12836" class="Symbol">}</a> <a id="12838" class="Symbol">→</a>
    <a id="12844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃[</a> <a id="12847" href="plfa.part1.Quantifiers.html#12847" class="Bound">x</a> <a id="12849" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="12851" class="Symbol">(</a><a id="12852" href="plfa.part1.Quantifiers.html#12823" class="Bound">B</a> <a id="12854" href="plfa.part1.Quantifiers.html#12847" class="Bound">x</a> <a id="12856" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12858" href="plfa.part1.Quantifiers.html#12825" class="Bound">C</a> <a id="12860" href="plfa.part1.Quantifiers.html#12847" class="Bound">x</a><a id="12861" class="Symbol">)</a> <a id="12863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="12865" class="Symbol">(</a><a id="12866" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="12869" href="plfa.part1.Quantifiers.html#12869" class="Bound">x</a> <a id="12871" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="12873" href="plfa.part1.Quantifiers.html#12823" class="Bound">B</a> <a id="12875" href="plfa.part1.Quantifiers.html#12869" class="Bound">x</a><a id="12876" class="Symbol">)</a> <a id="12878" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12880" class="Symbol">(</a><a id="12881" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="12884" href="plfa.part1.Quantifiers.html#12884" class="Bound">x</a> <a id="12886" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="12888" href="plfa.part1.Quantifiers.html#12825" class="Bound">C</a> <a id="12890" href="plfa.part1.Quantifiers.html#12884" class="Bound">x</a><a id="12891" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃×-implies-×∃` (practice)
{:/}

#### 练习 `∃×-implies-×∃`（实践）

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明合取的存在命题蕴涵了存在命题的合取：

{% raw %}<pre class="Agda"><a id="13110" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="13122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13122" class="Postulate">∃×-implies-×∃</a> <a id="13136" class="Symbol">:</a> <a id="13138" class="Symbol">∀</a> <a id="13140" class="Symbol">{</a><a id="13141" href="plfa.part1.Quantifiers.html#13141" class="Bound">A</a> <a id="13143" class="Symbol">:</a> <a id="13145" class="PrimitiveType">Set</a><a id="13148" class="Symbol">}</a> <a id="13150" class="Symbol">{</a><a id="13151" href="plfa.part1.Quantifiers.html#13151" class="Bound">B</a> <a id="13153" href="plfa.part1.Quantifiers.html#13153" class="Bound">C</a> <a id="13155" class="Symbol">:</a> <a id="13157" href="plfa.part1.Quantifiers.html#13141" class="Bound">A</a> <a id="13159" class="Symbol">→</a> <a id="13161" class="PrimitiveType">Set</a><a id="13164" class="Symbol">}</a> <a id="13166" class="Symbol">→</a>
    <a id="13172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃[</a> <a id="13175" href="plfa.part1.Quantifiers.html#13175" class="Bound">x</a> <a id="13177" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="13179" class="Symbol">(</a><a id="13180" href="plfa.part1.Quantifiers.html#13151" class="Bound">B</a> <a id="13182" href="plfa.part1.Quantifiers.html#13175" class="Bound">x</a> <a id="13184" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="13186" href="plfa.part1.Quantifiers.html#13153" class="Bound">C</a> <a id="13188" href="plfa.part1.Quantifiers.html#13175" class="Bound">x</a><a id="13189" class="Symbol">)</a> <a id="13191" class="Symbol">→</a> <a id="13193" class="Symbol">(</a><a id="13194" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="13197" href="plfa.part1.Quantifiers.html#13197" class="Bound">x</a> <a id="13199" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="13201" href="plfa.part1.Quantifiers.html#13151" class="Bound">B</a> <a id="13203" href="plfa.part1.Quantifiers.html#13197" class="Bound">x</a><a id="13204" class="Symbol">)</a> <a id="13206" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="13208" class="Symbol">(</a><a id="13209" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="13212" href="plfa.part1.Quantifiers.html#13212" class="Bound">x</a> <a id="13214" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="13216" href="plfa.part1.Quantifiers.html#13153" class="Bound">C</a> <a id="13218" href="plfa.part1.Quantifiers.html#13212" class="Bound">x</a><a id="13219" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∃-⊎` (practice)
{:/}

#### 练习 `∃-⊎`（实践）

{::comment}
Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.
{:/}

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

{::comment}
## An existential example
{:/}

## 一个存在量化的例子

{::comment}
Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{:/}

回忆我们在 [Relations]({{ site.baseurl }}/Relations/)
章节中定义的 `even` 和 `odd`：

{% raw %}<pre class="Agda"><a id="13852" class="Keyword">data</a> <a id="even"></a><a id="13857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13857" class="Datatype">even</a> <a id="13862" class="Symbol">:</a> <a id="13864" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13866" class="Symbol">→</a> <a id="13868" class="PrimitiveType">Set</a>
<a id="13872" class="Keyword">data</a> <a id="odd"></a><a id="13877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13877" class="Datatype">odd</a>  <a id="13882" class="Symbol">:</a> <a id="13884" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13886" class="Symbol">→</a> <a id="13888" class="PrimitiveType">Set</a>

<a id="13893" class="Keyword">data</a> <a id="13898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13857" class="Datatype">even</a> <a id="13903" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13912" class="InductiveConstructor">even-zero</a> <a id="13922" class="Symbol">:</a> <a id="13924" href="plfa.part1.Quantifiers.html#13857" class="Datatype">even</a> <a id="13929" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="13937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13937" class="InductiveConstructor">even-suc</a> <a id="13946" class="Symbol">:</a> <a id="13948" class="Symbol">∀</a> <a id="13950" class="Symbol">{</a><a id="13951" href="plfa.part1.Quantifiers.html#13951" class="Bound">n</a> <a id="13953" class="Symbol">:</a> <a id="13955" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13956" class="Symbol">}</a>
    <a id="13962" class="Symbol">→</a> <a id="13964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13877" class="Datatype">odd</a> <a id="13968" href="plfa.part1.Quantifiers.html#13951" class="Bound">n</a>
      <a id="13976" class="Comment">------------</a>
    <a id="13993" class="Symbol">→</a> <a id="13995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13857" class="Datatype">even</a> <a id="14000" class="Symbol">(</a><a id="14001" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14005" href="plfa.part1.Quantifiers.html#13951" class="Bound">n</a><a id="14006" class="Symbol">)</a>

<a id="14009" class="Keyword">data</a> <a id="14014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13877" class="Datatype">odd</a> <a id="14018" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14026" class="InductiveConstructor">odd-suc</a> <a id="14034" class="Symbol">:</a> <a id="14036" class="Symbol">∀</a> <a id="14038" class="Symbol">{</a><a id="14039" href="plfa.part1.Quantifiers.html#14039" class="Bound">n</a> <a id="14041" class="Symbol">:</a> <a id="14043" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14044" class="Symbol">}</a>
    <a id="14050" class="Symbol">→</a> <a id="14052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13857" class="Datatype">even</a> <a id="14057" href="plfa.part1.Quantifiers.html#14039" class="Bound">n</a>
      <a id="14065" class="Comment">-----------</a>
    <a id="14081" class="Symbol">→</a> <a id="14083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13877" class="Datatype">odd</a> <a id="14087" class="Symbol">(</a><a id="14088" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14092" href="plfa.part1.Quantifiers.html#14039" class="Bound">n</a><a id="14093" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.
{:/}

如果一个数是 0 或者它是奇数的后继，那么这个数是偶数。如果一个数是偶数的后继，那么这个数是奇数。

{::comment}
We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:
{:/}

我们接下来要证明，一个数是偶数当且仅当这个数是一个数的两倍，一个数是奇数当且仅当这个数是一个数的两倍多一。换句话说，我们要证明的是：

{::comment}
`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`
{:/}

`even n`   当且仅当   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   当且仅当   `∃[ m ] (1 + m * 2 ≡ n)`

{::comment}
By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.
{:/}

惯例来说，我们往往将常数因子写在前面、将和里的常数项写在后面。但是这里我们没有按照惯例，而是反了过来，因为这样可以让证明更简单：

{::comment}
Here is the proof in the forward direction:
{:/}

这是向前方向的证明：

{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="15088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15088" class="Function">even-∃</a> <a id="15095" class="Symbol">:</a> <a id="15097" class="Symbol">∀</a> <a id="15099" class="Symbol">{</a><a id="15100" href="plfa.part1.Quantifiers.html#15100" class="Bound">n</a> <a id="15102" class="Symbol">:</a> <a id="15104" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15105" class="Symbol">}</a> <a id="15107" class="Symbol">→</a> <a id="15109" href="plfa.part1.Quantifiers.html#13857" class="Datatype">even</a> <a id="15114" href="plfa.part1.Quantifiers.html#15100" class="Bound">n</a> <a id="15116" class="Symbol">→</a> <a id="15118" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="15121" href="plfa.part1.Quantifiers.html#15121" class="Bound">m</a> <a id="15123" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="15125" class="Symbol">(</a>    <a id="15130" href="plfa.part1.Quantifiers.html#15121" class="Bound">m</a> <a id="15132" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="15134" class="Number">2</a> <a id="15136" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15138" href="plfa.part1.Quantifiers.html#15100" class="Bound">n</a><a id="15139" class="Symbol">)</a>
<a id="odd-∃"></a><a id="15141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15141" class="Function">odd-∃</a>  <a id="15148" class="Symbol">:</a> <a id="15150" class="Symbol">∀</a> <a id="15152" class="Symbol">{</a><a id="15153" href="plfa.part1.Quantifiers.html#15153" class="Bound">n</a> <a id="15155" class="Symbol">:</a> <a id="15157" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15158" class="Symbol">}</a> <a id="15160" class="Symbol">→</a>  <a id="15163" href="plfa.part1.Quantifiers.html#13877" class="Datatype">odd</a> <a id="15167" href="plfa.part1.Quantifiers.html#15153" class="Bound">n</a> <a id="15169" class="Symbol">→</a> <a id="15171" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="15174" href="plfa.part1.Quantifiers.html#15174" class="Bound">m</a> <a id="15176" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="15178" class="Symbol">(</a><a id="15179" class="Number">1</a> <a id="15181" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="15183" href="plfa.part1.Quantifiers.html#15174" class="Bound">m</a> <a id="15185" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="15187" class="Number">2</a> <a id="15189" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15191" href="plfa.part1.Quantifiers.html#15153" class="Bound">n</a><a id="15192" class="Symbol">)</a>

<a id="15195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15088" class="Function">even-∃</a> <a id="15202" href="plfa.part1.Quantifiers.html#13912" class="InductiveConstructor">even-zero</a>                       <a id="15234" class="Symbol">=</a>  <a id="15237" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="15239" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="15244" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="15246" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15251" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>
<a id="15253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15088" class="Function">even-∃</a> <a id="15260" class="Symbol">(</a><a id="15261" href="plfa.part1.Quantifiers.html#13937" class="InductiveConstructor">even-suc</a> <a id="15270" href="plfa.part1.Quantifiers.html#15270" class="Bound">o</a><a id="15271" class="Symbol">)</a> <a id="15273" class="Keyword">with</a> <a id="15278" href="plfa.part1.Quantifiers.html#15141" class="Function">odd-∃</a> <a id="15284" href="plfa.part1.Quantifiers.html#15270" class="Bound">o</a>
<a id="15286" class="Symbol">...</a>                    <a id="15309" class="Symbol">|</a> <a id="15311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7218" class="InductiveConstructor Operator">⟨</a> <a id="15313" href="plfa.part1.Quantifiers.html#15313" class="Bound">m</a> <a id="15315" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="15317" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15322" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>  <a id="15325" class="Symbol">=</a>  <a id="15328" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="15330" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15334" href="plfa.part1.Quantifiers.html#15313" class="Bound">m</a> <a id="15336" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="15338" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15343" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>

<a id="15346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15141" class="Function">odd-∃</a>  <a id="15353" class="Symbol">(</a><a id="15354" href="plfa.part1.Quantifiers.html#14026" class="InductiveConstructor">odd-suc</a> <a id="15362" href="plfa.part1.Quantifiers.html#15362" class="Bound">e</a><a id="15363" class="Symbol">)</a>  <a id="15366" class="Keyword">with</a> <a id="15371" href="plfa.part1.Quantifiers.html#15088" class="Function">even-∃</a> <a id="15378" href="plfa.part1.Quantifiers.html#15362" class="Bound">e</a>
<a id="15380" class="Symbol">...</a>                    <a id="15403" class="Symbol">|</a> <a id="15405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7218" class="InductiveConstructor Operator">⟨</a> <a id="15407" href="plfa.part1.Quantifiers.html#15407" class="Bound">m</a> <a id="15409" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="15411" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15416" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>  <a id="15419" class="Symbol">=</a>  <a id="15422" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="15424" href="plfa.part1.Quantifiers.html#15407" class="Bound">m</a> <a id="15426" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="15428" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15433" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}
{::comment}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:
{:/}

我们定义两个相互递归的函数。给定 `n` 是奇数或者是偶数的证明，我们返回一个数
`m`，以及 `m * 2 ≡ n` 或者 `1 + m * 2 ≡ n` 的证明。我们根据 `n` 是奇数或者是偶数的证明进行归纳：

{::comment}
* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.
{:/}

* 如果这个数是偶数，因为它是 0，那么我们返回数据对 0 ，以及 0 的两倍是 0 的证明。

* 如果这个数是偶数，因为它是比一个奇数多 1，那么我们可以使用归纳假设，来获得一个数 `m` 和
`1 + m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `suc m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

* 如果这个数是奇数，因为它是一个偶数的后继，那么我们可以使用归纳假设，来获得一个数 `m` 和
`m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `1 + m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

{::comment}
This completes the proof in the forward direction.
{:/}

这样，我们就完成了正方向的证明。

{::comment}
Here is the proof in the reverse direction:
{:/}

接下来是反方向的证明：

{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="16985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16985" class="Function">∃-even</a> <a id="16992" class="Symbol">:</a> <a id="16994" class="Symbol">∀</a> <a id="16996" class="Symbol">{</a><a id="16997" href="plfa.part1.Quantifiers.html#16997" class="Bound">n</a> <a id="16999" class="Symbol">:</a> <a id="17001" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17002" class="Symbol">}</a> <a id="17004" class="Symbol">→</a> <a id="17006" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="17009" href="plfa.part1.Quantifiers.html#17009" class="Bound">m</a> <a id="17011" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="17013" class="Symbol">(</a>    <a id="17018" href="plfa.part1.Quantifiers.html#17009" class="Bound">m</a> <a id="17020" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="17022" class="Number">2</a> <a id="17024" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17026" href="plfa.part1.Quantifiers.html#16997" class="Bound">n</a><a id="17027" class="Symbol">)</a> <a id="17029" class="Symbol">→</a> <a id="17031" href="plfa.part1.Quantifiers.html#13857" class="Datatype">even</a> <a id="17036" href="plfa.part1.Quantifiers.html#16997" class="Bound">n</a>
<a id="∃-odd"></a><a id="17038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#17038" class="Function">∃-odd</a>  <a id="17045" class="Symbol">:</a> <a id="17047" class="Symbol">∀</a> <a id="17049" class="Symbol">{</a><a id="17050" href="plfa.part1.Quantifiers.html#17050" class="Bound">n</a> <a id="17052" class="Symbol">:</a> <a id="17054" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17055" class="Symbol">}</a> <a id="17057" class="Symbol">→</a> <a id="17059" href="plfa.part1.Quantifiers.html#10565" class="Function">∃[</a> <a id="17062" href="plfa.part1.Quantifiers.html#17062" class="Bound">m</a> <a id="17064" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="17066" class="Symbol">(</a><a id="17067" class="Number">1</a> <a id="17069" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17071" href="plfa.part1.Quantifiers.html#17062" class="Bound">m</a> <a id="17073" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="17075" class="Number">2</a> <a id="17077" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17079" href="plfa.part1.Quantifiers.html#17050" class="Bound">n</a><a id="17080" class="Symbol">)</a> <a id="17082" class="Symbol">→</a>  <a id="17085" href="plfa.part1.Quantifiers.html#13877" class="Datatype">odd</a> <a id="17089" href="plfa.part1.Quantifiers.html#17050" class="Bound">n</a>

<a id="17092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16985" class="Function">∃-even</a> <a id="17099" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a>  <a id="17102" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="17107" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="17109" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17114" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>  <a id="17117" class="Symbol">=</a>  <a id="17120" href="plfa.part1.Quantifiers.html#13912" class="InductiveConstructor">even-zero</a>
<a id="17130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16985" class="Function">∃-even</a> <a id="17137" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="17139" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="17143" href="plfa.part1.Quantifiers.html#17143" class="Bound">m</a> <a id="17145" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="17147" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17152" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>  <a id="17155" class="Symbol">=</a>  <a id="17158" href="plfa.part1.Quantifiers.html#13937" class="InductiveConstructor">even-suc</a> <a id="17167" class="Symbol">(</a><a id="17168" href="plfa.part1.Quantifiers.html#17038" class="Function">∃-odd</a> <a id="17174" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="17176" href="plfa.part1.Quantifiers.html#17143" class="Bound">m</a> <a id="17178" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="17180" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17185" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a><a id="17186" class="Symbol">)</a>

<a id="17189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#17038" class="Function">∃-odd</a>  <a id="17196" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a>     <a id="17202" href="plfa.part1.Quantifiers.html#17202" class="Bound">m</a> <a id="17204" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="17206" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17211" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a>  <a id="17214" class="Symbol">=</a>  <a id="17217" href="plfa.part1.Quantifiers.html#14026" class="InductiveConstructor">odd-suc</a> <a id="17225" class="Symbol">(</a><a id="17226" href="plfa.part1.Quantifiers.html#16985" class="Function">∃-even</a> <a id="17233" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="17235" href="plfa.part1.Quantifiers.html#17202" class="Bound">m</a> <a id="17237" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="17239" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17244" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a><a id="17245" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:
{:/}

给定一个是另一个数两倍的数，我们需要证明这个数是偶数。给定一个是另一个数两倍多一的数，我们需要证明这个数是奇数。我们对于存在量化的证明进行归纳。在偶数的情况，我们也需要考虑两种一个数是另一个数两倍的情况。

{::comment}
- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.
{:/}

- 在偶数是 `zero` 的情况中，我们需要证明 `zero * 2` 是偶数，由 `even-zero` 可得。

- 在偶数是 `suc n` 的情况中，我们需要证明 `suc m * 2` 是偶数。归纳假设告诉我们，
`1 + m * 2` 是奇数，那么所求证的结果由 `even-suc` 可得。

- 在偶数的情况中，我们需要证明 `1 + m * 2` 是奇数。归纳假设告诉我们，`m * 2` 是偶数，那么所求证的结果由 `odd-suc` 可得。

{::comment}
This completes the proof in the backward direction.
{:/}

这样，我们就完成了向后方向的证明。

{::comment}
#### Exercise `∃-even-odd` (practice)
{:/}

#### 练习 `∃-even-odd`（实践）

{::comment}
How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.
{:/}

如果我们用 `2 * m` 代替 `m * 2`，`2 * m + 1` 代替 `1 + m * 2`，上述证明会变得复杂多少呢？用这种方法来重写 `∃-even` 和 `∃-odd`。

{::comment}
{% raw %}<pre class="Agda"><a id="18830" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18867" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃-+-≤` (practice)
{:/}

#### 练习 `∃-+-≤`（实践）

{::comment}
Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.
{:/}

证明当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时 `y ≤ z` 成立。

{::comment}
{% raw %}<pre class="Agda"><a id="19119" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="19156" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Existentials, Universals, and Negation
{:/}

## 存在量化、全称量化和否定

{::comment}
Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{:/}

存在量化的否定与否定的全称量化是同构的。考虑到存在量化是析构的推广，全称量化是合构的推广，这样的结果与析构的否定与否定的合构是同构的结果相似。

{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="19650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19650" class="Function">¬∃≃∀¬</a> <a id="19656" class="Symbol">:</a> <a id="19658" class="Symbol">∀</a> <a id="19660" class="Symbol">{</a><a id="19661" href="plfa.part1.Quantifiers.html#19661" class="Bound">A</a> <a id="19663" class="Symbol">:</a> <a id="19665" class="PrimitiveType">Set</a><a id="19668" class="Symbol">}</a> <a id="19670" class="Symbol">{</a><a id="19671" href="plfa.part1.Quantifiers.html#19671" class="Bound">B</a> <a id="19673" class="Symbol">:</a> <a id="19675" href="plfa.part1.Quantifiers.html#19661" class="Bound">A</a> <a id="19677" class="Symbol">→</a> <a id="19679" class="PrimitiveType">Set</a><a id="19682" class="Symbol">}</a>
  <a id="19686" class="Symbol">→</a> <a id="19688" class="Symbol">(</a><a id="19689" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="19691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃[</a> <a id="19694" href="plfa.part1.Quantifiers.html#19694" class="Bound">x</a> <a id="19696" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="19698" href="plfa.part1.Quantifiers.html#19671" class="Bound">B</a> <a id="19700" href="plfa.part1.Quantifiers.html#19694" class="Bound">x</a><a id="19701" class="Symbol">)</a> <a id="19703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="19705" class="Symbol">∀</a> <a id="19707" href="plfa.part1.Quantifiers.html#19707" class="Bound">x</a> <a id="19709" class="Symbol">→</a> <a id="19711" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="19713" href="plfa.part1.Quantifiers.html#19671" class="Bound">B</a> <a id="19715" href="plfa.part1.Quantifiers.html#19707" class="Bound">x</a>
<a id="19717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19650" class="Function">¬∃≃∀¬</a> <a id="19723" class="Symbol">=</a>
  <a id="19727" class="Keyword">record</a>
    <a id="19738" class="Symbol">{</a> <a id="19740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="19748" class="Symbol">=</a>  <a id="19751" class="Symbol">λ{</a> <a id="19754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19754" class="Bound">¬∃xy</a> <a id="19759" href="plfa.part1.Quantifiers.html#19759" class="Bound">x</a> <a id="19761" href="plfa.part1.Quantifiers.html#19761" class="Bound">y</a> <a id="19763" class="Symbol">→</a> <a id="19765" href="plfa.part1.Quantifiers.html#19754" class="Bound">¬∃xy</a> <a id="19770" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="19772" href="plfa.part1.Quantifiers.html#19759" class="Bound">x</a> <a id="19774" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="19776" href="plfa.part1.Quantifiers.html#19761" class="Bound">y</a> <a id="19778" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="19780" class="Symbol">}</a>
    <a id="19786" class="Symbol">;</a> <a id="19788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="19796" class="Symbol">=</a>  <a id="19799" class="Symbol">λ{</a> <a id="19802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19802" class="Bound">∀¬xy</a> <a id="19807" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="19809" href="plfa.part1.Quantifiers.html#19809" class="Bound">x</a> <a id="19811" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="19813" href="plfa.part1.Quantifiers.html#19813" class="Bound">y</a> <a id="19815" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="19817" class="Symbol">→</a> <a id="19819" href="plfa.part1.Quantifiers.html#19802" class="Bound">∀¬xy</a> <a id="19824" href="plfa.part1.Quantifiers.html#19809" class="Bound">x</a> <a id="19826" href="plfa.part1.Quantifiers.html#19813" class="Bound">y</a> <a id="19828" class="Symbol">}</a>
    <a id="19834" class="Symbol">;</a> <a id="19836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="19844" class="Symbol">=</a>  <a id="19847" class="Symbol">λ{</a> <a id="19850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19850" class="Bound">¬∃xy</a> <a id="19855" class="Symbol">→</a> <a id="19857" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="19872" class="Symbol">λ{</a> <a id="19875" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟨</a> <a id="19877" href="plfa.part1.Quantifiers.html#19877" class="Bound">x</a> <a id="19879" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">,</a> <a id="19881" href="plfa.part1.Quantifiers.html#19881" class="Bound">y</a> <a id="19883" href="plfa.part1.Quantifiers.html#7218" class="InductiveConstructor Operator">⟩</a> <a id="19885" class="Symbol">→</a> <a id="19887" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19892" class="Symbol">}</a> <a id="19894" class="Symbol">}</a>
    <a id="19900" class="Symbol">;</a> <a id="19902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="19910" class="Symbol">=</a>  <a id="19913" class="Symbol">λ{</a> <a id="19916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19916" class="Bound">∀¬xy</a> <a id="19921" class="Symbol">→</a> <a id="19923" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19928" class="Symbol">}</a>
    <a id="19934" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.
{:/}

在 `to` 的方向，给定了一个 `¬ ∃[ x ] B x` 类型的值 `¬∃xy`，需要证明给定一个 `x` 的值，可以推导出 `¬ B x`。换句话说，给定一个 `B x` 类型的值 `y`，我们可以推导出假。将 `x` 和 `y`
合并起来我们就得到了 `∃[ x ] B x` 类型的值 `⟨ x , y ⟩`，对其使用 `¬∃xy` 即可获得矛盾。

{::comment}
In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.
{:/}

在 `from` 的方向，给定了一个 `∀ x → ¬ B x` 类型的值 `∀¬xy`，需要证明从一个类型为
`∃[ x ] B x` 类型的值 `⟨ x , y ⟩` ，我们可以推导出假。将 `∀¬xy` 使用于 `x` 之上，可以得到类型为 `¬ B x` 的值，对其使用 `y` 即可获得矛盾。

{::comment}
The two inverse proofs are straightforward, where one direction
requires extensionality.
{:/}

两个逆的证明很直接，其中有一个方向需要外延性。

{::comment}
#### Exercise `∃¬-implies-¬∀` (recommended)
{:/}

#### 练习 `∃¬-implies-¬∀` （推荐）

{::comment}
Show that existential of a negation implies negation of a universal:
{:/}

证明否定的存在量化蕴涵了全称量化的否定：

{% raw %}<pre class="Agda"><a id="21251" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="21263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#21263" class="Postulate">∃¬-implies-¬∀</a> <a id="21277" class="Symbol">:</a> <a id="21279" class="Symbol">∀</a> <a id="21281" class="Symbol">{</a><a id="21282" href="plfa.part1.Quantifiers.html#21282" class="Bound">A</a> <a id="21284" class="Symbol">:</a> <a id="21286" class="PrimitiveType">Set</a><a id="21289" class="Symbol">}</a> <a id="21291" class="Symbol">{</a><a id="21292" href="plfa.part1.Quantifiers.html#21292" class="Bound">B</a> <a id="21294" class="Symbol">:</a> <a id="21296" href="plfa.part1.Quantifiers.html#21282" class="Bound">A</a> <a id="21298" class="Symbol">→</a> <a id="21300" class="PrimitiveType">Set</a><a id="21303" class="Symbol">}</a>
    <a id="21309" class="Symbol">→</a> <a id="21311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10565" class="Function">∃[</a> <a id="21314" href="plfa.part1.Quantifiers.html#21314" class="Bound">x</a> <a id="21316" href="plfa.part1.Quantifiers.html#10565" class="Function">]</a> <a id="21318" class="Symbol">(</a><a id="21319" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="21321" href="plfa.part1.Quantifiers.html#21292" class="Bound">B</a> <a id="21323" href="plfa.part1.Quantifiers.html#21314" class="Bound">x</a><a id="21324" class="Symbol">)</a>
      <a id="21332" class="Comment">--------------</a>
    <a id="21351" class="Symbol">→</a> <a id="21353" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="21355" class="Symbol">(∀</a> <a id="21358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#21358" class="Bound">x</a> <a id="21360" class="Symbol">→</a> <a id="21362" href="plfa.part1.Quantifiers.html#21292" class="Bound">B</a> <a id="21364" href="plfa.part1.Quantifiers.html#21358" class="Bound">x</a><a id="21365" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立吗？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}
{:/}

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:
{:/}

回忆在练习 [Bin]({{ site.baseurl }}/Naturals/#Bin)、
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws) 和
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates) 中，我们定义了比特串数据类型 `Bin` 来表示自然数，并要求你定义了下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

{::comment}
And to establish the following properties:
{:/}

以及证明了下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

{::comment}
Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

使用上述，证明 `ℕ` 与 `∃[ b ](Can b)` 之间存在同构。

我们建议证明以下引理，它描述了对于给定的二进制数 `b`，`One b` 只有一个证明，
`Can b`，也是如此。

    ≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'

    ≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

{::comment}
{% raw %}<pre class="Agda"><a id="22966" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="23003" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章中相似的定义：

{% raw %}<pre class="Agda"><a id="23192" class="Keyword">import</a> <a id="23199" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="23212" class="Keyword">using</a> <a id="23218" class="Symbol">(</a><a id="23219" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="23220" class="Symbol">;</a> <a id="23222" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="23225" class="Symbol">;</a> <a id="23227" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="23228" class="Symbol">;</a> <a id="23230" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="23238" class="Symbol">;</a> <a id="23240" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="23248" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)

{:/}

本章节使用下列 Unicode：

    Π  U+03A0  大写希腊字母 PI (\Pi)
    Σ  U+03A3  大写希腊字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
