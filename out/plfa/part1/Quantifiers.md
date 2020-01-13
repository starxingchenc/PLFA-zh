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
Chapter Induction we showed addition is associative:
{:/}

我们用依赖函数类型（Dependent Function Type）来形式化全称量化，这样的形式在书中贯穿始终。例如，在归纳一章中，我们证明了加法满足结合律：

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
appears free in `B x` but bound in `∀ (x : A) → B x`.

通常给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 后的命题。变量 `x` 在 `B x` 中以自由变量的形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

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
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。


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

{% raw %}<pre class="Agda"><a id="7050" class="Keyword">data</a> <a id="Σ"></a><a id="7055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7055" class="Datatype">Σ</a> <a id="7057" class="Symbol">(</a><a id="7058" href="plfa.part1.Quantifiers.html#7058" class="Bound">A</a> <a id="7060" class="Symbol">:</a> <a id="7062" class="PrimitiveType">Set</a><a id="7065" class="Symbol">)</a> <a id="7067" class="Symbol">(</a><a id="7068" href="plfa.part1.Quantifiers.html#7068" class="Bound">B</a> <a id="7070" class="Symbol">:</a> <a id="7072" href="plfa.part1.Quantifiers.html#7058" class="Bound">A</a> <a id="7074" class="Symbol">→</a> <a id="7076" class="PrimitiveType">Set</a><a id="7079" class="Symbol">)</a> <a id="7081" class="Symbol">:</a> <a id="7083" class="PrimitiveType">Set</a> <a id="7087" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="7095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7095" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="7101" class="Symbol">:</a> <a id="7103" class="Symbol">(</a><a id="7104" href="plfa.part1.Quantifiers.html#7104" class="Bound">x</a> <a id="7106" class="Symbol">:</a> <a id="7108" href="plfa.part1.Quantifiers.html#7058" class="Bound">A</a><a id="7109" class="Symbol">)</a> <a id="7111" class="Symbol">→</a> <a id="7113" href="plfa.part1.Quantifiers.html#7068" class="Bound">B</a> <a id="7115" href="plfa.part1.Quantifiers.html#7104" class="Bound">x</a> <a id="7117" class="Symbol">→</a> <a id="7119" href="plfa.part1.Quantifiers.html#7055" class="Datatype">Σ</a> <a id="7121" href="plfa.part1.Quantifiers.html#7058" class="Bound">A</a> <a id="7123" href="plfa.part1.Quantifiers.html#7068" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="7230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7230" class="Function">Σ-syntax</a> <a id="7239" class="Symbol">=</a> <a id="7241" href="plfa.part1.Quantifiers.html#7055" class="Datatype">Σ</a>
<a id="7243" class="Keyword">infix</a> <a id="7249" class="Number">2</a> <a id="7251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7230" class="Function">Σ-syntax</a>
<a id="7260" class="Keyword">syntax</a> <a id="7267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7230" class="Function">Σ-syntax</a> <a id="7276" class="Bound">A</a> <a id="7278" class="Symbol">(λ</a> <a id="7281" class="Bound">x</a> <a id="7283" class="Symbol">→</a> <a id="7285" class="Bound">B</a><a id="7286" class="Symbol">)</a> <a id="7288" class="Symbol">=</a> <a id="7290" class="Function">Σ[</a> <a id="7293" class="Bound">x</a> <a id="7295" class="Function">∈</a> <a id="7297" class="Bound">A</a> <a id="7299" class="Function">]</a> <a id="7301" class="Bound">B</a>
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

{% raw %}<pre class="Agda"><a id="7955" class="Keyword">record</a> <a id="Σ′"></a><a id="7962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7962" class="Record">Σ′</a> <a id="7965" class="Symbol">(</a><a id="7966" href="plfa.part1.Quantifiers.html#7966" class="Bound">A</a> <a id="7968" class="Symbol">:</a> <a id="7970" class="PrimitiveType">Set</a><a id="7973" class="Symbol">)</a> <a id="7975" class="Symbol">(</a><a id="7976" href="plfa.part1.Quantifiers.html#7976" class="Bound">B</a> <a id="7978" class="Symbol">:</a> <a id="7980" href="plfa.part1.Quantifiers.html#7966" class="Bound">A</a> <a id="7982" class="Symbol">→</a> <a id="7984" class="PrimitiveType">Set</a><a id="7987" class="Symbol">)</a> <a id="7989" class="Symbol">:</a> <a id="7991" class="PrimitiveType">Set</a> <a id="7995" class="Keyword">where</a>
  <a id="8003" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="8013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8013" class="Field">proj₁′</a> <a id="8020" class="Symbol">:</a> <a id="8022" href="plfa.part1.Quantifiers.html#7966" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="8028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8028" class="Field">proj₂′</a> <a id="8035" class="Symbol">:</a> <a id="8037" href="plfa.part1.Quantifiers.html#7976" class="Bound">B</a> <a id="8039" href="plfa.part1.Quantifiers.html#8013" class="Field">proj₁′</a>
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

{% raw %}<pre class="Agda"><a id="∃"></a><a id="10389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10389" class="Function">∃</a> <a id="10391" class="Symbol">:</a> <a id="10393" class="Symbol">∀</a> <a id="10395" class="Symbol">{</a><a id="10396" href="plfa.part1.Quantifiers.html#10396" class="Bound">A</a> <a id="10398" class="Symbol">:</a> <a id="10400" class="PrimitiveType">Set</a><a id="10403" class="Symbol">}</a> <a id="10405" class="Symbol">(</a><a id="10406" href="plfa.part1.Quantifiers.html#10406" class="Bound">B</a> <a id="10408" class="Symbol">:</a> <a id="10410" href="plfa.part1.Quantifiers.html#10396" class="Bound">A</a> <a id="10412" class="Symbol">→</a> <a id="10414" class="PrimitiveType">Set</a><a id="10417" class="Symbol">)</a> <a id="10419" class="Symbol">→</a> <a id="10421" class="PrimitiveType">Set</a>
<a id="10425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10389" class="Function">∃</a> <a id="10427" class="Symbol">{</a><a id="10428" href="plfa.part1.Quantifiers.html#10428" class="Bound">A</a><a id="10429" class="Symbol">}</a> <a id="10431" href="plfa.part1.Quantifiers.html#10431" class="Bound">B</a> <a id="10433" class="Symbol">=</a> <a id="10435" href="plfa.part1.Quantifiers.html#7055" class="Datatype">Σ</a> <a id="10437" href="plfa.part1.Quantifiers.html#10428" class="Bound">A</a> <a id="10439" href="plfa.part1.Quantifiers.html#10431" class="Bound">B</a>

<a id="∃-syntax"></a><a id="10442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃-syntax</a> <a id="10451" class="Symbol">=</a> <a id="10453" href="plfa.part1.Quantifiers.html#10389" class="Function">∃</a>
<a id="10455" class="Keyword">syntax</a> <a id="10462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃-syntax</a> <a id="10471" class="Symbol">(λ</a> <a id="10474" class="Bound">x</a> <a id="10476" class="Symbol">→</a> <a id="10478" class="Bound">B</a><a id="10479" class="Symbol">)</a> <a id="10481" class="Symbol">=</a> <a id="10483" class="Function">∃[</a> <a id="10486" class="Bound">x</a> <a id="10488" class="Function">]</a> <a id="10490" class="Bound">B</a>
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

{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="11007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11007" class="Function">∃-elim</a> <a id="11014" class="Symbol">:</a> <a id="11016" class="Symbol">∀</a> <a id="11018" class="Symbol">{</a><a id="11019" href="plfa.part1.Quantifiers.html#11019" class="Bound">A</a> <a id="11021" class="Symbol">:</a> <a id="11023" class="PrimitiveType">Set</a><a id="11026" class="Symbol">}</a> <a id="11028" class="Symbol">{</a><a id="11029" href="plfa.part1.Quantifiers.html#11029" class="Bound">B</a> <a id="11031" class="Symbol">:</a> <a id="11033" href="plfa.part1.Quantifiers.html#11019" class="Bound">A</a> <a id="11035" class="Symbol">→</a> <a id="11037" class="PrimitiveType">Set</a><a id="11040" class="Symbol">}</a> <a id="11042" class="Symbol">{</a><a id="11043" href="plfa.part1.Quantifiers.html#11043" class="Bound">C</a> <a id="11045" class="Symbol">:</a> <a id="11047" class="PrimitiveType">Set</a><a id="11050" class="Symbol">}</a>
  <a id="11054" class="Symbol">→</a> <a id="11056" class="Symbol">(∀</a> <a id="11059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11059" class="Bound">x</a> <a id="11061" class="Symbol">→</a> <a id="11063" href="plfa.part1.Quantifiers.html#11029" class="Bound">B</a> <a id="11065" href="plfa.part1.Quantifiers.html#11059" class="Bound">x</a> <a id="11067" class="Symbol">→</a> <a id="11069" href="plfa.part1.Quantifiers.html#11043" class="Bound">C</a><a id="11070" class="Symbol">)</a>
  <a id="11074" class="Symbol">→</a> <a id="11076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃[</a> <a id="11079" href="plfa.part1.Quantifiers.html#11079" class="Bound">x</a> <a id="11081" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="11083" href="plfa.part1.Quantifiers.html#11029" class="Bound">B</a> <a id="11085" href="plfa.part1.Quantifiers.html#11079" class="Bound">x</a>
    <a id="11091" class="Comment">---------------</a>
  <a id="11109" class="Symbol">→</a> <a id="11111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11043" class="Bound">C</a>
<a id="11113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11007" class="Function">∃-elim</a> <a id="11120" href="plfa.part1.Quantifiers.html#11120" class="Bound">f</a> <a id="11122" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="11124" href="plfa.part1.Quantifiers.html#11124" class="Bound">x</a> <a id="11126" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="11128" href="plfa.part1.Quantifiers.html#11128" class="Bound">y</a> <a id="11130" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="11132" class="Symbol">=</a> <a id="11134" href="plfa.part1.Quantifiers.html#11120" class="Bound">f</a> <a id="11136" href="plfa.part1.Quantifiers.html#11124" class="Bound">x</a> <a id="11138" href="plfa.part1.Quantifiers.html#11128" class="Bound">y</a>
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

{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="11834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11834" class="Function">∀∃-currying</a> <a id="11846" class="Symbol">:</a> <a id="11848" class="Symbol">∀</a> <a id="11850" class="Symbol">{</a><a id="11851" href="plfa.part1.Quantifiers.html#11851" class="Bound">A</a> <a id="11853" class="Symbol">:</a> <a id="11855" class="PrimitiveType">Set</a><a id="11858" class="Symbol">}</a> <a id="11860" class="Symbol">{</a><a id="11861" href="plfa.part1.Quantifiers.html#11861" class="Bound">B</a> <a id="11863" class="Symbol">:</a> <a id="11865" href="plfa.part1.Quantifiers.html#11851" class="Bound">A</a> <a id="11867" class="Symbol">→</a> <a id="11869" class="PrimitiveType">Set</a><a id="11872" class="Symbol">}</a> <a id="11874" class="Symbol">{</a><a id="11875" href="plfa.part1.Quantifiers.html#11875" class="Bound">C</a> <a id="11877" class="Symbol">:</a> <a id="11879" class="PrimitiveType">Set</a><a id="11882" class="Symbol">}</a>
  <a id="11886" class="Symbol">→</a> <a id="11888" class="Symbol">(∀</a> <a id="11891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11891" class="Bound">x</a> <a id="11893" class="Symbol">→</a> <a id="11895" href="plfa.part1.Quantifiers.html#11861" class="Bound">B</a> <a id="11897" href="plfa.part1.Quantifiers.html#11891" class="Bound">x</a> <a id="11899" class="Symbol">→</a> <a id="11901" href="plfa.part1.Quantifiers.html#11875" class="Bound">C</a><a id="11902" class="Symbol">)</a> <a id="11904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="11906" class="Symbol">(</a><a id="11907" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="11910" href="plfa.part1.Quantifiers.html#11910" class="Bound">x</a> <a id="11912" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="11914" href="plfa.part1.Quantifiers.html#11861" class="Bound">B</a> <a id="11916" href="plfa.part1.Quantifiers.html#11910" class="Bound">x</a> <a id="11918" class="Symbol">→</a> <a id="11920" href="plfa.part1.Quantifiers.html#11875" class="Bound">C</a><a id="11921" class="Symbol">)</a>
<a id="11923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11834" class="Function">∀∃-currying</a> <a id="11935" class="Symbol">=</a>
  <a id="11939" class="Keyword">record</a>
    <a id="11950" class="Symbol">{</a> <a id="11952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="11960" class="Symbol">=</a>  <a id="11963" class="Symbol">λ{</a> <a id="11966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11966" class="Bound">f</a> <a id="11968" class="Symbol">→</a> <a id="11970" class="Symbol">λ{</a> <a id="11973" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="11975" href="plfa.part1.Quantifiers.html#11975" class="Bound">x</a> <a id="11977" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="11979" href="plfa.part1.Quantifiers.html#11979" class="Bound">y</a> <a id="11981" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="11983" class="Symbol">→</a> <a id="11985" href="plfa.part1.Quantifiers.html#11966" class="Bound">f</a> <a id="11987" href="plfa.part1.Quantifiers.html#11975" class="Bound">x</a> <a id="11989" href="plfa.part1.Quantifiers.html#11979" class="Bound">y</a> <a id="11991" class="Symbol">}}</a>
    <a id="11998" class="Symbol">;</a> <a id="12000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="12008" class="Symbol">=</a>  <a id="12011" class="Symbol">λ{</a> <a id="12014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12014" class="Bound">g</a> <a id="12016" class="Symbol">→</a> <a id="12018" class="Symbol">λ{</a> <a id="12021" href="plfa.part1.Quantifiers.html#12021" class="Bound">x</a> <a id="12023" class="Symbol">→</a> <a id="12025" class="Symbol">λ{</a> <a id="12028" href="plfa.part1.Quantifiers.html#12028" class="Bound">y</a> <a id="12030" class="Symbol">→</a> <a id="12032" href="plfa.part1.Quantifiers.html#12014" class="Bound">g</a> <a id="12034" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="12036" href="plfa.part1.Quantifiers.html#12021" class="Bound">x</a> <a id="12038" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="12040" href="plfa.part1.Quantifiers.html#12028" class="Bound">y</a> <a id="12042" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="12044" class="Symbol">}}}</a>
    <a id="12052" class="Symbol">;</a> <a id="12054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="12062" class="Symbol">=</a>  <a id="12065" class="Symbol">λ{</a> <a id="12068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12068" class="Bound">f</a> <a id="12070" class="Symbol">→</a> <a id="12072" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12077" class="Symbol">}</a>
    <a id="12083" class="Symbol">;</a> <a id="12085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="12093" class="Symbol">=</a>  <a id="12096" class="Symbol">λ{</a> <a id="12099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12099" class="Bound">g</a> <a id="12101" class="Symbol">→</a> <a id="12103" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="12118" class="Symbol">λ{</a> <a id="12121" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="12123" href="plfa.part1.Quantifiers.html#12123" class="Bound">x</a> <a id="12125" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="12127" href="plfa.part1.Quantifiers.html#12127" class="Bound">y</a> <a id="12129" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="12131" class="Symbol">→</a> <a id="12133" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12138" class="Symbol">}}</a>
    <a id="12145" class="Symbol">}</a>
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

{% raw %}<pre class="Agda"><a id="12661" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="12673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12673" class="Postulate">∃-distrib-⊎</a> <a id="12685" class="Symbol">:</a> <a id="12687" class="Symbol">∀</a> <a id="12689" class="Symbol">{</a><a id="12690" href="plfa.part1.Quantifiers.html#12690" class="Bound">A</a> <a id="12692" class="Symbol">:</a> <a id="12694" class="PrimitiveType">Set</a><a id="12697" class="Symbol">}</a> <a id="12699" class="Symbol">{</a><a id="12700" href="plfa.part1.Quantifiers.html#12700" class="Bound">B</a> <a id="12702" href="plfa.part1.Quantifiers.html#12702" class="Bound">C</a> <a id="12704" class="Symbol">:</a> <a id="12706" href="plfa.part1.Quantifiers.html#12690" class="Bound">A</a> <a id="12708" class="Symbol">→</a> <a id="12710" class="PrimitiveType">Set</a><a id="12713" class="Symbol">}</a> <a id="12715" class="Symbol">→</a>
    <a id="12721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃[</a> <a id="12724" href="plfa.part1.Quantifiers.html#12724" class="Bound">x</a> <a id="12726" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="12728" class="Symbol">(</a><a id="12729" href="plfa.part1.Quantifiers.html#12700" class="Bound">B</a> <a id="12731" href="plfa.part1.Quantifiers.html#12724" class="Bound">x</a> <a id="12733" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12735" href="plfa.part1.Quantifiers.html#12702" class="Bound">C</a> <a id="12737" href="plfa.part1.Quantifiers.html#12724" class="Bound">x</a><a id="12738" class="Symbol">)</a> <a id="12740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="12742" class="Symbol">(</a><a id="12743" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="12746" href="plfa.part1.Quantifiers.html#12746" class="Bound">x</a> <a id="12748" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="12750" href="plfa.part1.Quantifiers.html#12700" class="Bound">B</a> <a id="12752" href="plfa.part1.Quantifiers.html#12746" class="Bound">x</a><a id="12753" class="Symbol">)</a> <a id="12755" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12757" class="Symbol">(</a><a id="12758" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="12761" href="plfa.part1.Quantifiers.html#12761" class="Bound">x</a> <a id="12763" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="12765" href="plfa.part1.Quantifiers.html#12702" class="Bound">C</a> <a id="12767" href="plfa.part1.Quantifiers.html#12761" class="Bound">x</a><a id="12768" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃×-implies-×∃` (practice)
{:/}

#### 练习 `∃×-implies-×∃`（实践）

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明合取的存在命题蕴涵了存在命题的合取：

{% raw %}<pre class="Agda"><a id="12987" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="12999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#12999" class="Postulate">∃×-implies-×∃</a> <a id="13013" class="Symbol">:</a> <a id="13015" class="Symbol">∀</a> <a id="13017" class="Symbol">{</a><a id="13018" href="plfa.part1.Quantifiers.html#13018" class="Bound">A</a> <a id="13020" class="Symbol">:</a> <a id="13022" class="PrimitiveType">Set</a><a id="13025" class="Symbol">}</a> <a id="13027" class="Symbol">{</a><a id="13028" href="plfa.part1.Quantifiers.html#13028" class="Bound">B</a> <a id="13030" href="plfa.part1.Quantifiers.html#13030" class="Bound">C</a> <a id="13032" class="Symbol">:</a> <a id="13034" href="plfa.part1.Quantifiers.html#13018" class="Bound">A</a> <a id="13036" class="Symbol">→</a> <a id="13038" class="PrimitiveType">Set</a><a id="13041" class="Symbol">}</a> <a id="13043" class="Symbol">→</a>
    <a id="13049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃[</a> <a id="13052" href="plfa.part1.Quantifiers.html#13052" class="Bound">x</a> <a id="13054" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="13056" class="Symbol">(</a><a id="13057" href="plfa.part1.Quantifiers.html#13028" class="Bound">B</a> <a id="13059" href="plfa.part1.Quantifiers.html#13052" class="Bound">x</a> <a id="13061" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="13063" href="plfa.part1.Quantifiers.html#13030" class="Bound">C</a> <a id="13065" href="plfa.part1.Quantifiers.html#13052" class="Bound">x</a><a id="13066" class="Symbol">)</a> <a id="13068" class="Symbol">→</a> <a id="13070" class="Symbol">(</a><a id="13071" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="13074" href="plfa.part1.Quantifiers.html#13074" class="Bound">x</a> <a id="13076" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="13078" href="plfa.part1.Quantifiers.html#13028" class="Bound">B</a> <a id="13080" href="plfa.part1.Quantifiers.html#13074" class="Bound">x</a><a id="13081" class="Symbol">)</a> <a id="13083" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="13085" class="Symbol">(</a><a id="13086" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="13089" href="plfa.part1.Quantifiers.html#13089" class="Bound">x</a> <a id="13091" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="13093" href="plfa.part1.Quantifiers.html#13030" class="Bound">C</a> <a id="13095" href="plfa.part1.Quantifiers.html#13089" class="Bound">x</a><a id="13096" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="13729" class="Keyword">data</a> <a id="even"></a><a id="13734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13734" class="Datatype">even</a> <a id="13739" class="Symbol">:</a> <a id="13741" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13743" class="Symbol">→</a> <a id="13745" class="PrimitiveType">Set</a>
<a id="13749" class="Keyword">data</a> <a id="odd"></a><a id="13754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13754" class="Datatype">odd</a>  <a id="13759" class="Symbol">:</a> <a id="13761" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13763" class="Symbol">→</a> <a id="13765" class="PrimitiveType">Set</a>

<a id="13770" class="Keyword">data</a> <a id="13775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13734" class="Datatype">even</a> <a id="13780" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13789" class="InductiveConstructor">even-zero</a> <a id="13799" class="Symbol">:</a> <a id="13801" href="plfa.part1.Quantifiers.html#13734" class="Datatype">even</a> <a id="13806" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="13814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13814" class="InductiveConstructor">even-suc</a> <a id="13823" class="Symbol">:</a> <a id="13825" class="Symbol">∀</a> <a id="13827" class="Symbol">{</a><a id="13828" href="plfa.part1.Quantifiers.html#13828" class="Bound">n</a> <a id="13830" class="Symbol">:</a> <a id="13832" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13833" class="Symbol">}</a>
    <a id="13839" class="Symbol">→</a> <a id="13841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13754" class="Datatype">odd</a> <a id="13845" href="plfa.part1.Quantifiers.html#13828" class="Bound">n</a>
      <a id="13853" class="Comment">------------</a>
    <a id="13870" class="Symbol">→</a> <a id="13872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13734" class="Datatype">even</a> <a id="13877" class="Symbol">(</a><a id="13878" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13882" href="plfa.part1.Quantifiers.html#13828" class="Bound">n</a><a id="13883" class="Symbol">)</a>

<a id="13886" class="Keyword">data</a> <a id="13891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13754" class="Datatype">odd</a> <a id="13895" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="13903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13903" class="InductiveConstructor">odd-suc</a> <a id="13911" class="Symbol">:</a> <a id="13913" class="Symbol">∀</a> <a id="13915" class="Symbol">{</a><a id="13916" href="plfa.part1.Quantifiers.html#13916" class="Bound">n</a> <a id="13918" class="Symbol">:</a> <a id="13920" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13921" class="Symbol">}</a>
    <a id="13927" class="Symbol">→</a> <a id="13929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13734" class="Datatype">even</a> <a id="13934" href="plfa.part1.Quantifiers.html#13916" class="Bound">n</a>
      <a id="13942" class="Comment">-----------</a>
    <a id="13958" class="Symbol">→</a> <a id="13960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13754" class="Datatype">odd</a> <a id="13964" class="Symbol">(</a><a id="13965" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13969" href="plfa.part1.Quantifiers.html#13916" class="Bound">n</a><a id="13970" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="14965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14965" class="Function">even-∃</a> <a id="14972" class="Symbol">:</a> <a id="14974" class="Symbol">∀</a> <a id="14976" class="Symbol">{</a><a id="14977" href="plfa.part1.Quantifiers.html#14977" class="Bound">n</a> <a id="14979" class="Symbol">:</a> <a id="14981" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14982" class="Symbol">}</a> <a id="14984" class="Symbol">→</a> <a id="14986" href="plfa.part1.Quantifiers.html#13734" class="Datatype">even</a> <a id="14991" href="plfa.part1.Quantifiers.html#14977" class="Bound">n</a> <a id="14993" class="Symbol">→</a> <a id="14995" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="14998" href="plfa.part1.Quantifiers.html#14998" class="Bound">m</a> <a id="15000" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="15002" class="Symbol">(</a>    <a id="15007" href="plfa.part1.Quantifiers.html#14998" class="Bound">m</a> <a id="15009" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="15011" class="Number">2</a> <a id="15013" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15015" href="plfa.part1.Quantifiers.html#14977" class="Bound">n</a><a id="15016" class="Symbol">)</a>
<a id="odd-∃"></a><a id="15018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15018" class="Function">odd-∃</a>  <a id="15025" class="Symbol">:</a> <a id="15027" class="Symbol">∀</a> <a id="15029" class="Symbol">{</a><a id="15030" href="plfa.part1.Quantifiers.html#15030" class="Bound">n</a> <a id="15032" class="Symbol">:</a> <a id="15034" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15035" class="Symbol">}</a> <a id="15037" class="Symbol">→</a>  <a id="15040" href="plfa.part1.Quantifiers.html#13754" class="Datatype">odd</a> <a id="15044" href="plfa.part1.Quantifiers.html#15030" class="Bound">n</a> <a id="15046" class="Symbol">→</a> <a id="15048" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="15051" href="plfa.part1.Quantifiers.html#15051" class="Bound">m</a> <a id="15053" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="15055" class="Symbol">(</a><a id="15056" class="Number">1</a> <a id="15058" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="15060" href="plfa.part1.Quantifiers.html#15051" class="Bound">m</a> <a id="15062" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="15064" class="Number">2</a> <a id="15066" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15068" href="plfa.part1.Quantifiers.html#15030" class="Bound">n</a><a id="15069" class="Symbol">)</a>

<a id="15072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14965" class="Function">even-∃</a> <a id="15079" href="plfa.part1.Quantifiers.html#13789" class="InductiveConstructor">even-zero</a>                       <a id="15111" class="Symbol">=</a>  <a id="15114" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="15116" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="15121" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="15123" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15128" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>
<a id="15130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14965" class="Function">even-∃</a> <a id="15137" class="Symbol">(</a><a id="15138" href="plfa.part1.Quantifiers.html#13814" class="InductiveConstructor">even-suc</a> <a id="15147" href="plfa.part1.Quantifiers.html#15147" class="Bound">o</a><a id="15148" class="Symbol">)</a> <a id="15150" class="Keyword">with</a> <a id="15155" href="plfa.part1.Quantifiers.html#15018" class="Function">odd-∃</a> <a id="15161" href="plfa.part1.Quantifiers.html#15147" class="Bound">o</a>
<a id="15163" class="Symbol">...</a>                    <a id="15186" class="Symbol">|</a> <a id="15188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7095" class="InductiveConstructor Operator">⟨</a> <a id="15190" href="plfa.part1.Quantifiers.html#15190" class="Bound">m</a> <a id="15192" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="15194" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15199" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>  <a id="15202" class="Symbol">=</a>  <a id="15205" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="15207" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15211" href="plfa.part1.Quantifiers.html#15190" class="Bound">m</a> <a id="15213" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="15215" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15220" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>

<a id="15223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#15018" class="Function">odd-∃</a>  <a id="15230" class="Symbol">(</a><a id="15231" href="plfa.part1.Quantifiers.html#13903" class="InductiveConstructor">odd-suc</a> <a id="15239" href="plfa.part1.Quantifiers.html#15239" class="Bound">e</a><a id="15240" class="Symbol">)</a>  <a id="15243" class="Keyword">with</a> <a id="15248" href="plfa.part1.Quantifiers.html#14965" class="Function">even-∃</a> <a id="15255" href="plfa.part1.Quantifiers.html#15239" class="Bound">e</a>
<a id="15257" class="Symbol">...</a>                    <a id="15280" class="Symbol">|</a> <a id="15282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7095" class="InductiveConstructor Operator">⟨</a> <a id="15284" href="plfa.part1.Quantifiers.html#15284" class="Bound">m</a> <a id="15286" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="15288" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15293" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>  <a id="15296" class="Symbol">=</a>  <a id="15299" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="15301" href="plfa.part1.Quantifiers.html#15284" class="Bound">m</a> <a id="15303" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="15305" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="15310" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>
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

{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="16862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16862" class="Function">∃-even</a> <a id="16869" class="Symbol">:</a> <a id="16871" class="Symbol">∀</a> <a id="16873" class="Symbol">{</a><a id="16874" href="plfa.part1.Quantifiers.html#16874" class="Bound">n</a> <a id="16876" class="Symbol">:</a> <a id="16878" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16879" class="Symbol">}</a> <a id="16881" class="Symbol">→</a> <a id="16883" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="16886" href="plfa.part1.Quantifiers.html#16886" class="Bound">m</a> <a id="16888" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="16890" class="Symbol">(</a>    <a id="16895" href="plfa.part1.Quantifiers.html#16886" class="Bound">m</a> <a id="16897" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16899" class="Number">2</a> <a id="16901" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16903" href="plfa.part1.Quantifiers.html#16874" class="Bound">n</a><a id="16904" class="Symbol">)</a> <a id="16906" class="Symbol">→</a> <a id="16908" href="plfa.part1.Quantifiers.html#13734" class="Datatype">even</a> <a id="16913" href="plfa.part1.Quantifiers.html#16874" class="Bound">n</a>
<a id="∃-odd"></a><a id="16915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16915" class="Function">∃-odd</a>  <a id="16922" class="Symbol">:</a> <a id="16924" class="Symbol">∀</a> <a id="16926" class="Symbol">{</a><a id="16927" href="plfa.part1.Quantifiers.html#16927" class="Bound">n</a> <a id="16929" class="Symbol">:</a> <a id="16931" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16932" class="Symbol">}</a> <a id="16934" class="Symbol">→</a> <a id="16936" href="plfa.part1.Quantifiers.html#10442" class="Function">∃[</a> <a id="16939" href="plfa.part1.Quantifiers.html#16939" class="Bound">m</a> <a id="16941" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="16943" class="Symbol">(</a><a id="16944" class="Number">1</a> <a id="16946" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16948" href="plfa.part1.Quantifiers.html#16939" class="Bound">m</a> <a id="16950" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16952" class="Number">2</a> <a id="16954" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16956" href="plfa.part1.Quantifiers.html#16927" class="Bound">n</a><a id="16957" class="Symbol">)</a> <a id="16959" class="Symbol">→</a>  <a id="16962" href="plfa.part1.Quantifiers.html#13754" class="Datatype">odd</a> <a id="16966" href="plfa.part1.Quantifiers.html#16927" class="Bound">n</a>

<a id="16969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16862" class="Function">∃-even</a> <a id="16976" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a>  <a id="16979" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16984" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="16986" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16991" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>  <a id="16994" class="Symbol">=</a>  <a id="16997" href="plfa.part1.Quantifiers.html#13789" class="InductiveConstructor">even-zero</a>
<a id="17007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16862" class="Function">∃-even</a> <a id="17014" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="17016" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="17020" href="plfa.part1.Quantifiers.html#17020" class="Bound">m</a> <a id="17022" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="17024" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17029" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>  <a id="17032" class="Symbol">=</a>  <a id="17035" href="plfa.part1.Quantifiers.html#13814" class="InductiveConstructor">even-suc</a> <a id="17044" class="Symbol">(</a><a id="17045" href="plfa.part1.Quantifiers.html#16915" class="Function">∃-odd</a> <a id="17051" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="17053" href="plfa.part1.Quantifiers.html#17020" class="Bound">m</a> <a id="17055" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="17057" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17062" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a><a id="17063" class="Symbol">)</a>

<a id="17066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#16915" class="Function">∃-odd</a>  <a id="17073" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a>     <a id="17079" href="plfa.part1.Quantifiers.html#17079" class="Bound">m</a> <a id="17081" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="17083" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17088" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a>  <a id="17091" class="Symbol">=</a>  <a id="17094" href="plfa.part1.Quantifiers.html#13903" class="InductiveConstructor">odd-suc</a> <a id="17102" class="Symbol">(</a><a id="17103" href="plfa.part1.Quantifiers.html#16862" class="Function">∃-even</a> <a id="17110" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="17112" href="plfa.part1.Quantifiers.html#17079" class="Bound">m</a> <a id="17114" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="17116" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="17121" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a><a id="17122" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="18707" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18744" class="Comment">-- 请将代码写在此处。</a>
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
{% raw %}<pre class="Agda"><a id="18996" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="19033" class="Comment">-- 请将代码写在此处。</a>
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

{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="19527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19527" class="Function">¬∃≃∀¬</a> <a id="19533" class="Symbol">:</a> <a id="19535" class="Symbol">∀</a> <a id="19537" class="Symbol">{</a><a id="19538" href="plfa.part1.Quantifiers.html#19538" class="Bound">A</a> <a id="19540" class="Symbol">:</a> <a id="19542" class="PrimitiveType">Set</a><a id="19545" class="Symbol">}</a> <a id="19547" class="Symbol">{</a><a id="19548" href="plfa.part1.Quantifiers.html#19548" class="Bound">B</a> <a id="19550" class="Symbol">:</a> <a id="19552" href="plfa.part1.Quantifiers.html#19538" class="Bound">A</a> <a id="19554" class="Symbol">→</a> <a id="19556" class="PrimitiveType">Set</a><a id="19559" class="Symbol">}</a>
  <a id="19563" class="Symbol">→</a> <a id="19565" class="Symbol">(</a><a id="19566" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="19568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃[</a> <a id="19571" href="plfa.part1.Quantifiers.html#19571" class="Bound">x</a> <a id="19573" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="19575" href="plfa.part1.Quantifiers.html#19548" class="Bound">B</a> <a id="19577" href="plfa.part1.Quantifiers.html#19571" class="Bound">x</a><a id="19578" class="Symbol">)</a> <a id="19580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="19582" class="Symbol">∀</a> <a id="19584" href="plfa.part1.Quantifiers.html#19584" class="Bound">x</a> <a id="19586" class="Symbol">→</a> <a id="19588" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="19590" href="plfa.part1.Quantifiers.html#19548" class="Bound">B</a> <a id="19592" href="plfa.part1.Quantifiers.html#19584" class="Bound">x</a>
<a id="19594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19527" class="Function">¬∃≃∀¬</a> <a id="19600" class="Symbol">=</a>
  <a id="19604" class="Keyword">record</a>
    <a id="19615" class="Symbol">{</a> <a id="19617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5889" class="Field">to</a>      <a id="19625" class="Symbol">=</a>  <a id="19628" class="Symbol">λ{</a> <a id="19631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19631" class="Bound">¬∃xy</a> <a id="19636" href="plfa.part1.Quantifiers.html#19636" class="Bound">x</a> <a id="19638" href="plfa.part1.Quantifiers.html#19638" class="Bound">y</a> <a id="19640" class="Symbol">→</a> <a id="19642" href="plfa.part1.Quantifiers.html#19631" class="Bound">¬∃xy</a> <a id="19647" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="19649" href="plfa.part1.Quantifiers.html#19636" class="Bound">x</a> <a id="19651" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="19653" href="plfa.part1.Quantifiers.html#19638" class="Bound">y</a> <a id="19655" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="19657" class="Symbol">}</a>
    <a id="19663" class="Symbol">;</a> <a id="19665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5906" class="Field">from</a>    <a id="19673" class="Symbol">=</a>  <a id="19676" class="Symbol">λ{</a> <a id="19679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19679" class="Bound">∀¬xy</a> <a id="19684" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="19686" href="plfa.part1.Quantifiers.html#19686" class="Bound">x</a> <a id="19688" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="19690" href="plfa.part1.Quantifiers.html#19690" class="Bound">y</a> <a id="19692" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="19694" class="Symbol">→</a> <a id="19696" href="plfa.part1.Quantifiers.html#19679" class="Bound">∀¬xy</a> <a id="19701" href="plfa.part1.Quantifiers.html#19686" class="Bound">x</a> <a id="19703" href="plfa.part1.Quantifiers.html#19690" class="Bound">y</a> <a id="19705" class="Symbol">}</a>
    <a id="19711" class="Symbol">;</a> <a id="19713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5923" class="Field">from∘to</a> <a id="19721" class="Symbol">=</a>  <a id="19724" class="Symbol">λ{</a> <a id="19727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19727" class="Bound">¬∃xy</a> <a id="19732" class="Symbol">→</a> <a id="19734" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a> <a id="19749" class="Symbol">λ{</a> <a id="19752" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟨</a> <a id="19754" href="plfa.part1.Quantifiers.html#19754" class="Bound">x</a> <a id="19756" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">,</a> <a id="19758" href="plfa.part1.Quantifiers.html#19758" class="Bound">y</a> <a id="19760" href="plfa.part1.Quantifiers.html#7095" class="InductiveConstructor Operator">⟩</a> <a id="19762" class="Symbol">→</a> <a id="19764" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19769" class="Symbol">}</a> <a id="19771" class="Symbol">}</a>
    <a id="19777" class="Symbol">;</a> <a id="19779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5965" class="Field">to∘from</a> <a id="19787" class="Symbol">=</a>  <a id="19790" class="Symbol">λ{</a> <a id="19793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#19793" class="Bound">∀¬xy</a> <a id="19798" class="Symbol">→</a> <a id="19800" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19805" class="Symbol">}</a>
    <a id="19811" class="Symbol">}</a>
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

{% raw %}<pre class="Agda"><a id="21128" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="21140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#21140" class="Postulate">∃¬-implies-¬∀</a> <a id="21154" class="Symbol">:</a> <a id="21156" class="Symbol">∀</a> <a id="21158" class="Symbol">{</a><a id="21159" href="plfa.part1.Quantifiers.html#21159" class="Bound">A</a> <a id="21161" class="Symbol">:</a> <a id="21163" class="PrimitiveType">Set</a><a id="21166" class="Symbol">}</a> <a id="21168" class="Symbol">{</a><a id="21169" href="plfa.part1.Quantifiers.html#21169" class="Bound">B</a> <a id="21171" class="Symbol">:</a> <a id="21173" href="plfa.part1.Quantifiers.html#21159" class="Bound">A</a> <a id="21175" class="Symbol">→</a> <a id="21177" class="PrimitiveType">Set</a><a id="21180" class="Symbol">}</a>
    <a id="21186" class="Symbol">→</a> <a id="21188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10442" class="Function">∃[</a> <a id="21191" href="plfa.part1.Quantifiers.html#21191" class="Bound">x</a> <a id="21193" href="plfa.part1.Quantifiers.html#10442" class="Function">]</a> <a id="21195" class="Symbol">(</a><a id="21196" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="21198" href="plfa.part1.Quantifiers.html#21169" class="Bound">B</a> <a id="21200" href="plfa.part1.Quantifiers.html#21191" class="Bound">x</a><a id="21201" class="Symbol">)</a>
      <a id="21209" class="Comment">--------------</a>
    <a id="21228" class="Symbol">→</a> <a id="21230" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="21232" class="Symbol">(∀</a> <a id="21235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#21235" class="Bound">x</a> <a id="21237" class="Symbol">→</a> <a id="21239" href="plfa.part1.Quantifiers.html#21169" class="Bound">B</a> <a id="21241" href="plfa.part1.Quantifiers.html#21235" class="Bound">x</a><a id="21242" class="Symbol">)</a>
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

{::comment}
{% raw %}<pre class="Agda"><a id="22420" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="22457" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章中相似的定义：

{% raw %}<pre class="Agda"><a id="22646" class="Keyword">import</a> <a id="22653" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="22666" class="Keyword">using</a> <a id="22672" class="Symbol">(</a><a id="22673" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="22674" class="Symbol">;</a> <a id="22676" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="22679" class="Symbol">;</a> <a id="22681" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="22682" class="Symbol">;</a> <a id="22684" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="22692" class="Symbol">;</a> <a id="22694" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="22702" class="Symbol">)</a>
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
