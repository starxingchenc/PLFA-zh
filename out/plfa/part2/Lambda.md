---
src       : "src/plfa/part2/Lambda.lagda.md"
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

{% raw %}<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}" class="Module">plfa.part2.Lambda</a> <a id="176" class="Keyword">where</a>
</pre>{% endraw %}
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties]({{ site.baseurl }}/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
intrinsically-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables and extrinsically-typed terms,
partly because names are easier than indices to read,
and partly because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

{% raw %}<pre class="Agda"><a id="2304" class="Keyword">open</a> <a id="2309" class="Keyword">import</a> <a id="2316" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2354" class="Keyword">using</a> <a id="2360" class="Symbol">(</a><a id="2361" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2364" class="Symbol">;</a> <a id="2366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2369" class="Symbol">;</a> <a id="2371" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2375" class="Symbol">)</a>
<a id="2377" class="Keyword">open</a> <a id="2382" class="Keyword">import</a> <a id="2389" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2401" class="Keyword">using</a> <a id="2407" class="Symbol">(</a><a id="2408" href="Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2414" class="Symbol">;</a> <a id="2416" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2419" class="Symbol">)</a>
<a id="2421" class="Keyword">open</a> <a id="2426" class="Keyword">import</a> <a id="2433" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2442" class="Keyword">using</a> <a id="2448" class="Symbol">(</a><a id="2449" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2450" class="Symbol">;</a> <a id="2452" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2456" class="Symbol">;</a> <a id="2458" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2461" class="Symbol">)</a>
<a id="2463" class="Keyword">open</a> <a id="2468" class="Keyword">import</a> <a id="2475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2486" class="Keyword">using</a> <a id="2492" class="Symbol">(</a><a id="2493" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2494" class="Symbol">;</a> <a id="2496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2502" class="Symbol">)</a>
<a id="2504" class="Keyword">open</a> <a id="2509" class="Keyword">import</a> <a id="2516" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2533" class="Keyword">using</a> <a id="2539" class="Symbol">(</a><a id="2540" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2543" class="Symbol">;</a> <a id="2545" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2548" class="Symbol">;</a> <a id="2550" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2552" class="Symbol">;</a> <a id="2554" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2556" class="Symbol">)</a>
<a id="2558" class="Keyword">open</a> <a id="2563" class="Keyword">import</a> <a id="2570" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2580" class="Keyword">using</a> <a id="2586" class="Symbol">(</a><a id="2587" href="Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2591" class="Symbol">;</a> <a id="2593" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2596" class="Symbol">;</a> <a id="2598" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2600" class="Symbol">)</a>
</pre>{% endraw %}
## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc M ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

And here it is formalised in Agda:
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3697" class="Function">Id</a> <a id="3700" class="Symbol">:</a> <a id="3702" class="PrimitiveType">Set</a>
<a id="3706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3697" class="Function">Id</a> <a id="3709" class="Symbol">=</a> <a id="3711" href="Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3719" class="Keyword">infix</a>  <a id="3726" class="Number">5</a>  <a id="3729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3734" class="Keyword">infix</a>  <a id="3741" class="Number">5</a>  <a id="3744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3749" class="Keyword">infixl</a> <a id="3756" class="Number">7</a>  <a id="3759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34338" class="InductiveConstructor Operator">_·_</a>
<a id="3763" class="Keyword">infix</a>  <a id="3770" class="Number">8</a>  <a id="3773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc_</a>
<a id="3779" class="Keyword">infix</a>  <a id="3786" class="Number">9</a>  <a id="3789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`_</a>

<a id="3793" class="Keyword">data</a> <a id="Term"></a><a id="3798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3798" class="Datatype">Term</a> <a id="3803" class="Symbol">:</a> <a id="3805" class="PrimitiveType">Set</a> <a id="3809" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`_</a>                      <a id="3841" class="Symbol">:</a>  <a id="3844" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="3847" class="Symbol">→</a> <a id="3849" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3880" class="Symbol">:</a>  <a id="3883" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="3886" class="Symbol">→</a> <a id="3888" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="3893" class="Symbol">→</a> <a id="3895" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">_·_</a>                     <a id="3926" class="Symbol">:</a>  <a id="3929" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="3934" class="Symbol">→</a> <a id="3936" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="3941" class="Symbol">→</a> <a id="3943" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3950" class="InductiveConstructor">`zero</a>                   <a id="3974" class="Symbol">:</a>  <a id="3977" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc_</a>                   <a id="4008" class="Symbol">:</a>  <a id="4011" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="4016" class="Symbol">→</a> <a id="4018" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="4025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="4049" class="Symbol">:</a>  <a id="4052" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="4057" class="Symbol">→</a> <a id="4059" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="4064" class="Symbol">→</a> <a id="4066" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="4069" class="Symbol">→</a> <a id="4071" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="4076" class="Symbol">→</a> <a id="4078" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4109" class="Symbol">:</a>  <a id="4112" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="4115" class="Symbol">→</a> <a id="4117" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="4122" class="Symbol">→</a> <a id="4124" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4526" class="Function">two</a> <a id="4530" class="Symbol">:</a> <a id="4532" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="4537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4526" class="Function">two</a> <a id="4541" class="Symbol">=</a> <a id="4543" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="4548" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="4553" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4560" class="Function">plus</a> <a id="4565" class="Symbol">:</a> <a id="4567" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="4572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4560" class="Function">plus</a> <a id="4577" class="Symbol">=</a> <a id="4579" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">μ</a> <a id="4581" class="String">&quot;+&quot;</a> <a id="4585" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="4587" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="4589" class="String">&quot;m&quot;</a> <a id="4593" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="4595" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="4597" class="String">&quot;n&quot;</a> <a id="4601" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
         <a id="4612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="4617" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="4619" class="String">&quot;m&quot;</a>
           <a id="4634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="4641" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="4643" class="String">&quot;n&quot;</a>
           <a id="4658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">|suc</a> <a id="4663" class="String">&quot;m&quot;</a> <a id="4667" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="4669" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="4674" class="Symbol">(</a><a id="4675" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="4677" class="String">&quot;+&quot;</a> <a id="4681" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="4683" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="4685" class="String">&quot;m&quot;</a> <a id="4689" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="4691" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="4693" class="String">&quot;n&quot;</a><a id="4696" class="Symbol">)</a> <a id="4698" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
</pre>{% endraw %}The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals]({{ site.baseurl }}/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5775" class="Function">twoᶜ</a> <a id="5780" class="Symbol">:</a> <a id="5782" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="5787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5775" class="Function">twoᶜ</a> <a id="5792" class="Symbol">=</a>  <a id="5795" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5797" class="String">&quot;s&quot;</a> <a id="5801" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5803" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5805" class="String">&quot;z&quot;</a> <a id="5809" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5811" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5813" class="String">&quot;s&quot;</a> <a id="5817" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5819" class="Symbol">(</a><a id="5820" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5822" class="String">&quot;s&quot;</a> <a id="5826" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5828" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5830" class="String">&quot;z&quot;</a><a id="5833" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5836" class="Function">plusᶜ</a> <a id="5842" class="Symbol">:</a> <a id="5844" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="5849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5836" class="Function">plusᶜ</a> <a id="5855" class="Symbol">=</a>  <a id="5858" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5860" class="String">&quot;m&quot;</a> <a id="5864" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5866" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5868" class="String">&quot;n&quot;</a> <a id="5872" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5874" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5876" class="String">&quot;s&quot;</a> <a id="5880" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5882" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5884" class="String">&quot;z&quot;</a> <a id="5888" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
         <a id="5899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="5901" class="String">&quot;m&quot;</a> <a id="5905" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5907" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5909" class="String">&quot;s&quot;</a> <a id="5913" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5915" class="Symbol">(</a><a id="5916" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5918" class="String">&quot;n&quot;</a> <a id="5922" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5924" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5926" class="String">&quot;s&quot;</a> <a id="5930" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="5932" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5934" class="String">&quot;z&quot;</a><a id="5937" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="5945" class="Symbol">:</a> <a id="5947" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="5952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="5957" class="Symbol">=</a> <a id="5959" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="5961" class="String">&quot;n&quot;</a> <a id="5965" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="5967" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="5972" class="Symbol">(</a><a id="5973" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="5975" class="String">&quot;n&quot;</a><a id="5978" class="Symbol">)</a>
</pre>{% endraw %}The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

{% raw %}<pre class="Agda"><a id="6860" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7141" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch) {#primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7385" class="Function Operator">ƛ′_⇒_</a> <a id="7391" class="Symbol">:</a> <a id="7393" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7398" class="Symbol">→</a> <a id="7400" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7405" class="Symbol">→</a> <a id="7407" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="7412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7385" class="Function Operator">ƛ′</a> <a id="7415" class="Symbol">(</a><a id="7416" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="7418" href="plfa.part2.Lambda.html#7418" class="Bound">x</a><a id="7419" class="Symbol">)</a> <a id="7421" href="plfa.part2.Lambda.html#7385" class="Function Operator">⇒</a> <a id="7423" href="plfa.part2.Lambda.html#7423" class="Bound">N</a>  <a id="7426" class="Symbol">=</a>  <a id="7429" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="7431" href="plfa.part2.Lambda.html#7418" class="Bound">x</a> <a id="7433" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="7435" href="plfa.part2.Lambda.html#7423" class="Bound">N</a>
<a id="7437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7385" class="CatchallClause Function Operator">ƛ′</a><a id="7439" class="CatchallClause"> </a><a id="7440" class="CatchallClause Symbol">_</a><a id="7441" class="CatchallClause"> </a><a id="7442" href="plfa.part2.Lambda.html#7385" class="CatchallClause Function Operator">⇒</a><a id="7443" class="CatchallClause"> </a><a id="7444" class="CatchallClause Symbol">_</a>      <a id="7451" class="Symbol">=</a>  <a id="7454" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7461" href="plfa.part2.Lambda.html#7490" class="Postulate">impossible</a>
  <a id="7474" class="Keyword">where</a> <a id="7480" class="Keyword">postulate</a> <a id="7490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7490" class="Postulate">impossible</a> <a id="7501" class="Symbol">:</a> <a id="7503" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7528" class="Symbol">:</a> <a id="7530" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7535" class="Symbol">→</a> <a id="7537" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7542" class="Symbol">→</a> <a id="7544" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7549" class="Symbol">→</a> <a id="7551" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7556" class="Symbol">→</a> <a id="7558" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="7563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="Function Operator">case′</a> <a id="7569" href="plfa.part2.Lambda.html#7569" class="Bound">L</a> <a id="7571" href="plfa.part2.Lambda.html#7506" class="Function Operator">[zero⇒</a> <a id="7578" href="plfa.part2.Lambda.html#7578" class="Bound">M</a> <a id="7580" href="plfa.part2.Lambda.html#7506" class="Function Operator">|suc</a> <a id="7585" class="Symbol">(</a><a id="7586" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="7588" href="plfa.part2.Lambda.html#7588" class="Bound">x</a><a id="7589" class="Symbol">)</a> <a id="7591" href="plfa.part2.Lambda.html#7506" class="Function Operator">⇒</a> <a id="7593" href="plfa.part2.Lambda.html#7593" class="Bound">N</a> <a id="7595" href="plfa.part2.Lambda.html#7506" class="Function Operator">]</a>  <a id="7598" class="Symbol">=</a>  <a id="7601" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="7606" href="plfa.part2.Lambda.html#7569" class="Bound">L</a> <a id="7608" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="7615" href="plfa.part2.Lambda.html#7578" class="Bound">M</a> <a id="7617" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="7622" href="plfa.part2.Lambda.html#7588" class="Bound">x</a> <a id="7624" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="7626" href="plfa.part2.Lambda.html#7593" class="Bound">N</a> <a id="7628" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
<a id="7630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="CatchallClause Function Operator">case′</a><a id="7635" class="CatchallClause"> </a><a id="7636" class="CatchallClause Symbol">_</a><a id="7637" class="CatchallClause"> </a><a id="7638" href="plfa.part2.Lambda.html#7506" class="CatchallClause Function Operator">[zero⇒</a><a id="7644" class="CatchallClause"> </a><a id="7645" class="CatchallClause Symbol">_</a><a id="7646" class="CatchallClause"> </a><a id="7647" href="plfa.part2.Lambda.html#7506" class="CatchallClause Function Operator">|suc</a><a id="7651" class="CatchallClause"> </a><a id="7652" class="CatchallClause Symbol">_</a><a id="7653" class="CatchallClause"> </a><a id="7654" href="plfa.part2.Lambda.html#7506" class="CatchallClause Function Operator">⇒</a><a id="7655" class="CatchallClause"> </a><a id="7656" class="CatchallClause Symbol">_</a><a id="7657" class="CatchallClause"> </a><a id="7658" href="plfa.part2.Lambda.html#7506" class="CatchallClause Function Operator">]</a>      <a id="7665" class="Symbol">=</a>  <a id="7668" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7675" href="plfa.part2.Lambda.html#7704" class="Postulate">impossible</a>
  <a id="7688" class="Keyword">where</a> <a id="7694" class="Keyword">postulate</a> <a id="7704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7704" class="Postulate">impossible</a> <a id="7715" class="Symbol">:</a> <a id="7717" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7720" class="Function Operator">μ′_⇒_</a> <a id="7726" class="Symbol">:</a> <a id="7728" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7733" class="Symbol">→</a> <a id="7735" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="7740" class="Symbol">→</a> <a id="7742" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="7747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7720" class="Function Operator">μ′</a> <a id="7750" class="Symbol">(</a><a id="7751" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="7753" href="plfa.part2.Lambda.html#7753" class="Bound">x</a><a id="7754" class="Symbol">)</a> <a id="7756" href="plfa.part2.Lambda.html#7720" class="Function Operator">⇒</a> <a id="7758" href="plfa.part2.Lambda.html#7758" class="Bound">N</a>  <a id="7761" class="Symbol">=</a>  <a id="7764" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">μ</a> <a id="7766" href="plfa.part2.Lambda.html#7753" class="Bound">x</a> <a id="7768" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="7770" href="plfa.part2.Lambda.html#7758" class="Bound">N</a>
<a id="7772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7720" class="CatchallClause Function Operator">μ′</a><a id="7774" class="CatchallClause"> </a><a id="7775" class="CatchallClause Symbol">_</a><a id="7776" class="CatchallClause"> </a><a id="7777" href="plfa.part2.Lambda.html#7720" class="CatchallClause Function Operator">⇒</a><a id="7778" class="CatchallClause"> </a><a id="7779" class="CatchallClause Symbol">_</a>      <a id="7786" class="Symbol">=</a>  <a id="7789" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7796" href="plfa.part2.Lambda.html#7825" class="Postulate">impossible</a>
  <a id="7809" class="Keyword">where</a> <a id="7815" class="Keyword">postulate</a> <a id="7825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7825" class="Postulate">impossible</a> <a id="7836" class="Symbol">:</a> <a id="7838" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term

    ƛ′ two ⇒ two

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="8474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8474" class="Function">plus′</a> <a id="8480" class="Symbol">:</a> <a id="8482" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8474" class="Function">plus′</a> <a id="8493" class="Symbol">=</a> <a id="8495" href="plfa.part2.Lambda.html#7720" class="Function Operator">μ′</a> <a id="8498" href="plfa.part2.Lambda.html#8605" class="Function">+</a> <a id="8500" href="plfa.part2.Lambda.html#7720" class="Function Operator">⇒</a> <a id="8502" href="plfa.part2.Lambda.html#7385" class="Function Operator">ƛ′</a> <a id="8505" href="plfa.part2.Lambda.html#8619" class="Function">m</a> <a id="8507" href="plfa.part2.Lambda.html#7385" class="Function Operator">⇒</a> <a id="8509" href="plfa.part2.Lambda.html#7385" class="Function Operator">ƛ′</a> <a id="8512" href="plfa.part2.Lambda.html#8633" class="Function">n</a> <a id="8514" href="plfa.part2.Lambda.html#7385" class="Function Operator">⇒</a>
          <a id="8526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="Function Operator">case′</a> <a id="8532" href="plfa.part2.Lambda.html#8619" class="Function">m</a>
            <a id="8546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="Function Operator">[zero⇒</a> <a id="8553" href="plfa.part2.Lambda.html#8633" class="Function">n</a>
            <a id="8567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7506" class="Function Operator">|suc</a> <a id="8572" href="plfa.part2.Lambda.html#8619" class="Function">m</a> <a id="8574" href="plfa.part2.Lambda.html#7506" class="Function Operator">⇒</a> <a id="8576" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="8581" class="Symbol">(</a><a id="8582" href="plfa.part2.Lambda.html#8605" class="Function">+</a> <a id="8584" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="8586" href="plfa.part2.Lambda.html#8619" class="Function">m</a> <a id="8588" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="8590" href="plfa.part2.Lambda.html#8633" class="Function">n</a><a id="8591" class="Symbol">)</a> <a id="8593" href="plfa.part2.Lambda.html#7506" class="Function Operator">]</a>
  <a id="8597" class="Keyword">where</a>
  <a id="8605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8605" class="Function">+</a>  <a id="8608" class="Symbol">=</a>  <a id="8611" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="8613" class="String">&quot;+&quot;</a>
  <a id="8619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8619" class="Function">m</a>  <a id="8622" class="Symbol">=</a>  <a id="8625" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="8627" class="String">&quot;m&quot;</a>
  <a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8633" class="Function">n</a>  <a id="8636" class="Symbol">=</a>  <a id="8639" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="8641" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

{% raw %}<pre class="Agda"><a id="12172" class="Keyword">data</a> <a id="Value"></a><a id="12177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="12183" class="Symbol">:</a> <a id="12185" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="12190" class="Symbol">→</a> <a id="12192" class="PrimitiveType">Set</a> <a id="12196" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="12205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12205" class="InductiveConstructor">V-ƛ</a> <a id="12209" class="Symbol">:</a> <a id="12211" class="Symbol">∀</a> <a id="12213" class="Symbol">{</a><a id="12214" href="plfa.part2.Lambda.html#12214" class="Bound">x</a> <a id="12216" href="plfa.part2.Lambda.html#12216" class="Bound">N</a><a id="12217" class="Symbol">}</a>
      <a id="12225" class="Comment">---------------</a>
    <a id="12245" class="Symbol">→</a> <a id="12247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="12253" class="Symbol">(</a><a id="12254" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="12256" href="plfa.part2.Lambda.html#12214" class="Bound">x</a> <a id="12258" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="12260" href="plfa.part2.Lambda.html#12216" class="Bound">N</a><a id="12261" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="12266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12266" class="InductiveConstructor">V-zero</a> <a id="12273" class="Symbol">:</a>
      <a id="12281" class="Comment">-----------</a>
      <a id="12299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="12305" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="12314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12314" class="InductiveConstructor">V-suc</a> <a id="12320" class="Symbol">:</a> <a id="12322" class="Symbol">∀</a> <a id="12324" class="Symbol">{</a><a id="12325" href="plfa.part2.Lambda.html#12325" class="Bound">V</a><a id="12326" class="Symbol">}</a>
    <a id="12332" class="Symbol">→</a> <a id="12334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="12340" href="plfa.part2.Lambda.html#12325" class="Bound">V</a>
      <a id="12348" class="Comment">--------------</a>
    <a id="12367" class="Symbol">→</a> <a id="12369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="12375" class="Symbol">(</a><a id="12376" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="12381" href="plfa.part2.Lambda.html#12325" class="Bound">V</a><a id="12382" class="Symbol">)</a>
</pre>{% endraw %}
In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped]({{ site.baseurl }}/Untyped/).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

{% raw %}<pre class="Agda"><a id="15545" class="Keyword">infix</a> <a id="15551" class="Number">9</a> <a id="15553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15562" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="15562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15562" class="Function Operator">_[_:=_]</a> <a id="15570" class="Symbol">:</a> <a id="15572" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="15577" class="Symbol">→</a> <a id="15579" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="15582" class="Symbol">→</a> <a id="15584" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="15589" class="Symbol">→</a> <a id="15591" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="15596" class="Symbol">(</a><a id="15597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="15599" href="plfa.part2.Lambda.html#15599" class="Bound">x</a><a id="15600" class="Symbol">)</a> <a id="15602" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15604" href="plfa.part2.Lambda.html#15604" class="Bound">y</a> <a id="15606" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15609" href="plfa.part2.Lambda.html#15609" class="Bound">V</a> <a id="15611" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="15613" class="Keyword">with</a> <a id="15618" href="plfa.part2.Lambda.html#15599" class="Bound">x</a> <a id="15620" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15622" href="plfa.part2.Lambda.html#15604" class="Bound">y</a>
<a id="15624" class="Symbol">...</a> <a id="15628" class="Symbol">|</a> <a id="15630" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15634" class="Symbol">_</a>          <a id="15645" class="Symbol">=</a>  <a id="15648" class="Bound">V</a>
<a id="15650" class="Symbol">...</a> <a id="15654" class="Symbol">|</a> <a id="15656" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15660" class="Symbol">_</a>          <a id="15671" class="Symbol">=</a>  <a id="15674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="15676" class="Bound">x</a>
<a id="15678" class="Symbol">(</a><a id="15679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="15681" href="plfa.part2.Lambda.html#15681" class="Bound">x</a> <a id="15683" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="15685" href="plfa.part2.Lambda.html#15685" class="Bound">N</a><a id="15686" class="Symbol">)</a> <a id="15688" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15690" href="plfa.part2.Lambda.html#15690" class="Bound">y</a> <a id="15692" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15695" href="plfa.part2.Lambda.html#15695" class="Bound">V</a> <a id="15697" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="15699" class="Keyword">with</a> <a id="15704" href="plfa.part2.Lambda.html#15681" class="Bound">x</a> <a id="15706" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15708" href="plfa.part2.Lambda.html#15690" class="Bound">y</a>
<a id="15710" class="Symbol">...</a> <a id="15714" class="Symbol">|</a> <a id="15716" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15720" class="Symbol">_</a>          <a id="15731" class="Symbol">=</a>  <a id="15734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="15736" class="Bound">x</a> <a id="15738" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="15740" class="Bound">N</a>
<a id="15742" class="Symbol">...</a> <a id="15746" class="Symbol">|</a> <a id="15748" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15752" class="Symbol">_</a>          <a id="15763" class="Symbol">=</a>  <a id="15766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="15768" class="Bound">x</a> <a id="15770" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="15772" class="Bound">N</a> <a id="15774" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15776" class="Bound">y</a> <a id="15778" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15781" class="Bound">V</a> <a id="15783" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>
<a id="15785" class="Symbol">(</a><a id="15786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15786" class="Bound">L</a> <a id="15788" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="15790" href="plfa.part2.Lambda.html#15790" class="Bound">M</a><a id="15791" class="Symbol">)</a> <a id="15793" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15795" href="plfa.part2.Lambda.html#15795" class="Bound">y</a> <a id="15797" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15800" href="plfa.part2.Lambda.html#15800" class="Bound">V</a> <a id="15802" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>   <a id="15806" class="Symbol">=</a>  <a id="15809" href="plfa.part2.Lambda.html#15786" class="Bound">L</a> <a id="15811" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15813" href="plfa.part2.Lambda.html#15795" class="Bound">y</a> <a id="15815" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15818" href="plfa.part2.Lambda.html#15800" class="Bound">V</a> <a id="15820" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="15822" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="15824" href="plfa.part2.Lambda.html#15790" class="Bound">M</a> <a id="15826" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15828" href="plfa.part2.Lambda.html#15795" class="Bound">y</a> <a id="15830" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15833" href="plfa.part2.Lambda.html#15800" class="Bound">V</a> <a id="15835" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>
<a id="15837" class="Symbol">(</a><a id="15838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3950" class="InductiveConstructor">`zero</a><a id="15843" class="Symbol">)</a> <a id="15845" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15847" href="plfa.part2.Lambda.html#15847" class="Bound">y</a> <a id="15849" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15852" href="plfa.part2.Lambda.html#15852" class="Bound">V</a> <a id="15854" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>   <a id="15858" class="Symbol">=</a>  <a id="15861" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
<a id="15867" class="Symbol">(</a><a id="15868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="15873" href="plfa.part2.Lambda.html#15873" class="Bound">M</a><a id="15874" class="Symbol">)</a> <a id="15876" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15878" href="plfa.part2.Lambda.html#15878" class="Bound">y</a> <a id="15880" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15883" href="plfa.part2.Lambda.html#15883" class="Bound">V</a> <a id="15885" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>  <a id="15888" class="Symbol">=</a>  <a id="15891" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="15896" href="plfa.part2.Lambda.html#15873" class="Bound">M</a> <a id="15898" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15900" href="plfa.part2.Lambda.html#15878" class="Bound">y</a> <a id="15902" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15905" href="plfa.part2.Lambda.html#15883" class="Bound">V</a> <a id="15907" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>
<a id="15909" class="Symbol">(</a><a id="15910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="15915" href="plfa.part2.Lambda.html#15915" class="Bound">L</a> <a id="15917" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="15924" href="plfa.part2.Lambda.html#15924" class="Bound">M</a> <a id="15926" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="15931" href="plfa.part2.Lambda.html#15931" class="Bound">x</a> <a id="15933" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="15935" href="plfa.part2.Lambda.html#15935" class="Bound">N</a> <a id="15937" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="15938" class="Symbol">)</a> <a id="15940" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15942" href="plfa.part2.Lambda.html#15942" class="Bound">y</a> <a id="15944" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="15947" href="plfa.part2.Lambda.html#15947" class="Bound">V</a> <a id="15949" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="15951" class="Keyword">with</a> <a id="15956" href="plfa.part2.Lambda.html#15931" class="Bound">x</a> <a id="15958" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15960" href="plfa.part2.Lambda.html#15942" class="Bound">y</a>
<a id="15962" class="Symbol">...</a> <a id="15966" class="Symbol">|</a> <a id="15968" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15972" class="Symbol">_</a>          <a id="15983" class="Symbol">=</a>  <a id="15986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="15991" class="Bound">L</a> <a id="15993" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="15995" class="Bound">y</a> <a id="15997" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16000" class="Bound">V</a> <a id="16002" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16004" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="16011" class="Bound">M</a> <a id="16013" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16015" class="Bound">y</a> <a id="16017" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16020" class="Bound">V</a> <a id="16022" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16024" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="16029" class="Bound">x</a> <a id="16031" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="16033" class="Bound">N</a> <a id="16035" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
<a id="16037" class="Symbol">...</a> <a id="16041" class="Symbol">|</a> <a id="16043" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16047" class="Symbol">_</a>          <a id="16058" class="Symbol">=</a>  <a id="16061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="16066" class="Bound">L</a> <a id="16068" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16070" class="Bound">y</a> <a id="16072" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16075" class="Bound">V</a> <a id="16077" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16079" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="16086" class="Bound">M</a> <a id="16088" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16090" class="Bound">y</a> <a id="16092" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16095" class="Bound">V</a> <a id="16097" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16099" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="16104" class="Bound">x</a> <a id="16106" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="16108" class="Bound">N</a> <a id="16110" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16112" class="Bound">y</a> <a id="16114" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16117" class="Bound">V</a> <a id="16119" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16121" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
<a id="16123" class="Symbol">(</a><a id="16124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ</a> <a id="16126" href="plfa.part2.Lambda.html#16126" class="Bound">x</a> <a id="16128" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="16130" href="plfa.part2.Lambda.html#16130" class="Bound">N</a><a id="16131" class="Symbol">)</a> <a id="16133" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16135" href="plfa.part2.Lambda.html#16135" class="Bound">y</a> <a id="16137" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16140" href="plfa.part2.Lambda.html#16140" class="Bound">V</a> <a id="16142" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="16144" class="Keyword">with</a> <a id="16149" href="plfa.part2.Lambda.html#16126" class="Bound">x</a> <a id="16151" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="16153" href="plfa.part2.Lambda.html#16135" class="Bound">y</a>
<a id="16155" class="Symbol">...</a> <a id="16159" class="Symbol">|</a> <a id="16161" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="16165" class="Symbol">_</a>          <a id="16176" class="Symbol">=</a>  <a id="16179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ</a> <a id="16181" class="Bound">x</a> <a id="16183" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="16185" class="Bound">N</a>
<a id="16187" class="Symbol">...</a> <a id="16191" class="Symbol">|</a> <a id="16193" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16197" class="Symbol">_</a>          <a id="16208" class="Symbol">=</a>  <a id="16211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ</a> <a id="16213" class="Bound">x</a> <a id="16215" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="16217" class="Bound">N</a> <a id="16219" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="16221" class="Bound">y</a> <a id="16223" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="16226" class="Bound">V</a> <a id="16228" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>
</pre>{% endraw %}
Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

{% raw %}<pre class="Agda"><a id="16995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16995" class="Function">_</a> <a id="16997" class="Symbol">:</a> <a id="16999" class="Symbol">(</a><a id="17000" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17002" class="String">&quot;z&quot;</a> <a id="17006" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17008" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17010" class="String">&quot;s&quot;</a> <a id="17014" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17016" class="Symbol">(</a><a id="17017" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17019" class="String">&quot;s&quot;</a> <a id="17023" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17025" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17027" class="String">&quot;z&quot;</a><a id="17030" class="Symbol">))</a> <a id="17033" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="17035" class="String">&quot;s&quot;</a> <a id="17039" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="17042" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17047" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="17049" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17051" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17053" class="String">&quot;z&quot;</a> <a id="17057" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17059" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17064" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17066" class="Symbol">(</a><a id="17067" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17072" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17074" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17076" class="String">&quot;z&quot;</a><a id="17079" class="Symbol">)</a>
<a id="17081" class="Symbol">_</a> <a id="17083" class="Symbol">=</a> <a id="17085" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17091" class="Function">_</a> <a id="17093" class="Symbol">:</a> <a id="17095" class="Symbol">(</a><a id="17096" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17101" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17103" class="Symbol">(</a><a id="17104" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17109" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17111" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17113" class="String">&quot;z&quot;</a><a id="17116" class="Symbol">))</a> <a id="17119" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="17121" class="String">&quot;z&quot;</a> <a id="17125" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="17128" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="17134" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="17136" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17138" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17143" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17145" class="Symbol">(</a><a id="17146" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="17151" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="17153" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="17158" class="Symbol">)</a>
<a id="17160" class="Symbol">_</a> <a id="17162" class="Symbol">=</a> <a id="17164" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17170" class="Function">_</a> <a id="17172" class="Symbol">:</a> <a id="17174" class="Symbol">(</a><a id="17175" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17177" class="String">&quot;x&quot;</a> <a id="17181" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17183" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17185" class="String">&quot;y&quot;</a><a id="17188" class="Symbol">)</a> <a id="17190" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="17192" class="String">&quot;y&quot;</a> <a id="17196" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="17199" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="17205" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="17207" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17209" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17211" class="String">&quot;x&quot;</a> <a id="17215" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17217" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
<a id="17223" class="Symbol">_</a> <a id="17225" class="Symbol">=</a> <a id="17227" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17233" class="Function">_</a> <a id="17235" class="Symbol">:</a> <a id="17237" class="Symbol">(</a><a id="17238" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17240" class="String">&quot;x&quot;</a> <a id="17244" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17246" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17248" class="String">&quot;x&quot;</a><a id="17251" class="Symbol">)</a> <a id="17253" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="17255" class="String">&quot;x&quot;</a> <a id="17259" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="17262" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="17268" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="17270" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17272" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17274" class="String">&quot;x&quot;</a> <a id="17278" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17280" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17282" class="String">&quot;x&quot;</a>
<a id="17286" class="Symbol">_</a> <a id="17288" class="Symbol">=</a> <a id="17290" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17296" class="Function">_</a> <a id="17298" class="Symbol">:</a> <a id="17300" class="Symbol">(</a><a id="17301" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17303" class="String">&quot;y&quot;</a> <a id="17307" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17309" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17311" class="String">&quot;y&quot;</a><a id="17314" class="Symbol">)</a> <a id="17316" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="17318" class="String">&quot;x&quot;</a> <a id="17322" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="17325" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="17331" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a> <a id="17333" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17335" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="17337" class="String">&quot;y&quot;</a> <a id="17341" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="17343" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="17345" class="String">&quot;y&quot;</a>
<a id="17349" class="Symbol">_</a> <a id="17351" class="Symbol">=</a> <a id="17353" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

{% raw %}<pre class="Agda"><a id="17976" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that 
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

{% raw %}<pre class="Agda"><a id="20184" class="Keyword">infix</a> <a id="20190" class="Number">4</a> <a id="20192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20203" class="Datatype Operator">_—→_</a>

<a id="20198" class="Keyword">data</a> <a id="_—→_"></a><a id="20203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20203" class="Datatype Operator">_—→_</a> <a id="20208" class="Symbol">:</a> <a id="20210" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="20215" class="Symbol">→</a> <a id="20217" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="20222" class="Symbol">→</a> <a id="20224" class="PrimitiveType">Set</a> <a id="20228" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="20237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20237" class="InductiveConstructor">ξ-·₁</a> <a id="20242" class="Symbol">:</a> <a id="20244" class="Symbol">∀</a> <a id="20246" class="Symbol">{</a><a id="20247" href="plfa.part2.Lambda.html#20247" class="Bound">L</a> <a id="20249" href="plfa.part2.Lambda.html#20249" class="Bound">L′</a> <a id="20252" href="plfa.part2.Lambda.html#20252" class="Bound">M</a><a id="20253" class="Symbol">}</a>
    <a id="20259" class="Symbol">→</a> <a id="20261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20247" class="Bound">L</a> <a id="20263" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20266" href="plfa.part2.Lambda.html#20249" class="Bound">L′</a>
      <a id="20275" class="Comment">-----------------</a>
    <a id="20297" class="Symbol">→</a> <a id="20299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20247" class="Bound">L</a> <a id="20301" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="20303" href="plfa.part2.Lambda.html#20252" class="Bound">M</a> <a id="20305" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20308" href="plfa.part2.Lambda.html#20249" class="Bound">L′</a> <a id="20311" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="20313" href="plfa.part2.Lambda.html#20252" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="20318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20318" class="InductiveConstructor">ξ-·₂</a> <a id="20323" class="Symbol">:</a> <a id="20325" class="Symbol">∀</a> <a id="20327" class="Symbol">{</a><a id="20328" href="plfa.part2.Lambda.html#20328" class="Bound">V</a> <a id="20330" href="plfa.part2.Lambda.html#20330" class="Bound">M</a> <a id="20332" href="plfa.part2.Lambda.html#20332" class="Bound">M′</a><a id="20334" class="Symbol">}</a>
    <a id="20340" class="Symbol">→</a> <a id="20342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="20348" href="plfa.part2.Lambda.html#20328" class="Bound">V</a>
    <a id="20354" class="Symbol">→</a> <a id="20356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20330" class="Bound">M</a> <a id="20358" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20361" href="plfa.part2.Lambda.html#20332" class="Bound">M′</a>
      <a id="20370" class="Comment">-----------------</a>
    <a id="20392" class="Symbol">→</a> <a id="20394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20328" class="Bound">V</a> <a id="20396" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="20398" href="plfa.part2.Lambda.html#20330" class="Bound">M</a> <a id="20400" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20403" href="plfa.part2.Lambda.html#20328" class="Bound">V</a> <a id="20405" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="20407" href="plfa.part2.Lambda.html#20332" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="20413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20413" class="InductiveConstructor">β-ƛ</a> <a id="20417" class="Symbol">:</a> <a id="20419" class="Symbol">∀</a> <a id="20421" class="Symbol">{</a><a id="20422" href="plfa.part2.Lambda.html#20422" class="Bound">x</a> <a id="20424" href="plfa.part2.Lambda.html#20424" class="Bound">N</a> <a id="20426" href="plfa.part2.Lambda.html#20426" class="Bound">V</a><a id="20427" class="Symbol">}</a>
    <a id="20433" class="Symbol">→</a> <a id="20435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="20441" href="plfa.part2.Lambda.html#20426" class="Bound">V</a>
      <a id="20449" class="Comment">------------------------------</a>
    <a id="20484" class="Symbol">→</a> <a id="20486" class="Symbol">(</a><a id="20487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="20489" href="plfa.part2.Lambda.html#20422" class="Bound">x</a> <a id="20491" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="20493" href="plfa.part2.Lambda.html#20424" class="Bound">N</a><a id="20494" class="Symbol">)</a> <a id="20496" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="20498" href="plfa.part2.Lambda.html#20426" class="Bound">V</a> <a id="20500" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20503" href="plfa.part2.Lambda.html#20424" class="Bound">N</a> <a id="20505" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="20507" href="plfa.part2.Lambda.html#20422" class="Bound">x</a> <a id="20509" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="20512" href="plfa.part2.Lambda.html#20426" class="Bound">V</a> <a id="20514" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="20519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20519" class="InductiveConstructor">ξ-suc</a> <a id="20525" class="Symbol">:</a> <a id="20527" class="Symbol">∀</a> <a id="20529" class="Symbol">{</a><a id="20530" href="plfa.part2.Lambda.html#20530" class="Bound">M</a> <a id="20532" href="plfa.part2.Lambda.html#20532" class="Bound">M′</a><a id="20534" class="Symbol">}</a>
    <a id="20540" class="Symbol">→</a> <a id="20542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20530" class="Bound">M</a> <a id="20544" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20547" href="plfa.part2.Lambda.html#20532" class="Bound">M′</a>
      <a id="20556" class="Comment">------------------</a>
    <a id="20579" class="Symbol">→</a> <a id="20581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="20586" href="plfa.part2.Lambda.html#20530" class="Bound">M</a> <a id="20588" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20591" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="20596" href="plfa.part2.Lambda.html#20532" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="20602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20602" class="InductiveConstructor">ξ-case</a> <a id="20609" class="Symbol">:</a> <a id="20611" class="Symbol">∀</a> <a id="20613" class="Symbol">{</a><a id="20614" href="plfa.part2.Lambda.html#20614" class="Bound">x</a> <a id="20616" href="plfa.part2.Lambda.html#20616" class="Bound">L</a> <a id="20618" href="plfa.part2.Lambda.html#20618" class="Bound">L′</a> <a id="20621" href="plfa.part2.Lambda.html#20621" class="Bound">M</a> <a id="20623" href="plfa.part2.Lambda.html#20623" class="Bound">N</a><a id="20624" class="Symbol">}</a>
    <a id="20630" class="Symbol">→</a> <a id="20632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20616" class="Bound">L</a> <a id="20634" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20637" href="plfa.part2.Lambda.html#20618" class="Bound">L′</a>
      <a id="20646" class="Comment">-----------------------------------------------------------------</a>
    <a id="20716" class="Symbol">→</a> <a id="20718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="20723" href="plfa.part2.Lambda.html#20616" class="Bound">L</a> <a id="20725" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="20732" href="plfa.part2.Lambda.html#20621" class="Bound">M</a> <a id="20734" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="20739" href="plfa.part2.Lambda.html#20614" class="Bound">x</a> <a id="20741" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="20743" href="plfa.part2.Lambda.html#20623" class="Bound">N</a> <a id="20745" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a> <a id="20747" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20750" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="20755" href="plfa.part2.Lambda.html#20618" class="Bound">L′</a> <a id="20758" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="20765" href="plfa.part2.Lambda.html#20621" class="Bound">M</a> <a id="20767" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="20772" href="plfa.part2.Lambda.html#20614" class="Bound">x</a> <a id="20774" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="20776" href="plfa.part2.Lambda.html#20623" class="Bound">N</a> <a id="20778" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20783" class="InductiveConstructor">β-zero</a> <a id="20790" class="Symbol">:</a> <a id="20792" class="Symbol">∀</a> <a id="20794" class="Symbol">{</a><a id="20795" href="plfa.part2.Lambda.html#20795" class="Bound">x</a> <a id="20797" href="plfa.part2.Lambda.html#20797" class="Bound">M</a> <a id="20799" href="plfa.part2.Lambda.html#20799" class="Bound">N</a><a id="20800" class="Symbol">}</a>
      <a id="20808" class="Comment">----------------------------------------</a>
    <a id="20853" class="Symbol">→</a> <a id="20855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="20860" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="20866" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="20873" href="plfa.part2.Lambda.html#20797" class="Bound">M</a> <a id="20875" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="20880" href="plfa.part2.Lambda.html#20795" class="Bound">x</a> <a id="20882" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="20884" href="plfa.part2.Lambda.html#20799" class="Bound">N</a> <a id="20886" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a> <a id="20888" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="20891" href="plfa.part2.Lambda.html#20797" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20896" class="InductiveConstructor">β-suc</a> <a id="20902" class="Symbol">:</a> <a id="20904" class="Symbol">∀</a> <a id="20906" class="Symbol">{</a><a id="20907" href="plfa.part2.Lambda.html#20907" class="Bound">x</a> <a id="20909" href="plfa.part2.Lambda.html#20909" class="Bound">V</a> <a id="20911" href="plfa.part2.Lambda.html#20911" class="Bound">M</a> <a id="20913" href="plfa.part2.Lambda.html#20913" class="Bound">N</a><a id="20914" class="Symbol">}</a>
    <a id="20920" class="Symbol">→</a> <a id="20922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12177" class="Datatype">Value</a> <a id="20928" href="plfa.part2.Lambda.html#20909" class="Bound">V</a>
      <a id="20936" class="Comment">---------------------------------------------------</a>
    <a id="20992" class="Symbol">→</a> <a id="20994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="20999" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="21004" href="plfa.part2.Lambda.html#20909" class="Bound">V</a> <a id="21006" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="21013" href="plfa.part2.Lambda.html#20911" class="Bound">M</a> <a id="21015" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="21020" href="plfa.part2.Lambda.html#20907" class="Bound">x</a> <a id="21022" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="21024" href="plfa.part2.Lambda.html#20913" class="Bound">N</a> <a id="21026" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a> <a id="21028" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="21031" href="plfa.part2.Lambda.html#20913" class="Bound">N</a> <a id="21033" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="21035" href="plfa.part2.Lambda.html#20907" class="Bound">x</a> <a id="21037" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="21040" href="plfa.part2.Lambda.html#20909" class="Bound">V</a> <a id="21042" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="21047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#21047" class="InductiveConstructor">β-μ</a> <a id="21051" class="Symbol">:</a> <a id="21053" class="Symbol">∀</a> <a id="21055" class="Symbol">{</a><a id="21056" href="plfa.part2.Lambda.html#21056" class="Bound">x</a> <a id="21058" href="plfa.part2.Lambda.html#21058" class="Bound">M</a><a id="21059" class="Symbol">}</a>
      <a id="21067" class="Comment">------------------------------</a>
    <a id="21102" class="Symbol">→</a> <a id="21104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4085" class="InductiveConstructor Operator">μ</a> <a id="21106" href="plfa.part2.Lambda.html#21056" class="Bound">x</a> <a id="21108" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="21110" href="plfa.part2.Lambda.html#21058" class="Bound">M</a> <a id="21112" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="21115" href="plfa.part2.Lambda.html#21058" class="Bound">M</a> <a id="21117" href="plfa.part2.Lambda.html#15562" class="Function Operator">[</a> <a id="21119" href="plfa.part2.Lambda.html#21056" class="Bound">x</a> <a id="21121" href="plfa.part2.Lambda.html#15562" class="Function Operator">:=</a> <a id="21124" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">μ</a> <a id="21126" href="plfa.part2.Lambda.html#21056" class="Bound">x</a> <a id="21128" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="21130" href="plfa.part2.Lambda.html#21058" class="Bound">M</a> <a id="21132" href="plfa.part2.Lambda.html#15562" class="Function Operator">]</a>
</pre>{% endraw %}
The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality]({{ site.baseurl }}/Equality/):
{% raw %}<pre class="Agda"><a id="23128" class="Keyword">infix</a>  <a id="23135" class="Number">2</a> <a id="23137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23193" class="Datatype Operator">_—↠_</a>
<a id="23142" class="Keyword">infix</a>  <a id="23149" class="Number">1</a> <a id="23151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin_</a>
<a id="23158" class="Keyword">infixr</a> <a id="23165" class="Number">2</a> <a id="23167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="23175" class="Keyword">infix</a>  <a id="23182" class="Number">3</a> <a id="23184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23226" class="InductiveConstructor Operator">_∎</a>

<a id="23188" class="Keyword">data</a> <a id="_—↠_"></a><a id="23193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23193" class="Datatype Operator">_—↠_</a> <a id="23198" class="Symbol">:</a> <a id="23200" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="23205" class="Symbol">→</a> <a id="23207" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="23212" class="Symbol">→</a> <a id="23214" class="PrimitiveType">Set</a> <a id="23218" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="23226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23226" class="InductiveConstructor Operator">_∎</a> <a id="23229" class="Symbol">:</a> <a id="23231" class="Symbol">∀</a> <a id="23233" href="plfa.part2.Lambda.html#23233" class="Bound">M</a>
      <a id="23241" class="Comment">---------</a>
    <a id="23255" class="Symbol">→</a> <a id="23257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23233" class="Bound">M</a> <a id="23259" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="23262" href="plfa.part2.Lambda.html#23233" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="23267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="23275" class="Symbol">:</a> <a id="23277" class="Symbol">∀</a> <a id="23279" href="plfa.part2.Lambda.html#23279" class="Bound">L</a> <a id="23281" class="Symbol">{</a><a id="23282" href="plfa.part2.Lambda.html#23282" class="Bound">M</a> <a id="23284" href="plfa.part2.Lambda.html#23284" class="Bound">N</a><a id="23285" class="Symbol">}</a>
    <a id="23291" class="Symbol">→</a> <a id="23293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23279" class="Bound">L</a> <a id="23295" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="23298" href="plfa.part2.Lambda.html#23282" class="Bound">M</a>
    <a id="23304" class="Symbol">→</a> <a id="23306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23282" class="Bound">M</a> <a id="23308" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="23311" href="plfa.part2.Lambda.html#23284" class="Bound">N</a>
      <a id="23319" class="Comment">---------</a>
    <a id="23333" class="Symbol">→</a> <a id="23335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23279" class="Bound">L</a> <a id="23337" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="23340" href="plfa.part2.Lambda.html#23284" class="Bound">N</a>

<a id="begin_"></a><a id="23343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin_</a> <a id="23350" class="Symbol">:</a> <a id="23352" class="Symbol">∀</a> <a id="23354" class="Symbol">{</a><a id="23355" href="plfa.part2.Lambda.html#23355" class="Bound">M</a> <a id="23357" href="plfa.part2.Lambda.html#23357" class="Bound">N</a><a id="23358" class="Symbol">}</a>
  <a id="23362" class="Symbol">→</a> <a id="23364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23355" class="Bound">M</a> <a id="23366" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="23369" href="plfa.part2.Lambda.html#23357" class="Bound">N</a>
    <a id="23375" class="Comment">------</a>
  <a id="23384" class="Symbol">→</a> <a id="23386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23355" class="Bound">M</a> <a id="23388" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="23391" href="plfa.part2.Lambda.html#23357" class="Bound">N</a>
<a id="23393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin</a> <a id="23399" href="plfa.part2.Lambda.html#23399" class="Bound">M—↠N</a> <a id="23404" class="Symbol">=</a> <a id="23406" href="plfa.part2.Lambda.html#23399" class="Bound">M—↠N</a>
</pre>{% endraw %}We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
{% raw %}<pre class="Agda"><a id="24089" class="Keyword">data</a> <a id="_—↠′_"></a><a id="24094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24094" class="Datatype Operator">_—↠′_</a> <a id="24100" class="Symbol">:</a> <a id="24102" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="24107" class="Symbol">→</a> <a id="24109" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="24114" class="Symbol">→</a> <a id="24116" class="PrimitiveType">Set</a> <a id="24120" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="24129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24129" class="InductiveConstructor">step′</a> <a id="24135" class="Symbol">:</a> <a id="24137" class="Symbol">∀</a> <a id="24139" class="Symbol">{</a><a id="24140" href="plfa.part2.Lambda.html#24140" class="Bound">M</a> <a id="24142" href="plfa.part2.Lambda.html#24142" class="Bound">N</a><a id="24143" class="Symbol">}</a>
    <a id="24149" class="Symbol">→</a> <a id="24151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24140" class="Bound">M</a> <a id="24153" href="plfa.part2.Lambda.html#20203" class="Datatype Operator">—→</a> <a id="24156" href="plfa.part2.Lambda.html#24142" class="Bound">N</a>
      <a id="24164" class="Comment">-------</a>
    <a id="24176" class="Symbol">→</a> <a id="24178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24140" class="Bound">M</a> <a id="24180" href="plfa.part2.Lambda.html#24094" class="Datatype Operator">—↠′</a> <a id="24184" href="plfa.part2.Lambda.html#24142" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="24189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24189" class="InductiveConstructor">refl′</a> <a id="24195" class="Symbol">:</a> <a id="24197" class="Symbol">∀</a> <a id="24199" class="Symbol">{</a><a id="24200" href="plfa.part2.Lambda.html#24200" class="Bound">M</a><a id="24201" class="Symbol">}</a>
      <a id="24209" class="Comment">-------</a>
    <a id="24221" class="Symbol">→</a> <a id="24223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24200" class="Bound">M</a> <a id="24225" href="plfa.part2.Lambda.html#24094" class="Datatype Operator">—↠′</a> <a id="24229" href="plfa.part2.Lambda.html#24200" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="24234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24234" class="InductiveConstructor">trans′</a> <a id="24241" class="Symbol">:</a> <a id="24243" class="Symbol">∀</a> <a id="24245" class="Symbol">{</a><a id="24246" href="plfa.part2.Lambda.html#24246" class="Bound">L</a> <a id="24248" href="plfa.part2.Lambda.html#24248" class="Bound">M</a> <a id="24250" href="plfa.part2.Lambda.html#24250" class="Bound">N</a><a id="24251" class="Symbol">}</a>
    <a id="24257" class="Symbol">→</a> <a id="24259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24246" class="Bound">L</a> <a id="24261" href="plfa.part2.Lambda.html#24094" class="Datatype Operator">—↠′</a> <a id="24265" href="plfa.part2.Lambda.html#24248" class="Bound">M</a>
    <a id="24271" class="Symbol">→</a> <a id="24273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24248" class="Bound">M</a> <a id="24275" href="plfa.part2.Lambda.html#24094" class="Datatype Operator">—↠′</a> <a id="24279" href="plfa.part2.Lambda.html#24250" class="Bound">N</a>
      <a id="24287" class="Comment">-------</a>
    <a id="24299" class="Symbol">→</a> <a id="24301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24246" class="Bound">L</a> <a id="24303" href="plfa.part2.Lambda.html#24094" class="Datatype Operator">—↠′</a> <a id="24307" href="plfa.part2.Lambda.html#24250" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24683" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

    confluence : ∀ {L M N} → ∃[ P ]
      ( ((L —↠ M) × (L —↠ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

    diamond : ∀ {L M N} → ∃[ P ]
      ( ((L —→ M) × (L —→ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

The reduction system studied in this chapter is deterministic.
In symbols:

    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
        ------
      → M ≡ N

It is easy to show that every deterministic relation satisfies
the diamond property, and that every relation that satisfies
the diamond property is confluent.  Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
{% raw %}<pre class="Agda"><a id="26253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26253" class="Function">_</a> <a id="26255" class="Symbol">:</a> <a id="26257" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="26262" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26264" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="26269" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26271" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="26277" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="26280" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26285" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26290" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
<a id="26296" class="Symbol">_</a> <a id="26298" class="Symbol">=</a>
  <a id="26302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin</a>
    <a id="26312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5775" class="Function">twoᶜ</a> <a id="26317" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26319" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="26324" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26326" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="26334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26338" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="26343" class="Symbol">(</a><a id="26344" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26348" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="26351" class="Symbol">)</a> <a id="26353" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26359" class="Symbol">(</a><a id="26360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="26362" class="String">&quot;z&quot;</a> <a id="26366" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="26368" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="26373" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26375" class="Symbol">(</a><a id="26376" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="26381" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26383" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26385" class="String">&quot;z&quot;</a><a id="26388" class="Symbol">))</a> <a id="26391" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26393" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="26401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26405" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26409" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a> <a id="26416" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="26427" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26429" class="Symbol">(</a><a id="26430" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="26435" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26437" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="26442" class="Symbol">)</a>
  <a id="26446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26450" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="26455" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="26459" class="Symbol">(</a><a id="26460" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26464" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="26470" class="Symbol">)</a> <a id="26472" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="26483" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26485" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26490" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="26498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26502" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26506" class="Symbol">(</a><a id="26507" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="26513" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="26519" class="Symbol">)</a> <a id="26521" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="26532" class="Symbol">(</a><a id="26533" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26538" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="26543" class="Symbol">)</a>
  <a id="26547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23226" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26626" class="Function">_</a> <a id="26628" class="Symbol">:</a> <a id="26630" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="26635" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26637" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="26641" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26643" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="26647" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="26650" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26655" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26660" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26665" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26670" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
<a id="26676" class="Symbol">_</a> <a id="26678" class="Symbol">=</a>
  <a id="26682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin</a>
    <a id="26692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4560" class="Function">plus</a> <a id="26697" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26699" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="26703" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26705" href="plfa.part2.Lambda.html#4526" class="Function">two</a>
  <a id="26711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26715" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="26720" class="Symbol">(</a><a id="26721" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="26726" href="plfa.part2.Lambda.html#21047" class="InductiveConstructor">β-μ</a><a id="26729" class="Symbol">)</a> <a id="26731" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26737" class="Symbol">(</a><a id="26738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="26740" class="String">&quot;m&quot;</a> <a id="26744" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="26746" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="26748" class="String">&quot;n&quot;</a> <a id="26752" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="26760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="26765" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26767" class="String">&quot;m&quot;</a> <a id="26771" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="26778" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26780" class="String">&quot;n&quot;</a> <a id="26784" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="26789" class="String">&quot;m&quot;</a> <a id="26793" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="26795" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26800" class="Symbol">(</a><a id="26801" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="26806" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26808" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26810" class="String">&quot;m&quot;</a> <a id="26814" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26816" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26818" class="String">&quot;n&quot;</a><a id="26821" class="Symbol">)</a> <a id="26823" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="26824" class="Symbol">)</a>
        <a id="26834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="26836" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="26840" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26842" href="plfa.part2.Lambda.html#4526" class="Function">two</a>
  <a id="26848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26852" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="26857" class="Symbol">(</a><a id="26858" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26862" class="Symbol">(</a><a id="26863" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="26869" class="Symbol">(</a><a id="26870" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="26876" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="26882" class="Symbol">)))</a> <a id="26886" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="26892" class="Symbol">(</a><a id="26893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="26895" class="String">&quot;n&quot;</a> <a id="26899" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="26907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="26912" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="26916" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="26923" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26925" class="String">&quot;n&quot;</a> <a id="26929" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="26934" class="String">&quot;m&quot;</a> <a id="26938" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="26940" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="26945" class="Symbol">(</a><a id="26946" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="26951" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26953" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26955" class="String">&quot;m&quot;</a> <a id="26959" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="26961" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="26963" class="String">&quot;n&quot;</a><a id="26966" class="Symbol">)</a> <a id="26968" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="26969" class="Symbol">)</a>
         <a id="26980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="26982" href="plfa.part2.Lambda.html#4526" class="Function">two</a>
  <a id="26988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="26992" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="26996" class="Symbol">(</a><a id="26997" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27003" class="Symbol">(</a><a id="27004" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27010" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27016" class="Symbol">))</a> <a id="27019" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="27030" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="27034" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27041" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="27045" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27050" class="String">&quot;m&quot;</a> <a id="27054" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27056" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27061" class="Symbol">(</a><a id="27062" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27067" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27069" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27071" class="String">&quot;m&quot;</a> <a id="27075" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27077" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27080" class="Symbol">)</a> <a id="27082" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
  <a id="27086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27090" href="plfa.part2.Lambda.html#20896" class="InductiveConstructor">β-suc</a> <a id="27096" class="Symbol">(</a><a id="27097" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27103" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27109" class="Symbol">)</a> <a id="27111" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27122" class="Symbol">(</a><a id="27123" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27128" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27130" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27135" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27141" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27143" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27146" class="Symbol">)</a>
  <a id="27150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27154" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27160" class="Symbol">(</a><a id="27161" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27166" class="Symbol">(</a><a id="27167" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27172" href="plfa.part2.Lambda.html#21047" class="InductiveConstructor">β-μ</a><a id="27175" class="Symbol">))</a> <a id="27178" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27189" class="Symbol">((</a><a id="27191" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27193" class="String">&quot;m&quot;</a> <a id="27197" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="27199" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27201" class="String">&quot;n&quot;</a> <a id="27205" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="27213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="27218" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27220" class="String">&quot;m&quot;</a> <a id="27224" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27231" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27233" class="String">&quot;n&quot;</a> <a id="27237" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27242" class="String">&quot;m&quot;</a> <a id="27246" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27248" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27253" class="Symbol">(</a><a id="27254" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27259" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27261" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27263" class="String">&quot;m&quot;</a> <a id="27267" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27269" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27271" class="String">&quot;n&quot;</a><a id="27274" class="Symbol">)</a> <a id="27276" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="27277" class="Symbol">)</a>
        <a id="27287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="27289" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27294" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27300" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27302" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27305" class="Symbol">)</a>
  <a id="27309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27313" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27319" class="Symbol">(</a><a id="27320" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27325" class="Symbol">(</a><a id="27326" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="27330" class="Symbol">(</a><a id="27331" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27337" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27343" class="Symbol">)))</a> <a id="27347" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27358" class="Symbol">((</a><a id="27360" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27362" class="String">&quot;n&quot;</a> <a id="27366" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="27374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="27379" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27384" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27390" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27397" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27399" class="String">&quot;n&quot;</a> <a id="27403" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27408" class="String">&quot;m&quot;</a> <a id="27412" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27414" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27419" class="Symbol">(</a><a id="27420" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27425" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27427" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27429" class="String">&quot;m&quot;</a> <a id="27433" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27435" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27437" class="String">&quot;n&quot;</a><a id="27440" class="Symbol">)</a> <a id="27442" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="27443" class="Symbol">)</a>
        <a id="27453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="27455" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27458" class="Symbol">)</a>
  <a id="27462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27466" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27472" class="Symbol">(</a><a id="27473" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="27477" class="Symbol">(</a><a id="27478" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27484" class="Symbol">(</a><a id="27485" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27491" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27497" class="Symbol">)))</a> <a id="27501" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27512" class="Symbol">(</a><a id="27513" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="27518" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27523" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27529" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27536" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="27540" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27545" class="String">&quot;m&quot;</a> <a id="27549" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27551" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27556" class="Symbol">(</a><a id="27557" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27562" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27564" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27566" class="String">&quot;m&quot;</a> <a id="27570" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27572" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27575" class="Symbol">)</a> <a id="27577" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="27578" class="Symbol">)</a>
  <a id="27582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27586" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27592" class="Symbol">(</a><a id="27593" href="plfa.part2.Lambda.html#20896" class="InductiveConstructor">β-suc</a> <a id="27599" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27605" class="Symbol">)</a> <a id="27607" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27618" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27623" class="Symbol">(</a><a id="27624" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27629" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27631" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27637" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27639" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27642" class="Symbol">)</a>
  <a id="27646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27650" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27656" class="Symbol">(</a><a id="27657" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27663" class="Symbol">(</a><a id="27664" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27669" class="Symbol">(</a><a id="27670" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27675" href="plfa.part2.Lambda.html#21047" class="InductiveConstructor">β-μ</a><a id="27678" class="Symbol">)))</a> <a id="27682" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27693" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27698" class="Symbol">((</a><a id="27700" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27702" class="String">&quot;m&quot;</a> <a id="27706" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="27708" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27710" class="String">&quot;n&quot;</a> <a id="27714" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="27722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="27727" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27729" class="String">&quot;m&quot;</a> <a id="27733" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27740" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27742" class="String">&quot;n&quot;</a> <a id="27746" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27751" class="String">&quot;m&quot;</a> <a id="27755" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27757" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27762" class="Symbol">(</a><a id="27763" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27768" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27770" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27772" class="String">&quot;m&quot;</a> <a id="27776" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27778" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27780" class="String">&quot;n&quot;</a><a id="27783" class="Symbol">)</a> <a id="27785" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="27786" class="Symbol">)</a>
        <a id="27796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="27798" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27804" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27806" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27809" class="Symbol">)</a>
  <a id="27813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27817" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27823" class="Symbol">(</a><a id="27824" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27830" class="Symbol">(</a><a id="27831" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="27836" class="Symbol">(</a><a id="27837" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="27841" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="27847" class="Symbol">)))</a> <a id="27851" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="27857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="27862" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27867" class="Symbol">((</a><a id="27869" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="27871" class="String">&quot;n&quot;</a> <a id="27875" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a>
      <a id="27883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4025" class="InductiveConstructor Operator">case</a> <a id="27888" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="27894" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="27901" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27903" class="String">&quot;n&quot;</a> <a id="27907" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="27912" class="String">&quot;m&quot;</a> <a id="27916" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="27918" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="27923" class="Symbol">(</a><a id="27924" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="27929" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27931" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27933" class="String">&quot;m&quot;</a> <a id="27937" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="27939" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="27941" class="String">&quot;n&quot;</a><a id="27944" class="Symbol">)</a> <a id="27946" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="27947" class="Symbol">)</a>
        <a id="27957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="27959" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="27962" class="Symbol">)</a>
  <a id="27966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="27970" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27976" class="Symbol">(</a><a id="27977" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="27983" class="Symbol">(</a><a id="27984" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="27988" class="Symbol">(</a><a id="27989" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="27995" class="Symbol">(</a><a id="27996" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="28002" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="28008" class="Symbol">))))</a> <a id="28013" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="28024" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28029" class="Symbol">(</a><a id="28030" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="28035" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="28041" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="28048" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="28052" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="28057" class="String">&quot;m&quot;</a> <a id="28061" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="28063" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28068" class="Symbol">(</a><a id="28069" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="28074" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28076" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28078" class="String">&quot;m&quot;</a> <a id="28082" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28084" href="plfa.part2.Lambda.html#4526" class="Function">two</a><a id="28087" class="Symbol">)</a> <a id="28089" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a><a id="28090" class="Symbol">)</a>
  <a id="28094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28098" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="28104" class="Symbol">(</a><a id="28105" href="plfa.part2.Lambda.html#20519" class="InductiveConstructor">ξ-suc</a> <a id="28111" href="plfa.part2.Lambda.html#20783" class="InductiveConstructor">β-zero</a><a id="28117" class="Symbol">)</a> <a id="28119" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="28130" class="Symbol">(</a><a id="28131" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28136" class="Symbol">(</a><a id="28137" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28142" class="Symbol">(</a><a id="28143" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28148" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="28153" class="Symbol">)))</a>
  <a id="28159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23226" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="28230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#28230" class="Function">_</a> <a id="28232" class="Symbol">:</a> <a id="28234" href="plfa.part2.Lambda.html#5836" class="Function">plusᶜ</a> <a id="28240" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28242" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28247" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28249" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28254" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28256" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28261" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28263" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="28269" href="plfa.part2.Lambda.html#23193" class="Datatype Operator">—↠</a> <a id="28272" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28277" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28282" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28287" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="28292" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
<a id="28298" class="Symbol">_</a> <a id="28300" class="Symbol">=</a>
  <a id="28304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23343" class="Function Operator">begin</a>
    <a id="28314" class="Symbol">(</a><a id="28315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28317" class="String">&quot;m&quot;</a> <a id="28321" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28323" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28325" class="String">&quot;n&quot;</a> <a id="28329" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28331" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28333" class="String">&quot;s&quot;</a> <a id="28337" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28339" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28341" class="String">&quot;z&quot;</a> <a id="28345" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28347" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28349" class="String">&quot;m&quot;</a> <a id="28353" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28355" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28357" class="String">&quot;s&quot;</a> <a id="28361" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28363" class="Symbol">(</a><a id="28364" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28366" class="String">&quot;n&quot;</a> <a id="28370" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28372" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28374" class="String">&quot;s&quot;</a> <a id="28378" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28380" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28382" class="String">&quot;z&quot;</a><a id="28385" class="Symbol">))</a>
      <a id="28394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="28396" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28401" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28403" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28408" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28410" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28415" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28417" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="28425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28429" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28434" class="Symbol">(</a><a id="28435" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28440" class="Symbol">(</a><a id="28441" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28446" class="Symbol">(</a><a id="28447" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28451" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="28454" class="Symbol">)))</a> <a id="28458" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28464" class="Symbol">(</a><a id="28465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28467" class="String">&quot;n&quot;</a> <a id="28471" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28473" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28475" class="String">&quot;s&quot;</a> <a id="28479" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28481" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28483" class="String">&quot;z&quot;</a> <a id="28487" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28489" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28494" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28496" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28498" class="String">&quot;s&quot;</a> <a id="28502" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28504" class="Symbol">(</a><a id="28505" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28507" class="String">&quot;n&quot;</a> <a id="28511" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28513" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28515" class="String">&quot;s&quot;</a> <a id="28519" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28521" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28523" class="String">&quot;z&quot;</a><a id="28526" class="Symbol">))</a>
      <a id="28535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3902" class="InductiveConstructor Operator">·</a> <a id="28537" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28542" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28544" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28549" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28551" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="28559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28563" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28568" class="Symbol">(</a><a id="28569" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28574" class="Symbol">(</a><a id="28575" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28579" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="28582" class="Symbol">))</a> <a id="28585" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28591" class="Symbol">(</a><a id="28592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28594" class="String">&quot;s&quot;</a> <a id="28598" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28600" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28602" class="String">&quot;z&quot;</a> <a id="28606" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28608" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28613" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28615" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28617" class="String">&quot;s&quot;</a> <a id="28621" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28623" class="Symbol">(</a><a id="28624" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28629" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28631" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28633" class="String">&quot;s&quot;</a> <a id="28637" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28639" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28641" class="String">&quot;z&quot;</a><a id="28644" class="Symbol">))</a> <a id="28647" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28649" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28654" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28656" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="28664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28668" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28673" class="Symbol">(</a><a id="28674" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28678" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="28681" class="Symbol">)</a> <a id="28683" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28689" class="Symbol">(</a><a id="28690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28692" class="String">&quot;z&quot;</a> <a id="28696" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28698" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28703" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28705" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28710" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28712" class="Symbol">(</a><a id="28713" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28718" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28720" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28725" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28727" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28729" class="String">&quot;z&quot;</a><a id="28732" class="Symbol">))</a> <a id="28735" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28737" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a>
  <a id="28745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28749" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28753" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a> <a id="28760" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5775" class="Function">twoᶜ</a> <a id="28771" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28773" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28778" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28780" class="Symbol">(</a><a id="28781" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28786" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28788" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28793" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28795" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="28800" class="Symbol">)</a>
  <a id="28804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28808" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28813" class="Symbol">(</a><a id="28814" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28818" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="28821" class="Symbol">)</a> <a id="28823" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28829" class="Symbol">(</a><a id="28830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28832" class="String">&quot;z&quot;</a> <a id="28836" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28838" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28843" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28845" class="Symbol">(</a><a id="28846" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28851" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28853" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28855" class="String">&quot;z&quot;</a><a id="28858" class="Symbol">))</a> <a id="28861" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28863" class="Symbol">(</a><a id="28864" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="28869" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28871" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28876" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28878" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="28883" class="Symbol">)</a>
  <a id="28887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="28891" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="28896" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="28900" class="Symbol">(</a><a id="28901" href="plfa.part2.Lambda.html#20237" class="InductiveConstructor">ξ-·₁</a> <a id="28906" class="Symbol">(</a><a id="28907" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="28911" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a><a id="28914" class="Symbol">))</a> <a id="28917" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="28923" class="Symbol">(</a><a id="28924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28926" class="String">&quot;z&quot;</a> <a id="28930" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28932" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28937" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28939" class="Symbol">(</a><a id="28940" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28945" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28947" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28949" class="String">&quot;z&quot;</a><a id="28952" class="Symbol">))</a> <a id="28955" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28957" class="Symbol">((</a><a id="28959" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="28961" class="String">&quot;z&quot;</a> <a id="28965" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="28967" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28972" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28974" class="Symbol">(</a><a id="28975" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="28980" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28982" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="28984" class="String">&quot;z&quot;</a><a id="28987" class="Symbol">))</a> <a id="28990" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="28992" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="28997" class="Symbol">)</a>
  <a id="29001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29005" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="29010" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="29014" class="Symbol">(</a><a id="29015" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29019" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29025" class="Symbol">)</a> <a id="29027" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="29033" class="Symbol">(</a><a id="29034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="29036" class="String">&quot;z&quot;</a> <a id="29040" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="29042" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29047" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29049" class="Symbol">(</a><a id="29050" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29055" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29057" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="29059" class="String">&quot;z&quot;</a><a id="29062" class="Symbol">))</a> <a id="29065" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29067" class="Symbol">(</a><a id="29068" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29073" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29075" class="Symbol">(</a><a id="29076" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29081" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29083" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29088" class="Symbol">))</a>
  <a id="29093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29097" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="29102" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="29106" class="Symbol">(</a><a id="29107" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="29112" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="29116" class="Symbol">(</a><a id="29117" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29121" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29127" class="Symbol">))</a> <a id="29130" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="29136" class="Symbol">(</a><a id="29137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="29139" class="String">&quot;z&quot;</a> <a id="29143" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="29145" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29150" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29152" class="Symbol">(</a><a id="29153" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29158" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29160" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="29162" class="String">&quot;z&quot;</a><a id="29165" class="Symbol">))</a> <a id="29168" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29170" class="Symbol">(</a><a id="29171" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29176" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29178" class="Symbol">(</a><a id="29179" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29184" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29189" class="Symbol">))</a>
  <a id="29194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29198" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="29203" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="29207" class="Symbol">(</a><a id="29208" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29212" class="Symbol">(</a><a id="29213" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29219" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29225" class="Symbol">))</a> <a id="29228" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="29234" class="Symbol">(</a><a id="29235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3856" class="InductiveConstructor Operator">ƛ</a> <a id="29237" class="String">&quot;z&quot;</a> <a id="29241" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="29243" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29248" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29250" class="Symbol">(</a><a id="29251" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29256" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29258" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="29260" class="String">&quot;z&quot;</a><a id="29263" class="Symbol">))</a> <a id="29266" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29268" class="Symbol">(</a><a id="29269" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29274" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29279" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29284" class="Symbol">)</a>
  <a id="29288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29292" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29296" class="Symbol">(</a><a id="29297" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29303" class="Symbol">(</a><a id="29304" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29310" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29316" class="Symbol">))</a> <a id="29319" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="29325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="29330" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29332" class="Symbol">(</a><a id="29333" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="29338" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29340" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29345" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29350" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29355" class="Symbol">)</a>
  <a id="29359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29363" href="plfa.part2.Lambda.html#20318" class="InductiveConstructor">ξ-·₂</a> <a id="29368" href="plfa.part2.Lambda.html#12205" class="InductiveConstructor">V-ƛ</a> <a id="29372" class="Symbol">(</a><a id="29373" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29377" class="Symbol">(</a><a id="29378" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29384" class="Symbol">(</a><a id="29385" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29391" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29397" class="Symbol">)))</a> <a id="29401" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
    <a id="29407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5940" class="Function">sucᶜ</a> <a id="29412" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="29414" class="Symbol">(</a><a id="29415" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29420" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29425" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29430" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29435" class="Symbol">)</a>
  <a id="29439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23267" class="InductiveConstructor Operator">—→⟨</a> <a id="29443" href="plfa.part2.Lambda.html#20413" class="InductiveConstructor">β-ƛ</a> <a id="29447" class="Symbol">(</a><a id="29448" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29454" class="Symbol">(</a><a id="29455" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29461" class="Symbol">(</a><a id="29462" href="plfa.part2.Lambda.html#12314" class="InductiveConstructor">V-suc</a> <a id="29468" href="plfa.part2.Lambda.html#12266" class="InductiveConstructor">V-zero</a><a id="29474" class="Symbol">)))</a> <a id="29478" href="plfa.part2.Lambda.html#23267" class="InductiveConstructor Operator">⟩</a>
   <a id="29483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="29488" class="Symbol">(</a><a id="29489" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29494" class="Symbol">(</a><a id="29495" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29500" class="Symbol">(</a><a id="29501" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="29506" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a><a id="29511" class="Symbol">)))</a>
  <a id="29517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23226" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29719" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="30019" class="Keyword">infixr</a> <a id="30026" class="Number">7</a> <a id="30028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30057" class="InductiveConstructor Operator">_⇒_</a>

<a id="30033" class="Keyword">data</a> <a id="Type"></a><a id="30038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30038" class="Datatype">Type</a> <a id="30043" class="Symbol">:</a> <a id="30045" class="PrimitiveType">Set</a> <a id="30049" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="30057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30057" class="InductiveConstructor Operator">_⇒_</a> <a id="30061" class="Symbol">:</a> <a id="30063" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="30068" class="Symbol">→</a> <a id="30070" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="30075" class="Symbol">→</a> <a id="30077" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="30084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30084" class="InductiveConstructor">`ℕ</a> <a id="30087" class="Symbol">:</a> <a id="30089" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a>
</pre>{% endraw %}
### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

{% raw %}<pre class="Agda"><a id="31674" class="Keyword">infixl</a> <a id="31681" class="Number">5</a>  <a id="31684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31736" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31691" class="Keyword">data</a> <a id="Context"></a><a id="31696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31696" class="Datatype">Context</a> <a id="31704" class="Symbol">:</a> <a id="31706" class="PrimitiveType">Set</a> <a id="31710" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31718" class="InductiveConstructor">∅</a>     <a id="31724" class="Symbol">:</a> <a id="31726" href="plfa.part2.Lambda.html#31696" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31736" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31742" class="Symbol">:</a> <a id="31744" href="plfa.part2.Lambda.html#31696" class="Datatype">Context</a> <a id="31752" class="Symbol">→</a> <a id="31754" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="31757" class="Symbol">→</a> <a id="31759" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="31764" class="Symbol">→</a> <a id="31766" href="plfa.part2.Lambda.html#31696" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="32019" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
{% raw %}<pre class="Agda"><a id="32908" class="Keyword">infix</a>  <a id="32915" class="Number">4</a>  <a id="32918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32930" class="Datatype Operator">_∋_⦂_</a>

<a id="32925" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32930" class="Datatype Operator">_∋_⦂_</a> <a id="32936" class="Symbol">:</a> <a id="32938" href="plfa.part2.Lambda.html#31696" class="Datatype">Context</a> <a id="32946" class="Symbol">→</a> <a id="32948" href="plfa.part2.Lambda.html#3697" class="Function">Id</a> <a id="32951" class="Symbol">→</a> <a id="32953" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="32958" class="Symbol">→</a> <a id="32960" class="PrimitiveType">Set</a> <a id="32964" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32973" class="InductiveConstructor">Z</a> <a id="32975" class="Symbol">:</a> <a id="32977" class="Symbol">∀</a> <a id="32979" class="Symbol">{</a><a id="32980" href="plfa.part2.Lambda.html#32980" class="Bound">Γ</a> <a id="32982" href="plfa.part2.Lambda.html#32982" class="Bound">x</a> <a id="32984" href="plfa.part2.Lambda.html#32984" class="Bound">A</a><a id="32985" class="Symbol">}</a>
      <a id="32993" class="Comment">------------------</a>
    <a id="33016" class="Symbol">→</a> <a id="33018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32980" class="Bound">Γ</a> <a id="33020" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">,</a> <a id="33022" href="plfa.part2.Lambda.html#32982" class="Bound">x</a> <a id="33024" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">⦂</a> <a id="33026" href="plfa.part2.Lambda.html#32984" class="Bound">A</a> <a id="33028" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="33030" href="plfa.part2.Lambda.html#32982" class="Bound">x</a> <a id="33032" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="33034" href="plfa.part2.Lambda.html#32984" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="33039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33039" class="InductiveConstructor">S</a> <a id="33041" class="Symbol">:</a> <a id="33043" class="Symbol">∀</a> <a id="33045" class="Symbol">{</a><a id="33046" href="plfa.part2.Lambda.html#33046" class="Bound">Γ</a> <a id="33048" href="plfa.part2.Lambda.html#33048" class="Bound">x</a> <a id="33050" href="plfa.part2.Lambda.html#33050" class="Bound">y</a> <a id="33052" href="plfa.part2.Lambda.html#33052" class="Bound">A</a> <a id="33054" href="plfa.part2.Lambda.html#33054" class="Bound">B</a><a id="33055" class="Symbol">}</a>
    <a id="33061" class="Symbol">→</a> <a id="33063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33048" class="Bound">x</a> <a id="33065" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="33067" href="plfa.part2.Lambda.html#33050" class="Bound">y</a>
    <a id="33073" class="Symbol">→</a> <a id="33075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33046" class="Bound">Γ</a> <a id="33077" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="33079" href="plfa.part2.Lambda.html#33048" class="Bound">x</a> <a id="33081" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="33083" href="plfa.part2.Lambda.html#33052" class="Bound">A</a>
      <a id="33091" class="Comment">------------------</a>
    <a id="33114" class="Symbol">→</a> <a id="33116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33046" class="Bound">Γ</a> <a id="33118" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">,</a> <a id="33120" href="plfa.part2.Lambda.html#33050" class="Bound">y</a> <a id="33122" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">⦂</a> <a id="33124" href="plfa.part2.Lambda.html#33054" class="Bound">B</a> <a id="33126" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="33128" href="plfa.part2.Lambda.html#33048" class="Bound">x</a> <a id="33130" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="33132" href="plfa.part2.Lambda.html#33052" class="Bound">A</a>
</pre>{% endraw %}
The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
{% raw %}<pre class="Agda"><a id="34072" class="Keyword">infix</a>  <a id="34079" class="Number">4</a>  <a id="34082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34094" class="Datatype Operator">_⊢_⦂_</a>

<a id="34089" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="34094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34094" class="Datatype Operator">_⊢_⦂_</a> <a id="34100" class="Symbol">:</a> <a id="34102" href="plfa.part2.Lambda.html#31696" class="Datatype">Context</a> <a id="34110" class="Symbol">→</a> <a id="34112" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="34117" class="Symbol">→</a> <a id="34119" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="34124" class="Symbol">→</a> <a id="34126" class="PrimitiveType">Set</a> <a id="34130" class="Keyword">where</a>

  <a id="34139" class="Comment">-- Axiom </a>
  <a id="_⊢_⦂_.⊢`"></a><a id="34151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34151" class="InductiveConstructor">⊢`</a> <a id="34154" class="Symbol">:</a> <a id="34156" class="Symbol">∀</a> <a id="34158" class="Symbol">{</a><a id="34159" href="plfa.part2.Lambda.html#34159" class="Bound">Γ</a> <a id="34161" href="plfa.part2.Lambda.html#34161" class="Bound">x</a> <a id="34163" href="plfa.part2.Lambda.html#34163" class="Bound">A</a><a id="34164" class="Symbol">}</a>
    <a id="34170" class="Symbol">→</a> <a id="34172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34159" class="Bound">Γ</a> <a id="34174" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="34176" href="plfa.part2.Lambda.html#34161" class="Bound">x</a> <a id="34178" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="34180" href="plfa.part2.Lambda.html#34163" class="Bound">A</a>
      <a id="34188" class="Comment">-----------</a>
    <a id="34204" class="Symbol">→</a> <a id="34206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34159" class="Bound">Γ</a> <a id="34208" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34210" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="34212" href="plfa.part2.Lambda.html#34161" class="Bound">x</a> <a id="34214" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34216" href="plfa.part2.Lambda.html#34163" class="Bound">A</a>

  <a id="34221" class="Comment">-- ⇒-I </a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="34231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34231" class="InductiveConstructor">⊢ƛ</a> <a id="34234" class="Symbol">:</a> <a id="34236" class="Symbol">∀</a> <a id="34238" class="Symbol">{</a><a id="34239" href="plfa.part2.Lambda.html#34239" class="Bound">Γ</a> <a id="34241" href="plfa.part2.Lambda.html#34241" class="Bound">x</a> <a id="34243" href="plfa.part2.Lambda.html#34243" class="Bound">N</a> <a id="34245" href="plfa.part2.Lambda.html#34245" class="Bound">A</a> <a id="34247" href="plfa.part2.Lambda.html#34247" class="Bound">B</a><a id="34248" class="Symbol">}</a>
    <a id="34254" class="Symbol">→</a> <a id="34256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34239" class="Bound">Γ</a> <a id="34258" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">,</a> <a id="34260" href="plfa.part2.Lambda.html#34241" class="Bound">x</a> <a id="34262" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">⦂</a> <a id="34264" href="plfa.part2.Lambda.html#34245" class="Bound">A</a> <a id="34266" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34268" href="plfa.part2.Lambda.html#34243" class="Bound">N</a> <a id="34270" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34272" href="plfa.part2.Lambda.html#34247" class="Bound">B</a>
      <a id="34280" class="Comment">-------------------</a>
    <a id="34304" class="Symbol">→</a> <a id="34306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34239" class="Bound">Γ</a> <a id="34308" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34310" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="34312" href="plfa.part2.Lambda.html#34241" class="Bound">x</a> <a id="34314" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="34316" href="plfa.part2.Lambda.html#34243" class="Bound">N</a> <a id="34318" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34320" href="plfa.part2.Lambda.html#34245" class="Bound">A</a> <a id="34322" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="34324" href="plfa.part2.Lambda.html#34247" class="Bound">B</a>

  <a id="34329" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="34338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34338" class="InductiveConstructor Operator">_·_</a> <a id="34342" class="Symbol">:</a> <a id="34344" class="Symbol">∀</a> <a id="34346" class="Symbol">{</a><a id="34347" href="plfa.part2.Lambda.html#34347" class="Bound">Γ</a> <a id="34349" href="plfa.part2.Lambda.html#34349" class="Bound">L</a> <a id="34351" href="plfa.part2.Lambda.html#34351" class="Bound">M</a> <a id="34353" href="plfa.part2.Lambda.html#34353" class="Bound">A</a> <a id="34355" href="plfa.part2.Lambda.html#34355" class="Bound">B</a><a id="34356" class="Symbol">}</a>
    <a id="34362" class="Symbol">→</a> <a id="34364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34347" class="Bound">Γ</a> <a id="34366" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34368" href="plfa.part2.Lambda.html#34349" class="Bound">L</a> <a id="34370" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34372" href="plfa.part2.Lambda.html#34353" class="Bound">A</a> <a id="34374" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="34376" href="plfa.part2.Lambda.html#34355" class="Bound">B</a>
    <a id="34382" class="Symbol">→</a> <a id="34384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34347" class="Bound">Γ</a> <a id="34386" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34388" href="plfa.part2.Lambda.html#34351" class="Bound">M</a> <a id="34390" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34392" href="plfa.part2.Lambda.html#34353" class="Bound">A</a>
      <a id="34400" class="Comment">-------------</a>
    <a id="34418" class="Symbol">→</a> <a id="34420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34347" class="Bound">Γ</a> <a id="34422" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34424" href="plfa.part2.Lambda.html#34349" class="Bound">L</a> <a id="34426" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="34428" href="plfa.part2.Lambda.html#34351" class="Bound">M</a> <a id="34430" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34432" href="plfa.part2.Lambda.html#34355" class="Bound">B</a>

  <a id="34437" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="34447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34447" class="InductiveConstructor">⊢zero</a> <a id="34453" class="Symbol">:</a> <a id="34455" class="Symbol">∀</a> <a id="34457" class="Symbol">{</a><a id="34458" href="plfa.part2.Lambda.html#34458" class="Bound">Γ</a><a id="34459" class="Symbol">}</a>
      <a id="34467" class="Comment">--------------</a>
    <a id="34486" class="Symbol">→</a> <a id="34488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34458" class="Bound">Γ</a> <a id="34490" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34492" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="34498" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34500" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>

  <a id="34506" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="34516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34516" class="InductiveConstructor">⊢suc</a> <a id="34521" class="Symbol">:</a> <a id="34523" class="Symbol">∀</a> <a id="34525" class="Symbol">{</a><a id="34526" href="plfa.part2.Lambda.html#34526" class="Bound">Γ</a> <a id="34528" href="plfa.part2.Lambda.html#34528" class="Bound">M</a><a id="34529" class="Symbol">}</a>
    <a id="34535" class="Symbol">→</a> <a id="34537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34526" class="Bound">Γ</a> <a id="34539" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34541" href="plfa.part2.Lambda.html#34528" class="Bound">M</a> <a id="34543" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34545" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
      <a id="34554" class="Comment">---------------</a>
    <a id="34574" class="Symbol">→</a> <a id="34576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34526" class="Bound">Γ</a> <a id="34578" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34580" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="34585" href="plfa.part2.Lambda.html#34528" class="Bound">M</a> <a id="34587" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34589" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>

  <a id="34595" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="34604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34604" class="InductiveConstructor">⊢case</a> <a id="34610" class="Symbol">:</a> <a id="34612" class="Symbol">∀</a> <a id="34614" class="Symbol">{</a><a id="34615" href="plfa.part2.Lambda.html#34615" class="Bound">Γ</a> <a id="34617" href="plfa.part2.Lambda.html#34617" class="Bound">L</a> <a id="34619" href="plfa.part2.Lambda.html#34619" class="Bound">M</a> <a id="34621" href="plfa.part2.Lambda.html#34621" class="Bound">x</a> <a id="34623" href="plfa.part2.Lambda.html#34623" class="Bound">N</a> <a id="34625" href="plfa.part2.Lambda.html#34625" class="Bound">A</a><a id="34626" class="Symbol">}</a>
    <a id="34632" class="Symbol">→</a> <a id="34634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34615" class="Bound">Γ</a> <a id="34636" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34638" href="plfa.part2.Lambda.html#34617" class="Bound">L</a> <a id="34640" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34642" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
    <a id="34649" class="Symbol">→</a> <a id="34651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34615" class="Bound">Γ</a> <a id="34653" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34655" href="plfa.part2.Lambda.html#34619" class="Bound">M</a> <a id="34657" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34659" href="plfa.part2.Lambda.html#34625" class="Bound">A</a>
    <a id="34665" class="Symbol">→</a> <a id="34667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34615" class="Bound">Γ</a> <a id="34669" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">,</a> <a id="34671" href="plfa.part2.Lambda.html#34621" class="Bound">x</a> <a id="34673" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">⦂</a> <a id="34675" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a> <a id="34678" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34680" href="plfa.part2.Lambda.html#34623" class="Bound">N</a> <a id="34682" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34684" href="plfa.part2.Lambda.html#34625" class="Bound">A</a>
      <a id="34692" class="Comment">-------------------------------------</a>
    <a id="34734" class="Symbol">→</a> <a id="34736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34615" class="Bound">Γ</a> <a id="34738" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34740" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="34745" href="plfa.part2.Lambda.html#34617" class="Bound">L</a> <a id="34747" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="34754" href="plfa.part2.Lambda.html#34619" class="Bound">M</a> <a id="34756" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="34761" href="plfa.part2.Lambda.html#34621" class="Bound">x</a> <a id="34763" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="34765" href="plfa.part2.Lambda.html#34623" class="Bound">N</a> <a id="34767" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a> <a id="34769" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34771" href="plfa.part2.Lambda.html#34625" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34776" class="InductiveConstructor">⊢μ</a> <a id="34779" class="Symbol">:</a> <a id="34781" class="Symbol">∀</a> <a id="34783" class="Symbol">{</a><a id="34784" href="plfa.part2.Lambda.html#34784" class="Bound">Γ</a> <a id="34786" href="plfa.part2.Lambda.html#34786" class="Bound">x</a> <a id="34788" href="plfa.part2.Lambda.html#34788" class="Bound">M</a> <a id="34790" href="plfa.part2.Lambda.html#34790" class="Bound">A</a><a id="34791" class="Symbol">}</a>
    <a id="34797" class="Symbol">→</a> <a id="34799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34784" class="Bound">Γ</a> <a id="34801" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">,</a> <a id="34803" href="plfa.part2.Lambda.html#34786" class="Bound">x</a> <a id="34805" href="plfa.part2.Lambda.html#31736" class="InductiveConstructor Operator">⦂</a> <a id="34807" href="plfa.part2.Lambda.html#34790" class="Bound">A</a> <a id="34809" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34811" href="plfa.part2.Lambda.html#34788" class="Bound">M</a> <a id="34813" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34815" href="plfa.part2.Lambda.html#34790" class="Bound">A</a>
      <a id="34823" class="Comment">-----------------</a>
    <a id="34845" class="Symbol">→</a> <a id="34847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34784" class="Bound">Γ</a> <a id="34849" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="34851" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">μ</a> <a id="34853" href="plfa.part2.Lambda.html#34786" class="Bound">x</a> <a id="34855" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="34857" href="plfa.part2.Lambda.html#34788" class="Bound">M</a> <a id="34859" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="34861" href="plfa.part2.Lambda.html#34790" class="Bound">A</a>
</pre>{% endraw %}
Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37345" class="Function">Ch</a> <a id="37348" class="Symbol">:</a> <a id="37350" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a> <a id="37355" class="Symbol">→</a> <a id="37357" href="plfa.part2.Lambda.html#30038" class="Datatype">Type</a>
<a id="37362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37345" class="Function">Ch</a> <a id="37365" href="plfa.part2.Lambda.html#37365" class="Bound">A</a> <a id="37367" class="Symbol">=</a> <a id="37369" class="Symbol">(</a><a id="37370" href="plfa.part2.Lambda.html#37365" class="Bound">A</a> <a id="37372" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="37374" href="plfa.part2.Lambda.html#37365" class="Bound">A</a><a id="37375" class="Symbol">)</a> <a id="37377" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="37379" href="plfa.part2.Lambda.html#37365" class="Bound">A</a> <a id="37381" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="37383" href="plfa.part2.Lambda.html#37365" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37386" class="Function">⊢twoᶜ</a> <a id="37392" class="Symbol">:</a> <a id="37394" class="Symbol">∀</a> <a id="37396" class="Symbol">{</a><a id="37397" href="plfa.part2.Lambda.html#37397" class="Bound">Γ</a> <a id="37399" href="plfa.part2.Lambda.html#37399" class="Bound">A</a><a id="37400" class="Symbol">}</a> <a id="37402" class="Symbol">→</a> <a id="37404" href="plfa.part2.Lambda.html#37397" class="Bound">Γ</a> <a id="37406" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="37408" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="37413" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="37415" href="plfa.part2.Lambda.html#37345" class="Function">Ch</a> <a id="37418" href="plfa.part2.Lambda.html#37399" class="Bound">A</a>
<a id="37420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37386" class="Function">⊢twoᶜ</a> <a id="37426" class="Symbol">=</a> <a id="37428" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="37431" class="Symbol">(</a><a id="37432" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="37435" class="Symbol">(</a><a id="37436" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37439" href="plfa.part2.Lambda.html#37472" class="Function">∋s</a> <a id="37442" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37444" class="Symbol">(</a><a id="37445" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37448" href="plfa.part2.Lambda.html#37472" class="Function">∋s</a> <a id="37451" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37453" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37456" href="plfa.part2.Lambda.html#37489" class="Function">∋z</a><a id="37458" class="Symbol">)))</a>
  <a id="37464" class="Keyword">where</a>
  <a id="37472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37472" class="Function">∋s</a> <a id="37475" class="Symbol">=</a> <a id="37477" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37479" class="Symbol">(λ())</a> <a id="37485" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>
  <a id="37489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37489" class="Function">∋z</a> <a id="37492" class="Symbol">=</a> <a id="37494" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37567" class="Function">⊢two</a> <a id="37572" class="Symbol">:</a> <a id="37574" class="Symbol">∀</a> <a id="37576" class="Symbol">{</a><a id="37577" href="plfa.part2.Lambda.html#37577" class="Bound">Γ</a><a id="37578" class="Symbol">}</a> <a id="37580" class="Symbol">→</a> <a id="37582" href="plfa.part2.Lambda.html#37577" class="Bound">Γ</a> <a id="37584" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="37586" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="37590" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="37592" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
<a id="37595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37567" class="Function">⊢two</a> <a id="37600" class="Symbol">=</a> <a id="37602" href="plfa.part2.Lambda.html#34516" class="InductiveConstructor">⊢suc</a> <a id="37607" class="Symbol">(</a><a id="37608" href="plfa.part2.Lambda.html#34516" class="InductiveConstructor">⊢suc</a> <a id="37613" href="plfa.part2.Lambda.html#34447" class="InductiveConstructor">⊢zero</a><a id="37618" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37621" class="Function">⊢plus</a> <a id="37627" class="Symbol">:</a> <a id="37629" class="Symbol">∀</a> <a id="37631" class="Symbol">{</a><a id="37632" href="plfa.part2.Lambda.html#37632" class="Bound">Γ</a><a id="37633" class="Symbol">}</a> <a id="37635" class="Symbol">→</a> <a id="37637" href="plfa.part2.Lambda.html#37632" class="Bound">Γ</a> <a id="37639" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="37641" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="37646" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="37648" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a> <a id="37651" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="37653" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a> <a id="37656" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="37658" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
<a id="37661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37621" class="Function">⊢plus</a> <a id="37667" class="Symbol">=</a> <a id="37669" href="plfa.part2.Lambda.html#34776" class="InductiveConstructor">⊢μ</a> <a id="37672" class="Symbol">(</a><a id="37673" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="37676" class="Symbol">(</a><a id="37677" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="37680" class="Symbol">(</a><a id="37681" href="plfa.part2.Lambda.html#34604" class="InductiveConstructor">⊢case</a> <a id="37687" class="Symbol">(</a><a id="37688" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37691" href="plfa.part2.Lambda.html#37798" class="Function">∋m</a><a id="37693" class="Symbol">)</a> <a id="37695" class="Symbol">(</a><a id="37696" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37699" href="plfa.part2.Lambda.html#37818" class="Function">∋n</a><a id="37701" class="Symbol">)</a>
         <a id="37712" class="Symbol">(</a><a id="37713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34516" class="InductiveConstructor">⊢suc</a> <a id="37718" class="Symbol">(</a><a id="37719" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37722" href="plfa.part2.Lambda.html#37758" class="Function">∋+</a> <a id="37725" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37727" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37730" href="plfa.part2.Lambda.html#37828" class="Function">∋m′</a> <a id="37734" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37736" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="37739" href="plfa.part2.Lambda.html#37838" class="Function">∋n′</a><a id="37742" class="Symbol">)))))</a>
  <a id="37750" class="Keyword">where</a>
  <a id="37758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37758" class="Function">∋+</a>  <a id="37762" class="Symbol">=</a> <a id="37764" class="Symbol">(</a><a id="37765" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37767" class="Symbol">(λ())</a> <a id="37773" class="Symbol">(</a><a id="37774" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37776" class="Symbol">(λ())</a> <a id="37782" class="Symbol">(</a><a id="37783" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37785" class="Symbol">(λ())</a> <a id="37791" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a><a id="37792" class="Symbol">)))</a>
  <a id="37798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37798" class="Function">∋m</a>  <a id="37802" class="Symbol">=</a> <a id="37804" class="Symbol">(</a><a id="37805" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37807" class="Symbol">(λ())</a> <a id="37813" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a><a id="37814" class="Symbol">)</a>
  <a id="37818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37818" class="Function">∋n</a>  <a id="37822" class="Symbol">=</a> <a id="37824" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>
  <a id="37828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37828" class="Function">∋m′</a> <a id="37832" class="Symbol">=</a> <a id="37834" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>
  <a id="37838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37838" class="Function">∋n′</a> <a id="37842" class="Symbol">=</a> <a id="37844" class="Symbol">(</a><a id="37845" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="37847" class="Symbol">(λ())</a> <a id="37853" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a><a id="37854" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="37857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37857" class="Function">⊢2+2</a> <a id="37862" class="Symbol">:</a> <a id="37864" href="plfa.part2.Lambda.html#31718" class="InductiveConstructor">∅</a> <a id="37866" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="37868" href="plfa.part2.Lambda.html#4560" class="Function">plus</a> <a id="37873" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="37875" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="37879" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="37881" href="plfa.part2.Lambda.html#4526" class="Function">two</a> <a id="37885" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="37887" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
<a id="37890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37857" class="Function">⊢2+2</a> <a id="37895" class="Symbol">=</a> <a id="37897" href="plfa.part2.Lambda.html#37621" class="Function">⊢plus</a> <a id="37903" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37905" href="plfa.part2.Lambda.html#37567" class="Function">⊢two</a> <a id="37910" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="37912" href="plfa.part2.Lambda.html#37567" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38559" class="Function">⊢plusᶜ</a> <a id="38566" class="Symbol">:</a> <a id="38568" class="Symbol">∀</a> <a id="38570" class="Symbol">{</a><a id="38571" href="plfa.part2.Lambda.html#38571" class="Bound">Γ</a> <a id="38573" href="plfa.part2.Lambda.html#38573" class="Bound">A</a><a id="38574" class="Symbol">}</a> <a id="38576" class="Symbol">→</a> <a id="38578" href="plfa.part2.Lambda.html#38571" class="Bound">Γ</a>  <a id="38581" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="38583" href="plfa.part2.Lambda.html#5836" class="Function">plusᶜ</a> <a id="38589" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="38591" href="plfa.part2.Lambda.html#37345" class="Function">Ch</a> <a id="38594" href="plfa.part2.Lambda.html#38573" class="Bound">A</a> <a id="38596" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="38598" href="plfa.part2.Lambda.html#37345" class="Function">Ch</a> <a id="38601" href="plfa.part2.Lambda.html#38573" class="Bound">A</a> <a id="38603" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="38605" href="plfa.part2.Lambda.html#37345" class="Function">Ch</a> <a id="38608" href="plfa.part2.Lambda.html#38573" class="Bound">A</a>
<a id="38610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38559" class="Function">⊢plusᶜ</a> <a id="38617" class="Symbol">=</a> <a id="38619" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="38622" class="Symbol">(</a><a id="38623" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="38626" class="Symbol">(</a><a id="38627" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="38630" class="Symbol">(</a><a id="38631" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="38634" class="Symbol">(</a><a id="38635" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38638" href="plfa.part2.Lambda.html#38689" class="Function">∋m</a> <a id="38641" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38643" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38646" href="plfa.part2.Lambda.html#38753" class="Function">∋s</a> <a id="38649" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38651" class="Symbol">(</a><a id="38652" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38655" href="plfa.part2.Lambda.html#38726" class="Function">∋n</a> <a id="38658" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38660" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38663" href="plfa.part2.Lambda.html#38753" class="Function">∋s</a> <a id="38666" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38668" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38671" href="plfa.part2.Lambda.html#38770" class="Function">∋z</a><a id="38673" class="Symbol">)))))</a>
  <a id="38681" class="Keyword">where</a>
  <a id="38689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38689" class="Function">∋m</a> <a id="38692" class="Symbol">=</a> <a id="38694" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38696" class="Symbol">(λ())</a> <a id="38702" class="Symbol">(</a><a id="38703" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38705" class="Symbol">(λ())</a> <a id="38711" class="Symbol">(</a><a id="38712" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38714" class="Symbol">(λ())</a> <a id="38720" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a><a id="38721" class="Symbol">))</a>
  <a id="38726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38726" class="Function">∋n</a> <a id="38729" class="Symbol">=</a> <a id="38731" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38733" class="Symbol">(λ())</a> <a id="38739" class="Symbol">(</a><a id="38740" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38742" class="Symbol">(λ())</a> <a id="38748" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a><a id="38749" class="Symbol">)</a>
  <a id="38753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38753" class="Function">∋s</a> <a id="38756" class="Symbol">=</a> <a id="38758" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="38760" class="Symbol">(λ())</a> <a id="38766" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>
  <a id="38770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38770" class="Function">∋z</a> <a id="38773" class="Symbol">=</a> <a id="38775" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="38778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38778" class="Function">⊢sucᶜ</a> <a id="38784" class="Symbol">:</a> <a id="38786" class="Symbol">∀</a> <a id="38788" class="Symbol">{</a><a id="38789" href="plfa.part2.Lambda.html#38789" class="Bound">Γ</a><a id="38790" class="Symbol">}</a> <a id="38792" class="Symbol">→</a> <a id="38794" href="plfa.part2.Lambda.html#38789" class="Bound">Γ</a> <a id="38796" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="38798" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="38803" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="38805" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a> <a id="38808" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="38810" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
<a id="38813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38778" class="Function">⊢sucᶜ</a> <a id="38819" class="Symbol">=</a> <a id="38821" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="38824" class="Symbol">(</a><a id="38825" href="plfa.part2.Lambda.html#34516" class="InductiveConstructor">⊢suc</a> <a id="38830" class="Symbol">(</a><a id="38831" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="38834" href="plfa.part2.Lambda.html#38849" class="Function">∋n</a><a id="38836" class="Symbol">))</a>
  <a id="38841" class="Keyword">where</a>
  <a id="38849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38849" class="Function">∋n</a> <a id="38852" class="Symbol">=</a> <a id="38854" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="38857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38857" class="Function">⊢2+2ᶜ</a> <a id="38863" class="Symbol">:</a> <a id="38865" href="plfa.part2.Lambda.html#31718" class="InductiveConstructor">∅</a> <a id="38867" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="38869" href="plfa.part2.Lambda.html#5836" class="Function">plusᶜ</a> <a id="38875" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="38877" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="38882" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="38884" href="plfa.part2.Lambda.html#5775" class="Function">twoᶜ</a> <a id="38889" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="38891" href="plfa.part2.Lambda.html#5940" class="Function">sucᶜ</a> <a id="38896" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="38898" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="38904" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="38906" href="plfa.part2.Lambda.html#30084" class="InductiveConstructor">`ℕ</a>
<a id="38909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38857" class="Function">⊢2+2ᶜ</a> <a id="38915" class="Symbol">=</a> <a id="38917" href="plfa.part2.Lambda.html#38559" class="Function">⊢plusᶜ</a> <a id="38924" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38926" href="plfa.part2.Lambda.html#37386" class="Function">⊢twoᶜ</a> <a id="38932" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38934" href="plfa.part2.Lambda.html#37386" class="Function">⊢twoᶜ</a> <a id="38940" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38942" href="plfa.part2.Lambda.html#38778" class="Function">⊢sucᶜ</a> <a id="38948" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="38950" href="plfa.part2.Lambda.html#34447" class="InductiveConstructor">⊢zero</a>
</pre>{% endraw %}
### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference]({{ site.baseurl }}/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40266" class="Function">∋-injective</a> <a id="40278" class="Symbol">:</a> <a id="40280" class="Symbol">∀</a> <a id="40282" class="Symbol">{</a><a id="40283" href="plfa.part2.Lambda.html#40283" class="Bound">Γ</a> <a id="40285" href="plfa.part2.Lambda.html#40285" class="Bound">x</a> <a id="40287" href="plfa.part2.Lambda.html#40287" class="Bound">A</a> <a id="40289" href="plfa.part2.Lambda.html#40289" class="Bound">B</a><a id="40290" class="Symbol">}</a> <a id="40292" class="Symbol">→</a> <a id="40294" href="plfa.part2.Lambda.html#40283" class="Bound">Γ</a> <a id="40296" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="40298" href="plfa.part2.Lambda.html#40285" class="Bound">x</a> <a id="40300" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="40302" href="plfa.part2.Lambda.html#40287" class="Bound">A</a> <a id="40304" class="Symbol">→</a> <a id="40306" href="plfa.part2.Lambda.html#40283" class="Bound">Γ</a> <a id="40308" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">∋</a> <a id="40310" href="plfa.part2.Lambda.html#40285" class="Bound">x</a> <a id="40312" href="plfa.part2.Lambda.html#32930" class="Datatype Operator">⦂</a> <a id="40314" href="plfa.part2.Lambda.html#40289" class="Bound">B</a> <a id="40316" class="Symbol">→</a> <a id="40318" href="plfa.part2.Lambda.html#40287" class="Bound">A</a> <a id="40320" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40322" href="plfa.part2.Lambda.html#40289" class="Bound">B</a>
<a id="40324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40266" class="Function">∋-injective</a> <a id="40336" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>        <a id="40345" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>          <a id="40356" class="Symbol">=</a>  <a id="40359" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40266" class="Function">∋-injective</a> <a id="40376" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>        <a id="40385" class="Symbol">(</a><a id="40386" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="40388" href="plfa.part2.Lambda.html#40388" class="Bound">x≢</a> <a id="40391" class="Symbol">_)</a>   <a id="40396" class="Symbol">=</a>  <a id="40399" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40406" class="Symbol">(</a><a id="40407" href="plfa.part2.Lambda.html#40388" class="Bound">x≢</a> <a id="40410" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40414" class="Symbol">)</a>
<a id="40416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40266" class="Function">∋-injective</a> <a id="40428" class="Symbol">(</a><a id="40429" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="40431" href="plfa.part2.Lambda.html#40431" class="Bound">x≢</a> <a id="40434" class="Symbol">_)</a> <a id="40437" href="plfa.part2.Lambda.html#32973" class="InductiveConstructor">Z</a>          <a id="40448" class="Symbol">=</a>  <a id="40451" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40458" class="Symbol">(</a><a id="40459" href="plfa.part2.Lambda.html#40431" class="Bound">x≢</a> <a id="40462" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40466" class="Symbol">)</a>
<a id="40468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40266" class="Function">∋-injective</a> <a id="40480" class="Symbol">(</a><a id="40481" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="40483" class="Symbol">_</a> <a id="40485" href="plfa.part2.Lambda.html#40485" class="Bound">∋x</a><a id="40487" class="Symbol">)</a> <a id="40489" class="Symbol">(</a><a id="40490" href="plfa.part2.Lambda.html#33039" class="InductiveConstructor">S</a> <a id="40492" class="Symbol">_</a> <a id="40494" href="plfa.part2.Lambda.html#40494" class="Bound">∋x′</a><a id="40497" class="Symbol">)</a>  <a id="40500" class="Symbol">=</a>  <a id="40503" href="plfa.part2.Lambda.html#40266" class="Function">∋-injective</a> <a id="40515" href="plfa.part2.Lambda.html#40485" class="Bound">∋x</a> <a id="40518" href="plfa.part2.Lambda.html#40494" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `` ƛ "x" ⇒ ` "x" `` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="40961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40961" class="Function">nope₁</a> <a id="40967" class="Symbol">:</a> <a id="40969" class="Symbol">∀</a> <a id="40971" class="Symbol">{</a><a id="40972" href="plfa.part2.Lambda.html#40972" class="Bound">A</a><a id="40973" class="Symbol">}</a> <a id="40975" class="Symbol">→</a> <a id="40977" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="40979" class="Symbol">(</a><a id="40980" href="plfa.part2.Lambda.html#31718" class="InductiveConstructor">∅</a> <a id="40982" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="40984" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="40990" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="40992" href="plfa.part2.Lambda.html#3984" class="InductiveConstructor Operator">`suc</a> <a id="40997" href="plfa.part2.Lambda.html#3950" class="InductiveConstructor">`zero</a> <a id="41003" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="41005" href="plfa.part2.Lambda.html#40972" class="Bound">A</a><a id="41006" class="Symbol">)</a>
<a id="41008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40961" class="Function">nope₁</a> <a id="41014" class="Symbol">(()</a> <a id="41018" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="41020" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41225" class="Function">nope₂</a> <a id="41231" class="Symbol">:</a> <a id="41233" class="Symbol">∀</a> <a id="41235" class="Symbol">{</a><a id="41236" href="plfa.part2.Lambda.html#41236" class="Bound">A</a><a id="41237" class="Symbol">}</a> <a id="41239" class="Symbol">→</a> <a id="41241" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41243" class="Symbol">(</a><a id="41244" href="plfa.part2.Lambda.html#31718" class="InductiveConstructor">∅</a> <a id="41246" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="41248" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="41250" class="String">&quot;x&quot;</a> <a id="41254" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="41256" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="41258" class="String">&quot;x&quot;</a> <a id="41262" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="41264" href="plfa.part2.Lambda.html#3817" class="InductiveConstructor Operator">`</a> <a id="41266" class="String">&quot;x&quot;</a> <a id="41270" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="41272" href="plfa.part2.Lambda.html#41236" class="Bound">A</a><a id="41273" class="Symbol">)</a>
<a id="41275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41225" class="Function">nope₂</a> <a id="41281" class="Symbol">(</a><a id="41282" href="plfa.part2.Lambda.html#34231" class="InductiveConstructor">⊢ƛ</a> <a id="41285" class="Symbol">(</a><a id="41286" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="41289" href="plfa.part2.Lambda.html#41289" class="Bound">∋x</a> <a id="41292" href="plfa.part2.Lambda.html#34338" class="InductiveConstructor Operator">·</a> <a id="41294" href="plfa.part2.Lambda.html#34151" class="InductiveConstructor">⊢`</a> <a id="41297" href="plfa.part2.Lambda.html#41297" class="Bound">∋x′</a><a id="41300" class="Symbol">))</a>  <a id="41304" class="Symbol">=</a>  <a id="41307" href="plfa.part2.Lambda.html#41352" class="Function">contradiction</a> <a id="41321" class="Symbol">(</a><a id="41322" href="plfa.part2.Lambda.html#40266" class="Function">∋-injective</a> <a id="41334" href="plfa.part2.Lambda.html#41289" class="Bound">∋x</a> <a id="41337" href="plfa.part2.Lambda.html#41297" class="Bound">∋x′</a><a id="41340" class="Symbol">)</a>
  <a id="41344" class="Keyword">where</a>
  <a id="41352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41352" class="Function">contradiction</a> <a id="41366" class="Symbol">:</a> <a id="41368" class="Symbol">∀</a> <a id="41370" class="Symbol">{</a><a id="41371" href="plfa.part2.Lambda.html#41371" class="Bound">A</a> <a id="41373" href="plfa.part2.Lambda.html#41373" class="Bound">B</a><a id="41374" class="Symbol">}</a> <a id="41376" class="Symbol">→</a> <a id="41378" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41380" class="Symbol">(</a><a id="41381" href="plfa.part2.Lambda.html#41371" class="Bound">A</a> <a id="41383" href="plfa.part2.Lambda.html#30057" class="InductiveConstructor Operator">⇒</a> <a id="41385" href="plfa.part2.Lambda.html#41373" class="Bound">B</a> <a id="41387" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41389" href="plfa.part2.Lambda.html#41371" class="Bound">A</a><a id="41390" class="Symbol">)</a>
  <a id="41394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41352" class="Function">contradiction</a> <a id="41408" class="Symbol">()</a>
</pre>{% endraw %}

#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `⊢mul` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42083" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊢mulᶜ` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42250" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
