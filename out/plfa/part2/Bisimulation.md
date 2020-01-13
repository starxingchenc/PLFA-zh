---
src       : "src/plfa/part2/Bisimulation.lagda.md"
title     : "Bisimulation: Relating reduction systems"
layout    : page
prev      : /More/
permalink : /Bisimulation/
next      : /Inference/
---

{% raw %}<pre class="Agda"><a id="156" class="Keyword">module</a> <a id="163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}" class="Module">plfa.part2.Bisimulation</a> <a id="187" class="Keyword">where</a>
</pre>{% endraw %}
Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More]({{ site.baseurl }}/More/):
{% raw %}<pre class="Agda"><a id="3625" class="Keyword">open</a> <a id="3630" class="Keyword">import</a> <a id="3637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}" class="Module">plfa.part2.More</a>
</pre>{% endraw %}

## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
{% raw %}<pre class="Agda"><a id="3762" class="Keyword">infix</a>  <a id="3769" class="Number">4</a> <a id="3771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3808" class="Datatype Operator">_~_</a>
<a id="3775" class="Keyword">infix</a>  <a id="3782" class="Number">5</a> <a id="3784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3915" class="InductiveConstructor Operator">~ƛ_</a>
<a id="3788" class="Keyword">infix</a>  <a id="3795" class="Number">7</a> <a id="3797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4000" class="InductiveConstructor Operator">_~·_</a>

<a id="3803" class="Keyword">data</a> <a id="_~_"></a><a id="3808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3808" class="Datatype Operator">_~_</a> <a id="3812" class="Symbol">:</a> <a id="3814" class="Symbol">∀</a> <a id="3816" class="Symbol">{</a><a id="3817" href="plfa.part2.Bisimulation.html#3817" class="Bound">Γ</a> <a id="3819" href="plfa.part2.Bisimulation.html#3819" class="Bound">A</a><a id="3820" class="Symbol">}</a> <a id="3822" class="Symbol">→</a> <a id="3824" class="Symbol">(</a><a id="3825" href="plfa.part2.Bisimulation.html#3817" class="Bound">Γ</a> <a id="3827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="3829" href="plfa.part2.Bisimulation.html#3819" class="Bound">A</a><a id="3830" class="Symbol">)</a> <a id="3832" class="Symbol">→</a> <a id="3834" class="Symbol">(</a><a id="3835" href="plfa.part2.Bisimulation.html#3817" class="Bound">Γ</a> <a id="3837" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="3839" href="plfa.part2.Bisimulation.html#3819" class="Bound">A</a><a id="3840" class="Symbol">)</a> <a id="3842" class="Symbol">→</a> <a id="3844" class="PrimitiveType">Set</a> <a id="3848" class="Keyword">where</a>

  <a id="_~_.~`"></a><a id="3857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3857" class="InductiveConstructor">~`</a> <a id="3860" class="Symbol">:</a> <a id="3862" class="Symbol">∀</a> <a id="3864" class="Symbol">{</a><a id="3865" href="plfa.part2.Bisimulation.html#3865" class="Bound">Γ</a> <a id="3867" href="plfa.part2.Bisimulation.html#3867" class="Bound">A</a><a id="3868" class="Symbol">}</a> <a id="3870" class="Symbol">{</a><a id="3871" href="plfa.part2.Bisimulation.html#3871" class="Bound">x</a> <a id="3873" class="Symbol">:</a> <a id="3875" href="plfa.part2.Bisimulation.html#3865" class="Bound">Γ</a> <a id="3877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="3879" href="plfa.part2.Bisimulation.html#3867" class="Bound">A</a><a id="3880" class="Symbol">}</a>
     <a id="3887" class="Comment">---------</a>
   <a id="3900" class="Symbol">→</a> <a id="3902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14967" class="InductiveConstructor Operator">`</a> <a id="3904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3871" class="Bound">x</a> <a id="3906" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="3908" href="plfa.part2.More.html#14967" class="InductiveConstructor Operator">`</a> <a id="3910" href="plfa.part2.Bisimulation.html#3871" class="Bound">x</a>

  <a id="_~_.~ƛ_"></a><a id="3915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3915" class="InductiveConstructor Operator">~ƛ_</a> <a id="3919" class="Symbol">:</a> <a id="3921" class="Symbol">∀</a> <a id="3923" class="Symbol">{</a><a id="3924" href="plfa.part2.Bisimulation.html#3924" class="Bound">Γ</a> <a id="3926" href="plfa.part2.Bisimulation.html#3926" class="Bound">A</a> <a id="3928" href="plfa.part2.Bisimulation.html#3928" class="Bound">B</a><a id="3929" class="Symbol">}</a> <a id="3931" class="Symbol">{</a><a id="3932" href="plfa.part2.Bisimulation.html#3932" class="Bound">N</a> <a id="3934" href="plfa.part2.Bisimulation.html#3934" class="Bound">N†</a> <a id="3937" class="Symbol">:</a> <a id="3939" href="plfa.part2.Bisimulation.html#3924" class="Bound">Γ</a> <a id="3941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14640" class="InductiveConstructor Operator">,</a> <a id="3943" href="plfa.part2.Bisimulation.html#3926" class="Bound">A</a> <a id="3945" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="3947" href="plfa.part2.Bisimulation.html#3928" class="Bound">B</a><a id="3948" class="Symbol">}</a>
    <a id="3954" class="Symbol">→</a> <a id="3956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3932" class="Bound">N</a> <a id="3958" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="3960" href="plfa.part2.Bisimulation.html#3934" class="Bound">N†</a>
      <a id="3969" class="Comment">----------</a>
    <a id="3984" class="Symbol">→</a> <a id="3986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#15035" class="InductiveConstructor Operator">ƛ</a> <a id="3988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#3932" class="Bound">N</a> <a id="3990" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="3992" href="plfa.part2.More.html#15035" class="InductiveConstructor Operator">ƛ</a> <a id="3994" href="plfa.part2.Bisimulation.html#3934" class="Bound">N†</a>

  <a id="_~_._~·_"></a><a id="4000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4000" class="InductiveConstructor Operator">_~·_</a> <a id="4005" class="Symbol">:</a> <a id="4007" class="Symbol">∀</a> <a id="4009" class="Symbol">{</a><a id="4010" href="plfa.part2.Bisimulation.html#4010" class="Bound">Γ</a> <a id="4012" href="plfa.part2.Bisimulation.html#4012" class="Bound">A</a> <a id="4014" href="plfa.part2.Bisimulation.html#4014" class="Bound">B</a><a id="4015" class="Symbol">}</a> <a id="4017" class="Symbol">{</a><a id="4018" href="plfa.part2.Bisimulation.html#4018" class="Bound">L</a> <a id="4020" href="plfa.part2.Bisimulation.html#4020" class="Bound">L†</a> <a id="4023" class="Symbol">:</a> <a id="4025" href="plfa.part2.Bisimulation.html#4010" class="Bound">Γ</a> <a id="4027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="4029" href="plfa.part2.Bisimulation.html#4012" class="Bound">A</a> <a id="4031" href="plfa.part2.More.html#14503" class="InductiveConstructor Operator">⇒</a> <a id="4033" href="plfa.part2.Bisimulation.html#4014" class="Bound">B</a><a id="4034" class="Symbol">}</a> <a id="4036" class="Symbol">{</a><a id="4037" href="plfa.part2.Bisimulation.html#4037" class="Bound">M</a> <a id="4039" href="plfa.part2.Bisimulation.html#4039" class="Bound">M†</a> <a id="4042" class="Symbol">:</a> <a id="4044" href="plfa.part2.Bisimulation.html#4010" class="Bound">Γ</a> <a id="4046" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="4048" href="plfa.part2.Bisimulation.html#4012" class="Bound">A</a><a id="4049" class="Symbol">}</a>
    <a id="4055" class="Symbol">→</a> <a id="4057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4018" class="Bound">L</a> <a id="4059" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4061" href="plfa.part2.Bisimulation.html#4020" class="Bound">L†</a>
    <a id="4068" class="Symbol">→</a> <a id="4070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4037" class="Bound">M</a> <a id="4072" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4074" href="plfa.part2.Bisimulation.html#4039" class="Bound">M†</a>
      <a id="4083" class="Comment">---------------</a>
    <a id="4103" class="Symbol">→</a> <a id="4105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4018" class="Bound">L</a> <a id="4107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#15103" class="InductiveConstructor Operator">·</a> <a id="4109" href="plfa.part2.Bisimulation.html#4037" class="Bound">M</a> <a id="4111" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4113" href="plfa.part2.Bisimulation.html#4020" class="Bound">L†</a> <a id="4116" href="plfa.part2.More.html#15103" class="InductiveConstructor Operator">·</a> <a id="4118" href="plfa.part2.Bisimulation.html#4039" class="Bound">M†</a>

  <a id="_~_.~let"></a><a id="4124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4124" class="InductiveConstructor">~let</a> <a id="4129" class="Symbol">:</a> <a id="4131" class="Symbol">∀</a> <a id="4133" class="Symbol">{</a><a id="4134" href="plfa.part2.Bisimulation.html#4134" class="Bound">Γ</a> <a id="4136" href="plfa.part2.Bisimulation.html#4136" class="Bound">A</a> <a id="4138" href="plfa.part2.Bisimulation.html#4138" class="Bound">B</a><a id="4139" class="Symbol">}</a> <a id="4141" class="Symbol">{</a><a id="4142" href="plfa.part2.Bisimulation.html#4142" class="Bound">M</a> <a id="4144" href="plfa.part2.Bisimulation.html#4144" class="Bound">M†</a> <a id="4147" class="Symbol">:</a> <a id="4149" href="plfa.part2.Bisimulation.html#4134" class="Bound">Γ</a> <a id="4151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="4153" href="plfa.part2.Bisimulation.html#4136" class="Bound">A</a><a id="4154" class="Symbol">}</a> <a id="4156" class="Symbol">{</a><a id="4157" href="plfa.part2.Bisimulation.html#4157" class="Bound">N</a> <a id="4159" href="plfa.part2.Bisimulation.html#4159" class="Bound">N†</a> <a id="4162" class="Symbol">:</a> <a id="4164" href="plfa.part2.Bisimulation.html#4134" class="Bound">Γ</a> <a id="4166" href="plfa.part2.More.html#14640" class="InductiveConstructor Operator">,</a> <a id="4168" href="plfa.part2.Bisimulation.html#4136" class="Bound">A</a> <a id="4170" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="4172" href="plfa.part2.Bisimulation.html#4138" class="Bound">B</a><a id="4173" class="Symbol">}</a>
    <a id="4179" class="Symbol">→</a> <a id="4181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4142" class="Bound">M</a> <a id="4183" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4185" href="plfa.part2.Bisimulation.html#4144" class="Bound">M†</a>
    <a id="4192" class="Symbol">→</a> <a id="4194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4157" class="Bound">N</a> <a id="4196" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4198" href="plfa.part2.Bisimulation.html#4159" class="Bound">N†</a>
      <a id="4207" class="Comment">----------------------</a>
    <a id="4234" class="Symbol">→</a> <a id="4236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#15609" class="InductiveConstructor">`let</a> <a id="4241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4142" class="Bound">M</a> <a id="4243" href="plfa.part2.Bisimulation.html#4157" class="Bound">N</a> <a id="4245" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="4247" class="Symbol">(</a><a id="4248" href="plfa.part2.More.html#15035" class="InductiveConstructor Operator">ƛ</a> <a id="4250" href="plfa.part2.Bisimulation.html#4159" class="Bound">N†</a><a id="4252" class="Symbol">)</a> <a id="4254" href="plfa.part2.More.html#15103" class="InductiveConstructor Operator">·</a> <a id="4256" href="plfa.part2.Bisimulation.html#4144" class="Bound">M†</a>
</pre>{% endraw %}The language in Chapter [More]({{ site.baseurl }}/More/) has more constructs, which we could easily add.
However, leaving the simulation small let's us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†` (practice)

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

{% raw %}<pre class="Agda"><a id="4741" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
{% raw %}<pre class="Agda"><a id="~val"></a><a id="4968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4968" class="Function">~val</a> <a id="4973" class="Symbol">:</a> <a id="4975" class="Symbol">∀</a> <a id="4977" class="Symbol">{</a><a id="4978" href="plfa.part2.Bisimulation.html#4978" class="Bound">Γ</a> <a id="4980" href="plfa.part2.Bisimulation.html#4980" class="Bound">A</a><a id="4981" class="Symbol">}</a> <a id="4983" class="Symbol">{</a><a id="4984" href="plfa.part2.Bisimulation.html#4984" class="Bound">M</a> <a id="4986" href="plfa.part2.Bisimulation.html#4986" class="Bound">M†</a> <a id="4989" class="Symbol">:</a> <a id="4991" href="plfa.part2.Bisimulation.html#4978" class="Bound">Γ</a> <a id="4993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="4995" href="plfa.part2.Bisimulation.html#4980" class="Bound">A</a><a id="4996" class="Symbol">}</a>
  <a id="5000" class="Symbol">→</a> <a id="5002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4984" class="Bound">M</a> <a id="5004" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="5006" href="plfa.part2.Bisimulation.html#4986" class="Bound">M†</a>
  <a id="5011" class="Symbol">→</a> <a id="5013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#18854" class="Datatype">Value</a> <a id="5019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4984" class="Bound">M</a>
    <a id="5025" class="Comment">--------</a>
  <a id="5036" class="Symbol">→</a> <a id="5038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#18854" class="Datatype">Value</a> <a id="5044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4986" class="Bound">M†</a>
<a id="5047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4968" class="Function">~val</a> <a id="5052" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a>           <a id="5065" class="Symbol">()</a>
<a id="5068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4968" class="Function">~val</a> <a id="5073" class="Symbol">(</a><a id="5074" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="5077" href="plfa.part2.Bisimulation.html#5077" class="Bound">~N</a><a id="5079" class="Symbol">)</a>      <a id="5086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#18909" class="InductiveConstructor">V-ƛ</a>  <a id="5091" class="Symbol">=</a>  <a id="5094" href="plfa.part2.More.html#18909" class="InductiveConstructor">V-ƛ</a>
<a id="5098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4968" class="Function">~val</a> <a id="5103" class="Symbol">(</a><a id="5104" href="plfa.part2.Bisimulation.html#5104" class="Bound">~L</a> <a id="5107" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="5110" href="plfa.part2.Bisimulation.html#5110" class="Bound">~M</a><a id="5112" class="Symbol">)</a>   <a id="5116" class="Symbol">()</a>
<a id="5119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#4968" class="Function">~val</a> <a id="5124" class="Symbol">(</a><a id="5125" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="5130" href="plfa.part2.Bisimulation.html#5130" class="Bound">~M</a> <a id="5133" href="plfa.part2.Bisimulation.html#5133" class="Bound">~N</a><a id="5135" class="Symbol">)</a> <a id="5137" class="Symbol">()</a>
</pre>{% endraw %}It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹` (practice)

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

{% raw %}<pre class="Agda"><a id="5382" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

{% raw %}<pre class="Agda"><a id="~rename"></a><a id="5637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5637" class="Function">~rename</a> <a id="5645" class="Symbol">:</a> <a id="5647" class="Symbol">∀</a> <a id="5649" class="Symbol">{</a><a id="5650" href="plfa.part2.Bisimulation.html#5650" class="Bound">Γ</a> <a id="5652" href="plfa.part2.Bisimulation.html#5652" class="Bound">Δ</a><a id="5653" class="Symbol">}</a>
  <a id="5657" class="Symbol">→</a> <a id="5659" class="Symbol">(</a><a id="5660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5660" class="Bound">ρ</a> <a id="5662" class="Symbol">:</a> <a id="5664" class="Symbol">∀</a> <a id="5666" class="Symbol">{</a><a id="5667" href="plfa.part2.Bisimulation.html#5667" class="Bound">A</a><a id="5668" class="Symbol">}</a> <a id="5670" class="Symbol">→</a> <a id="5672" href="plfa.part2.Bisimulation.html#5650" class="Bound">Γ</a> <a id="5674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="5676" href="plfa.part2.Bisimulation.html#5667" class="Bound">A</a> <a id="5678" class="Symbol">→</a> <a id="5680" href="plfa.part2.Bisimulation.html#5652" class="Bound">Δ</a> <a id="5682" href="plfa.part2.More.html#14724" class="Datatype Operator">∋</a> <a id="5684" href="plfa.part2.Bisimulation.html#5667" class="Bound">A</a><a id="5685" class="Symbol">)</a>
    <a id="5691" class="Comment">----------------------------------------------------------</a>
  <a id="5752" class="Symbol">→</a> <a id="5754" class="Symbol">(∀</a> <a id="5757" class="Symbol">{</a><a id="5758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5758" class="Bound">A</a><a id="5759" class="Symbol">}</a> <a id="5761" class="Symbol">{</a><a id="5762" href="plfa.part2.Bisimulation.html#5762" class="Bound">M</a> <a id="5764" href="plfa.part2.Bisimulation.html#5764" class="Bound">M†</a> <a id="5767" class="Symbol">:</a> <a id="5769" href="plfa.part2.Bisimulation.html#5650" class="Bound">Γ</a> <a id="5771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="5773" href="plfa.part2.Bisimulation.html#5758" class="Bound">A</a><a id="5774" class="Symbol">}</a> <a id="5776" class="Symbol">→</a> <a id="5778" href="plfa.part2.Bisimulation.html#5762" class="Bound">M</a> <a id="5780" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="5782" href="plfa.part2.Bisimulation.html#5764" class="Bound">M†</a> <a id="5785" class="Symbol">→</a> <a id="5787" href="plfa.part2.More.html#16654" class="Function">rename</a> <a id="5794" href="plfa.part2.Bisimulation.html#5660" class="Bound">ρ</a> <a id="5796" href="plfa.part2.Bisimulation.html#5762" class="Bound">M</a> <a id="5798" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="5800" href="plfa.part2.More.html#16654" class="Function">rename</a> <a id="5807" href="plfa.part2.Bisimulation.html#5660" class="Bound">ρ</a> <a id="5809" href="plfa.part2.Bisimulation.html#5764" class="Bound">M†</a><a id="5811" class="Symbol">)</a>
<a id="5813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5637" class="Function">~rename</a> <a id="5821" href="plfa.part2.Bisimulation.html#5821" class="Bound">ρ</a> <a id="5823" class="Symbol">(</a><a id="5824" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a><a id="5826" class="Symbol">)</a>          <a id="5837" class="Symbol">=</a>  <a id="5840" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a>
<a id="5843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5637" class="Function">~rename</a> <a id="5851" href="plfa.part2.Bisimulation.html#5851" class="Bound">ρ</a> <a id="5853" class="Symbol">(</a><a id="5854" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="5857" href="plfa.part2.Bisimulation.html#5857" class="Bound">~N</a><a id="5859" class="Symbol">)</a>       <a id="5867" class="Symbol">=</a>  <a id="5870" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="5873" class="Symbol">(</a><a id="5874" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="5882" class="Symbol">(</a><a id="5883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#16535" class="Function">ext</a> <a id="5887" href="plfa.part2.Bisimulation.html#5851" class="Bound">ρ</a><a id="5888" class="Symbol">)</a> <a id="5890" href="plfa.part2.Bisimulation.html#5857" class="Bound">~N</a><a id="5892" class="Symbol">)</a>
<a id="5894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5637" class="Function">~rename</a> <a id="5902" href="plfa.part2.Bisimulation.html#5902" class="Bound">ρ</a> <a id="5904" class="Symbol">(</a><a id="5905" href="plfa.part2.Bisimulation.html#5905" class="Bound">~L</a> <a id="5908" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="5911" href="plfa.part2.Bisimulation.html#5911" class="Bound">~M</a><a id="5913" class="Symbol">)</a>    <a id="5918" class="Symbol">=</a>  <a id="5921" class="Symbol">(</a><a id="5922" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="5930" href="plfa.part2.Bisimulation.html#5902" class="Bound">ρ</a> <a id="5932" href="plfa.part2.Bisimulation.html#5905" class="Bound">~L</a><a id="5934" class="Symbol">)</a> <a id="5936" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="5939" class="Symbol">(</a><a id="5940" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="5948" href="plfa.part2.Bisimulation.html#5902" class="Bound">ρ</a> <a id="5950" href="plfa.part2.Bisimulation.html#5911" class="Bound">~M</a><a id="5952" class="Symbol">)</a>
<a id="5954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#5637" class="Function">~rename</a> <a id="5962" href="plfa.part2.Bisimulation.html#5962" class="Bound">ρ</a> <a id="5964" class="Symbol">(</a><a id="5965" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="5970" href="plfa.part2.Bisimulation.html#5970" class="Bound">~M</a> <a id="5973" href="plfa.part2.Bisimulation.html#5973" class="Bound">~N</a><a id="5975" class="Symbol">)</a>  <a id="5978" class="Symbol">=</a>  <a id="5981" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="5986" class="Symbol">(</a><a id="5987" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="5995" href="plfa.part2.Bisimulation.html#5962" class="Bound">ρ</a> <a id="5997" href="plfa.part2.Bisimulation.html#5970" class="Bound">~M</a><a id="5999" class="Symbol">)</a> <a id="6001" class="Symbol">(</a><a id="6002" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="6010" class="Symbol">(</a><a id="6011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#16535" class="Function">ext</a> <a id="6015" href="plfa.part2.Bisimulation.html#5962" class="Bound">ρ</a><a id="6016" class="Symbol">)</a> <a id="6018" href="plfa.part2.Bisimulation.html#5973" class="Bound">~N</a><a id="6020" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
{% raw %}<pre class="Agda"><a id="~exts"></a><a id="6750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6750" class="Function">~exts</a> <a id="6756" class="Symbol">:</a> <a id="6758" class="Symbol">∀</a> <a id="6760" class="Symbol">{</a><a id="6761" href="plfa.part2.Bisimulation.html#6761" class="Bound">Γ</a> <a id="6763" href="plfa.part2.Bisimulation.html#6763" class="Bound">Δ</a><a id="6764" class="Symbol">}</a>
  <a id="6768" class="Symbol">→</a> <a id="6770" class="Symbol">{</a><a id="6771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6771" class="Bound">σ</a>  <a id="6774" class="Symbol">:</a> <a id="6776" class="Symbol">∀</a> <a id="6778" class="Symbol">{</a><a id="6779" href="plfa.part2.Bisimulation.html#6779" class="Bound">A</a><a id="6780" class="Symbol">}</a> <a id="6782" class="Symbol">→</a> <a id="6784" href="plfa.part2.Bisimulation.html#6761" class="Bound">Γ</a> <a id="6786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="6788" href="plfa.part2.Bisimulation.html#6779" class="Bound">A</a> <a id="6790" class="Symbol">→</a> <a id="6792" href="plfa.part2.Bisimulation.html#6763" class="Bound">Δ</a> <a id="6794" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="6796" href="plfa.part2.Bisimulation.html#6779" class="Bound">A</a><a id="6797" class="Symbol">}</a>
  <a id="6801" class="Symbol">→</a> <a id="6803" class="Symbol">{</a><a id="6804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6804" class="Bound">σ†</a> <a id="6807" class="Symbol">:</a> <a id="6809" class="Symbol">∀</a> <a id="6811" class="Symbol">{</a><a id="6812" href="plfa.part2.Bisimulation.html#6812" class="Bound">A</a><a id="6813" class="Symbol">}</a> <a id="6815" class="Symbol">→</a> <a id="6817" href="plfa.part2.Bisimulation.html#6761" class="Bound">Γ</a> <a id="6819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="6821" href="plfa.part2.Bisimulation.html#6812" class="Bound">A</a> <a id="6823" class="Symbol">→</a> <a id="6825" href="plfa.part2.Bisimulation.html#6763" class="Bound">Δ</a> <a id="6827" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="6829" href="plfa.part2.Bisimulation.html#6812" class="Bound">A</a><a id="6830" class="Symbol">}</a>
  <a id="6834" class="Symbol">→</a> <a id="6836" class="Symbol">(∀</a> <a id="6839" class="Symbol">{</a><a id="6840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6840" class="Bound">A</a><a id="6841" class="Symbol">}</a> <a id="6843" class="Symbol">→</a> <a id="6845" class="Symbol">(</a><a id="6846" href="plfa.part2.Bisimulation.html#6846" class="Bound">x</a> <a id="6848" class="Symbol">:</a> <a id="6850" href="plfa.part2.Bisimulation.html#6761" class="Bound">Γ</a> <a id="6852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="6854" href="plfa.part2.Bisimulation.html#6840" class="Bound">A</a><a id="6855" class="Symbol">)</a> <a id="6857" class="Symbol">→</a> <a id="6859" href="plfa.part2.Bisimulation.html#6771" class="Bound">σ</a> <a id="6861" href="plfa.part2.Bisimulation.html#6846" class="Bound">x</a> <a id="6863" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="6865" href="plfa.part2.Bisimulation.html#6804" class="Bound">σ†</a> <a id="6868" href="plfa.part2.Bisimulation.html#6846" class="Bound">x</a><a id="6869" class="Symbol">)</a>
    <a id="6875" class="Comment">--------------------------------------------------</a>
  <a id="6928" class="Symbol">→</a> <a id="6930" class="Symbol">(∀</a> <a id="6933" class="Symbol">{</a><a id="6934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6934" class="Bound">A</a> <a id="6936" href="plfa.part2.Bisimulation.html#6936" class="Bound">B</a><a id="6937" class="Symbol">}</a> <a id="6939" class="Symbol">→</a> <a id="6941" class="Symbol">(</a><a id="6942" href="plfa.part2.Bisimulation.html#6942" class="Bound">x</a> <a id="6944" class="Symbol">:</a> <a id="6946" href="plfa.part2.Bisimulation.html#6761" class="Bound">Γ</a> <a id="6948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14640" class="InductiveConstructor Operator">,</a> <a id="6950" href="plfa.part2.Bisimulation.html#6936" class="Bound">B</a> <a id="6952" href="plfa.part2.More.html#14724" class="Datatype Operator">∋</a> <a id="6954" href="plfa.part2.Bisimulation.html#6934" class="Bound">A</a><a id="6955" class="Symbol">)</a> <a id="6957" class="Symbol">→</a> <a id="6959" href="plfa.part2.More.html#17473" class="Function">exts</a> <a id="6964" href="plfa.part2.Bisimulation.html#6771" class="Bound">σ</a> <a id="6966" href="plfa.part2.Bisimulation.html#6942" class="Bound">x</a> <a id="6968" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="6970" href="plfa.part2.More.html#17473" class="Function">exts</a> <a id="6975" href="plfa.part2.Bisimulation.html#6804" class="Bound">σ†</a> <a id="6978" href="plfa.part2.Bisimulation.html#6942" class="Bound">x</a><a id="6979" class="Symbol">)</a>
<a id="6981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6750" class="Function">~exts</a> <a id="6987" href="plfa.part2.Bisimulation.html#6987" class="Bound">~σ</a> <a id="6990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14760" class="InductiveConstructor">Z</a>      <a id="6997" class="Symbol">=</a>  <a id="7000" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a>
<a id="7003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#6750" class="Function">~exts</a> <a id="7009" href="plfa.part2.Bisimulation.html#7009" class="Bound">~σ</a> <a id="7012" class="Symbol">(</a><a id="7013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14807" class="InductiveConstructor Operator">S</a> <a id="7015" href="plfa.part2.Bisimulation.html#7015" class="Bound">x</a><a id="7016" class="Symbol">)</a>  <a id="7019" class="Symbol">=</a>  <a id="7022" href="plfa.part2.Bisimulation.html#5637" class="Function">~rename</a> <a id="7030" href="plfa.part2.More.html#14807" class="InductiveConstructor Operator">S_</a> <a id="7033" class="Symbol">(</a><a id="7034" href="plfa.part2.Bisimulation.html#7009" class="Bound">~σ</a> <a id="7037" href="plfa.part2.Bisimulation.html#7015" class="Bound">x</a><a id="7038" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
{% raw %}<pre class="Agda"><a id="~subst"></a><a id="7496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7496" class="Function">~subst</a> <a id="7503" class="Symbol">:</a> <a id="7505" class="Symbol">∀</a> <a id="7507" class="Symbol">{</a><a id="7508" href="plfa.part2.Bisimulation.html#7508" class="Bound">Γ</a> <a id="7510" href="plfa.part2.Bisimulation.html#7510" class="Bound">Δ</a><a id="7511" class="Symbol">}</a>
  <a id="7515" class="Symbol">→</a> <a id="7517" class="Symbol">{</a><a id="7518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7518" class="Bound">σ</a>  <a id="7521" class="Symbol">:</a> <a id="7523" class="Symbol">∀</a> <a id="7525" class="Symbol">{</a><a id="7526" href="plfa.part2.Bisimulation.html#7526" class="Bound">A</a><a id="7527" class="Symbol">}</a> <a id="7529" class="Symbol">→</a> <a id="7531" href="plfa.part2.Bisimulation.html#7508" class="Bound">Γ</a> <a id="7533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="7535" href="plfa.part2.Bisimulation.html#7526" class="Bound">A</a> <a id="7537" class="Symbol">→</a> <a id="7539" href="plfa.part2.Bisimulation.html#7510" class="Bound">Δ</a> <a id="7541" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="7543" href="plfa.part2.Bisimulation.html#7526" class="Bound">A</a><a id="7544" class="Symbol">}</a>
  <a id="7548" class="Symbol">→</a> <a id="7550" class="Symbol">{</a><a id="7551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7551" class="Bound">σ†</a> <a id="7554" class="Symbol">:</a> <a id="7556" class="Symbol">∀</a> <a id="7558" class="Symbol">{</a><a id="7559" href="plfa.part2.Bisimulation.html#7559" class="Bound">A</a><a id="7560" class="Symbol">}</a> <a id="7562" class="Symbol">→</a> <a id="7564" href="plfa.part2.Bisimulation.html#7508" class="Bound">Γ</a> <a id="7566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="7568" href="plfa.part2.Bisimulation.html#7559" class="Bound">A</a> <a id="7570" class="Symbol">→</a> <a id="7572" href="plfa.part2.Bisimulation.html#7510" class="Bound">Δ</a> <a id="7574" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="7576" href="plfa.part2.Bisimulation.html#7559" class="Bound">A</a><a id="7577" class="Symbol">}</a>
  <a id="7581" class="Symbol">→</a> <a id="7583" class="Symbol">(∀</a> <a id="7586" class="Symbol">{</a><a id="7587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7587" class="Bound">A</a><a id="7588" class="Symbol">}</a> <a id="7590" class="Symbol">→</a> <a id="7592" class="Symbol">(</a><a id="7593" href="plfa.part2.Bisimulation.html#7593" class="Bound">x</a> <a id="7595" class="Symbol">:</a> <a id="7597" href="plfa.part2.Bisimulation.html#7508" class="Bound">Γ</a> <a id="7599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14724" class="Datatype Operator">∋</a> <a id="7601" href="plfa.part2.Bisimulation.html#7587" class="Bound">A</a><a id="7602" class="Symbol">)</a> <a id="7604" class="Symbol">→</a> <a id="7606" href="plfa.part2.Bisimulation.html#7518" class="Bound">σ</a> <a id="7608" href="plfa.part2.Bisimulation.html#7593" class="Bound">x</a> <a id="7610" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="7612" href="plfa.part2.Bisimulation.html#7551" class="Bound">σ†</a> <a id="7615" href="plfa.part2.Bisimulation.html#7593" class="Bound">x</a><a id="7616" class="Symbol">)</a>
    <a id="7622" class="Comment">---------------------------------------------------------</a>
  <a id="7682" class="Symbol">→</a> <a id="7684" class="Symbol">(∀</a> <a id="7687" class="Symbol">{</a><a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7688" class="Bound">A</a><a id="7689" class="Symbol">}</a> <a id="7691" class="Symbol">{</a><a id="7692" href="plfa.part2.Bisimulation.html#7692" class="Bound">M</a> <a id="7694" href="plfa.part2.Bisimulation.html#7694" class="Bound">M†</a> <a id="7697" class="Symbol">:</a> <a id="7699" href="plfa.part2.Bisimulation.html#7508" class="Bound">Γ</a> <a id="7701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="7703" href="plfa.part2.Bisimulation.html#7688" class="Bound">A</a><a id="7704" class="Symbol">}</a> <a id="7706" class="Symbol">→</a> <a id="7708" href="plfa.part2.Bisimulation.html#7692" class="Bound">M</a> <a id="7710" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="7712" href="plfa.part2.Bisimulation.html#7694" class="Bound">M†</a> <a id="7715" class="Symbol">→</a> <a id="7717" href="plfa.part2.More.html#17605" class="Function">subst</a> <a id="7723" href="plfa.part2.Bisimulation.html#7518" class="Bound">σ</a> <a id="7725" href="plfa.part2.Bisimulation.html#7692" class="Bound">M</a> <a id="7727" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="7729" href="plfa.part2.More.html#17605" class="Function">subst</a> <a id="7735" href="plfa.part2.Bisimulation.html#7551" class="Bound">σ†</a> <a id="7738" href="plfa.part2.Bisimulation.html#7694" class="Bound">M†</a><a id="7740" class="Symbol">)</a>
<a id="7742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7496" class="Function">~subst</a> <a id="7749" href="plfa.part2.Bisimulation.html#7749" class="Bound">~σ</a> <a id="7752" class="Symbol">(</a><a id="7753" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a> <a id="7756" class="Symbol">{</a><a id="7757" class="Argument">x</a> <a id="7759" class="Symbol">=</a> <a id="7761" href="plfa.part2.Bisimulation.html#7761" class="Bound">x</a><a id="7762" class="Symbol">})</a>  <a id="7766" class="Symbol">=</a>  <a id="7769" href="plfa.part2.Bisimulation.html#7749" class="Bound">~σ</a> <a id="7772" href="plfa.part2.Bisimulation.html#7761" class="Bound">x</a>
<a id="7774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7496" class="Function">~subst</a> <a id="7781" href="plfa.part2.Bisimulation.html#7781" class="Bound">~σ</a> <a id="7784" class="Symbol">(</a><a id="7785" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="7788" href="plfa.part2.Bisimulation.html#7788" class="Bound">~N</a><a id="7790" class="Symbol">)</a>       <a id="7798" class="Symbol">=</a>  <a id="7801" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="7804" class="Symbol">(</a><a id="7805" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="7812" class="Symbol">(</a><a id="7813" href="plfa.part2.Bisimulation.html#6750" class="Function">~exts</a> <a id="7819" href="plfa.part2.Bisimulation.html#7781" class="Bound">~σ</a><a id="7821" class="Symbol">)</a> <a id="7823" href="plfa.part2.Bisimulation.html#7788" class="Bound">~N</a><a id="7825" class="Symbol">)</a>
<a id="7827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7496" class="Function">~subst</a> <a id="7834" href="plfa.part2.Bisimulation.html#7834" class="Bound">~σ</a> <a id="7837" class="Symbol">(</a><a id="7838" href="plfa.part2.Bisimulation.html#7838" class="Bound">~L</a> <a id="7841" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="7844" href="plfa.part2.Bisimulation.html#7844" class="Bound">~M</a><a id="7846" class="Symbol">)</a>    <a id="7851" class="Symbol">=</a>  <a id="7854" class="Symbol">(</a><a id="7855" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="7862" href="plfa.part2.Bisimulation.html#7834" class="Bound">~σ</a> <a id="7865" href="plfa.part2.Bisimulation.html#7838" class="Bound">~L</a><a id="7867" class="Symbol">)</a> <a id="7869" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="7872" class="Symbol">(</a><a id="7873" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="7880" href="plfa.part2.Bisimulation.html#7834" class="Bound">~σ</a> <a id="7883" href="plfa.part2.Bisimulation.html#7844" class="Bound">~M</a><a id="7885" class="Symbol">)</a>
<a id="7887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#7496" class="Function">~subst</a> <a id="7894" href="plfa.part2.Bisimulation.html#7894" class="Bound">~σ</a> <a id="7897" class="Symbol">(</a><a id="7898" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="7903" href="plfa.part2.Bisimulation.html#7903" class="Bound">~M</a> <a id="7906" href="plfa.part2.Bisimulation.html#7906" class="Bound">~N</a><a id="7908" class="Symbol">)</a>  <a id="7911" class="Symbol">=</a>  <a id="7914" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="7919" class="Symbol">(</a><a id="7920" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="7927" href="plfa.part2.Bisimulation.html#7894" class="Bound">~σ</a> <a id="7930" href="plfa.part2.Bisimulation.html#7903" class="Bound">~M</a><a id="7932" class="Symbol">)</a> <a id="7934" class="Symbol">(</a><a id="7935" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="7942" class="Symbol">(</a><a id="7943" href="plfa.part2.Bisimulation.html#6750" class="Function">~exts</a> <a id="7949" href="plfa.part2.Bisimulation.html#7894" class="Bound">~σ</a><a id="7951" class="Symbol">)</a> <a id="7953" href="plfa.part2.Bisimulation.html#7906" class="Bound">~N</a><a id="7955" class="Symbol">)</a>
</pre>{% endraw %}Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
{% raw %}<pre class="Agda"><a id="~sub"></a><a id="8345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8345" class="Function">~sub</a> <a id="8350" class="Symbol">:</a> <a id="8352" class="Symbol">∀</a> <a id="8354" class="Symbol">{</a><a id="8355" href="plfa.part2.Bisimulation.html#8355" class="Bound">Γ</a> <a id="8357" href="plfa.part2.Bisimulation.html#8357" class="Bound">A</a> <a id="8359" href="plfa.part2.Bisimulation.html#8359" class="Bound">B</a><a id="8360" class="Symbol">}</a> <a id="8362" class="Symbol">{</a><a id="8363" href="plfa.part2.Bisimulation.html#8363" class="Bound">N</a> <a id="8365" href="plfa.part2.Bisimulation.html#8365" class="Bound">N†</a> <a id="8368" class="Symbol">:</a> <a id="8370" href="plfa.part2.Bisimulation.html#8355" class="Bound">Γ</a> <a id="8372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14640" class="InductiveConstructor Operator">,</a> <a id="8374" href="plfa.part2.Bisimulation.html#8359" class="Bound">B</a> <a id="8376" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="8378" href="plfa.part2.Bisimulation.html#8357" class="Bound">A</a><a id="8379" class="Symbol">}</a> <a id="8381" class="Symbol">{</a><a id="8382" href="plfa.part2.Bisimulation.html#8382" class="Bound">M</a> <a id="8384" href="plfa.part2.Bisimulation.html#8384" class="Bound">M†</a> <a id="8387" class="Symbol">:</a> <a id="8389" href="plfa.part2.Bisimulation.html#8355" class="Bound">Γ</a> <a id="8391" href="plfa.part2.More.html#14915" class="Datatype Operator">⊢</a> <a id="8393" href="plfa.part2.Bisimulation.html#8359" class="Bound">B</a><a id="8394" class="Symbol">}</a>
  <a id="8398" class="Symbol">→</a> <a id="8400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8363" class="Bound">N</a> <a id="8402" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="8404" href="plfa.part2.Bisimulation.html#8365" class="Bound">N†</a>
  <a id="8409" class="Symbol">→</a> <a id="8411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8382" class="Bound">M</a> <a id="8413" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="8415" href="plfa.part2.Bisimulation.html#8384" class="Bound">M†</a>
    <a id="8422" class="Comment">-----------------------</a>
  <a id="8448" class="Symbol">→</a> <a id="8450" class="Symbol">(</a><a id="8451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8363" class="Bound">N</a> <a id="8453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#18398" class="Function Operator">[</a> <a id="8455" href="plfa.part2.Bisimulation.html#8382" class="Bound">M</a> <a id="8457" href="plfa.part2.More.html#18398" class="Function Operator">]</a><a id="8458" class="Symbol">)</a> <a id="8460" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="8462" class="Symbol">(</a><a id="8463" href="plfa.part2.Bisimulation.html#8365" class="Bound">N†</a> <a id="8466" href="plfa.part2.More.html#18398" class="Function Operator">[</a> <a id="8468" href="plfa.part2.Bisimulation.html#8384" class="Bound">M†</a> <a id="8471" href="plfa.part2.More.html#18398" class="Function Operator">]</a><a id="8472" class="Symbol">)</a>
<a id="8474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8345" class="Function">~sub</a> <a id="8479" class="Symbol">{</a><a id="8480" href="plfa.part2.Bisimulation.html#8480" class="Bound">Γ</a><a id="8481" class="Symbol">}</a> <a id="8483" class="Symbol">{</a><a id="8484" href="plfa.part2.Bisimulation.html#8484" class="Bound">A</a><a id="8485" class="Symbol">}</a> <a id="8487" class="Symbol">{</a><a id="8488" href="plfa.part2.Bisimulation.html#8488" class="Bound">B</a><a id="8489" class="Symbol">}</a> <a id="8491" href="plfa.part2.Bisimulation.html#8491" class="Bound">~N</a> <a id="8494" href="plfa.part2.Bisimulation.html#8494" class="Bound">~M</a> <a id="8497" class="Symbol">=</a> <a id="8499" href="plfa.part2.Bisimulation.html#7496" class="Function">~subst</a> <a id="8506" class="Symbol">{</a><a id="8507" href="plfa.part2.Bisimulation.html#8480" class="Bound">Γ</a> <a id="8509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14640" class="InductiveConstructor Operator">,</a> <a id="8511" href="plfa.part2.Bisimulation.html#8488" class="Bound">B</a><a id="8512" class="Symbol">}</a> <a id="8514" class="Symbol">{</a><a id="8515" href="plfa.part2.Bisimulation.html#8480" class="Bound">Γ</a><a id="8516" class="Symbol">}</a> <a id="8518" href="plfa.part2.Bisimulation.html#8538" class="Function">~σ</a> <a id="8521" class="Symbol">{</a><a id="8522" href="plfa.part2.Bisimulation.html#8484" class="Bound">A</a><a id="8523" class="Symbol">}</a> <a id="8525" href="plfa.part2.Bisimulation.html#8491" class="Bound">~N</a>
  <a id="8530" class="Keyword">where</a>
  <a id="8538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8538" class="Function">~σ</a> <a id="8541" class="Symbol">:</a> <a id="8543" class="Symbol">∀</a> <a id="8545" class="Symbol">{</a><a id="8546" href="plfa.part2.Bisimulation.html#8546" class="Bound">A</a><a id="8547" class="Symbol">}</a> <a id="8549" class="Symbol">→</a> <a id="8551" class="Symbol">(</a><a id="8552" href="plfa.part2.Bisimulation.html#8552" class="Bound">x</a> <a id="8554" class="Symbol">:</a> <a id="8556" href="plfa.part2.Bisimulation.html#8480" class="Bound">Γ</a> <a id="8558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14640" class="InductiveConstructor Operator">,</a> <a id="8560" href="plfa.part2.Bisimulation.html#8488" class="Bound">B</a> <a id="8562" href="plfa.part2.More.html#14724" class="Datatype Operator">∋</a> <a id="8564" href="plfa.part2.Bisimulation.html#8546" class="Bound">A</a><a id="8565" class="Symbol">)</a> <a id="8567" class="Symbol">→</a> <a id="8569" class="Symbol">_</a> <a id="8571" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="8573" class="Symbol">_</a>
  <a id="8577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8538" class="Function">~σ</a> <a id="8580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14760" class="InductiveConstructor">Z</a>      <a id="8587" class="Symbol">=</a>  <a id="8590" href="plfa.part2.Bisimulation.html#8494" class="Bound">~M</a>
  <a id="8595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#8538" class="Function">~σ</a> <a id="8598" class="Symbol">(</a><a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14807" class="InductiveConstructor Operator">S</a> <a id="8601" href="plfa.part2.Bisimulation.html#8601" class="Bound">x</a><a id="8602" class="Symbol">)</a>  <a id="8605" class="Symbol">=</a>  <a id="8608" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a>
</pre>{% endraw %}Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
{% raw %}<pre class="Agda"><a id="9277" class="Keyword">data</a> <a id="Leg"></a><a id="9282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9282" class="Datatype">Leg</a> <a id="9286" class="Symbol">{</a><a id="9287" href="plfa.part2.Bisimulation.html#9287" class="Bound">Γ</a> <a id="9289" href="plfa.part2.Bisimulation.html#9289" class="Bound">A</a><a id="9290" class="Symbol">}</a> <a id="9292" class="Symbol">(</a><a id="9293" href="plfa.part2.Bisimulation.html#9293" class="Bound">M†</a> <a id="9296" href="plfa.part2.Bisimulation.html#9296" class="Bound">N</a> <a id="9298" class="Symbol">:</a> <a id="9300" href="plfa.part2.Bisimulation.html#9287" class="Bound">Γ</a> <a id="9302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="9304" href="plfa.part2.Bisimulation.html#9289" class="Bound">A</a><a id="9305" class="Symbol">)</a> <a id="9307" class="Symbol">:</a> <a id="9309" class="PrimitiveType">Set</a> <a id="9313" class="Keyword">where</a>

  <a id="Leg.leg"></a><a id="9322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9322" class="InductiveConstructor">leg</a> <a id="9326" class="Symbol">:</a> <a id="9328" class="Symbol">∀</a> <a id="9330" class="Symbol">{</a><a id="9331" href="plfa.part2.Bisimulation.html#9331" class="Bound">N†</a> <a id="9334" class="Symbol">:</a> <a id="9336" href="plfa.part2.Bisimulation.html#9287" class="Bound">Γ</a> <a id="9338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="9340" href="plfa.part2.Bisimulation.html#9289" class="Bound">A</a><a id="9341" class="Symbol">}</a>
    <a id="9347" class="Symbol">→</a> <a id="9349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9296" class="Bound">N</a> <a id="9351" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="9353" href="plfa.part2.Bisimulation.html#9331" class="Bound">N†</a>
    <a id="9360" class="Symbol">→</a> <a id="9362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9293" class="Bound">M†</a> <a id="9365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19511" class="Datatype Operator">—→</a> <a id="9368" href="plfa.part2.Bisimulation.html#9331" class="Bound">N†</a>
      <a id="9377" class="Comment">--------</a>
    <a id="9390" class="Symbol">→</a> <a id="9392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9282" class="Datatype">Leg</a> <a id="9396" href="plfa.part2.Bisimulation.html#9293" class="Bound">M†</a> <a id="9399" href="plfa.part2.Bisimulation.html#9296" class="Bound">N</a>
</pre>{% endraw %}For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
{% raw %}<pre class="Agda"><a id="sim"></a><a id="9658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9662" class="Symbol">:</a> <a id="9664" class="Symbol">∀</a> <a id="9666" class="Symbol">{</a><a id="9667" href="plfa.part2.Bisimulation.html#9667" class="Bound">Γ</a> <a id="9669" href="plfa.part2.Bisimulation.html#9669" class="Bound">A</a><a id="9670" class="Symbol">}</a> <a id="9672" class="Symbol">{</a><a id="9673" href="plfa.part2.Bisimulation.html#9673" class="Bound">M</a> <a id="9675" href="plfa.part2.Bisimulation.html#9675" class="Bound">M†</a> <a id="9678" href="plfa.part2.Bisimulation.html#9678" class="Bound">N</a> <a id="9680" class="Symbol">:</a> <a id="9682" href="plfa.part2.Bisimulation.html#9667" class="Bound">Γ</a> <a id="9684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#14915" class="Datatype Operator">⊢</a> <a id="9686" href="plfa.part2.Bisimulation.html#9669" class="Bound">A</a><a id="9687" class="Symbol">}</a>
  <a id="9691" class="Symbol">→</a> <a id="9693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9673" class="Bound">M</a> <a id="9695" href="plfa.part2.Bisimulation.html#3808" class="Datatype Operator">~</a> <a id="9697" href="plfa.part2.Bisimulation.html#9675" class="Bound">M†</a>
  <a id="9702" class="Symbol">→</a> <a id="9704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9673" class="Bound">M</a> <a id="9706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19511" class="Datatype Operator">—→</a> <a id="9709" href="plfa.part2.Bisimulation.html#9678" class="Bound">N</a>
    <a id="9715" class="Comment">---------</a>
  <a id="9727" class="Symbol">→</a> <a id="9729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9282" class="Datatype">Leg</a>  <a id="9734" href="plfa.part2.Bisimulation.html#9675" class="Bound">M†</a> <a id="9737" href="plfa.part2.Bisimulation.html#9678" class="Bound">N</a>
<a id="9739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9743" href="plfa.part2.Bisimulation.html#3857" class="InductiveConstructor">~`</a>              <a id="9759" class="Symbol">()</a>
<a id="9762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9766" class="Symbol">(</a><a id="9767" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="9770" href="plfa.part2.Bisimulation.html#9770" class="Bound">~N</a><a id="9772" class="Symbol">)</a>         <a id="9782" class="Symbol">()</a>
<a id="9785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9789" class="Symbol">(</a><a id="9790" href="plfa.part2.Bisimulation.html#9790" class="Bound">~L</a> <a id="9793" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="9796" href="plfa.part2.Bisimulation.html#9796" class="Bound">~M</a><a id="9798" class="Symbol">)</a>      <a id="9805" class="Symbol">(</a><a id="9806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19577" class="InductiveConstructor">ξ-·₁</a> <a id="9811" href="plfa.part2.Bisimulation.html#9811" class="Bound">L—→</a><a id="9814" class="Symbol">)</a>
  <a id="9818" class="Keyword">with</a> <a id="9823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9827" href="plfa.part2.Bisimulation.html#9790" class="Bound">~L</a> <a id="9830" href="plfa.part2.Bisimulation.html#9811" class="Bound">L—→</a>
<a id="9834" class="Symbol">...</a>  <a id="9839" class="Symbol">|</a> <a id="9841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9322" class="InductiveConstructor">leg</a> <a id="9845" href="plfa.part2.Bisimulation.html#9845" class="Bound">~L′</a> <a id="9849" href="plfa.part2.Bisimulation.html#9849" class="Bound">L†—→</a>                 <a id="9870" class="Symbol">=</a>  <a id="9873" href="plfa.part2.Bisimulation.html#9322" class="InductiveConstructor">leg</a> <a id="9877" class="Symbol">(</a><a id="9878" href="plfa.part2.Bisimulation.html#9845" class="Bound">~L′</a> <a id="9882" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="9885" class="Bound">~M</a><a id="9887" class="Symbol">)</a>   <a id="9891" class="Symbol">(</a><a id="9892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19577" class="InductiveConstructor">ξ-·₁</a> <a id="9897" href="plfa.part2.Bisimulation.html#9849" class="Bound">L†—→</a><a id="9901" class="Symbol">)</a>
<a id="9903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9907" class="Symbol">(</a><a id="9908" href="plfa.part2.Bisimulation.html#9908" class="Bound">~V</a> <a id="9911" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="9914" href="plfa.part2.Bisimulation.html#9914" class="Bound">~M</a><a id="9916" class="Symbol">)</a>      <a id="9923" class="Symbol">(</a><a id="9924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19686" class="InductiveConstructor">ξ-·₂</a> <a id="9929" href="plfa.part2.Bisimulation.html#9929" class="Bound">VV</a> <a id="9932" href="plfa.part2.Bisimulation.html#9932" class="Bound">M—→</a><a id="9935" class="Symbol">)</a>
  <a id="9939" class="Keyword">with</a> <a id="9944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="9948" href="plfa.part2.Bisimulation.html#9914" class="Bound">~M</a> <a id="9951" href="plfa.part2.Bisimulation.html#9932" class="Bound">M—→</a>
<a id="9955" class="Symbol">...</a>  <a id="9960" class="Symbol">|</a> <a id="9962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9322" class="InductiveConstructor">leg</a> <a id="9966" href="plfa.part2.Bisimulation.html#9966" class="Bound">~M′</a> <a id="9970" href="plfa.part2.Bisimulation.html#9970" class="Bound">M†—→</a>                 <a id="9991" class="Symbol">=</a>  <a id="9994" href="plfa.part2.Bisimulation.html#9322" class="InductiveConstructor">leg</a> <a id="9998" class="Symbol">(</a><a id="9999" class="Bound">~V</a> <a id="10002" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="10005" href="plfa.part2.Bisimulation.html#9966" class="Bound">~M′</a><a id="10008" class="Symbol">)</a>   <a id="10012" class="Symbol">(</a><a id="10013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19686" class="InductiveConstructor">ξ-·₂</a> <a id="10018" class="Symbol">(</a><a id="10019" href="plfa.part2.Bisimulation.html#4968" class="Function">~val</a> <a id="10024" class="Bound">~V</a> <a id="10027" class="Bound">VV</a><a id="10029" class="Symbol">)</a> <a id="10031" href="plfa.part2.Bisimulation.html#9970" class="Bound">M†—→</a><a id="10035" class="Symbol">)</a>
<a id="10037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="10041" class="Symbol">((</a><a id="10043" href="plfa.part2.Bisimulation.html#3915" class="InductiveConstructor Operator">~ƛ</a> <a id="10046" href="plfa.part2.Bisimulation.html#10046" class="Bound">~N</a><a id="10048" class="Symbol">)</a> <a id="10050" href="plfa.part2.Bisimulation.html#4000" class="InductiveConstructor Operator">~·</a> <a id="10053" href="plfa.part2.Bisimulation.html#10053" class="Bound">~V</a><a id="10055" class="Symbol">)</a> <a id="10057" class="Symbol">(</a><a id="10058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19809" class="InductiveConstructor">β-ƛ</a> <a id="10062" href="plfa.part2.Bisimulation.html#10062" class="Bound">VV</a><a id="10064" class="Symbol">)</a>        <a id="10073" class="Symbol">=</a>  <a id="10076" href="plfa.part2.Bisimulation.html#9322" class="InductiveConstructor">leg</a> <a id="10080" class="Symbol">(</a><a id="10081" href="plfa.part2.Bisimulation.html#8345" class="Function">~sub</a> <a id="10086" href="plfa.part2.Bisimulation.html#10046" class="Bound">~N</a> <a id="10089" href="plfa.part2.Bisimulation.html#10053" class="Bound">~V</a><a id="10091" class="Symbol">)</a>  <a id="10094" class="Symbol">(</a><a id="10095" href="plfa.part2.More.html#19809" class="InductiveConstructor">β-ƛ</a> <a id="10099" class="Symbol">(</a><a id="10100" href="plfa.part2.Bisimulation.html#4968" class="Function">~val</a> <a id="10105" href="plfa.part2.Bisimulation.html#10053" class="Bound">~V</a> <a id="10108" href="plfa.part2.Bisimulation.html#10062" class="Bound">VV</a><a id="10110" class="Symbol">))</a>
<a id="10113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="10117" class="Symbol">(</a><a id="10118" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="10123" href="plfa.part2.Bisimulation.html#10123" class="Bound">~M</a> <a id="10126" href="plfa.part2.Bisimulation.html#10126" class="Bound">~N</a><a id="10128" class="Symbol">)</a>    <a id="10133" class="Symbol">(</a><a id="10134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#20859" class="InductiveConstructor">ξ-let</a> <a id="10140" href="plfa.part2.Bisimulation.html#10140" class="Bound">M—→</a><a id="10143" class="Symbol">)</a>
  <a id="10147" class="Keyword">with</a> <a id="10152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="10156" href="plfa.part2.Bisimulation.html#10123" class="Bound">~M</a> <a id="10159" href="plfa.part2.Bisimulation.html#10140" class="Bound">M—→</a>
<a id="10163" class="Symbol">...</a>  <a id="10168" class="Symbol">|</a> <a id="10170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9322" class="InductiveConstructor">leg</a> <a id="10174" href="plfa.part2.Bisimulation.html#10174" class="Bound">~M′</a> <a id="10178" href="plfa.part2.Bisimulation.html#10178" class="Bound">M†—→</a>                 <a id="10199" class="Symbol">=</a>  <a id="10202" href="plfa.part2.Bisimulation.html#9322" class="InductiveConstructor">leg</a> <a id="10206" class="Symbol">(</a><a id="10207" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="10212" href="plfa.part2.Bisimulation.html#10174" class="Bound">~M′</a> <a id="10216" class="Bound">~N</a><a id="10218" class="Symbol">)</a> <a id="10220" class="Symbol">(</a><a id="10221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#19686" class="InductiveConstructor">ξ-·₂</a> <a id="10226" href="plfa.part2.More.html#18909" class="InductiveConstructor">V-ƛ</a> <a id="10230" href="plfa.part2.Bisimulation.html#10178" class="Bound">M†—→</a><a id="10234" class="Symbol">)</a>
<a id="10236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Bisimulation.md %}{% raw %}#9658" class="Function">sim</a> <a id="10240" class="Symbol">(</a><a id="10241" href="plfa.part2.Bisimulation.html#4124" class="InductiveConstructor">~let</a> <a id="10246" href="plfa.part2.Bisimulation.html#10246" class="Bound">~V</a> <a id="10249" href="plfa.part2.Bisimulation.html#10249" class="Bound">~N</a><a id="10251" class="Symbol">)</a>    <a id="10256" class="Symbol">(</a><a id="10257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/More.md %}{% raw %}#20981" class="InductiveConstructor">β-let</a> <a id="10263" href="plfa.part2.Bisimulation.html#10263" class="Bound">VV</a><a id="10265" class="Symbol">)</a>      <a id="10272" class="Symbol">=</a>  <a id="10275" href="plfa.part2.Bisimulation.html#9322" class="InductiveConstructor">leg</a> <a id="10279" class="Symbol">(</a><a id="10280" href="plfa.part2.Bisimulation.html#8345" class="Function">~sub</a> <a id="10285" href="plfa.part2.Bisimulation.html#10249" class="Bound">~N</a> <a id="10288" href="plfa.part2.Bisimulation.html#10246" class="Bound">~V</a><a id="10290" class="Symbol">)</a>  <a id="10293" class="Symbol">(</a><a id="10294" href="plfa.part2.More.html#19809" class="InductiveConstructor">β-ƛ</a> <a id="10298" class="Symbol">(</a><a id="10299" href="plfa.part2.Bisimulation.html#4968" class="Function">~val</a> <a id="10304" href="plfa.part2.Bisimulation.html#10246" class="Bound">~V</a> <a id="10307" href="plfa.part2.Bisimulation.html#10263" class="Bound">VV</a><a id="10309" class="Symbol">))</a>
</pre>{% endraw %}The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

{% raw %}<pre class="Agda"><a id="14090" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `products` (practice)

Show that the two formulations of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

{% raw %}<pre class="Agda"><a id="14420" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
