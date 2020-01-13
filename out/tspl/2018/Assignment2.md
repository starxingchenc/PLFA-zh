---
src       : "courses/tspl/2018/Assignment2.lagda.md"
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /TSPL/2018/Assignment2/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}" class="Module">Assignment2</a> <a id="131" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

<!-- This assignment is due **4pm Thursday 18 October** (Week 5). -->

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="686" class="Keyword">import</a> <a id="693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="731" class="Symbol">as</a> <a id="734" class="Module">Eq</a>
<a id="737" class="Keyword">open</a> <a id="742" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="745" class="Keyword">using</a> <a id="751" class="Symbol">(</a><a id="752" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="755" class="Symbol">;</a> <a id="757" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="761" class="Symbol">;</a> <a id="763" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="767" class="Symbol">;</a> <a id="769" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="772" class="Symbol">)</a>
<a id="774" class="Keyword">open</a> <a id="779" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="794" class="Keyword">using</a> <a id="800" class="Symbol">(</a><a id="801" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="807" class="Symbol">;</a> <a id="809" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="814" class="Symbol">;</a> <a id="816" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="822" class="Symbol">;</a> <a id="824" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="826" class="Symbol">)</a>
<a id="828" class="Keyword">open</a> <a id="833" class="Keyword">import</a> <a id="840" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="849" class="Keyword">using</a> <a id="855" class="Symbol">(</a><a id="856" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="857" class="Symbol">;</a> <a id="859" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="863" class="Symbol">;</a> <a id="865" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="868" class="Symbol">;</a> <a id="870" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="873" class="Symbol">;</a> <a id="875" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="878" class="Symbol">;</a> <a id="880" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="883" class="Symbol">;</a> <a id="885" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="888" class="Symbol">;</a> <a id="890" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="893" class="Symbol">;</a> <a id="895" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="898" class="Symbol">)</a>
<a id="900" class="Keyword">open</a> <a id="905" class="Keyword">import</a> <a id="912" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="932" class="Keyword">using</a> <a id="938" class="Symbol">(</a><a id="939" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="946" class="Symbol">;</a> <a id="948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="959" class="Symbol">;</a> <a id="961" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="966" class="Symbol">;</a> <a id="968" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="974" class="Symbol">;</a>
  <a id="978" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="984" class="Symbol">;</a> <a id="986" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="993" class="Symbol">;</a> <a id="995" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1004" class="Symbol">;</a> <a id="1006" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1013" class="Symbol">;</a> <a id="1015" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1024" class="Symbol">;</a> <a id="1026" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1035" class="Symbol">;</a> <a id="1037" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1045" class="Symbol">)</a>
<a id="1047" class="Keyword">open</a> <a id="1052" class="Keyword">import</a> <a id="1059" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1072" class="Keyword">using</a> <a id="1078" class="Symbol">(</a><a id="1079" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1082" class="Symbol">;</a> <a id="1084" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1089" class="Symbol">;</a> <a id="1091" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1096" class="Symbol">)</a> <a id="1098" class="Keyword">renaming</a> <a id="1107" class="Symbol">(</a><a id="1108" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1112" class="Symbol">to</a> <a id="1115" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1120" class="Symbol">)</a>
<a id="1122" class="Keyword">open</a> <a id="1127" class="Keyword">import</a> <a id="1134" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1144" class="Keyword">using</a> <a id="1150" class="Symbol">(</a><a id="1151" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1152" class="Symbol">;</a> <a id="1154" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1156" class="Symbol">)</a>
<a id="1158" class="Keyword">open</a> <a id="1163" class="Keyword">import</a> <a id="1170" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1179" class="Keyword">using</a> <a id="1185" class="Symbol">(</a><a id="1186" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1189" class="Symbol">;</a> <a id="1191" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1195" class="Symbol">;</a> <a id="1197" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1201" class="Symbol">)</a> <a id="1203" class="Keyword">renaming</a> <a id="1212" class="Symbol">(</a><a id="1213" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1219" class="Symbol">to</a> <a id="1222" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1228" class="Symbol">)</a>
<a id="1230" class="Keyword">open</a> <a id="1235" class="Keyword">import</a> <a id="1242" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1253" class="Keyword">using</a> <a id="1259" class="Symbol">(</a><a id="1260" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1261" class="Symbol">;</a> <a id="1263" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1269" class="Symbol">)</a>
<a id="1271" class="Keyword">open</a> <a id="1276" class="Keyword">import</a> <a id="1283" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1298" class="Keyword">using</a> <a id="1304" class="Symbol">(</a><a id="1305" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1309" class="Symbol">;</a> <a id="1311" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1315" class="Symbol">;</a> <a id="1317" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1322" class="Symbol">;</a> <a id="1324" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1325" class="Symbol">;</a> <a id="1327" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1330" class="Symbol">;</a> <a id="1332" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1335" class="Symbol">;</a> <a id="1337" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1340" class="Symbol">)</a>
<a id="1342" class="Keyword">open</a> <a id="1347" class="Keyword">import</a> <a id="1354" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1371" class="Keyword">using</a> <a id="1377" class="Symbol">(</a><a id="1378" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1380" class="Symbol">;</a> <a id="1382" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1385" class="Symbol">;</a> <a id="1387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1390" class="Symbol">;</a> <a id="1392" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1394" class="Symbol">)</a>
<a id="1396" class="Keyword">open</a> <a id="1401" class="Keyword">import</a> <a id="1408" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1435" class="Keyword">using</a> <a id="1441" class="Symbol">(</a><a id="1442" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1445" class="Symbol">;</a> <a id="1447" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1456" class="Symbol">;</a> <a id="1458" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1469" class="Symbol">)</a>
<a id="1471" class="Keyword">open</a> <a id="1476" class="Keyword">import</a> <a id="1483" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1509" class="Keyword">using</a> <a id="1515" class="Symbol">(</a><a id="1516" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="1518" class="Symbol">)</a>
<a id="1520" class="Keyword">open</a> <a id="1525" class="Keyword">import</a> <a id="1532" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="1557" class="Keyword">using</a> <a id="1563" class="Symbol">(</a><a id="1564" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="1571" class="Symbol">)</a>
<a id="1573" class="Keyword">open</a> <a id="1578" class="Keyword">import</a> <a id="1585" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="1606" class="Keyword">using</a> <a id="1612" class="Symbol">(</a><a id="1613" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="1620" class="Symbol">)</a>
<a id="1622" class="Keyword">open</a> <a id="1627" class="Keyword">import</a> <a id="1634" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1660" class="Keyword">using</a> <a id="1666" class="Symbol">(</a><a id="1667" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="1681" class="Symbol">)</a>
<a id="1683" class="Keyword">open</a> <a id="1688" class="Keyword">import</a> <a id="1695" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1708" class="Keyword">using</a> <a id="1714" class="Symbol">(</a><a id="1715" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="1716" class="Symbol">;</a> <a id="1718" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="1721" class="Symbol">;</a> <a id="1723" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1724" class="Symbol">;</a> <a id="1726" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="1734" class="Symbol">;</a> <a id="1736" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1744" class="Symbol">)</a>
<a id="1746" class="Keyword">open</a> <a id="1751" class="Keyword">import</a> <a id="1758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1779" class="Keyword">using</a> <a id="1785" class="Symbol">(</a><a id="1786" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="1789" class="Symbol">;</a> <a id="1791" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="1794" class="Symbol">;</a> <a id="1796" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="1799" class="Symbol">)</a>
<a id="1801" class="Keyword">open</a> <a id="1806" class="Keyword">import</a> <a id="1813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1836" class="Keyword">using</a> <a id="1842" class="Symbol">(</a><a id="1843" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="1846" class="Symbol">;</a> <a id="1848" href="plfa.part1.Isomorphism.html#9384" class="Function">≃-sym</a><a id="1853" class="Symbol">;</a> <a id="1855" href="plfa.part1.Isomorphism.html#9781" class="Function">≃-trans</a><a id="1862" class="Symbol">;</a> <a id="1864" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">_≲_</a><a id="1867" class="Symbol">;</a> <a id="1869" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="1883" class="Symbol">)</a>
<a id="1885" class="Keyword">open</a> <a id="1890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}
## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="2422" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="2434" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2434" class="Postulate">≃-implies-≲</a> <a id="2446" class="Symbol">:</a> <a id="2448" class="Symbol">∀</a> <a id="2450" class="Symbol">{</a><a id="2451" href="Assignment2.html#2451" class="Bound">A</a> <a id="2453" href="Assignment2.html#2453" class="Bound">B</a> <a id="2455" class="Symbol">:</a> <a id="2457" class="PrimitiveType">Set</a><a id="2460" class="Symbol">}</a>
    <a id="2466" class="Symbol">→</a> <a id="2468" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2451" class="Bound">A</a> <a id="2470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="2472" href="Assignment2.html#2453" class="Bound">B</a>
      <a id="2480" class="Comment">-----</a>
    <a id="2490" class="Symbol">→</a> <a id="2492" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2451" class="Bound">A</a> <a id="2494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">≲</a> <a id="2496" href="Assignment2.html#2453" class="Bound">B</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
{% raw %}<pre class="Agda"><a id="2629" class="Keyword">record</a> <a id="_⇔_"></a><a id="2636" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2636" class="Record Operator">_⇔_</a> <a id="2640" class="Symbol">(</a><a id="2641" href="Assignment2.html#2641" class="Bound">A</a> <a id="2643" href="Assignment2.html#2643" class="Bound">B</a> <a id="2645" class="Symbol">:</a> <a id="2647" class="PrimitiveType">Set</a><a id="2650" class="Symbol">)</a> <a id="2652" class="Symbol">:</a> <a id="2654" class="PrimitiveType">Set</a> <a id="2658" class="Keyword">where</a>
  <a id="2666" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="2676" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2676" class="Field">to</a>   <a id="2681" class="Symbol">:</a> <a id="2683" href="Assignment2.html#2641" class="Bound">A</a> <a id="2685" class="Symbol">→</a> <a id="2687" href="Assignment2.html#2643" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="2693" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2693" class="Field">from</a> <a id="2698" class="Symbol">:</a> <a id="2700" href="Assignment2.html#2643" class="Bound">B</a> <a id="2702" class="Symbol">→</a> <a id="2704" href="Assignment2.html#2641" class="Bound">A</a>

<a id="2707" class="Keyword">open</a> <a id="2712" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2636" class="Module Operator">_⇔_</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
{% raw %}<pre class="Agda"><a id="2995" class="Keyword">data</a> <a id="Bin"></a><a id="3000" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3000" class="Datatype">Bin</a> <a id="3004" class="Symbol">:</a> <a id="3006" class="PrimitiveType">Set</a> <a id="3010" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="3018" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3018" class="InductiveConstructor">nil</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Assignment2.html#3000" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="3030" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3030" class="InductiveConstructor Operator">x0_</a> <a id="3034" class="Symbol">:</a> <a id="3036" href="Assignment2.html#3000" class="Datatype">Bin</a> <a id="3040" class="Symbol">→</a> <a id="3042" href="Assignment2.html#3000" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="3048" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3048" class="InductiveConstructor Operator">x1_</a> <a id="3052" class="Symbol">:</a> <a id="3054" href="Assignment2.html#3000" class="Datatype">Bin</a> <a id="3058" class="Symbol">→</a> <a id="3060" href="Assignment2.html#3000" class="Datatype">Bin</a>
</pre>{% endraw %}And ask you to define the following functions:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
Why is there not an isomorphism?


## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

#### Exercise `⊎-assoc`

Show sum is associative up to ismorphism.

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition.

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
{% raw %}<pre class="Agda"><a id="3869" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="3881" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3881" class="Postulate">⊎-weak-×</a> <a id="3890" class="Symbol">:</a> <a id="3892" class="Symbol">∀</a> <a id="3894" class="Symbol">{</a><a id="3895" href="Assignment2.html#3895" class="Bound">A</a> <a id="3897" href="Assignment2.html#3897" class="Bound">B</a> <a id="3899" href="Assignment2.html#3899" class="Bound">C</a> <a id="3901" class="Symbol">:</a> <a id="3903" class="PrimitiveType">Set</a><a id="3906" class="Symbol">}</a> <a id="3908" class="Symbol">→</a> <a id="3910" class="Symbol">(</a><a id="3911" href="Assignment2.html#3895" class="Bound">A</a> <a id="3913" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3915" href="Assignment2.html#3897" class="Bound">B</a><a id="3916" class="Symbol">)</a> <a id="3918" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3920" href="Assignment2.html#3899" class="Bound">C</a> <a id="3922" class="Symbol">→</a> <a id="3924" href="Assignment2.html#3895" class="Bound">A</a> <a id="3926" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3928" class="Symbol">(</a><a id="3929" href="Assignment2.html#3897" class="Bound">B</a> <a id="3931" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3933" href="Assignment2.html#3899" class="Bound">C</a><a id="3934" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
{% raw %}<pre class="Agda"><a id="4174" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="4186" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#4186" class="Postulate">⊎×-implies-×⊎</a> <a id="4200" class="Symbol">:</a> <a id="4202" class="Symbol">∀</a> <a id="4204" class="Symbol">{</a><a id="4205" href="Assignment2.html#4205" class="Bound">A</a> <a id="4207" href="Assignment2.html#4207" class="Bound">B</a> <a id="4209" href="Assignment2.html#4209" class="Bound">C</a> <a id="4211" href="Assignment2.html#4211" class="Bound">D</a> <a id="4213" class="Symbol">:</a> <a id="4215" class="PrimitiveType">Set</a><a id="4218" class="Symbol">}</a> <a id="4220" class="Symbol">→</a> <a id="4222" class="Symbol">(</a><a id="4223" href="Assignment2.html#4205" class="Bound">A</a> <a id="4225" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4227" href="Assignment2.html#4207" class="Bound">B</a><a id="4228" class="Symbol">)</a> <a id="4230" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4232" class="Symbol">(</a><a id="4233" href="Assignment2.html#4209" class="Bound">C</a> <a id="4235" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4237" href="Assignment2.html#4211" class="Bound">D</a><a id="4238" class="Symbol">)</a> <a id="4240" class="Symbol">→</a> <a id="4242" class="Symbol">(</a><a id="4243" href="Assignment2.html#4205" class="Bound">A</a> <a id="4245" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4247" href="Assignment2.html#4209" class="Bound">C</a><a id="4248" class="Symbol">)</a> <a id="4250" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4252" class="Symbol">(</a><a id="4253" href="Assignment2.html#4207" class="Bound">B</a> <a id="4255" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4257" href="Assignment2.html#4211" class="Bound">D</a><a id="4258" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.


## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="5740" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#5740" class="Function">Stable</a> <a id="5747" class="Symbol">:</a> <a id="5749" class="PrimitiveType">Set</a> <a id="5753" class="Symbol">→</a> <a id="5755" class="PrimitiveType">Set</a>
<a id="5759" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#5740" class="Function">Stable</a> <a id="5766" href="Assignment2.html#5766" class="Bound">A</a> <a id="5768" class="Symbol">=</a> <a id="5770" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5772" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5774" href="Assignment2.html#5766" class="Bound">A</a> <a id="5776" class="Symbol">→</a> <a id="5778" href="Assignment2.html#5766" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
{% raw %}<pre class="Agda"><a id="5999" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="6011" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6011" class="Postulate">∀-distrib-×</a> <a id="6023" class="Symbol">:</a> <a id="6025" class="Symbol">∀</a> <a id="6027" class="Symbol">{</a><a id="6028" href="Assignment2.html#6028" class="Bound">A</a> <a id="6030" class="Symbol">:</a> <a id="6032" class="PrimitiveType">Set</a><a id="6035" class="Symbol">}</a> <a id="6037" class="Symbol">{</a><a id="6038" href="Assignment2.html#6038" class="Bound">B</a> <a id="6040" href="Assignment2.html#6040" class="Bound">C</a> <a id="6042" class="Symbol">:</a> <a id="6044" href="Assignment2.html#6028" class="Bound">A</a> <a id="6046" class="Symbol">→</a> <a id="6048" class="PrimitiveType">Set</a><a id="6051" class="Symbol">}</a> <a id="6053" class="Symbol">→</a>
    <a id="6059" class="Symbol">(∀</a> <a id="6062" class="Symbol">(</a><a id="6063" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6063" class="Bound">x</a> <a id="6065" class="Symbol">:</a> <a id="6067" href="Assignment2.html#6028" class="Bound">A</a><a id="6068" class="Symbol">)</a> <a id="6070" class="Symbol">→</a> <a id="6072" href="Assignment2.html#6038" class="Bound">B</a> <a id="6074" href="Assignment2.html#6063" class="Bound">x</a> <a id="6076" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6078" href="Assignment2.html#6040" class="Bound">C</a> <a id="6080" href="Assignment2.html#6063" class="Bound">x</a><a id="6081" class="Symbol">)</a> <a id="6083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="6085" class="Symbol">(∀</a> <a id="6088" class="Symbol">(</a><a id="6089" href="Assignment2.html#6089" class="Bound">x</a> <a id="6091" class="Symbol">:</a> <a id="6093" href="Assignment2.html#6028" class="Bound">A</a><a id="6094" class="Symbol">)</a> <a id="6096" class="Symbol">→</a> <a id="6098" href="Assignment2.html#6038" class="Bound">B</a> <a id="6100" href="Assignment2.html#6089" class="Bound">x</a><a id="6101" class="Symbol">)</a> <a id="6103" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6105" class="Symbol">(∀</a> <a id="6108" class="Symbol">(</a><a id="6109" href="Assignment2.html#6109" class="Bound">x</a> <a id="6111" class="Symbol">:</a> <a id="6113" href="Assignment2.html#6028" class="Bound">A</a><a id="6114" class="Symbol">)</a> <a id="6116" class="Symbol">→</a> <a id="6118" href="Assignment2.html#6040" class="Bound">C</a> <a id="6120" href="Assignment2.html#6109" class="Bound">x</a><a id="6121" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
{% raw %}<pre class="Agda"><a id="6327" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="6339" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6339" class="Postulate">⊎∀-implies-∀⊎</a> <a id="6353" class="Symbol">:</a> <a id="6355" class="Symbol">∀</a> <a id="6357" class="Symbol">{</a><a id="6358" href="Assignment2.html#6358" class="Bound">A</a> <a id="6360" class="Symbol">:</a> <a id="6362" class="PrimitiveType">Set</a><a id="6365" class="Symbol">}</a> <a id="6367" class="Symbol">{</a> <a id="6369" href="Assignment2.html#6369" class="Bound">B</a> <a id="6371" href="Assignment2.html#6371" class="Bound">C</a> <a id="6373" class="Symbol">:</a> <a id="6375" href="Assignment2.html#6358" class="Bound">A</a> <a id="6377" class="Symbol">→</a> <a id="6379" class="PrimitiveType">Set</a> <a id="6383" class="Symbol">}</a> <a id="6385" class="Symbol">→</a>
    <a id="6391" class="Symbol">(∀</a> <a id="6394" class="Symbol">(</a><a id="6395" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6395" class="Bound">x</a> <a id="6397" class="Symbol">:</a> <a id="6399" href="Assignment2.html#6358" class="Bound">A</a><a id="6400" class="Symbol">)</a> <a id="6402" class="Symbol">→</a> <a id="6404" href="Assignment2.html#6369" class="Bound">B</a> <a id="6406" href="Assignment2.html#6395" class="Bound">x</a><a id="6407" class="Symbol">)</a> <a id="6409" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6411" class="Symbol">(∀</a> <a id="6414" class="Symbol">(</a><a id="6415" href="Assignment2.html#6415" class="Bound">x</a> <a id="6417" class="Symbol">:</a> <a id="6419" href="Assignment2.html#6358" class="Bound">A</a><a id="6420" class="Symbol">)</a> <a id="6422" class="Symbol">→</a> <a id="6424" href="Assignment2.html#6371" class="Bound">C</a> <a id="6426" href="Assignment2.html#6415" class="Bound">x</a><a id="6427" class="Symbol">)</a>  <a id="6430" class="Symbol">→</a>  <a id="6433" class="Symbol">∀</a> <a id="6435" class="Symbol">(</a><a id="6436" href="Assignment2.html#6436" class="Bound">x</a> <a id="6438" class="Symbol">:</a> <a id="6440" href="Assignment2.html#6358" class="Bound">A</a><a id="6441" class="Symbol">)</a> <a id="6443" class="Symbol">→</a> <a id="6445" href="Assignment2.html#6369" class="Bound">B</a> <a id="6447" href="Assignment2.html#6436" class="Bound">x</a> <a id="6449" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6451" href="Assignment2.html#6371" class="Bound">C</a> <a id="6453" href="Assignment2.html#6436" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
{% raw %}<pre class="Agda"><a id="6618" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="6630" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6630" class="Postulate">∃-distrib-⊎</a> <a id="6642" class="Symbol">:</a> <a id="6644" class="Symbol">∀</a> <a id="6646" class="Symbol">{</a><a id="6647" href="Assignment2.html#6647" class="Bound">A</a> <a id="6649" class="Symbol">:</a> <a id="6651" class="PrimitiveType">Set</a><a id="6654" class="Symbol">}</a> <a id="6656" class="Symbol">{</a><a id="6657" href="Assignment2.html#6657" class="Bound">B</a> <a id="6659" href="Assignment2.html#6659" class="Bound">C</a> <a id="6661" class="Symbol">:</a> <a id="6663" href="Assignment2.html#6647" class="Bound">A</a> <a id="6665" class="Symbol">→</a> <a id="6667" class="PrimitiveType">Set</a><a id="6670" class="Symbol">}</a> <a id="6672" class="Symbol">→</a>
    <a id="6678" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6681" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6681" class="Bound">x</a> <a id="6683" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6685" class="Symbol">(</a><a id="6686" href="Assignment2.html#6657" class="Bound">B</a> <a id="6688" href="Assignment2.html#6681" class="Bound">x</a> <a id="6690" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6692" href="Assignment2.html#6659" class="Bound">C</a> <a id="6694" href="Assignment2.html#6681" class="Bound">x</a><a id="6695" class="Symbol">)</a> <a id="6697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="6699" class="Symbol">(</a><a id="6700" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6703" href="Assignment2.html#6703" class="Bound">x</a> <a id="6705" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6707" href="Assignment2.html#6657" class="Bound">B</a> <a id="6709" href="Assignment2.html#6703" class="Bound">x</a><a id="6710" class="Symbol">)</a> <a id="6712" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6714" class="Symbol">(</a><a id="6715" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6718" href="Assignment2.html#6718" class="Bound">x</a> <a id="6720" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6722" href="Assignment2.html#6659" class="Bound">C</a> <a id="6724" href="Assignment2.html#6718" class="Bound">x</a><a id="6725" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
{% raw %}<pre class="Agda"><a id="6847" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="6859" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6859" class="Postulate">∃×-implies-×∃</a> <a id="6873" class="Symbol">:</a> <a id="6875" class="Symbol">∀</a> <a id="6877" class="Symbol">{</a><a id="6878" href="Assignment2.html#6878" class="Bound">A</a> <a id="6880" class="Symbol">:</a> <a id="6882" class="PrimitiveType">Set</a><a id="6885" class="Symbol">}</a> <a id="6887" class="Symbol">{</a> <a id="6889" href="Assignment2.html#6889" class="Bound">B</a> <a id="6891" href="Assignment2.html#6891" class="Bound">C</a> <a id="6893" class="Symbol">:</a> <a id="6895" href="Assignment2.html#6878" class="Bound">A</a> <a id="6897" class="Symbol">→</a> <a id="6899" class="PrimitiveType">Set</a> <a id="6903" class="Symbol">}</a> <a id="6905" class="Symbol">→</a>
    <a id="6911" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6914" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6914" class="Bound">x</a> <a id="6916" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6918" class="Symbol">(</a><a id="6919" href="Assignment2.html#6889" class="Bound">B</a> <a id="6921" href="Assignment2.html#6914" class="Bound">x</a> <a id="6923" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6925" href="Assignment2.html#6891" class="Bound">C</a> <a id="6927" href="Assignment2.html#6914" class="Bound">x</a><a id="6928" class="Symbol">)</a> <a id="6930" class="Symbol">→</a> <a id="6932" class="Symbol">(</a><a id="6933" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6936" href="Assignment2.html#6936" class="Bound">x</a> <a id="6938" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6940" href="Assignment2.html#6889" class="Bound">B</a> <a id="6942" href="Assignment2.html#6936" class="Bound">x</a><a id="6943" class="Symbol">)</a> <a id="6945" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6947" class="Symbol">(</a><a id="6948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6951" href="Assignment2.html#6951" class="Bound">x</a> <a id="6953" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6955" href="Assignment2.html#6891" class="Bound">C</a> <a id="6957" href="Assignment2.html#6951" class="Bound">x</a><a id="6958" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
{% raw %}<pre class="Agda"><a id="7453" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="7465" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7465" class="Postulate">∃¬-implies-¬∀</a> <a id="7479" class="Symbol">:</a> <a id="7481" class="Symbol">∀</a> <a id="7483" class="Symbol">{</a><a id="7484" href="Assignment2.html#7484" class="Bound">A</a> <a id="7486" class="Symbol">:</a> <a id="7488" class="PrimitiveType">Set</a><a id="7491" class="Symbol">}</a> <a id="7493" class="Symbol">{</a><a id="7494" href="Assignment2.html#7494" class="Bound">B</a> <a id="7496" class="Symbol">:</a> <a id="7498" href="Assignment2.html#7484" class="Bound">A</a> <a id="7500" class="Symbol">→</a> <a id="7502" class="PrimitiveType">Set</a><a id="7505" class="Symbol">}</a>
    <a id="7511" class="Symbol">→</a> <a id="7513" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7516" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7516" class="Bound">x</a> <a id="7518" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7520" class="Symbol">(</a><a id="7521" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7523" href="Assignment2.html#7494" class="Bound">B</a> <a id="7525" href="Assignment2.html#7516" class="Bound">x</a><a id="7526" class="Symbol">)</a>
      <a id="7534" class="Comment">--------------</a>
    <a id="7553" class="Symbol">→</a> <a id="7555" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7557" class="Symbol">(∀</a> <a id="7560" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7560" class="Bound">x</a> <a id="7562" class="Symbol">→</a> <a id="7564" href="Assignment2.html#7494" class="Bound">B</a> <a id="7566" href="Assignment2.html#7560" class="Bound">x</a><a id="7567" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers.

    data Bin : Set where
      nil : Bin
      x0_ : Bin → Bin
      x1_ : Bin → Bin

And ask you to define the following functions and predicates.

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties.

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
{% raw %}<pre class="Agda"><a id="8477" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="8489" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8489" class="Postulate Operator">_&lt;?_</a> <a id="8494" class="Symbol">:</a> <a id="8496" class="Symbol">∀</a> <a id="8498" class="Symbol">(</a><a id="8499" href="Assignment2.html#8499" class="Bound">m</a> <a id="8501" href="Assignment2.html#8501" class="Bound">n</a> <a id="8503" class="Symbol">:</a> <a id="8505" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8506" class="Symbol">)</a> <a id="8508" class="Symbol">→</a> <a id="8510" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8514" class="Symbol">(</a><a id="8515" href="Assignment2.html#8499" class="Bound">m</a> <a id="8517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#26539" class="Datatype Operator">&lt;</a> <a id="8519" href="Assignment2.html#8501" class="Bound">n</a><a id="8520" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
{% raw %}<pre class="Agda"><a id="8614" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="8626" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8626" class="Postulate Operator">_≡ℕ?_</a> <a id="8632" class="Symbol">:</a> <a id="8634" class="Symbol">∀</a> <a id="8636" class="Symbol">(</a><a id="8637" href="Assignment2.html#8637" class="Bound">m</a> <a id="8639" href="Assignment2.html#8639" class="Bound">n</a> <a id="8641" class="Symbol">:</a> <a id="8643" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8644" class="Symbol">)</a> <a id="8646" class="Symbol">→</a> <a id="8648" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8652" class="Symbol">(</a><a id="8653" href="Assignment2.html#8637" class="Bound">m</a> <a id="8655" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8657" href="Assignment2.html#8639" class="Bound">n</a><a id="8658" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
{% raw %}<pre class="Agda"><a id="8769" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="8781" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8781" class="Postulate">∧-×</a> <a id="8785" class="Symbol">:</a> <a id="8787" class="Symbol">∀</a> <a id="8789" class="Symbol">{</a><a id="8790" href="Assignment2.html#8790" class="Bound">A</a> <a id="8792" href="Assignment2.html#8792" class="Bound">B</a> <a id="8794" class="Symbol">:</a> <a id="8796" class="PrimitiveType">Set</a><a id="8799" class="Symbol">}</a> <a id="8801" class="Symbol">(</a><a id="8802" href="Assignment2.html#8802" class="Bound">x</a> <a id="8804" class="Symbol">:</a> <a id="8806" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8810" href="Assignment2.html#8790" class="Bound">A</a><a id="8811" class="Symbol">)</a> <a id="8813" class="Symbol">(</a><a id="8814" href="Assignment2.html#8814" class="Bound">y</a> <a id="8816" class="Symbol">:</a> <a id="8818" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8822" href="Assignment2.html#8792" class="Bound">B</a><a id="8823" class="Symbol">)</a> <a id="8825" class="Symbol">→</a> <a id="8827" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8829" href="Assignment2.html#8802" class="Bound">x</a> <a id="8831" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8833" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="8835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8837" href="Assignment2.html#8814" class="Bound">y</a> <a id="8839" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8841" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8843" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8845" href="Assignment2.html#8802" class="Bound">x</a> <a id="8847" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="8853" href="Assignment2.html#8814" class="Bound">y</a> <a id="8855" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-×"></a><a id="8859" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8859" class="Postulate">∨-×</a> <a id="8863" class="Symbol">:</a> <a id="8865" class="Symbol">∀</a> <a id="8867" class="Symbol">{</a><a id="8868" href="Assignment2.html#8868" class="Bound">A</a> <a id="8870" href="Assignment2.html#8870" class="Bound">B</a> <a id="8872" class="Symbol">:</a> <a id="8874" class="PrimitiveType">Set</a><a id="8877" class="Symbol">}</a> <a id="8879" class="Symbol">(</a><a id="8880" href="Assignment2.html#8880" class="Bound">x</a> <a id="8882" class="Symbol">:</a> <a id="8884" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8888" href="Assignment2.html#8868" class="Bound">A</a><a id="8889" class="Symbol">)</a> <a id="8891" class="Symbol">(</a><a id="8892" href="Assignment2.html#8892" class="Bound">y</a> <a id="8894" class="Symbol">:</a> <a id="8896" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8900" href="Assignment2.html#8870" class="Bound">B</a><a id="8901" class="Symbol">)</a> <a id="8903" class="Symbol">→</a> <a id="8905" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8907" href="Assignment2.html#8880" class="Bound">x</a> <a id="8909" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8911" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="8913" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8915" href="Assignment2.html#8892" class="Bound">y</a> <a id="8917" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8919" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8921" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8923" href="Assignment2.html#8880" class="Bound">x</a> <a id="8925" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="8931" href="Assignment2.html#8892" class="Bound">y</a> <a id="8933" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="8937" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8937" class="Postulate">not-¬</a> <a id="8943" class="Symbol">:</a> <a id="8945" class="Symbol">∀</a> <a id="8947" class="Symbol">{</a><a id="8948" href="Assignment2.html#8948" class="Bound">A</a> <a id="8950" class="Symbol">:</a> <a id="8952" class="PrimitiveType">Set</a><a id="8955" class="Symbol">}</a> <a id="8957" class="Symbol">(</a><a id="8958" href="Assignment2.html#8958" class="Bound">x</a> <a id="8960" class="Symbol">:</a> <a id="8962" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8966" href="Assignment2.html#8948" class="Bound">A</a><a id="8967" class="Symbol">)</a> <a id="8969" class="Symbol">→</a> <a id="8971" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="8975" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8977" href="Assignment2.html#8958" class="Bound">x</a> <a id="8979" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8981" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8983" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8985" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="8988" href="Assignment2.html#8958" class="Bound">x</a> <a id="8990" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
{% raw %}<pre class="Agda"><a id="9211" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="9223" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9223" class="Postulate Operator">_iff_</a> <a id="9229" class="Symbol">:</a> <a id="9231" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9236" class="Symbol">→</a> <a id="9238" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9243" class="Symbol">→</a> <a id="9245" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="9252" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9252" class="Postulate Operator">_⇔-dec_</a> <a id="9260" class="Symbol">:</a> <a id="9262" class="Symbol">∀</a> <a id="9264" class="Symbol">{</a><a id="9265" href="Assignment2.html#9265" class="Bound">A</a> <a id="9267" href="Assignment2.html#9267" class="Bound">B</a> <a id="9269" class="Symbol">:</a> <a id="9271" class="PrimitiveType">Set</a><a id="9274" class="Symbol">}</a> <a id="9276" class="Symbol">→</a> <a id="9278" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9282" href="Assignment2.html#9265" class="Bound">A</a> <a id="9284" class="Symbol">→</a> <a id="9286" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9290" href="Assignment2.html#9267" class="Bound">B</a> <a id="9292" class="Symbol">→</a> <a id="9294" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9298" class="Symbol">(</a><a id="9299" href="Assignment2.html#9265" class="Bound">A</a> <a id="9301" href="Assignment2.html#2636" class="Record Operator">⇔</a> <a id="9303" href="Assignment2.html#9267" class="Bound">B</a><a id="9304" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="9308" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9308" class="Postulate">iff-⇔</a> <a id="9314" class="Symbol">:</a> <a id="9316" class="Symbol">∀</a> <a id="9318" class="Symbol">{</a><a id="9319" href="Assignment2.html#9319" class="Bound">A</a> <a id="9321" href="Assignment2.html#9321" class="Bound">B</a> <a id="9323" class="Symbol">:</a> <a id="9325" class="PrimitiveType">Set</a><a id="9328" class="Symbol">}</a> <a id="9330" class="Symbol">(</a><a id="9331" href="Assignment2.html#9331" class="Bound">x</a> <a id="9333" class="Symbol">:</a> <a id="9335" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9339" href="Assignment2.html#9319" class="Bound">A</a><a id="9340" class="Symbol">)</a> <a id="9342" class="Symbol">(</a><a id="9343" href="Assignment2.html#9343" class="Bound">y</a> <a id="9345" class="Symbol">:</a> <a id="9347" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9351" href="Assignment2.html#9321" class="Bound">B</a><a id="9352" class="Symbol">)</a> <a id="9354" class="Symbol">→</a> <a id="9356" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9358" href="Assignment2.html#9331" class="Bound">x</a> <a id="9360" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9362" href="Assignment2.html#9223" class="Postulate Operator">iff</a> <a id="9366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9368" href="Assignment2.html#9343" class="Bound">y</a> <a id="9370" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9372" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9374" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9376" href="Assignment2.html#9331" class="Bound">x</a> <a id="9378" href="Assignment2.html#9252" class="Postulate Operator">⇔-dec</a> <a id="9384" href="Assignment2.html#9343" class="Bound">y</a> <a id="9386" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
