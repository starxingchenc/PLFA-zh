---
src       : "courses/puc/2019/Assignment3.lagda.md"
title     : "Assignment3: PUC Assignment 3"
layout    : page
permalink : /PUC/2019/Assignment3/
---

{% raw %}<pre class="Agda"><a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}" class="Module">Assignment3</a> <a id="129" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="555" class="Keyword">import</a> <a id="562" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="600" class="Symbol">as</a> <a id="603" class="Module">Eq</a>
<a id="606" class="Keyword">open</a> <a id="611" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="614" class="Keyword">using</a> <a id="620" class="Symbol">(</a><a id="621" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="624" class="Symbol">;</a> <a id="626" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="630" class="Symbol">;</a> <a id="632" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="636" class="Symbol">;</a> <a id="638" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="641" class="Symbol">)</a>
<a id="643" class="Keyword">open</a> <a id="648" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="676" class="Symbol">;</a> <a id="678" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="683" class="Symbol">;</a> <a id="685" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="691" class="Symbol">;</a> <a id="693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="695" class="Symbol">)</a>
<a id="697" class="Keyword">open</a> <a id="702" class="Keyword">import</a> <a id="709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="724" class="Keyword">using</a> <a id="730" class="Symbol">(</a><a id="731" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="735" class="Symbol">;</a> <a id="737" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="741" class="Symbol">;</a> <a id="743" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="748" class="Symbol">;</a> <a id="750" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="751" class="Symbol">;</a> <a id="753" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="756" class="Symbol">;</a> <a id="758" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="761" class="Symbol">;</a> <a id="763" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="766" class="Symbol">)</a>
<a id="768" class="Keyword">open</a> <a id="773" class="Keyword">import</a> <a id="780" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="789" class="Keyword">using</a> <a id="795" class="Symbol">(</a><a id="796" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="797" class="Symbol">;</a> <a id="799" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="803" class="Symbol">;</a> <a id="805" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="808" class="Symbol">;</a> <a id="810" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="813" class="Symbol">;</a> <a id="815" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="818" class="Symbol">;</a> <a id="820" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="823" class="Symbol">;</a> <a id="825" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="828" class="Symbol">;</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="833" class="Symbol">;</a> <a id="835" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="838" class="Symbol">)</a>
<a id="840" class="Keyword">open</a> <a id="845" class="Keyword">import</a> <a id="852" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="872" class="Keyword">using</a>
  <a id="880" class="Symbol">(</a><a id="881" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="888" class="Symbol">;</a> <a id="890" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11679" class="Function">+-identityˡ</a><a id="901" class="Symbol">;</a> <a id="903" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="914" class="Symbol">;</a> <a id="916" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#18464" class="Function">*-assoc</a><a id="923" class="Symbol">;</a> <a id="925" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17362" class="Function">*-identityˡ</a><a id="936" class="Symbol">;</a> <a id="938" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17426" class="Function">*-identityʳ</a><a id="949" class="Symbol">)</a>
<a id="951" class="Keyword">open</a> <a id="956" class="Keyword">import</a> <a id="963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="980" class="Keyword">using</a> <a id="986" class="Symbol">(</a><a id="987" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="989" class="Symbol">;</a> <a id="991" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="994" class="Symbol">;</a> <a id="996" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="999" class="Symbol">;</a> <a id="1001" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1003" class="Symbol">)</a>
<a id="1005" class="Keyword">open</a> <a id="1010" class="Keyword">import</a> <a id="1017" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1030" class="Keyword">using</a> <a id="1036" class="Symbol">(</a><a id="1037" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1040" class="Symbol">;</a> <a id="1042" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1043" class="Symbol">;</a> <a id="1045" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1053" class="Symbol">)</a> <a id="1055" class="Keyword">renaming</a> <a id="1064" class="Symbol">(</a><a id="1065" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1069" class="Symbol">to</a> <a id="1072" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1077" class="Symbol">)</a>
<a id="1079" class="Keyword">open</a> <a id="1084" class="Keyword">import</a> <a id="1091" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1102" class="Keyword">using</a> <a id="1108" class="Symbol">(</a><a id="1109" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1110" class="Symbol">;</a> <a id="1112" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1118" class="Symbol">)</a>
<a id="1120" class="Keyword">open</a> <a id="1125" class="Keyword">import</a> <a id="1132" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1141" class="Keyword">using</a> <a id="1147" class="Symbol">(</a><a id="1148" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1151" class="Symbol">)</a>
<a id="1153" class="Keyword">open</a> <a id="1158" class="Keyword">import</a> <a id="1165" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html" class="Module">Algebra.Structures</a> <a id="1184" class="Keyword">using</a> <a id="1190" class="Symbol">(</a><a id="1191" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html#2215" class="Record">IsMonoid</a><a id="1199" class="Symbol">)</a>
<a id="1201" class="Keyword">open</a> <a id="1206" class="Keyword">import</a> <a id="1213" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1219" class="Keyword">using</a> <a id="1225" class="Symbol">(</a><a id="1226" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1231" class="Symbol">)</a>
<a id="1233" class="Keyword">open</a> <a id="1238" class="Keyword">import</a> <a id="1245" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1260" class="Keyword">using</a> <a id="1266" class="Symbol">(</a><a id="1267" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1276" class="Symbol">)</a>
<a id="1278" class="Keyword">open</a> <a id="1283" class="Keyword">import</a> <a id="1290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1311" class="Keyword">using</a> <a id="1317" class="Symbol">(</a><a id="1318" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="1321" class="Symbol">;</a> <a id="1323" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="1326" class="Symbol">;</a> <a id="1328" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="1331" class="Symbol">)</a>
<a id="1333" class="Keyword">open</a> <a id="1338" class="Keyword">import</a> <a id="1345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1368" class="Keyword">using</a> <a id="1374" class="Symbol">(</a><a id="1375" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="1378" class="Symbol">;</a> <a id="1380" href="plfa.part1.Isomorphism.html#9384" class="Function">≃-sym</a><a id="1385" class="Symbol">;</a> <a id="1387" href="plfa.part1.Isomorphism.html#9781" class="Function">≃-trans</a><a id="1394" class="Symbol">;</a> <a id="1396" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">_≲_</a><a id="1399" class="Symbol">;</a> <a id="1401" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="1415" class="Symbol">)</a>
<a id="1417" class="Keyword">open</a> <a id="1422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
<a id="1457" class="Keyword">open</a> <a id="1462" class="Keyword">import</a> <a id="1469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}" class="Module">plfa.part1.Lists</a> <a id="1486" class="Keyword">using</a> <a id="1492" class="Symbol">(</a><a id="1493" href="plfa.part1.Lists.html#1296" class="Datatype">List</a><a id="1497" class="Symbol">;</a> <a id="1499" href="plfa.part1.Lists.html#1325" class="InductiveConstructor">[]</a><a id="1501" class="Symbol">;</a> <a id="1503" href="plfa.part1.Lists.html#1340" class="InductiveConstructor Operator">_∷_</a><a id="1506" class="Symbol">;</a> <a id="1508" href="plfa.part1.Lists.html#3830" class="Operator">[_]</a><a id="1511" class="Symbol">;</a> <a id="1513" href="plfa.part1.Lists.html#3853" class="Operator">[_,_]</a><a id="1518" class="Symbol">;</a> <a id="1520" href="plfa.part1.Lists.html#3884" class="Operator">[_,_,_]</a><a id="1527" class="Symbol">;</a> <a id="1529" href="plfa.part1.Lists.html#3923" class="Operator">[_,_,_,_]</a><a id="1538" class="Symbol">;</a>
  <a id="1542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#4663" class="Function Operator">_++_</a><a id="1546" class="Symbol">;</a> <a id="1548" href="plfa.part1.Lists.html#11326" class="Function">reverse</a><a id="1555" class="Symbol">;</a> <a id="1557" href="plfa.part1.Lists.html#17187" class="Function">map</a><a id="1560" class="Symbol">;</a> <a id="1562" href="plfa.part1.Lists.html#20421" class="Function">foldr</a><a id="1567" class="Symbol">;</a> <a id="1569" href="plfa.part1.Lists.html#21601" class="Function">sum</a><a id="1572" class="Symbol">;</a> <a id="1574" href="plfa.part1.Lists.html#28889" class="Datatype">All</a><a id="1577" class="Symbol">;</a> <a id="1579" href="plfa.part1.Lists.html#31035" class="Datatype">Any</a><a id="1582" class="Symbol">;</a> <a id="1584" href="plfa.part1.Lists.html#31086" class="InductiveConstructor">here</a><a id="1588" class="Symbol">;</a> <a id="1590" href="plfa.part1.Lists.html#31143" class="InductiveConstructor">there</a><a id="1595" class="Symbol">;</a> <a id="1597" href="plfa.part1.Lists.html#31550" class="Function Operator">_∈_</a><a id="1600" class="Symbol">)</a>
<a id="1602" class="Keyword">open</a> <a id="1607" class="Keyword">import</a> <a id="1614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}" class="Module">plfa.part2.Lambda</a> <a id="1632" class="Keyword">hiding</a> <a id="1639" class="Symbol">(</a><a id="1640" href="plfa.part2.Lambda.html#7385" class="Function Operator">ƛ′_⇒_</a><a id="1645" class="Symbol">;</a> <a id="1647" href="plfa.part2.Lambda.html#7506" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a><a id="1668" class="Symbol">;</a> <a id="1670" href="plfa.part2.Lambda.html#7720" class="Function Operator">μ′_⇒_</a><a id="1675" class="Symbol">;</a> <a id="1677" href="plfa.part2.Lambda.html#8474" class="Function">plus′</a><a id="1682" class="Symbol">)</a>
<a id="1684" class="Keyword">open</a> <a id="1689" class="Keyword">import</a> <a id="1696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Properties.md %}{% raw %}" class="Module">plfa.part2.Properties</a> <a id="1718" class="Keyword">hiding</a> <a id="1725" class="Symbol">(</a><a id="1726" href="plfa.part2.Properties.html#11767" class="Postulate">value?</a><a id="1732" class="Symbol">;</a> <a id="1734" href="plfa.part2.Properties.html#41613" class="Postulate">unstuck</a><a id="1741" class="Symbol">;</a> <a id="1743" href="plfa.part2.Properties.html#41813" class="Postulate">preserves</a><a id="1752" class="Symbol">;</a> <a id="1754" href="plfa.part2.Properties.html#42050" class="Postulate">wttdgs</a><a id="1760" class="Symbol">)</a>
</pre>{% endraw %}
## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="2033" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2033" class="Function Operator">ƛ′_⇒_</a> <a id="2039" class="Symbol">:</a> <a id="2041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3798" class="Datatype">Term</a> <a id="2046" class="Symbol">→</a> <a id="2048" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="2053" class="Symbol">→</a> <a id="2055" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="2060" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2033" class="Function Operator">ƛ′</a> <a id="2063" class="Symbol">(</a><a id="2064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2066" href="Assignment3.html#2066" class="Bound">x</a><a id="2067" class="Symbol">)</a> <a id="2069" href="Assignment3.html#2033" class="Function Operator">⇒</a> <a id="2071" href="Assignment3.html#2071" class="Bound">N</a>  <a id="2074" class="Symbol">=</a>  <a id="2077" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">ƛ</a> <a id="2079" href="Assignment3.html#2066" class="Bound">x</a> <a id="2081" href="plfa.part2.Lambda.html#3856" class="InductiveConstructor Operator">⇒</a> <a id="2083" href="Assignment3.html#2071" class="Bound">N</a>
<a id="2085" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2033" class="CatchallClause Function Operator">ƛ′</a><a id="2087" class="CatchallClause"> </a><a id="2088" class="CatchallClause Symbol">_</a><a id="2089" class="CatchallClause"> </a><a id="2090" href="Assignment3.html#2033" class="CatchallClause Function Operator">⇒</a><a id="2091" class="CatchallClause"> </a><a id="2092" class="CatchallClause Symbol">_</a>      <a id="2099" class="Symbol">=</a>  <a id="2102" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2109" href="Assignment3.html#2138" class="Postulate">impossible</a>
  <a id="2122" class="Keyword">where</a> <a id="2128" class="Keyword">postulate</a> <a id="2138" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2138" class="Postulate">impossible</a> <a id="2149" class="Symbol">:</a> <a id="2151" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="2154" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="2176" class="Symbol">:</a> <a id="2178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3798" class="Datatype">Term</a> <a id="2183" class="Symbol">→</a> <a id="2185" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="2190" class="Symbol">→</a> <a id="2192" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="2197" class="Symbol">→</a> <a id="2199" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="2204" class="Symbol">→</a> <a id="2206" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="2211" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="Function Operator">case′</a> <a id="2217" href="Assignment3.html#2217" class="Bound">L</a> <a id="2219" href="Assignment3.html#2154" class="Function Operator">[zero⇒</a> <a id="2226" href="Assignment3.html#2226" class="Bound">M</a> <a id="2228" href="Assignment3.html#2154" class="Function Operator">|suc</a> <a id="2233" class="Symbol">(</a><a id="2234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2236" href="Assignment3.html#2236" class="Bound">x</a><a id="2237" class="Symbol">)</a> <a id="2239" href="Assignment3.html#2154" class="Function Operator">⇒</a> <a id="2241" href="Assignment3.html#2241" class="Bound">N</a> <a id="2243" href="Assignment3.html#2154" class="Function Operator">]</a>  <a id="2246" class="Symbol">=</a>  <a id="2249" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">case</a> <a id="2254" href="Assignment3.html#2217" class="Bound">L</a> <a id="2256" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">[zero⇒</a> <a id="2263" href="Assignment3.html#2226" class="Bound">M</a> <a id="2265" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">|suc</a> <a id="2270" href="Assignment3.html#2236" class="Bound">x</a> <a id="2272" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">⇒</a> <a id="2274" href="Assignment3.html#2241" class="Bound">N</a> <a id="2276" href="plfa.part2.Lambda.html#4025" class="InductiveConstructor Operator">]</a>
<a id="2278" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="CatchallClause Function Operator">case′</a><a id="2283" class="CatchallClause"> </a><a id="2284" class="CatchallClause Symbol">_</a><a id="2285" class="CatchallClause"> </a><a id="2286" href="Assignment3.html#2154" class="CatchallClause Function Operator">[zero⇒</a><a id="2292" class="CatchallClause"> </a><a id="2293" class="CatchallClause Symbol">_</a><a id="2294" class="CatchallClause"> </a><a id="2295" href="Assignment3.html#2154" class="CatchallClause Function Operator">|suc</a><a id="2299" class="CatchallClause"> </a><a id="2300" class="CatchallClause Symbol">_</a><a id="2301" class="CatchallClause"> </a><a id="2302" href="Assignment3.html#2154" class="CatchallClause Function Operator">⇒</a><a id="2303" class="CatchallClause"> </a><a id="2304" class="CatchallClause Symbol">_</a><a id="2305" class="CatchallClause"> </a><a id="2306" href="Assignment3.html#2154" class="CatchallClause Function Operator">]</a>      <a id="2313" class="Symbol">=</a>  <a id="2316" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2323" href="Assignment3.html#2352" class="Postulate">impossible</a>
  <a id="2336" class="Keyword">where</a> <a id="2342" class="Keyword">postulate</a> <a id="2352" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2352" class="Postulate">impossible</a> <a id="2363" class="Symbol">:</a> <a id="2365" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="2368" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2368" class="Function Operator">μ′_⇒_</a> <a id="2374" class="Symbol">:</a> <a id="2376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3798" class="Datatype">Term</a> <a id="2381" class="Symbol">→</a> <a id="2383" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a> <a id="2388" class="Symbol">→</a> <a id="2390" href="plfa.part2.Lambda.html#3798" class="Datatype">Term</a>
<a id="2395" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2368" class="Function Operator">μ′</a> <a id="2398" class="Symbol">(</a><a id="2399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2401" href="Assignment3.html#2401" class="Bound">x</a><a id="2402" class="Symbol">)</a> <a id="2404" href="Assignment3.html#2368" class="Function Operator">⇒</a> <a id="2406" href="Assignment3.html#2406" class="Bound">N</a>  <a id="2409" class="Symbol">=</a>  <a id="2412" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">μ</a> <a id="2414" href="Assignment3.html#2401" class="Bound">x</a> <a id="2416" href="plfa.part2.Lambda.html#4085" class="InductiveConstructor Operator">⇒</a> <a id="2418" href="Assignment3.html#2406" class="Bound">N</a>
<a id="2420" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2368" class="CatchallClause Function Operator">μ′</a><a id="2422" class="CatchallClause"> </a><a id="2423" class="CatchallClause Symbol">_</a><a id="2424" class="CatchallClause"> </a><a id="2425" href="Assignment3.html#2368" class="CatchallClause Function Operator">⇒</a><a id="2426" class="CatchallClause"> </a><a id="2427" class="CatchallClause Symbol">_</a>      <a id="2434" class="Symbol">=</a>  <a id="2437" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2444" href="Assignment3.html#2473" class="Postulate">impossible</a>
  <a id="2457" class="Keyword">where</a> <a id="2463" class="Keyword">postulate</a> <a id="2473" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2473" class="Postulate">impossible</a> <a id="2484" class="Symbol">:</a> <a id="2486" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows.
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="2552" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2552" class="Function">plus′</a> <a id="2558" class="Symbol">:</a> <a id="2560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3798" class="Datatype">Term</a>
<a id="2565" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2552" class="Function">plus′</a> <a id="2571" class="Symbol">=</a> <a id="2573" href="Assignment3.html#2368" class="Function Operator">μ′</a> <a id="2576" href="Assignment3.html#2683" class="Function">+</a> <a id="2578" href="Assignment3.html#2368" class="Function Operator">⇒</a> <a id="2580" href="Assignment3.html#2033" class="Function Operator">ƛ′</a> <a id="2583" href="Assignment3.html#2697" class="Function">m</a> <a id="2585" href="Assignment3.html#2033" class="Function Operator">⇒</a> <a id="2587" href="Assignment3.html#2033" class="Function Operator">ƛ′</a> <a id="2590" href="Assignment3.html#2711" class="Function">n</a> <a id="2592" href="Assignment3.html#2033" class="Function Operator">⇒</a>
          <a id="2604" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="Function Operator">case′</a> <a id="2610" href="Assignment3.html#2697" class="Function">m</a>
            <a id="2624" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="Function Operator">[zero⇒</a> <a id="2631" href="Assignment3.html#2711" class="Function">n</a>
            <a id="2645" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2154" class="Function Operator">|suc</a> <a id="2650" href="Assignment3.html#2697" class="Function">m</a> <a id="2652" href="Assignment3.html#2154" class="Function Operator">⇒</a> <a id="2654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3984" class="InductiveConstructor Operator">`suc</a> <a id="2659" class="Symbol">(</a><a id="2660" href="Assignment3.html#2683" class="Function">+</a> <a id="2662" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="2664" href="Assignment3.html#2697" class="Function">m</a> <a id="2666" href="plfa.part2.Lambda.html#3902" class="InductiveConstructor Operator">·</a> <a id="2668" href="Assignment3.html#2711" class="Function">n</a><a id="2669" class="Symbol">)</a> <a id="2671" href="Assignment3.html#2154" class="Function Operator">]</a>
  <a id="2675" class="Keyword">where</a>
  <a id="2683" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2683" class="Function">+</a>  <a id="2686" class="Symbol">=</a>  <a id="2689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2691" class="String">&quot;+&quot;</a>
  <a id="2697" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2697" class="Function">m</a>  <a id="2700" class="Symbol">=</a>  <a id="2703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2705" class="String">&quot;m&quot;</a>
  <a id="2711" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2711" class="Function">n</a>  <a id="2714" class="Symbol">=</a>  <a id="2717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3817" class="InductiveConstructor Operator">`</a> <a id="2719" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.


#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.


#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
{% raw %}<pre class="Agda"><a id="3862" class="Keyword">postulate</a>
  <a id="value?"></a><a id="3874" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#3874" class="Postulate">value?</a> <a id="3881" class="Symbol">:</a> <a id="3883" class="Symbol">∀</a> <a id="3885" class="Symbol">{</a><a id="3886" href="Assignment3.html#3886" class="Bound">A</a> <a id="3888" href="Assignment3.html#3888" class="Bound">M</a><a id="3889" class="Symbol">}</a> <a id="3891" class="Symbol">→</a> <a id="3893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31718" class="InductiveConstructor">∅</a> <a id="3895" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⊢</a> <a id="3897" href="Assignment3.html#3888" class="Bound">M</a> <a id="3899" href="plfa.part2.Lambda.html#34094" class="Datatype Operator">⦂</a> <a id="3901" href="Assignment3.html#3886" class="Bound">A</a> <a id="3903" class="Symbol">→</a> <a id="3905" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="3909" class="Symbol">(</a><a id="3910" href="plfa.part2.Lambda.html#12177" class="Datatype">Value</a> <a id="3916" href="Assignment3.html#3888" class="Bound">M</a><a id="3917" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.


#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.


#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.
