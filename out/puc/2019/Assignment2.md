---
src       : "courses/puc/2019/Assignment2.lagda.md"
title     : "Assignment2: PUC Assignment 2"
layout    : page
permalink : /PUC/2019/Assignment2/
---

{% raw %}<pre class="Agda"><a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}" class="Module">Assignment2</a> <a id="129" class="Keyword">where</a>
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
<a id="697" class="Keyword">open</a> <a id="702" class="Keyword">import</a> <a id="709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="718" class="Keyword">using</a> <a id="724" class="Symbol">(</a><a id="725" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="726" class="Symbol">;</a> <a id="728" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="732" class="Symbol">;</a> <a id="734" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="737" class="Symbol">;</a> <a id="739" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="742" class="Symbol">;</a> <a id="744" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="747" class="Symbol">;</a> <a id="749" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="752" class="Symbol">;</a> <a id="754" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="757" class="Symbol">;</a> <a id="759" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="762" class="Symbol">;</a> <a id="764" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="767" class="Symbol">)</a>
<a id="769" class="Keyword">open</a> <a id="774" class="Keyword">import</a> <a id="781" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="801" class="Keyword">using</a> <a id="807" class="Symbol">(</a><a id="808" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="815" class="Symbol">;</a> <a id="817" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="828" class="Symbol">;</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="835" class="Symbol">;</a> <a id="837" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="843" class="Symbol">;</a>
  <a id="847" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="853" class="Symbol">;</a> <a id="855" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="862" class="Symbol">;</a> <a id="864" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="873" class="Symbol">;</a> <a id="875" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="882" class="Symbol">;</a> <a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="893" class="Symbol">;</a> <a id="895" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="904" class="Symbol">;</a> <a id="906" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="914" class="Symbol">)</a>
<a id="916" class="Keyword">open</a> <a id="921" class="Keyword">import</a> <a id="928" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="941" class="Keyword">using</a> <a id="947" class="Symbol">(</a><a id="948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="951" class="Symbol">;</a> <a id="953" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="958" class="Symbol">;</a> <a id="960" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="965" class="Symbol">)</a> <a id="967" class="Keyword">renaming</a> <a id="976" class="Symbol">(</a><a id="977" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="981" class="Symbol">to</a> <a id="984" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="989" class="Symbol">)</a>
<a id="991" class="Keyword">open</a> <a id="996" class="Keyword">import</a> <a id="1003" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1016" class="Keyword">using</a> <a id="1022" class="Symbol">(</a><a id="1023" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="1024" class="Symbol">;</a> <a id="1026" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1027" class="Symbol">;</a> <a id="1029" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="1037" class="Symbol">;</a> <a id="1039" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1047" class="Symbol">)</a>
<a id="1049" class="Keyword">open</a> <a id="1054" class="Keyword">import</a> <a id="1061" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1071" class="Keyword">using</a> <a id="1077" class="Symbol">(</a><a id="1078" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1079" class="Symbol">;</a> <a id="1081" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1083" class="Symbol">)</a>
<a id="1085" class="Keyword">open</a> <a id="1090" class="Keyword">import</a> <a id="1097" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1106" class="Keyword">using</a> <a id="1112" class="Symbol">(</a><a id="1113" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1116" class="Symbol">;</a> <a id="1118" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1122" class="Symbol">;</a> <a id="1124" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1128" class="Symbol">)</a> <a id="1130" class="Keyword">renaming</a> <a id="1139" class="Symbol">(</a><a id="1140" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1146" class="Symbol">to</a> <a id="1149" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1155" class="Symbol">)</a>
<a id="1157" class="Keyword">open</a> <a id="1162" class="Keyword">import</a> <a id="1169" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1180" class="Keyword">using</a> <a id="1186" class="Symbol">(</a><a id="1187" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1188" class="Symbol">;</a> <a id="1190" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1196" class="Symbol">)</a>
<a id="1198" class="Keyword">open</a> <a id="1203" class="Keyword">import</a> <a id="1210" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1225" class="Keyword">using</a> <a id="1231" class="Symbol">(</a><a id="1232" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1236" class="Symbol">;</a> <a id="1238" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1242" class="Symbol">;</a> <a id="1244" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1249" class="Symbol">;</a> <a id="1251" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1252" class="Symbol">;</a> <a id="1254" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1257" class="Symbol">;</a> <a id="1259" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1262" class="Symbol">;</a> <a id="1264" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1267" class="Symbol">)</a>
<a id="1269" class="Keyword">open</a> <a id="1274" class="Keyword">import</a> <a id="1281" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1298" class="Keyword">using</a> <a id="1304" class="Symbol">(</a><a id="1305" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1307" class="Symbol">;</a> <a id="1309" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1312" class="Symbol">;</a> <a id="1314" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1317" class="Symbol">;</a> <a id="1319" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1321" class="Symbol">)</a>
<a id="1323" class="Keyword">open</a> <a id="1328" class="Keyword">import</a> <a id="1335" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1362" class="Keyword">using</a> <a id="1368" class="Symbol">(</a><a id="1369" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1372" class="Symbol">;</a> <a id="1374" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1383" class="Symbol">;</a> <a id="1385" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1396" class="Symbol">)</a>
<a id="1398" class="Keyword">open</a> <a id="1403" class="Keyword">import</a> <a id="1410" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1436" class="Keyword">using</a> <a id="1442" class="Symbol">(</a><a id="1443" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="1445" class="Symbol">)</a>
<a id="1447" class="Keyword">open</a> <a id="1452" class="Keyword">import</a> <a id="1459" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="1484" class="Keyword">using</a> <a id="1490" class="Symbol">(</a><a id="1491" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="1498" class="Symbol">)</a>
<a id="1500" class="Keyword">open</a> <a id="1505" class="Keyword">import</a> <a id="1512" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="1533" class="Keyword">using</a> <a id="1539" class="Symbol">(</a><a id="1540" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="1547" class="Symbol">)</a>
<a id="1549" class="Keyword">open</a> <a id="1554" class="Keyword">import</a> <a id="1561" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1587" class="Keyword">using</a> <a id="1593" class="Symbol">(</a><a id="1594" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="1608" class="Symbol">)</a>
<a id="1610" class="Keyword">open</a> <a id="1615" class="Keyword">import</a> <a id="1622" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1637" class="Keyword">using</a> <a id="1643" class="Symbol">(</a><a id="1644" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1653" class="Symbol">)</a>
<a id="1655" class="Keyword">open</a> <a id="1660" class="Keyword">import</a> <a id="1667" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1676" class="Keyword">using</a> <a id="1682" class="Symbol">(</a><a id="1683" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1686" class="Symbol">)</a>
<a id="1688" class="Keyword">open</a> <a id="1693" class="Keyword">import</a> <a id="1700" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1706" class="Keyword">using</a> <a id="1712" class="Symbol">(</a><a id="1713" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1718" class="Symbol">)</a>
<a id="1720" class="Keyword">open</a> <a id="1725" class="Keyword">import</a> <a id="1732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1753" class="Keyword">using</a> <a id="1759" class="Symbol">(</a><a id="1760" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="1763" class="Symbol">;</a> <a id="1765" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="1768" class="Symbol">;</a> <a id="1770" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="1773" class="Symbol">)</a>
<a id="1775" class="Keyword">open</a> <a id="1780" class="Keyword">import</a> <a id="1787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1810" class="Keyword">using</a> <a id="1816" class="Symbol">(</a><a id="1817" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="1820" class="Symbol">;</a> <a id="1822" href="plfa.part1.Isomorphism.html#9384" class="Function">≃-sym</a><a id="1827" class="Symbol">;</a> <a id="1829" href="plfa.part1.Isomorphism.html#9781" class="Function">≃-trans</a><a id="1836" class="Symbol">;</a> <a id="1838" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">_≲_</a><a id="1841" class="Symbol">;</a> <a id="1843" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="1857" class="Symbol">)</a>
<a id="1859" class="Keyword">open</a> <a id="1864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
<a id="1899" class="Keyword">open</a> <a id="1904" class="Keyword">import</a> <a id="1911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}" class="Module">plfa.part1.Lists</a> <a id="1928" class="Keyword">using</a> <a id="1934" class="Symbol">(</a><a id="1935" href="plfa.part1.Lists.html#1296" class="Datatype">List</a><a id="1939" class="Symbol">;</a> <a id="1941" href="plfa.part1.Lists.html#1325" class="InductiveConstructor">[]</a><a id="1943" class="Symbol">;</a> <a id="1945" href="plfa.part1.Lists.html#1340" class="InductiveConstructor Operator">_∷_</a><a id="1948" class="Symbol">;</a> <a id="1950" href="plfa.part1.Lists.html#3830" class="Operator">[_]</a><a id="1953" class="Symbol">;</a> <a id="1955" href="plfa.part1.Lists.html#3853" class="Operator">[_,_]</a><a id="1960" class="Symbol">;</a> <a id="1962" href="plfa.part1.Lists.html#3884" class="Operator">[_,_,_]</a><a id="1969" class="Symbol">;</a> <a id="1971" href="plfa.part1.Lists.html#3923" class="Operator">[_,_,_,_]</a><a id="1980" class="Symbol">;</a>
  <a id="1984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#4663" class="Function Operator">_++_</a><a id="1988" class="Symbol">;</a> <a id="1990" href="plfa.part1.Lists.html#11326" class="Function">reverse</a><a id="1997" class="Symbol">;</a> <a id="1999" href="plfa.part1.Lists.html#17187" class="Function">map</a><a id="2002" class="Symbol">;</a> <a id="2004" href="plfa.part1.Lists.html#20421" class="Function">foldr</a><a id="2009" class="Symbol">;</a> <a id="2011" href="plfa.part1.Lists.html#21601" class="Function">sum</a><a id="2014" class="Symbol">;</a> <a id="2016" href="plfa.part1.Lists.html#28889" class="Datatype">All</a><a id="2019" class="Symbol">;</a> <a id="2021" href="plfa.part1.Lists.html#31035" class="Datatype">Any</a><a id="2024" class="Symbol">;</a> <a id="2026" href="plfa.part1.Lists.html#31086" class="InductiveConstructor">here</a><a id="2030" class="Symbol">;</a> <a id="2032" href="plfa.part1.Lists.html#31143" class="InductiveConstructor">there</a><a id="2037" class="Symbol">;</a> <a id="2039" href="plfa.part1.Lists.html#31550" class="Function Operator">_∈_</a><a id="2042" class="Symbol">)</a>
</pre>{% endraw %}
## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an analogue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="2541" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="2553" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2553" class="Postulate">≃-implies-≲</a> <a id="2565" class="Symbol">:</a> <a id="2567" class="Symbol">∀</a> <a id="2569" class="Symbol">{</a><a id="2570" href="Assignment2.html#2570" class="Bound">A</a> <a id="2572" href="Assignment2.html#2572" class="Bound">B</a> <a id="2574" class="Symbol">:</a> <a id="2576" class="PrimitiveType">Set</a><a id="2579" class="Symbol">}</a>
    <a id="2585" class="Symbol">→</a> <a id="2587" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2570" class="Bound">A</a> <a id="2589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="2591" href="Assignment2.html#2572" class="Bound">B</a>
      <a id="2599" class="Comment">-----</a>
    <a id="2609" class="Symbol">→</a> <a id="2611" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2570" class="Bound">A</a> <a id="2613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">≲</a> <a id="2615" href="Assignment2.html#2572" class="Bound">B</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
{% raw %}<pre class="Agda"><a id="2748" class="Keyword">record</a> <a id="_⇔_"></a><a id="2755" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2755" class="Record Operator">_⇔_</a> <a id="2759" class="Symbol">(</a><a id="2760" href="Assignment2.html#2760" class="Bound">A</a> <a id="2762" href="Assignment2.html#2762" class="Bound">B</a> <a id="2764" class="Symbol">:</a> <a id="2766" class="PrimitiveType">Set</a><a id="2769" class="Symbol">)</a> <a id="2771" class="Symbol">:</a> <a id="2773" class="PrimitiveType">Set</a> <a id="2777" class="Keyword">where</a>
  <a id="2785" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="2795" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2795" class="Field">to</a>   <a id="2800" class="Symbol">:</a> <a id="2802" href="Assignment2.html#2760" class="Bound">A</a> <a id="2804" class="Symbol">→</a> <a id="2806" href="Assignment2.html#2762" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="2812" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2812" class="Field">from</a> <a id="2817" class="Symbol">:</a> <a id="2819" href="Assignment2.html#2762" class="Bound">B</a> <a id="2821" class="Symbol">→</a> <a id="2823" href="Assignment2.html#2760" class="Bound">A</a>

<a id="2826" class="Keyword">open</a> <a id="2831" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#2755" class="Module Operator">_⇔_</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
{% raw %}<pre class="Agda"><a id="3114" class="Keyword">data</a> <a id="Bin"></a><a id="3119" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#3119" class="Datatype">Bin</a> <a id="3123" class="Symbol">:</a> <a id="3125" class="PrimitiveType">Set</a> <a id="3129" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="3137" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#3137" class="InductiveConstructor">nil</a> <a id="3141" class="Symbol">:</a> <a id="3143" href="Assignment2.html#3119" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="3149" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#3149" class="InductiveConstructor Operator">x0_</a> <a id="3153" class="Symbol">:</a> <a id="3155" href="Assignment2.html#3119" class="Datatype">Bin</a> <a id="3159" class="Symbol">→</a> <a id="3161" href="Assignment2.html#3119" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="3167" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#3167" class="InductiveConstructor Operator">x1_</a> <a id="3171" class="Symbol">:</a> <a id="3173" href="Assignment2.html#3119" class="Datatype">Bin</a> <a id="3177" class="Symbol">→</a> <a id="3179" href="Assignment2.html#3119" class="Datatype">Bin</a>
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

Show sum is associative up to isomorphism.

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition.

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
{% raw %}<pre class="Agda"><a id="3989" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="4001" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#4001" class="Postulate">⊎-weak-×</a> <a id="4010" class="Symbol">:</a> <a id="4012" class="Symbol">∀</a> <a id="4014" class="Symbol">{</a><a id="4015" href="Assignment2.html#4015" class="Bound">A</a> <a id="4017" href="Assignment2.html#4017" class="Bound">B</a> <a id="4019" href="Assignment2.html#4019" class="Bound">C</a> <a id="4021" class="Symbol">:</a> <a id="4023" class="PrimitiveType">Set</a><a id="4026" class="Symbol">}</a> <a id="4028" class="Symbol">→</a> <a id="4030" class="Symbol">(</a><a id="4031" href="Assignment2.html#4015" class="Bound">A</a> <a id="4033" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4035" href="Assignment2.html#4017" class="Bound">B</a><a id="4036" class="Symbol">)</a> <a id="4038" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4040" href="Assignment2.html#4019" class="Bound">C</a> <a id="4042" class="Symbol">→</a> <a id="4044" href="Assignment2.html#4015" class="Bound">A</a> <a id="4046" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4048" class="Symbol">(</a><a id="4049" href="Assignment2.html#4017" class="Bound">B</a> <a id="4051" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4053" href="Assignment2.html#4019" class="Bound">C</a><a id="4054" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
{% raw %}<pre class="Agda"><a id="4294" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="4306" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#4306" class="Postulate">⊎×-implies-×⊎</a> <a id="4320" class="Symbol">:</a> <a id="4322" class="Symbol">∀</a> <a id="4324" class="Symbol">{</a><a id="4325" href="Assignment2.html#4325" class="Bound">A</a> <a id="4327" href="Assignment2.html#4327" class="Bound">B</a> <a id="4329" href="Assignment2.html#4329" class="Bound">C</a> <a id="4331" href="Assignment2.html#4331" class="Bound">D</a> <a id="4333" class="Symbol">:</a> <a id="4335" class="PrimitiveType">Set</a><a id="4338" class="Symbol">}</a> <a id="4340" class="Symbol">→</a> <a id="4342" class="Symbol">(</a><a id="4343" href="Assignment2.html#4325" class="Bound">A</a> <a id="4345" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4347" href="Assignment2.html#4327" class="Bound">B</a><a id="4348" class="Symbol">)</a> <a id="4350" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4352" class="Symbol">(</a><a id="4353" href="Assignment2.html#4329" class="Bound">C</a> <a id="4355" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4357" href="Assignment2.html#4331" class="Bound">D</a><a id="4358" class="Symbol">)</a> <a id="4360" class="Symbol">→</a> <a id="4362" class="Symbol">(</a><a id="4363" href="Assignment2.html#4325" class="Bound">A</a> <a id="4365" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4367" href="Assignment2.html#4329" class="Bound">C</a><a id="4368" class="Symbol">)</a> <a id="4370" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4372" class="Symbol">(</a><a id="4373" href="Assignment2.html#4327" class="Bound">B</a> <a id="4375" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4377" href="Assignment2.html#4331" class="Bound">D</a><a id="4378" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="5860" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#5860" class="Function">Stable</a> <a id="5867" class="Symbol">:</a> <a id="5869" class="PrimitiveType">Set</a> <a id="5873" class="Symbol">→</a> <a id="5875" class="PrimitiveType">Set</a>
<a id="5879" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#5860" class="Function">Stable</a> <a id="5886" href="Assignment2.html#5886" class="Bound">A</a> <a id="5888" class="Symbol">=</a> <a id="5890" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5892" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5894" href="Assignment2.html#5886" class="Bound">A</a> <a id="5896" class="Symbol">→</a> <a id="5898" href="Assignment2.html#5886" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
{% raw %}<pre class="Agda"><a id="6119" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="6131" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6131" class="Postulate">∀-distrib-×</a> <a id="6143" class="Symbol">:</a> <a id="6145" class="Symbol">∀</a> <a id="6147" class="Symbol">{</a><a id="6148" href="Assignment2.html#6148" class="Bound">A</a> <a id="6150" class="Symbol">:</a> <a id="6152" class="PrimitiveType">Set</a><a id="6155" class="Symbol">}</a> <a id="6157" class="Symbol">{</a><a id="6158" href="Assignment2.html#6158" class="Bound">B</a> <a id="6160" href="Assignment2.html#6160" class="Bound">C</a> <a id="6162" class="Symbol">:</a> <a id="6164" href="Assignment2.html#6148" class="Bound">A</a> <a id="6166" class="Symbol">→</a> <a id="6168" class="PrimitiveType">Set</a><a id="6171" class="Symbol">}</a> <a id="6173" class="Symbol">→</a>
    <a id="6179" class="Symbol">(∀</a> <a id="6182" class="Symbol">(</a><a id="6183" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6183" class="Bound">x</a> <a id="6185" class="Symbol">:</a> <a id="6187" href="Assignment2.html#6148" class="Bound">A</a><a id="6188" class="Symbol">)</a> <a id="6190" class="Symbol">→</a> <a id="6192" href="Assignment2.html#6158" class="Bound">B</a> <a id="6194" href="Assignment2.html#6183" class="Bound">x</a> <a id="6196" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6198" href="Assignment2.html#6160" class="Bound">C</a> <a id="6200" href="Assignment2.html#6183" class="Bound">x</a><a id="6201" class="Symbol">)</a> <a id="6203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="6205" class="Symbol">(∀</a> <a id="6208" class="Symbol">(</a><a id="6209" href="Assignment2.html#6209" class="Bound">x</a> <a id="6211" class="Symbol">:</a> <a id="6213" href="Assignment2.html#6148" class="Bound">A</a><a id="6214" class="Symbol">)</a> <a id="6216" class="Symbol">→</a> <a id="6218" href="Assignment2.html#6158" class="Bound">B</a> <a id="6220" href="Assignment2.html#6209" class="Bound">x</a><a id="6221" class="Symbol">)</a> <a id="6223" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6225" class="Symbol">(∀</a> <a id="6228" class="Symbol">(</a><a id="6229" href="Assignment2.html#6229" class="Bound">x</a> <a id="6231" class="Symbol">:</a> <a id="6233" href="Assignment2.html#6148" class="Bound">A</a><a id="6234" class="Symbol">)</a> <a id="6236" class="Symbol">→</a> <a id="6238" href="Assignment2.html#6160" class="Bound">C</a> <a id="6240" href="Assignment2.html#6229" class="Bound">x</a><a id="6241" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
{% raw %}<pre class="Agda"><a id="6447" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="6459" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6459" class="Postulate">⊎∀-implies-∀⊎</a> <a id="6473" class="Symbol">:</a> <a id="6475" class="Symbol">∀</a> <a id="6477" class="Symbol">{</a><a id="6478" href="Assignment2.html#6478" class="Bound">A</a> <a id="6480" class="Symbol">:</a> <a id="6482" class="PrimitiveType">Set</a><a id="6485" class="Symbol">}</a> <a id="6487" class="Symbol">{</a> <a id="6489" href="Assignment2.html#6489" class="Bound">B</a> <a id="6491" href="Assignment2.html#6491" class="Bound">C</a> <a id="6493" class="Symbol">:</a> <a id="6495" href="Assignment2.html#6478" class="Bound">A</a> <a id="6497" class="Symbol">→</a> <a id="6499" class="PrimitiveType">Set</a> <a id="6503" class="Symbol">}</a> <a id="6505" class="Symbol">→</a>
    <a id="6511" class="Symbol">(∀</a> <a id="6514" class="Symbol">(</a><a id="6515" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6515" class="Bound">x</a> <a id="6517" class="Symbol">:</a> <a id="6519" href="Assignment2.html#6478" class="Bound">A</a><a id="6520" class="Symbol">)</a> <a id="6522" class="Symbol">→</a> <a id="6524" href="Assignment2.html#6489" class="Bound">B</a> <a id="6526" href="Assignment2.html#6515" class="Bound">x</a><a id="6527" class="Symbol">)</a> <a id="6529" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6531" class="Symbol">(∀</a> <a id="6534" class="Symbol">(</a><a id="6535" href="Assignment2.html#6535" class="Bound">x</a> <a id="6537" class="Symbol">:</a> <a id="6539" href="Assignment2.html#6478" class="Bound">A</a><a id="6540" class="Symbol">)</a> <a id="6542" class="Symbol">→</a> <a id="6544" href="Assignment2.html#6491" class="Bound">C</a> <a id="6546" href="Assignment2.html#6535" class="Bound">x</a><a id="6547" class="Symbol">)</a>  <a id="6550" class="Symbol">→</a>  <a id="6553" class="Symbol">∀</a> <a id="6555" class="Symbol">(</a><a id="6556" href="Assignment2.html#6556" class="Bound">x</a> <a id="6558" class="Symbol">:</a> <a id="6560" href="Assignment2.html#6478" class="Bound">A</a><a id="6561" class="Symbol">)</a> <a id="6563" class="Symbol">→</a> <a id="6565" href="Assignment2.html#6489" class="Bound">B</a> <a id="6567" href="Assignment2.html#6556" class="Bound">x</a> <a id="6569" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6571" href="Assignment2.html#6491" class="Bound">C</a> <a id="6573" href="Assignment2.html#6556" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
{% raw %}<pre class="Agda"><a id="6738" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="6750" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6750" class="Postulate">∃-distrib-⊎</a> <a id="6762" class="Symbol">:</a> <a id="6764" class="Symbol">∀</a> <a id="6766" class="Symbol">{</a><a id="6767" href="Assignment2.html#6767" class="Bound">A</a> <a id="6769" class="Symbol">:</a> <a id="6771" class="PrimitiveType">Set</a><a id="6774" class="Symbol">}</a> <a id="6776" class="Symbol">{</a><a id="6777" href="Assignment2.html#6777" class="Bound">B</a> <a id="6779" href="Assignment2.html#6779" class="Bound">C</a> <a id="6781" class="Symbol">:</a> <a id="6783" href="Assignment2.html#6767" class="Bound">A</a> <a id="6785" class="Symbol">→</a> <a id="6787" class="PrimitiveType">Set</a><a id="6790" class="Symbol">}</a> <a id="6792" class="Symbol">→</a>
    <a id="6798" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6801" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6801" class="Bound">x</a> <a id="6803" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6805" class="Symbol">(</a><a id="6806" href="Assignment2.html#6777" class="Bound">B</a> <a id="6808" href="Assignment2.html#6801" class="Bound">x</a> <a id="6810" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6812" href="Assignment2.html#6779" class="Bound">C</a> <a id="6814" href="Assignment2.html#6801" class="Bound">x</a><a id="6815" class="Symbol">)</a> <a id="6817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="6819" class="Symbol">(</a><a id="6820" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6823" href="Assignment2.html#6823" class="Bound">x</a> <a id="6825" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6827" href="Assignment2.html#6777" class="Bound">B</a> <a id="6829" href="Assignment2.html#6823" class="Bound">x</a><a id="6830" class="Symbol">)</a> <a id="6832" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6834" class="Symbol">(</a><a id="6835" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6838" href="Assignment2.html#6838" class="Bound">x</a> <a id="6840" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6842" href="Assignment2.html#6779" class="Bound">C</a> <a id="6844" href="Assignment2.html#6838" class="Bound">x</a><a id="6845" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
{% raw %}<pre class="Agda"><a id="6967" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="6979" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#6979" class="Postulate">∃×-implies-×∃</a> <a id="6993" class="Symbol">:</a> <a id="6995" class="Symbol">∀</a> <a id="6997" class="Symbol">{</a><a id="6998" href="Assignment2.html#6998" class="Bound">A</a> <a id="7000" class="Symbol">:</a> <a id="7002" class="PrimitiveType">Set</a><a id="7005" class="Symbol">}</a> <a id="7007" class="Symbol">{</a> <a id="7009" href="Assignment2.html#7009" class="Bound">B</a> <a id="7011" href="Assignment2.html#7011" class="Bound">C</a> <a id="7013" class="Symbol">:</a> <a id="7015" href="Assignment2.html#6998" class="Bound">A</a> <a id="7017" class="Symbol">→</a> <a id="7019" class="PrimitiveType">Set</a> <a id="7023" class="Symbol">}</a> <a id="7025" class="Symbol">→</a>
    <a id="7031" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7034" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#7034" class="Bound">x</a> <a id="7036" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7038" class="Symbol">(</a><a id="7039" href="Assignment2.html#7009" class="Bound">B</a> <a id="7041" href="Assignment2.html#7034" class="Bound">x</a> <a id="7043" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7045" href="Assignment2.html#7011" class="Bound">C</a> <a id="7047" href="Assignment2.html#7034" class="Bound">x</a><a id="7048" class="Symbol">)</a> <a id="7050" class="Symbol">→</a> <a id="7052" class="Symbol">(</a><a id="7053" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7056" href="Assignment2.html#7056" class="Bound">x</a> <a id="7058" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7060" href="Assignment2.html#7009" class="Bound">B</a> <a id="7062" href="Assignment2.html#7056" class="Bound">x</a><a id="7063" class="Symbol">)</a> <a id="7065" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7067" class="Symbol">(</a><a id="7068" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7071" href="Assignment2.html#7071" class="Bound">x</a> <a id="7073" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7075" href="Assignment2.html#7011" class="Bound">C</a> <a id="7077" href="Assignment2.html#7071" class="Bound">x</a><a id="7078" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-|-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
{% raw %}<pre class="Agda"><a id="7573" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="7585" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#7585" class="Postulate">∃¬-implies-¬∀</a> <a id="7599" class="Symbol">:</a> <a id="7601" class="Symbol">∀</a> <a id="7603" class="Symbol">{</a><a id="7604" href="Assignment2.html#7604" class="Bound">A</a> <a id="7606" class="Symbol">:</a> <a id="7608" class="PrimitiveType">Set</a><a id="7611" class="Symbol">}</a> <a id="7613" class="Symbol">{</a><a id="7614" href="Assignment2.html#7614" class="Bound">B</a> <a id="7616" class="Symbol">:</a> <a id="7618" href="Assignment2.html#7604" class="Bound">A</a> <a id="7620" class="Symbol">→</a> <a id="7622" class="PrimitiveType">Set</a><a id="7625" class="Symbol">}</a>
    <a id="7631" class="Symbol">→</a> <a id="7633" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7636" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#7636" class="Bound">x</a> <a id="7638" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7640" class="Symbol">(</a><a id="7641" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7643" href="Assignment2.html#7614" class="Bound">B</a> <a id="7645" href="Assignment2.html#7636" class="Bound">x</a><a id="7646" class="Symbol">)</a>
      <a id="7654" class="Comment">--------------</a>
    <a id="7673" class="Symbol">→</a> <a id="7675" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7677" class="Symbol">(∀</a> <a id="7680" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#7680" class="Bound">x</a> <a id="7682" class="Symbol">→</a> <a id="7684" href="Assignment2.html#7614" class="Bound">B</a> <a id="7686" href="Assignment2.html#7680" class="Bound">x</a><a id="7687" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="8597" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="8609" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#8609" class="Postulate Operator">_&lt;?_</a> <a id="8614" class="Symbol">:</a> <a id="8616" class="Symbol">∀</a> <a id="8618" class="Symbol">(</a><a id="8619" href="Assignment2.html#8619" class="Bound">m</a> <a id="8621" href="Assignment2.html#8621" class="Bound">n</a> <a id="8623" class="Symbol">:</a> <a id="8625" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8626" class="Symbol">)</a> <a id="8628" class="Symbol">→</a> <a id="8630" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8634" class="Symbol">(</a><a id="8635" href="Assignment2.html#8619" class="Bound">m</a> <a id="8637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#26539" class="Datatype Operator">&lt;</a> <a id="8639" href="Assignment2.html#8621" class="Bound">n</a><a id="8640" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
{% raw %}<pre class="Agda"><a id="8734" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="8746" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#8746" class="Postulate Operator">_≡ℕ?_</a> <a id="8752" class="Symbol">:</a> <a id="8754" class="Symbol">∀</a> <a id="8756" class="Symbol">(</a><a id="8757" href="Assignment2.html#8757" class="Bound">m</a> <a id="8759" href="Assignment2.html#8759" class="Bound">n</a> <a id="8761" class="Symbol">:</a> <a id="8763" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8764" class="Symbol">)</a> <a id="8766" class="Symbol">→</a> <a id="8768" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8772" class="Symbol">(</a><a id="8773" href="Assignment2.html#8757" class="Bound">m</a> <a id="8775" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8777" href="Assignment2.html#8759" class="Bound">n</a><a id="8778" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
{% raw %}<pre class="Agda"><a id="8889" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="8901" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#8901" class="Postulate">∧-×</a> <a id="8905" class="Symbol">:</a> <a id="8907" class="Symbol">∀</a> <a id="8909" class="Symbol">{</a><a id="8910" href="Assignment2.html#8910" class="Bound">A</a> <a id="8912" href="Assignment2.html#8912" class="Bound">B</a> <a id="8914" class="Symbol">:</a> <a id="8916" class="PrimitiveType">Set</a><a id="8919" class="Symbol">}</a> <a id="8921" class="Symbol">(</a><a id="8922" href="Assignment2.html#8922" class="Bound">x</a> <a id="8924" class="Symbol">:</a> <a id="8926" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8930" href="Assignment2.html#8910" class="Bound">A</a><a id="8931" class="Symbol">)</a> <a id="8933" class="Symbol">(</a><a id="8934" href="Assignment2.html#8934" class="Bound">y</a> <a id="8936" class="Symbol">:</a> <a id="8938" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8942" href="Assignment2.html#8912" class="Bound">B</a><a id="8943" class="Symbol">)</a> <a id="8945" class="Symbol">→</a> <a id="8947" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8949" href="Assignment2.html#8922" class="Bound">x</a> <a id="8951" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8953" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="8955" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8957" href="Assignment2.html#8934" class="Bound">y</a> <a id="8959" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8961" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8965" href="Assignment2.html#8922" class="Bound">x</a> <a id="8967" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="8973" href="Assignment2.html#8934" class="Bound">y</a> <a id="8975" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-×"></a><a id="8979" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#8979" class="Postulate">∨-×</a> <a id="8983" class="Symbol">:</a> <a id="8985" class="Symbol">∀</a> <a id="8987" class="Symbol">{</a><a id="8988" href="Assignment2.html#8988" class="Bound">A</a> <a id="8990" href="Assignment2.html#8990" class="Bound">B</a> <a id="8992" class="Symbol">:</a> <a id="8994" class="PrimitiveType">Set</a><a id="8997" class="Symbol">}</a> <a id="8999" class="Symbol">(</a><a id="9000" href="Assignment2.html#9000" class="Bound">x</a> <a id="9002" class="Symbol">:</a> <a id="9004" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9008" href="Assignment2.html#8988" class="Bound">A</a><a id="9009" class="Symbol">)</a> <a id="9011" class="Symbol">(</a><a id="9012" href="Assignment2.html#9012" class="Bound">y</a> <a id="9014" class="Symbol">:</a> <a id="9016" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9020" href="Assignment2.html#8990" class="Bound">B</a><a id="9021" class="Symbol">)</a> <a id="9023" class="Symbol">→</a> <a id="9025" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9027" href="Assignment2.html#9000" class="Bound">x</a> <a id="9029" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9031" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="9033" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9035" href="Assignment2.html#9012" class="Bound">y</a> <a id="9037" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9039" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9041" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9043" href="Assignment2.html#9000" class="Bound">x</a> <a id="9045" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="9051" href="Assignment2.html#9012" class="Bound">y</a> <a id="9053" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="9057" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9057" class="Postulate">not-¬</a> <a id="9063" class="Symbol">:</a> <a id="9065" class="Symbol">∀</a> <a id="9067" class="Symbol">{</a><a id="9068" href="Assignment2.html#9068" class="Bound">A</a> <a id="9070" class="Symbol">:</a> <a id="9072" class="PrimitiveType">Set</a><a id="9075" class="Symbol">}</a> <a id="9077" class="Symbol">(</a><a id="9078" href="Assignment2.html#9078" class="Bound">x</a> <a id="9080" class="Symbol">:</a> <a id="9082" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9086" href="Assignment2.html#9068" class="Bound">A</a><a id="9087" class="Symbol">)</a> <a id="9089" class="Symbol">→</a> <a id="9091" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="9095" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9097" href="Assignment2.html#9078" class="Bound">x</a> <a id="9099" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9101" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9103" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9105" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="9108" href="Assignment2.html#9078" class="Bound">x</a> <a id="9110" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
{% raw %}<pre class="Agda"><a id="9331" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="9343" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9343" class="Postulate Operator">_iff_</a> <a id="9349" class="Symbol">:</a> <a id="9351" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9356" class="Symbol">→</a> <a id="9358" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9363" class="Symbol">→</a> <a id="9365" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="9372" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9372" class="Postulate Operator">_⇔-dec_</a> <a id="9380" class="Symbol">:</a> <a id="9382" class="Symbol">∀</a> <a id="9384" class="Symbol">{</a><a id="9385" href="Assignment2.html#9385" class="Bound">A</a> <a id="9387" href="Assignment2.html#9387" class="Bound">B</a> <a id="9389" class="Symbol">:</a> <a id="9391" class="PrimitiveType">Set</a><a id="9394" class="Symbol">}</a> <a id="9396" class="Symbol">→</a> <a id="9398" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9402" href="Assignment2.html#9385" class="Bound">A</a> <a id="9404" class="Symbol">→</a> <a id="9406" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9410" href="Assignment2.html#9387" class="Bound">B</a> <a id="9412" class="Symbol">→</a> <a id="9414" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9418" class="Symbol">(</a><a id="9419" href="Assignment2.html#9385" class="Bound">A</a> <a id="9421" href="Assignment2.html#2755" class="Record Operator">⇔</a> <a id="9423" href="Assignment2.html#9387" class="Bound">B</a><a id="9424" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="9428" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9428" class="Postulate">iff-⇔</a> <a id="9434" class="Symbol">:</a> <a id="9436" class="Symbol">∀</a> <a id="9438" class="Symbol">{</a><a id="9439" href="Assignment2.html#9439" class="Bound">A</a> <a id="9441" href="Assignment2.html#9441" class="Bound">B</a> <a id="9443" class="Symbol">:</a> <a id="9445" class="PrimitiveType">Set</a><a id="9448" class="Symbol">}</a> <a id="9450" class="Symbol">(</a><a id="9451" href="Assignment2.html#9451" class="Bound">x</a> <a id="9453" class="Symbol">:</a> <a id="9455" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9459" href="Assignment2.html#9439" class="Bound">A</a><a id="9460" class="Symbol">)</a> <a id="9462" class="Symbol">(</a><a id="9463" href="Assignment2.html#9463" class="Bound">y</a> <a id="9465" class="Symbol">:</a> <a id="9467" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9471" href="Assignment2.html#9441" class="Bound">B</a><a id="9472" class="Symbol">)</a> <a id="9474" class="Symbol">→</a> <a id="9476" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9478" href="Assignment2.html#9451" class="Bound">x</a> <a id="9480" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9482" href="Assignment2.html#9343" class="Postulate Operator">iff</a> <a id="9486" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9488" href="Assignment2.html#9463" class="Bound">y</a> <a id="9490" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9492" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9494" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9496" href="Assignment2.html#9451" class="Bound">x</a> <a id="9498" href="Assignment2.html#9372" class="Postulate Operator">⇔-dec</a> <a id="9504" href="Assignment2.html#9463" class="Bound">y</a> <a id="9506" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
## Lists

#### Exercise `reverse-++-commute` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.
{% raw %}<pre class="Agda"><a id="9698" class="Keyword">postulate</a>
  <a id="reverse-++-commute"></a><a id="9710" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9710" class="Postulate">reverse-++-commute</a> <a id="9729" class="Symbol">:</a> <a id="9731" class="Symbol">∀</a> <a id="9733" class="Symbol">{</a><a id="9734" href="Assignment2.html#9734" class="Bound">A</a> <a id="9736" class="Symbol">:</a> <a id="9738" class="PrimitiveType">Set</a><a id="9741" class="Symbol">}</a> <a id="9743" class="Symbol">{</a><a id="9744" href="Assignment2.html#9744" class="Bound">xs</a> <a id="9747" href="Assignment2.html#9747" class="Bound">ys</a> <a id="9750" class="Symbol">:</a> <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="9757" href="Assignment2.html#9734" class="Bound">A</a><a id="9758" class="Symbol">}</a>
    <a id="9764" class="Symbol">→</a> <a id="9766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#11326" class="Function">reverse</a> <a id="9774" class="Symbol">(</a><a id="9775" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#9744" class="Bound">xs</a> <a id="9778" href="plfa.part1.Lists.html#4663" class="Function Operator">++</a> <a id="9781" href="Assignment2.html#9747" class="Bound">ys</a><a id="9783" class="Symbol">)</a> <a id="9785" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9787" href="plfa.part1.Lists.html#11326" class="Function">reverse</a> <a id="9795" href="Assignment2.html#9747" class="Bound">ys</a> <a id="9798" href="plfa.part1.Lists.html#4663" class="Function Operator">++</a> <a id="9801" href="plfa.part1.Lists.html#11326" class="Function">reverse</a> <a id="9809" href="Assignment2.html#9744" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution.
{% raw %}<pre class="Agda"><a id="9994" class="Keyword">postulate</a>
  <a id="reverse-involutive"></a><a id="10006" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10006" class="Postulate">reverse-involutive</a> <a id="10025" class="Symbol">:</a> <a id="10027" class="Symbol">∀</a> <a id="10029" class="Symbol">{</a><a id="10030" href="Assignment2.html#10030" class="Bound">A</a> <a id="10032" class="Symbol">:</a> <a id="10034" class="PrimitiveType">Set</a><a id="10037" class="Symbol">}</a> <a id="10039" class="Symbol">{</a><a id="10040" href="Assignment2.html#10040" class="Bound">xs</a> <a id="10043" class="Symbol">:</a> <a id="10045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="10050" href="Assignment2.html#10030" class="Bound">A</a><a id="10051" class="Symbol">}</a>
    <a id="10057" class="Symbol">→</a> <a id="10059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#11326" class="Function">reverse</a> <a id="10067" class="Symbol">(</a><a id="10068" href="plfa.part1.Lists.html#11326" class="Function">reverse</a> <a id="10076" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10040" class="Bound">xs</a><a id="10078" class="Symbol">)</a> <a id="10080" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10082" href="Assignment2.html#10040" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `map-compose`

Prove that the map of a composition is equal to the composition of two maps.
{% raw %}<pre class="Agda"><a id="10200" class="Keyword">postulate</a>
  <a id="map-compose"></a><a id="10212" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10212" class="Postulate">map-compose</a> <a id="10224" class="Symbol">:</a> <a id="10226" class="Symbol">∀</a> <a id="10228" class="Symbol">{</a><a id="10229" href="Assignment2.html#10229" class="Bound">A</a> <a id="10231" href="Assignment2.html#10231" class="Bound">B</a> <a id="10233" href="Assignment2.html#10233" class="Bound">C</a> <a id="10235" class="Symbol">:</a> <a id="10237" class="PrimitiveType">Set</a><a id="10240" class="Symbol">}</a> <a id="10242" class="Symbol">{</a><a id="10243" href="Assignment2.html#10243" class="Bound">f</a> <a id="10245" class="Symbol">:</a> <a id="10247" href="Assignment2.html#10229" class="Bound">A</a> <a id="10249" class="Symbol">→</a> <a id="10251" href="Assignment2.html#10231" class="Bound">B</a><a id="10252" class="Symbol">}</a> <a id="10254" class="Symbol">{</a><a id="10255" href="Assignment2.html#10255" class="Bound">g</a> <a id="10257" class="Symbol">:</a> <a id="10259" href="Assignment2.html#10231" class="Bound">B</a> <a id="10261" class="Symbol">→</a> <a id="10263" href="Assignment2.html#10233" class="Bound">C</a><a id="10264" class="Symbol">}</a>
    <a id="10270" class="Symbol">→</a> <a id="10272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#17187" class="Function">map</a> <a id="10276" class="Symbol">(</a><a id="10277" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10255" class="Bound">g</a> <a id="10279" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="10281" href="Assignment2.html#10243" class="Bound">f</a><a id="10282" class="Symbol">)</a> <a id="10284" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10286" href="plfa.part1.Lists.html#17187" class="Function">map</a> <a id="10290" href="Assignment2.html#10255" class="Bound">g</a> <a id="10292" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="10294" href="plfa.part1.Lists.html#17187" class="Function">map</a> <a id="10298" href="Assignment2.html#10243" class="Bound">f</a>
</pre>{% endraw %}The last step of the proof requires extensionality.

#### Exercise `map-++-commute`

Prove the following relationship between map and append.
{% raw %}<pre class="Agda"><a id="10450" class="Keyword">postulate</a>
  <a id="map-++-commute"></a><a id="10462" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10462" class="Postulate">map-++-commute</a> <a id="10477" class="Symbol">:</a> <a id="10479" class="Symbol">∀</a> <a id="10481" class="Symbol">{</a><a id="10482" href="Assignment2.html#10482" class="Bound">A</a> <a id="10484" href="Assignment2.html#10484" class="Bound">B</a> <a id="10486" class="Symbol">:</a> <a id="10488" class="PrimitiveType">Set</a><a id="10491" class="Symbol">}</a> <a id="10493" class="Symbol">{</a><a id="10494" href="Assignment2.html#10494" class="Bound">f</a> <a id="10496" class="Symbol">:</a> <a id="10498" href="Assignment2.html#10482" class="Bound">A</a> <a id="10500" class="Symbol">→</a> <a id="10502" href="Assignment2.html#10484" class="Bound">B</a><a id="10503" class="Symbol">}</a> <a id="10505" class="Symbol">{</a><a id="10506" href="Assignment2.html#10506" class="Bound">xs</a> <a id="10509" href="Assignment2.html#10509" class="Bound">ys</a> <a id="10512" class="Symbol">:</a> <a id="10514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="10519" href="Assignment2.html#10482" class="Bound">A</a><a id="10520" class="Symbol">}</a>
   <a id="10525" class="Symbol">→</a>  <a id="10528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#17187" class="Function">map</a> <a id="10532" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10494" class="Bound">f</a> <a id="10534" class="Symbol">(</a><a id="10535" href="Assignment2.html#10506" class="Bound">xs</a> <a id="10538" href="plfa.part1.Lists.html#4663" class="Function Operator">++</a> <a id="10541" href="Assignment2.html#10509" class="Bound">ys</a><a id="10543" class="Symbol">)</a> <a id="10545" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10547" href="plfa.part1.Lists.html#17187" class="Function">map</a> <a id="10551" href="Assignment2.html#10494" class="Bound">f</a> <a id="10553" href="Assignment2.html#10506" class="Bound">xs</a> <a id="10556" href="plfa.part1.Lists.html#4663" class="Function Operator">++</a> <a id="10559" href="plfa.part1.Lists.html#17187" class="Function">map</a> <a id="10563" href="Assignment2.html#10494" class="Bound">f</a> <a id="10565" href="Assignment2.html#10509" class="Bound">ys</a>
</pre>{% endraw %}
#### Exercise `map-Tree`

Define a type of trees with leaves of type `A` and internal
nodes of type `B`.
{% raw %}<pre class="Agda"><a id="10682" class="Keyword">data</a> <a id="Tree"></a><a id="10687" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10687" class="Datatype">Tree</a> <a id="10692" class="Symbol">(</a><a id="10693" href="Assignment2.html#10693" class="Bound">A</a> <a id="10695" href="Assignment2.html#10695" class="Bound">B</a> <a id="10697" class="Symbol">:</a> <a id="10699" class="PrimitiveType">Set</a><a id="10702" class="Symbol">)</a> <a id="10704" class="Symbol">:</a> <a id="10706" class="PrimitiveType">Set</a> <a id="10710" class="Keyword">where</a>
  <a id="Tree.leaf"></a><a id="10718" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10718" class="InductiveConstructor">leaf</a> <a id="10723" class="Symbol">:</a> <a id="10725" href="Assignment2.html#10693" class="Bound">A</a> <a id="10727" class="Symbol">→</a> <a id="10729" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10734" href="Assignment2.html#10693" class="Bound">A</a> <a id="10736" href="Assignment2.html#10695" class="Bound">B</a>
  <a id="Tree.node"></a><a id="10740" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10740" class="InductiveConstructor">node</a> <a id="10745" class="Symbol">:</a> <a id="10747" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10752" href="Assignment2.html#10693" class="Bound">A</a> <a id="10754" href="Assignment2.html#10695" class="Bound">B</a> <a id="10756" class="Symbol">→</a> <a id="10758" href="Assignment2.html#10695" class="Bound">B</a> <a id="10760" class="Symbol">→</a> <a id="10762" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10767" href="Assignment2.html#10693" class="Bound">A</a> <a id="10769" href="Assignment2.html#10695" class="Bound">B</a> <a id="10771" class="Symbol">→</a> <a id="10773" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10778" href="Assignment2.html#10693" class="Bound">A</a> <a id="10780" href="Assignment2.html#10695" class="Bound">B</a>
</pre>{% endraw %}Define a suitable map operator over trees.
{% raw %}<pre class="Agda"><a id="10833" class="Keyword">postulate</a>
  <a id="map-Tree"></a><a id="10845" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10845" class="Postulate">map-Tree</a> <a id="10854" class="Symbol">:</a> <a id="10856" class="Symbol">∀</a> <a id="10858" class="Symbol">{</a><a id="10859" href="Assignment2.html#10859" class="Bound">A</a> <a id="10861" href="Assignment2.html#10861" class="Bound">B</a> <a id="10863" href="Assignment2.html#10863" class="Bound">C</a> <a id="10865" href="Assignment2.html#10865" class="Bound">D</a> <a id="10867" class="Symbol">:</a> <a id="10869" class="PrimitiveType">Set</a><a id="10872" class="Symbol">}</a>
    <a id="10878" class="Symbol">→</a> <a id="10880" class="Symbol">(</a><a id="10881" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#10859" class="Bound">A</a> <a id="10883" class="Symbol">→</a> <a id="10885" href="Assignment2.html#10863" class="Bound">C</a><a id="10886" class="Symbol">)</a> <a id="10888" class="Symbol">→</a> <a id="10890" class="Symbol">(</a><a id="10891" href="Assignment2.html#10861" class="Bound">B</a> <a id="10893" class="Symbol">→</a> <a id="10895" href="Assignment2.html#10865" class="Bound">D</a><a id="10896" class="Symbol">)</a> <a id="10898" class="Symbol">→</a> <a id="10900" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10905" href="Assignment2.html#10859" class="Bound">A</a> <a id="10907" href="Assignment2.html#10861" class="Bound">B</a> <a id="10909" class="Symbol">→</a> <a id="10911" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="10916" href="Assignment2.html#10863" class="Bound">C</a> <a id="10918" href="Assignment2.html#10865" class="Bound">D</a>
</pre>{% endraw %}
#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example,

    product [ 1 , 2 , 3 , 4 ] ≡ 24

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows.
{% raw %}<pre class="Agda"><a id="11180" class="Keyword">postulate</a>
  <a id="foldr-++"></a><a id="11192" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11192" class="Postulate">foldr-++</a> <a id="11201" class="Symbol">:</a> <a id="11203" class="Symbol">∀</a> <a id="11205" class="Symbol">{</a><a id="11206" href="Assignment2.html#11206" class="Bound">A</a> <a id="11208" href="Assignment2.html#11208" class="Bound">B</a> <a id="11210" class="Symbol">:</a> <a id="11212" class="PrimitiveType">Set</a><a id="11215" class="Symbol">}</a> <a id="11217" class="Symbol">(</a><a id="11218" href="Assignment2.html#11218" class="Bound Operator">_⊗_</a> <a id="11222" class="Symbol">:</a> <a id="11224" href="Assignment2.html#11206" class="Bound">A</a> <a id="11226" class="Symbol">→</a> <a id="11228" href="Assignment2.html#11208" class="Bound">B</a> <a id="11230" class="Symbol">→</a> <a id="11232" href="Assignment2.html#11208" class="Bound">B</a><a id="11233" class="Symbol">)</a> <a id="11235" class="Symbol">(</a><a id="11236" href="Assignment2.html#11236" class="Bound">e</a> <a id="11238" class="Symbol">:</a> <a id="11240" href="Assignment2.html#11208" class="Bound">B</a><a id="11241" class="Symbol">)</a> <a id="11243" class="Symbol">(</a><a id="11244" href="Assignment2.html#11244" class="Bound">xs</a> <a id="11247" href="Assignment2.html#11247" class="Bound">ys</a> <a id="11250" class="Symbol">:</a> <a id="11252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="11257" href="Assignment2.html#11206" class="Bound">A</a><a id="11258" class="Symbol">)</a> <a id="11260" class="Symbol">→</a>
    <a id="11266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#20421" class="Function">foldr</a> <a id="11272" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11218" class="Bound Operator">_⊗_</a> <a id="11276" href="Assignment2.html#11236" class="Bound">e</a> <a id="11278" class="Symbol">(</a><a id="11279" href="Assignment2.html#11244" class="Bound">xs</a> <a id="11282" href="plfa.part1.Lists.html#4663" class="Function Operator">++</a> <a id="11285" href="Assignment2.html#11247" class="Bound">ys</a><a id="11287" class="Symbol">)</a> <a id="11289" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11291" href="plfa.part1.Lists.html#20421" class="Function">foldr</a> <a id="11297" href="Assignment2.html#11218" class="Bound Operator">_⊗_</a> <a id="11301" class="Symbol">(</a><a id="11302" href="plfa.part1.Lists.html#20421" class="Function">foldr</a> <a id="11308" href="Assignment2.html#11218" class="Bound Operator">_⊗_</a> <a id="11312" href="Assignment2.html#11236" class="Bound">e</a> <a id="11314" href="Assignment2.html#11247" class="Bound">ys</a><a id="11316" class="Symbol">)</a> <a id="11318" href="Assignment2.html#11244" class="Bound">xs</a>
</pre>{% endraw %}

#### Exercise `map-is-foldr`

Show that map can be defined using fold.
{% raw %}<pre class="Agda"><a id="11402" class="Keyword">postulate</a>
  <a id="map-is-foldr"></a><a id="11414" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11414" class="Postulate">map-is-foldr</a> <a id="11427" class="Symbol">:</a> <a id="11429" class="Symbol">∀</a> <a id="11431" class="Symbol">{</a><a id="11432" href="Assignment2.html#11432" class="Bound">A</a> <a id="11434" href="Assignment2.html#11434" class="Bound">B</a> <a id="11436" class="Symbol">:</a> <a id="11438" class="PrimitiveType">Set</a><a id="11441" class="Symbol">}</a> <a id="11443" class="Symbol">{</a><a id="11444" href="Assignment2.html#11444" class="Bound">f</a> <a id="11446" class="Symbol">:</a> <a id="11448" href="Assignment2.html#11432" class="Bound">A</a> <a id="11450" class="Symbol">→</a> <a id="11452" href="Assignment2.html#11434" class="Bound">B</a><a id="11453" class="Symbol">}</a> <a id="11455" class="Symbol">→</a>
    <a id="11461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#17187" class="Function">map</a> <a id="11465" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11444" class="Bound">f</a> <a id="11467" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11469" href="plfa.part1.Lists.html#20421" class="Function">foldr</a> <a id="11475" class="Symbol">(λ</a> <a id="11478" href="Assignment2.html#11478" class="Bound">x</a> <a id="11480" href="Assignment2.html#11480" class="Bound">xs</a> <a id="11483" class="Symbol">→</a> <a id="11485" href="Assignment2.html#11444" class="Bound">f</a> <a id="11487" href="Assignment2.html#11478" class="Bound">x</a> <a id="11489" href="plfa.part1.Lists.html#1340" class="InductiveConstructor Operator">∷</a> <a id="11491" href="Assignment2.html#11480" class="Bound">xs</a><a id="11493" class="Symbol">)</a> <a id="11495" href="plfa.part1.Lists.html#1325" class="InductiveConstructor">[]</a>
</pre>{% endraw %}This requires extensionality.

#### Exercise `fold-Tree`

Define a suitable fold function for the type of trees given earlier.
{% raw %}<pre class="Agda"><a id="11633" class="Keyword">postulate</a>
  <a id="fold-Tree"></a><a id="11645" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11645" class="Postulate">fold-Tree</a> <a id="11655" class="Symbol">:</a> <a id="11657" class="Symbol">∀</a> <a id="11659" class="Symbol">{</a><a id="11660" href="Assignment2.html#11660" class="Bound">A</a> <a id="11662" href="Assignment2.html#11662" class="Bound">B</a> <a id="11664" href="Assignment2.html#11664" class="Bound">C</a> <a id="11666" class="Symbol">:</a> <a id="11668" class="PrimitiveType">Set</a><a id="11671" class="Symbol">}</a>
    <a id="11677" class="Symbol">→</a> <a id="11679" class="Symbol">(</a><a id="11680" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11660" class="Bound">A</a> <a id="11682" class="Symbol">→</a> <a id="11684" href="Assignment2.html#11664" class="Bound">C</a><a id="11685" class="Symbol">)</a> <a id="11687" class="Symbol">→</a> <a id="11689" class="Symbol">(</a><a id="11690" href="Assignment2.html#11664" class="Bound">C</a> <a id="11692" class="Symbol">→</a> <a id="11694" href="Assignment2.html#11662" class="Bound">B</a> <a id="11696" class="Symbol">→</a> <a id="11698" href="Assignment2.html#11664" class="Bound">C</a> <a id="11700" class="Symbol">→</a> <a id="11702" href="Assignment2.html#11664" class="Bound">C</a><a id="11703" class="Symbol">)</a> <a id="11705" class="Symbol">→</a> <a id="11707" href="Assignment2.html#10687" class="Datatype">Tree</a> <a id="11712" href="Assignment2.html#11660" class="Bound">A</a> <a id="11714" href="Assignment2.html#11662" class="Bound">B</a> <a id="11716" class="Symbol">→</a> <a id="11718" href="Assignment2.html#11664" class="Bound">C</a>
</pre>{% endraw %}
#### Exercise `map-is-fold-Tree`

Demonstrate an analogue of `map-is-foldr` for the type of trees.

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows.
{% raw %}<pre class="Agda"><a id="downFrom"></a><a id="11916" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11916" class="Function">downFrom</a> <a id="11925" class="Symbol">:</a> <a id="11927" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="11929" class="Symbol">→</a> <a id="11931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="11936" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="11938" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11916" class="Function">downFrom</a> <a id="11947" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="11956" class="Symbol">=</a>  <a id="11959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1325" class="InductiveConstructor">[]</a>
<a id="11962" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11916" class="Function">downFrom</a> <a id="11971" class="Symbol">(</a><a id="11972" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11976" href="Assignment2.html#11976" class="Bound">n</a><a id="11977" class="Symbol">)</a>  <a id="11980" class="Symbol">=</a>  <a id="11983" href="Assignment2.html#11976" class="Bound">n</a> <a id="11985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1340" class="InductiveConstructor Operator">∷</a> <a id="11987" href="Assignment2.html#11916" class="Function">downFrom</a> <a id="11996" href="Assignment2.html#11976" class="Bound">n</a>
</pre>{% endraw %}For example,
{% raw %}<pre class="Agda"><a id="12019" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#12019" class="Function">_</a> <a id="12021" class="Symbol">:</a> <a id="12023" href="Assignment2.html#11916" class="Function">downFrom</a> <a id="12032" class="Number">3</a> <a id="12034" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#3884" class="InductiveConstructor Operator">[</a> <a id="12038" class="Number">2</a> <a id="12040" href="plfa.part1.Lists.html#3884" class="InductiveConstructor Operator">,</a> <a id="12042" class="Number">1</a> <a id="12044" href="plfa.part1.Lists.html#3884" class="InductiveConstructor Operator">,</a> <a id="12046" class="Number">0</a> <a id="12048" href="plfa.part1.Lists.html#3884" class="InductiveConstructor Operator">]</a>
<a id="12050" class="Symbol">_</a> <a id="12052" class="Symbol">=</a> <a id="12054" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`.
{% raw %}<pre class="Agda"><a id="12150" class="Keyword">postulate</a>
  <a id="sum-downFrom"></a><a id="12162" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#12162" class="Postulate">sum-downFrom</a> <a id="12175" class="Symbol">:</a> <a id="12177" class="Symbol">∀</a> <a id="12179" class="Symbol">(</a><a id="12180" href="Assignment2.html#12180" class="Bound">n</a> <a id="12182" class="Symbol">:</a> <a id="12184" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12185" class="Symbol">)</a>
    <a id="12191" class="Symbol">→</a> <a id="12193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#21601" class="Function">sum</a> <a id="12197" class="Symbol">(</a><a id="12198" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#11916" class="Function">downFrom</a> <a id="12207" href="Assignment2.html#12180" class="Bound">n</a><a id="12208" class="Symbol">)</a> <a id="12210" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="12212" class="Number">2</a> <a id="12214" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12216" href="Assignment2.html#12180" class="Bound">n</a> <a id="12218" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="12220" class="Symbol">(</a><a id="12221" href="Assignment2.html#12180" class="Bound">n</a> <a id="12223" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">∸</a> <a id="12225" class="Number">1</a><a id="12226" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `foldl`

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example,

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z


#### Exercise `foldr-monoid-foldl`

Show that if `_⊕_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.


#### Exercise `¬Any≃All¬` (stretch)

First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly].
{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="13130" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13130" class="Function Operator">_∘′_</a> <a id="13135" class="Symbol">:</a> <a id="13137" class="Symbol">∀</a> <a id="13139" class="Symbol">{</a><a id="13140" href="Assignment2.html#13140" class="Bound">ℓ₁</a> <a id="13143" href="Assignment2.html#13143" class="Bound">ℓ₂</a> <a id="13146" href="Assignment2.html#13146" class="Bound">ℓ₃</a> <a id="13149" class="Symbol">:</a> <a id="13151" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="13156" class="Symbol">}</a> <a id="13158" class="Symbol">{</a><a id="13159" href="Assignment2.html#13159" class="Bound">A</a> <a id="13161" class="Symbol">:</a> <a id="13163" class="PrimitiveType">Set</a> <a id="13167" href="Assignment2.html#13140" class="Bound">ℓ₁</a><a id="13169" class="Symbol">}</a> <a id="13171" class="Symbol">{</a><a id="13172" href="Assignment2.html#13172" class="Bound">B</a> <a id="13174" class="Symbol">:</a> <a id="13176" class="PrimitiveType">Set</a> <a id="13180" href="Assignment2.html#13143" class="Bound">ℓ₂</a><a id="13182" class="Symbol">}</a> <a id="13184" class="Symbol">{</a><a id="13185" href="Assignment2.html#13185" class="Bound">C</a> <a id="13187" class="Symbol">:</a> <a id="13189" class="PrimitiveType">Set</a> <a id="13193" href="Assignment2.html#13146" class="Bound">ℓ₃</a><a id="13195" class="Symbol">}</a>
  <a id="13199" class="Symbol">→</a> <a id="13201" class="Symbol">(</a><a id="13202" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13172" class="Bound">B</a> <a id="13204" class="Symbol">→</a> <a id="13206" href="Assignment2.html#13185" class="Bound">C</a><a id="13207" class="Symbol">)</a> <a id="13209" class="Symbol">→</a> <a id="13211" class="Symbol">(</a><a id="13212" href="Assignment2.html#13159" class="Bound">A</a> <a id="13214" class="Symbol">→</a> <a id="13216" href="Assignment2.html#13172" class="Bound">B</a><a id="13217" class="Symbol">)</a> <a id="13219" class="Symbol">→</a> <a id="13221" href="Assignment2.html#13159" class="Bound">A</a> <a id="13223" class="Symbol">→</a> <a id="13225" href="Assignment2.html#13185" class="Bound">C</a>
<a id="13227" class="Symbol">(</a><a id="13228" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13228" class="Bound">g</a> <a id="13230" href="Assignment2.html#13130" class="Function Operator">∘′</a> <a id="13233" href="Assignment2.html#13233" class="Bound">f</a><a id="13234" class="Symbol">)</a> <a id="13236" href="Assignment2.html#13236" class="Bound">x</a>  <a id="13239" class="Symbol">=</a>  <a id="13242" href="Assignment2.html#13228" class="Bound">g</a> <a id="13244" class="Symbol">(</a><a id="13245" href="Assignment2.html#13233" class="Bound">f</a> <a id="13247" href="Assignment2.html#13236" class="Bound">x</a><a id="13248" class="Symbol">)</a>
</pre>{% endraw %}
Show that `Any` and `All` satisfy a version of De Morgan's Law.
{% raw %}<pre class="Agda"><a id="13323" class="Keyword">postulate</a>
  <a id="¬Any≃All¬"></a><a id="13335" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13335" class="Postulate">¬Any≃All¬</a> <a id="13345" class="Symbol">:</a> <a id="13347" class="Symbol">∀</a> <a id="13349" class="Symbol">{</a><a id="13350" href="Assignment2.html#13350" class="Bound">A</a> <a id="13352" class="Symbol">:</a> <a id="13354" class="PrimitiveType">Set</a><a id="13357" class="Symbol">}</a> <a id="13359" class="Symbol">(</a><a id="13360" href="Assignment2.html#13360" class="Bound">P</a> <a id="13362" class="Symbol">:</a> <a id="13364" href="Assignment2.html#13350" class="Bound">A</a> <a id="13366" class="Symbol">→</a> <a id="13368" class="PrimitiveType">Set</a><a id="13371" class="Symbol">)</a> <a id="13373" class="Symbol">(</a><a id="13374" href="Assignment2.html#13374" class="Bound">xs</a> <a id="13377" class="Symbol">:</a> <a id="13379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="13384" href="Assignment2.html#13350" class="Bound">A</a><a id="13385" class="Symbol">)</a>
    <a id="13391" class="Symbol">→</a> <a id="13393" class="Symbol">(</a><a id="13394" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13397" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13130" class="Function Operator">∘′</a> <a id="13400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#31035" class="Datatype">Any</a> <a id="13404" href="Assignment2.html#13360" class="Bound">P</a><a id="13405" class="Symbol">)</a> <a id="13407" href="Assignment2.html#13374" class="Bound">xs</a> <a id="13410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="13412" href="plfa.part1.Lists.html#28889" class="Datatype">All</a> <a id="13416" class="Symbol">(</a><a id="13417" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13420" href="Assignment2.html#13130" class="Function Operator">∘′</a> <a id="13423" href="Assignment2.html#13360" class="Bound">P</a><a id="13424" class="Symbol">)</a> <a id="13426" href="Assignment2.html#13374" class="Bound">xs</a>
</pre>{% endraw %}
Do we also have the following?
{% raw %}<pre class="Agda"><a id="13469" class="Keyword">postulate</a>
  <a id="¬All≃Any¬"></a><a id="13481" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13481" class="Postulate">¬All≃Any¬</a> <a id="13491" class="Symbol">:</a> <a id="13493" class="Symbol">∀</a> <a id="13495" class="Symbol">{</a><a id="13496" href="Assignment2.html#13496" class="Bound">A</a> <a id="13498" class="Symbol">:</a> <a id="13500" class="PrimitiveType">Set</a><a id="13503" class="Symbol">}</a> <a id="13505" class="Symbol">(</a><a id="13506" href="Assignment2.html#13506" class="Bound">P</a> <a id="13508" class="Symbol">:</a> <a id="13510" href="Assignment2.html#13496" class="Bound">A</a> <a id="13512" class="Symbol">→</a> <a id="13514" class="PrimitiveType">Set</a><a id="13517" class="Symbol">)</a> <a id="13519" class="Symbol">(</a><a id="13520" href="Assignment2.html#13520" class="Bound">xs</a> <a id="13523" class="Symbol">:</a> <a id="13525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="13530" href="Assignment2.html#13496" class="Bound">A</a><a id="13531" class="Symbol">)</a>
    <a id="13537" class="Symbol">→</a> <a id="13539" class="Symbol">(</a><a id="13540" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13543" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#13130" class="Function Operator">∘′</a> <a id="13546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#28889" class="Datatype">All</a> <a id="13550" href="Assignment2.html#13506" class="Bound">P</a><a id="13551" class="Symbol">)</a> <a id="13553" href="Assignment2.html#13520" class="Bound">xs</a> <a id="13556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="13558" href="plfa.part1.Lists.html#31035" class="Datatype">Any</a> <a id="13562" class="Symbol">(</a><a id="13563" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13566" href="Assignment2.html#13130" class="Function Operator">∘′</a> <a id="13569" href="Assignment2.html#13506" class="Bound">P</a><a id="13570" class="Symbol">)</a> <a id="13572" href="Assignment2.html#13520" class="Bound">xs</a>
</pre>{% endraw %}If so, prove; if not, explain why.


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `all?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `any?` which determine whether a predicates holds
for some element of a list.  Give their definitions.


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a list and a decidable predicate returns all elements of the
list satisfying the predicate.
{% raw %}<pre class="Agda"><a id="14127" class="Keyword">postulate</a>
  <a id="filter?"></a><a id="14139" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#14139" class="Postulate">filter?</a> <a id="14147" class="Symbol">:</a> <a id="14149" class="Symbol">∀</a> <a id="14151" class="Symbol">{</a><a id="14152" href="Assignment2.html#14152" class="Bound">A</a> <a id="14154" class="Symbol">:</a> <a id="14156" class="PrimitiveType">Set</a><a id="14159" class="Symbol">}</a> <a id="14161" class="Symbol">{</a><a id="14162" href="Assignment2.html#14162" class="Bound">P</a> <a id="14164" class="Symbol">:</a> <a id="14166" href="Assignment2.html#14152" class="Bound">A</a> <a id="14168" class="Symbol">→</a> <a id="14170" class="PrimitiveType">Set</a><a id="14173" class="Symbol">}</a>
    <a id="14179" class="Symbol">→</a> <a id="14181" class="Symbol">(</a><a id="14182" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment2.md %}{% raw %}#14182" class="Bound">P?</a> <a id="14185" class="Symbol">:</a> <a id="14187" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a> <a id="14197" href="Assignment2.html#14162" class="Bound">P</a><a id="14198" class="Symbol">)</a> <a id="14200" class="Symbol">→</a> <a id="14202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Lists.md %}{% raw %}#1296" class="Datatype">List</a> <a id="14207" href="Assignment2.html#14152" class="Bound">A</a> <a id="14209" class="Symbol">→</a> <a id="14211" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="14214" href="Assignment2.html#14214" class="Bound">ys</a> <a id="14217" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a><a id="14218" class="Symbol">(</a> <a id="14220" href="plfa.part1.Lists.html#28889" class="Datatype">All</a> <a id="14224" href="Assignment2.html#14162" class="Bound">P</a> <a id="14226" href="Assignment2.html#14214" class="Bound">ys</a> <a id="14229" class="Symbol">)</a>
</pre>{% endraw %}
