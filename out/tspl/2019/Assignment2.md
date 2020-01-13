---
src       : "courses/tspl/2019/Assignment2.lagda.md"
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /TSPL/2019/Assignment2/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}" class="Module">Assignment2</a> <a id="131" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
```bash
submit tspl cw2 Assignment2.lagda.md
```
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## Imports

{% raw %}<pre class="Agda"><a id="1247" class="Keyword">import</a> <a id="1254" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1292" class="Symbol">as</a> <a id="1295" class="Module">Eq</a>
<a id="1298" class="Keyword">open</a> <a id="1303" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1306" class="Keyword">using</a> <a id="1312" class="Symbol">(</a><a id="1313" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1316" class="Symbol">;</a> <a id="1318" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1322" class="Symbol">;</a> <a id="1324" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1328" class="Symbol">;</a> <a id="1330" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1333" class="Symbol">)</a>
<a id="1335" class="Keyword">open</a> <a id="1340" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1355" class="Keyword">using</a> <a id="1361" class="Symbol">(</a><a id="1362" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1368" class="Symbol">;</a> <a id="1370" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1375" class="Symbol">;</a> <a id="1377" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1383" class="Symbol">;</a> <a id="1385" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1387" class="Symbol">)</a>
<a id="1389" class="Keyword">open</a> <a id="1394" class="Keyword">import</a> <a id="1401" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1410" class="Keyword">using</a> <a id="1416" class="Symbol">(</a><a id="1417" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1418" class="Symbol">;</a> <a id="1420" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1424" class="Symbol">;</a> <a id="1426" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1429" class="Symbol">;</a> <a id="1431" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1434" class="Symbol">;</a> <a id="1436" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1439" class="Symbol">;</a> <a id="1441" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1444" class="Symbol">;</a> <a id="1446" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="1449" class="Symbol">;</a> <a id="1451" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="1454" class="Symbol">;</a> <a id="1456" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="1459" class="Symbol">)</a>
<a id="1461" class="Keyword">open</a> <a id="1466" class="Keyword">import</a> <a id="1473" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="1493" class="Keyword">using</a> <a id="1499" class="Symbol">(</a><a id="1500" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="1507" class="Symbol">;</a> <a id="1509" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="1520" class="Symbol">;</a> <a id="1522" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="1527" class="Symbol">;</a> <a id="1529" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="1535" class="Symbol">;</a>
  <a id="1539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="1545" class="Symbol">;</a> <a id="1547" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="1554" class="Symbol">;</a> <a id="1556" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1565" class="Symbol">;</a> <a id="1567" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1574" class="Symbol">;</a> <a id="1576" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1585" class="Symbol">;</a> <a id="1587" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1596" class="Symbol">;</a> <a id="1598" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1606" class="Symbol">)</a>
<a id="1608" class="Keyword">open</a> <a id="1613" class="Keyword">import</a> <a id="1620" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1633" class="Keyword">using</a> <a id="1639" class="Symbol">(</a><a id="1640" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1643" class="Symbol">;</a> <a id="1645" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1650" class="Symbol">;</a> <a id="1652" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1657" class="Symbol">)</a> <a id="1659" class="Keyword">renaming</a> <a id="1668" class="Symbol">(</a><a id="1669" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1673" class="Symbol">to</a> <a id="1676" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1681" class="Symbol">)</a>
<a id="1683" class="Keyword">open</a> <a id="1688" class="Keyword">import</a> <a id="1695" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1705" class="Keyword">using</a> <a id="1711" class="Symbol">(</a><a id="1712" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1713" class="Symbol">;</a> <a id="1715" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1717" class="Symbol">)</a>
<a id="1719" class="Keyword">open</a> <a id="1724" class="Keyword">import</a> <a id="1731" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1740" class="Keyword">using</a> <a id="1746" class="Symbol">(</a><a id="1747" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1750" class="Symbol">;</a> <a id="1752" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1756" class="Symbol">;</a> <a id="1758" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1762" class="Symbol">)</a> <a id="1764" class="Keyword">renaming</a> <a id="1773" class="Symbol">(</a><a id="1774" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1780" class="Symbol">to</a> <a id="1783" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1789" class="Symbol">)</a>
<a id="1791" class="Keyword">open</a> <a id="1796" class="Keyword">import</a> <a id="1803" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1814" class="Keyword">using</a> <a id="1820" class="Symbol">(</a><a id="1821" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1822" class="Symbol">;</a> <a id="1824" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1830" class="Symbol">)</a>
<a id="1832" class="Keyword">open</a> <a id="1837" class="Keyword">import</a> <a id="1844" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1859" class="Keyword">using</a> <a id="1865" class="Symbol">(</a><a id="1866" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1870" class="Symbol">;</a> <a id="1872" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1876" class="Symbol">;</a> <a id="1878" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1883" class="Symbol">;</a> <a id="1885" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1886" class="Symbol">;</a> <a id="1888" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1891" class="Symbol">;</a> <a id="1893" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1896" class="Symbol">;</a> <a id="1898" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1901" class="Symbol">)</a>
<a id="1903" class="Keyword">open</a> <a id="1908" class="Keyword">import</a> <a id="1915" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1932" class="Keyword">using</a> <a id="1938" class="Symbol">(</a><a id="1939" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1941" class="Symbol">;</a> <a id="1943" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1946" class="Symbol">;</a> <a id="1948" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1951" class="Symbol">;</a> <a id="1953" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1955" class="Symbol">)</a>
<a id="1957" class="Keyword">open</a> <a id="1962" class="Keyword">import</a> <a id="1969" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1996" class="Keyword">using</a> <a id="2002" class="Symbol">(</a><a id="2003" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="2006" class="Symbol">;</a> <a id="2008" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="2017" class="Symbol">;</a> <a id="2019" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="2030" class="Symbol">)</a>
<a id="2032" class="Keyword">open</a> <a id="2037" class="Keyword">import</a> <a id="2044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="2070" class="Keyword">using</a> <a id="2076" class="Symbol">(</a><a id="2077" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="2079" class="Symbol">)</a>
<a id="2081" class="Keyword">open</a> <a id="2086" class="Keyword">import</a> <a id="2093" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="2118" class="Keyword">using</a> <a id="2124" class="Symbol">(</a><a id="2125" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="2132" class="Symbol">)</a>
<a id="2134" class="Keyword">open</a> <a id="2139" class="Keyword">import</a> <a id="2146" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="2167" class="Keyword">using</a> <a id="2173" class="Symbol">(</a><a id="2174" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="2181" class="Symbol">)</a>
<a id="2183" class="Keyword">open</a> <a id="2188" class="Keyword">import</a> <a id="2195" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="2221" class="Keyword">using</a> <a id="2227" class="Symbol">(</a><a id="2228" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="2242" class="Symbol">)</a>
<a id="2244" class="Keyword">open</a> <a id="2249" class="Keyword">import</a> <a id="2256" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="2269" class="Keyword">using</a> <a id="2275" class="Symbol">(</a><a id="2276" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="2277" class="Symbol">;</a> <a id="2279" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="2282" class="Symbol">;</a> <a id="2284" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="2285" class="Symbol">;</a> <a id="2287" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="2295" class="Symbol">;</a> <a id="2297" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="2305" class="Symbol">)</a>
<a id="2307" class="Keyword">open</a> <a id="2312" class="Keyword">import</a> <a id="2319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="2340" class="Keyword">using</a> <a id="2346" class="Symbol">(</a><a id="2347" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="2350" class="Symbol">;</a> <a id="2352" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="2355" class="Symbol">;</a> <a id="2357" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="2360" class="Symbol">)</a>
<a id="2362" class="Keyword">open</a> <a id="2367" class="Keyword">import</a> <a id="2374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="2397" class="Keyword">using</a> <a id="2403" class="Symbol">(</a><a id="2404" href="plfa.part1.Isomorphism.html#5849" class="Record Operator">_≃_</a><a id="2407" class="Symbol">;</a> <a id="2409" href="plfa.part1.Isomorphism.html#9384" class="Function">≃-sym</a><a id="2414" class="Symbol">;</a> <a id="2416" href="plfa.part1.Isomorphism.html#9781" class="Function">≃-trans</a><a id="2423" class="Symbol">;</a> <a id="2425" href="plfa.part1.Isomorphism.html#11925" class="Record Operator">_≲_</a><a id="2428" class="Symbol">;</a> <a id="2430" href="plfa.part1.Isomorphism.html#3764" class="Postulate">extensionality</a><a id="2444" class="Symbol">)</a>
<a id="2446" class="Keyword">open</a> <a id="2451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#10993" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}
## Equality


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

{% raw %}<pre class="Agda"><a id="3142" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Isomorphism

#### Exercise `≃-implies-≲` (practice)

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="3280" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="3292" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3292" class="Postulate">≃-implies-≲</a> <a id="3304" class="Symbol">:</a> <a id="3306" class="Symbol">∀</a> <a id="3308" class="Symbol">{</a><a id="3309" href="Assignment2.html#3309" class="Bound">A</a> <a id="3311" href="Assignment2.html#3311" class="Bound">B</a> <a id="3313" class="Symbol">:</a> <a id="3315" class="PrimitiveType">Set</a><a id="3318" class="Symbol">}</a>
    <a id="3324" class="Symbol">→</a> <a id="3326" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3309" class="Bound">A</a> <a id="3328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="3330" href="Assignment2.html#3311" class="Bound">B</a>
      <a id="3338" class="Comment">-----</a>
    <a id="3348" class="Symbol">→</a> <a id="3350" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3309" class="Bound">A</a> <a id="3352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#11925" class="Record Operator">≲</a> <a id="3354" href="Assignment2.html#3311" class="Bound">B</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="3365" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (practice) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows:
{% raw %}<pre class="Agda"><a id="3516" class="Keyword">record</a> <a id="_⇔_"></a><a id="3523" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3523" class="Record Operator">_⇔_</a> <a id="3527" class="Symbol">(</a><a id="3528" href="Assignment2.html#3528" class="Bound">A</a> <a id="3530" href="Assignment2.html#3530" class="Bound">B</a> <a id="3532" class="Symbol">:</a> <a id="3534" class="PrimitiveType">Set</a><a id="3537" class="Symbol">)</a> <a id="3539" class="Symbol">:</a> <a id="3541" class="PrimitiveType">Set</a> <a id="3545" class="Keyword">where</a>
  <a id="3553" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="3563" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3563" class="Field">to</a>   <a id="3568" class="Symbol">:</a> <a id="3570" href="Assignment2.html#3528" class="Bound">A</a> <a id="3572" class="Symbol">→</a> <a id="3574" href="Assignment2.html#3530" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="3580" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3580" class="Field">from</a> <a id="3585" class="Symbol">:</a> <a id="3587" href="Assignment2.html#3530" class="Bound">B</a> <a id="3589" class="Symbol">→</a> <a id="3591" href="Assignment2.html#3528" class="Bound">A</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

{% raw %}<pre class="Agda"><a id="3665" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin) and
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{% raw %}<pre class="Agda"><a id="4174" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Why do `to` and `from` not form an isomorphism?

## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

{% raw %}<pre class="Agda"><a id="4421" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

{% raw %}<pre class="Agda"><a id="4535" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

{% raw %}<pre class="Agda"><a id="4647" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="4782" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="4915" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
{% raw %}<pre class="Agda"><a id="5027" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="5039" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#5039" class="Postulate">⊎-weak-×</a> <a id="5048" class="Symbol">:</a> <a id="5050" class="Symbol">∀</a> <a id="5052" class="Symbol">{</a><a id="5053" href="Assignment2.html#5053" class="Bound">A</a> <a id="5055" href="Assignment2.html#5055" class="Bound">B</a> <a id="5057" href="Assignment2.html#5057" class="Bound">C</a> <a id="5059" class="Symbol">:</a> <a id="5061" class="PrimitiveType">Set</a><a id="5064" class="Symbol">}</a> <a id="5066" class="Symbol">→</a> <a id="5068" class="Symbol">(</a><a id="5069" href="Assignment2.html#5053" class="Bound">A</a> <a id="5071" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5073" href="Assignment2.html#5055" class="Bound">B</a><a id="5074" class="Symbol">)</a> <a id="5076" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5078" href="Assignment2.html#5057" class="Bound">C</a> <a id="5080" class="Symbol">→</a> <a id="5082" href="Assignment2.html#5053" class="Bound">A</a> <a id="5084" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5086" class="Symbol">(</a><a id="5087" href="Assignment2.html#5055" class="Bound">B</a> <a id="5089" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5091" href="Assignment2.html#5057" class="Bound">C</a><a id="5092" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

{% raw %}<pre class="Agda"><a id="5234" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{% raw %}<pre class="Agda"><a id="5376" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="5388" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#5388" class="Postulate">⊎×-implies-×⊎</a> <a id="5402" class="Symbol">:</a> <a id="5404" class="Symbol">∀</a> <a id="5406" class="Symbol">{</a><a id="5407" href="Assignment2.html#5407" class="Bound">A</a> <a id="5409" href="Assignment2.html#5409" class="Bound">B</a> <a id="5411" href="Assignment2.html#5411" class="Bound">C</a> <a id="5413" href="Assignment2.html#5413" class="Bound">D</a> <a id="5415" class="Symbol">:</a> <a id="5417" class="PrimitiveType">Set</a><a id="5420" class="Symbol">}</a> <a id="5422" class="Symbol">→</a> <a id="5424" class="Symbol">(</a><a id="5425" href="Assignment2.html#5407" class="Bound">A</a> <a id="5427" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5429" href="Assignment2.html#5409" class="Bound">B</a><a id="5430" class="Symbol">)</a> <a id="5432" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5434" class="Symbol">(</a><a id="5435" href="Assignment2.html#5411" class="Bound">C</a> <a id="5437" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5439" href="Assignment2.html#5413" class="Bound">D</a><a id="5440" class="Symbol">)</a> <a id="5442" class="Symbol">→</a> <a id="5444" class="Symbol">(</a><a id="5445" href="Assignment2.html#5407" class="Bound">A</a> <a id="5447" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5449" href="Assignment2.html#5411" class="Bound">C</a><a id="5450" class="Symbol">)</a> <a id="5452" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5454" class="Symbol">(</a><a id="5455" href="Assignment2.html#5409" class="Bound">B</a> <a id="5457" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5459" href="Assignment2.html#5413" class="Bound">D</a><a id="5460" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="5540" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

{% raw %}<pre class="Agda"><a id="5777" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

{% raw %}<pre class="Agda"><a id="6187" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

{% raw %}<pre class="Agda"><a id="6459" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?

#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

{% raw %}<pre class="Agda"><a id="7074" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="7217" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7217" class="Function">Stable</a> <a id="7224" class="Symbol">:</a> <a id="7226" class="PrimitiveType">Set</a> <a id="7230" class="Symbol">→</a> <a id="7232" class="PrimitiveType">Set</a>
<a id="7236" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7217" class="Function">Stable</a> <a id="7243" href="Assignment2.html#7243" class="Bound">A</a> <a id="7245" class="Symbol">=</a> <a id="7247" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7249" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7251" href="Assignment2.html#7243" class="Bound">A</a> <a id="7253" class="Symbol">→</a> <a id="7255" href="Assignment2.html#7243" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

{% raw %}<pre class="Agda"><a id="7366" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Quantifiers


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
{% raw %}<pre class="Agda"><a id="7508" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="7520" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7520" class="Postulate">∀-distrib-×</a> <a id="7532" class="Symbol">:</a> <a id="7534" class="Symbol">∀</a> <a id="7536" class="Symbol">{</a><a id="7537" href="Assignment2.html#7537" class="Bound">A</a> <a id="7539" class="Symbol">:</a> <a id="7541" class="PrimitiveType">Set</a><a id="7544" class="Symbol">}</a> <a id="7546" class="Symbol">{</a><a id="7547" href="Assignment2.html#7547" class="Bound">B</a> <a id="7549" href="Assignment2.html#7549" class="Bound">C</a> <a id="7551" class="Symbol">:</a> <a id="7553" href="Assignment2.html#7537" class="Bound">A</a> <a id="7555" class="Symbol">→</a> <a id="7557" class="PrimitiveType">Set</a><a id="7560" class="Symbol">}</a> <a id="7562" class="Symbol">→</a>
    <a id="7568" class="Symbol">(∀</a> <a id="7571" class="Symbol">(</a><a id="7572" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7572" class="Bound">x</a> <a id="7574" class="Symbol">:</a> <a id="7576" href="Assignment2.html#7537" class="Bound">A</a><a id="7577" class="Symbol">)</a> <a id="7579" class="Symbol">→</a> <a id="7581" href="Assignment2.html#7547" class="Bound">B</a> <a id="7583" href="Assignment2.html#7572" class="Bound">x</a> <a id="7585" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7587" href="Assignment2.html#7549" class="Bound">C</a> <a id="7589" href="Assignment2.html#7572" class="Bound">x</a><a id="7590" class="Symbol">)</a> <a id="7592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="7594" class="Symbol">(∀</a> <a id="7597" class="Symbol">(</a><a id="7598" href="Assignment2.html#7598" class="Bound">x</a> <a id="7600" class="Symbol">:</a> <a id="7602" href="Assignment2.html#7537" class="Bound">A</a><a id="7603" class="Symbol">)</a> <a id="7605" class="Symbol">→</a> <a id="7607" href="Assignment2.html#7547" class="Bound">B</a> <a id="7609" href="Assignment2.html#7598" class="Bound">x</a><a id="7610" class="Symbol">)</a> <a id="7612" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7614" class="Symbol">(∀</a> <a id="7617" class="Symbol">(</a><a id="7618" href="Assignment2.html#7618" class="Bound">x</a> <a id="7620" class="Symbol">:</a> <a id="7622" href="Assignment2.html#7537" class="Bound">A</a><a id="7623" class="Symbol">)</a> <a id="7625" class="Symbol">→</a> <a id="7627" href="Assignment2.html#7549" class="Bound">C</a> <a id="7629" href="Assignment2.html#7618" class="Bound">x</a><a id="7630" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).


#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="7863" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="7875" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7875" class="Postulate">⊎∀-implies-∀⊎</a> <a id="7889" class="Symbol">:</a> <a id="7891" class="Symbol">∀</a> <a id="7893" class="Symbol">{</a><a id="7894" href="Assignment2.html#7894" class="Bound">A</a> <a id="7896" class="Symbol">:</a> <a id="7898" class="PrimitiveType">Set</a><a id="7901" class="Symbol">}</a> <a id="7903" class="Symbol">{</a><a id="7904" href="Assignment2.html#7904" class="Bound">B</a> <a id="7906" href="Assignment2.html#7906" class="Bound">C</a> <a id="7908" class="Symbol">:</a> <a id="7910" href="Assignment2.html#7894" class="Bound">A</a> <a id="7912" class="Symbol">→</a> <a id="7914" class="PrimitiveType">Set</a><a id="7917" class="Symbol">}</a> <a id="7919" class="Symbol">→</a>
    <a id="7925" class="Symbol">(∀</a> <a id="7928" class="Symbol">(</a><a id="7929" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7929" class="Bound">x</a> <a id="7931" class="Symbol">:</a> <a id="7933" href="Assignment2.html#7894" class="Bound">A</a><a id="7934" class="Symbol">)</a> <a id="7936" class="Symbol">→</a> <a id="7938" href="Assignment2.html#7904" class="Bound">B</a> <a id="7940" href="Assignment2.html#7929" class="Bound">x</a><a id="7941" class="Symbol">)</a> <a id="7943" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="7945" class="Symbol">(∀</a> <a id="7948" class="Symbol">(</a><a id="7949" href="Assignment2.html#7949" class="Bound">x</a> <a id="7951" class="Symbol">:</a> <a id="7953" href="Assignment2.html#7894" class="Bound">A</a><a id="7954" class="Symbol">)</a> <a id="7956" class="Symbol">→</a> <a id="7958" href="Assignment2.html#7906" class="Bound">C</a> <a id="7960" href="Assignment2.html#7949" class="Bound">x</a><a id="7961" class="Symbol">)</a>  <a id="7964" class="Symbol">→</a>  <a id="7967" class="Symbol">∀</a> <a id="7969" class="Symbol">(</a><a id="7970" href="Assignment2.html#7970" class="Bound">x</a> <a id="7972" class="Symbol">:</a> <a id="7974" href="Assignment2.html#7894" class="Bound">A</a><a id="7975" class="Symbol">)</a> <a id="7977" class="Symbol">→</a> <a id="7979" href="Assignment2.html#7904" class="Bound">B</a> <a id="7981" href="Assignment2.html#7970" class="Bound">x</a> <a id="7983" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="7985" href="Assignment2.html#7906" class="Bound">C</a> <a id="7987" href="Assignment2.html#7970" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
{% raw %}<pre class="Agda"><a id="8119" class="Keyword">data</a> <a id="Tri"></a><a id="8124" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8124" class="Datatype">Tri</a> <a id="8128" class="Symbol">:</a> <a id="8130" class="PrimitiveType">Set</a> <a id="8134" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="8142" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8142" class="InductiveConstructor">aa</a> <a id="8145" class="Symbol">:</a> <a id="8147" href="Assignment2.html#8124" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="8153" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8153" class="InductiveConstructor">bb</a> <a id="8156" class="Symbol">:</a> <a id="8158" href="Assignment2.html#8124" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="8164" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8164" class="InductiveConstructor">cc</a> <a id="8167" class="Symbol">:</a> <a id="8169" href="Assignment2.html#8124" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.


#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8408" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8420" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8420" class="Postulate">∃-distrib-⊎</a> <a id="8432" class="Symbol">:</a> <a id="8434" class="Symbol">∀</a> <a id="8436" class="Symbol">{</a><a id="8437" href="Assignment2.html#8437" class="Bound">A</a> <a id="8439" class="Symbol">:</a> <a id="8441" class="PrimitiveType">Set</a><a id="8444" class="Symbol">}</a> <a id="8446" class="Symbol">{</a><a id="8447" href="Assignment2.html#8447" class="Bound">B</a> <a id="8449" href="Assignment2.html#8449" class="Bound">C</a> <a id="8451" class="Symbol">:</a> <a id="8453" href="Assignment2.html#8437" class="Bound">A</a> <a id="8455" class="Symbol">→</a> <a id="8457" class="PrimitiveType">Set</a><a id="8460" class="Symbol">}</a> <a id="8462" class="Symbol">→</a>
    <a id="8468" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8471" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8471" class="Bound">x</a> <a id="8473" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8475" class="Symbol">(</a><a id="8476" href="Assignment2.html#8447" class="Bound">B</a> <a id="8478" href="Assignment2.html#8471" class="Bound">x</a> <a id="8480" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8482" href="Assignment2.html#8449" class="Bound">C</a> <a id="8484" href="Assignment2.html#8471" class="Bound">x</a><a id="8485" class="Symbol">)</a> <a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#5849" class="Record Operator">≃</a> <a id="8489" class="Symbol">(</a><a id="8490" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8493" href="Assignment2.html#8493" class="Bound">x</a> <a id="8495" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8497" href="Assignment2.html#8447" class="Bound">B</a> <a id="8499" href="Assignment2.html#8493" class="Bound">x</a><a id="8500" class="Symbol">)</a> <a id="8502" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8504" class="Symbol">(</a><a id="8505" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8508" href="Assignment2.html#8508" class="Bound">x</a> <a id="8510" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8512" href="Assignment2.html#8449" class="Bound">C</a> <a id="8514" href="Assignment2.html#8508" class="Bound">x</a><a id="8515" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="8649" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="8661" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8661" class="Postulate">∃×-implies-×∃</a> <a id="8675" class="Symbol">:</a> <a id="8677" class="Symbol">∀</a> <a id="8679" class="Symbol">{</a><a id="8680" href="Assignment2.html#8680" class="Bound">A</a> <a id="8682" class="Symbol">:</a> <a id="8684" class="PrimitiveType">Set</a><a id="8687" class="Symbol">}</a> <a id="8689" class="Symbol">{</a><a id="8690" href="Assignment2.html#8690" class="Bound">B</a> <a id="8692" href="Assignment2.html#8692" class="Bound">C</a> <a id="8694" class="Symbol">:</a> <a id="8696" href="Assignment2.html#8680" class="Bound">A</a> <a id="8698" class="Symbol">→</a> <a id="8700" class="PrimitiveType">Set</a><a id="8703" class="Symbol">}</a> <a id="8705" class="Symbol">→</a>
    <a id="8711" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8714" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8714" class="Bound">x</a> <a id="8716" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8718" class="Symbol">(</a><a id="8719" href="Assignment2.html#8690" class="Bound">B</a> <a id="8721" href="Assignment2.html#8714" class="Bound">x</a> <a id="8723" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8725" href="Assignment2.html#8692" class="Bound">C</a> <a id="8727" href="Assignment2.html#8714" class="Bound">x</a><a id="8728" class="Symbol">)</a> <a id="8730" class="Symbol">→</a> <a id="8732" class="Symbol">(</a><a id="8733" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8736" href="Assignment2.html#8736" class="Bound">x</a> <a id="8738" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8740" href="Assignment2.html#8690" class="Bound">B</a> <a id="8742" href="Assignment2.html#8736" class="Bound">x</a><a id="8743" class="Symbol">)</a> <a id="8745" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8747" class="Symbol">(</a><a id="8748" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8751" href="Assignment2.html#8751" class="Bound">x</a> <a id="8753" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8755" href="Assignment2.html#8692" class="Bound">C</a> <a id="8757" href="Assignment2.html#8751" class="Bound">x</a><a id="8758" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

{% raw %}<pre class="Agda"><a id="9185" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-|-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="9333" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
{% raw %}<pre class="Agda"><a id="9480" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="9492" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9492" class="Postulate">∃¬-implies-¬∀</a> <a id="9506" class="Symbol">:</a> <a id="9508" class="Symbol">∀</a> <a id="9510" class="Symbol">{</a><a id="9511" href="Assignment2.html#9511" class="Bound">A</a> <a id="9513" class="Symbol">:</a> <a id="9515" class="PrimitiveType">Set</a><a id="9518" class="Symbol">}</a> <a id="9520" class="Symbol">{</a><a id="9521" href="Assignment2.html#9521" class="Bound">B</a> <a id="9523" class="Symbol">:</a> <a id="9525" href="Assignment2.html#9511" class="Bound">A</a> <a id="9527" class="Symbol">→</a> <a id="9529" class="PrimitiveType">Set</a><a id="9532" class="Symbol">}</a>
    <a id="9538" class="Symbol">→</a> <a id="9540" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="9543" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9543" class="Bound">x</a> <a id="9545" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="9547" class="Symbol">(</a><a id="9548" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="9550" href="Assignment2.html#9521" class="Bound">B</a> <a id="9552" href="Assignment2.html#9543" class="Bound">x</a><a id="9553" class="Symbol">)</a>
      <a id="9561" class="Comment">--------------</a>
    <a id="9580" class="Symbol">→</a> <a id="9582" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="9584" class="Symbol">(∀</a> <a id="9587" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9587" class="Bound">x</a> <a id="9589" class="Symbol">→</a> <a id="9591" href="Assignment2.html#9521" class="Bound">B</a> <a id="9593" href="Assignment2.html#9587" class="Bound">x</a><a id="9594" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

{% raw %}<pre class="Agda"><a id="10338" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Decidable


#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:
{% raw %}<pre class="Agda"><a id="10501" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="10513" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10513" class="Postulate Operator">_&lt;?_</a> <a id="10518" class="Symbol">:</a> <a id="10520" class="Symbol">∀</a> <a id="10522" class="Symbol">(</a><a id="10523" href="Assignment2.html#10523" class="Bound">m</a> <a id="10525" href="Assignment2.html#10525" class="Bound">n</a> <a id="10527" class="Symbol">:</a> <a id="10529" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10530" class="Symbol">)</a> <a id="10532" class="Symbol">→</a> <a id="10534" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10538" class="Symbol">(</a><a id="10539" href="Assignment2.html#10523" class="Bound">m</a> <a id="10541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#26539" class="Datatype Operator">&lt;</a> <a id="10543" href="Assignment2.html#10525" class="Bound">n</a><a id="10544" class="Symbol">)</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="10555" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_` (practice)

Define a function to decide whether two naturals are equal:
{% raw %}<pre class="Agda"><a id="10681" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="10693" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10693" class="Postulate Operator">_≡ℕ?_</a> <a id="10699" class="Symbol">:</a> <a id="10701" class="Symbol">∀</a> <a id="10703" class="Symbol">(</a><a id="10704" href="Assignment2.html#10704" class="Bound">m</a> <a id="10706" href="Assignment2.html#10706" class="Bound">n</a> <a id="10708" class="Symbol">:</a> <a id="10710" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10711" class="Symbol">)</a> <a id="10713" class="Symbol">→</a> <a id="10715" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10719" class="Symbol">(</a><a id="10720" href="Assignment2.html#10704" class="Bound">m</a> <a id="10722" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10724" href="Assignment2.html#10706" class="Bound">n</a><a id="10725" class="Symbol">)</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="10736" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `erasure` (practice)

Show that erasure relates corresponding boolean and decidable operations:
{% raw %}<pre class="Agda"><a id="10879" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="10891" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10891" class="Postulate">∧-×</a> <a id="10895" class="Symbol">:</a> <a id="10897" class="Symbol">∀</a> <a id="10899" class="Symbol">{</a><a id="10900" href="Assignment2.html#10900" class="Bound">A</a> <a id="10902" href="Assignment2.html#10902" class="Bound">B</a> <a id="10904" class="Symbol">:</a> <a id="10906" class="PrimitiveType">Set</a><a id="10909" class="Symbol">}</a> <a id="10911" class="Symbol">(</a><a id="10912" href="Assignment2.html#10912" class="Bound">x</a> <a id="10914" class="Symbol">:</a> <a id="10916" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10920" href="Assignment2.html#10900" class="Bound">A</a><a id="10921" class="Symbol">)</a> <a id="10923" class="Symbol">(</a><a id="10924" href="Assignment2.html#10924" class="Bound">y</a> <a id="10926" class="Symbol">:</a> <a id="10928" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10932" href="Assignment2.html#10902" class="Bound">B</a><a id="10933" class="Symbol">)</a> <a id="10935" class="Symbol">→</a> <a id="10937" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10939" href="Assignment2.html#10912" class="Bound">x</a> <a id="10941" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10943" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="10945" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10947" href="Assignment2.html#10924" class="Bound">y</a> <a id="10949" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10951" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10953" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10955" href="Assignment2.html#10912" class="Bound">x</a> <a id="10957" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="10963" href="Assignment2.html#10924" class="Bound">y</a> <a id="10965" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-⊎"></a><a id="10969" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10969" class="Postulate">∨-⊎</a> <a id="10973" class="Symbol">:</a> <a id="10975" class="Symbol">∀</a> <a id="10977" class="Symbol">{</a><a id="10978" href="Assignment2.html#10978" class="Bound">A</a> <a id="10980" href="Assignment2.html#10980" class="Bound">B</a> <a id="10982" class="Symbol">:</a> <a id="10984" class="PrimitiveType">Set</a><a id="10987" class="Symbol">}</a> <a id="10989" class="Symbol">(</a><a id="10990" href="Assignment2.html#10990" class="Bound">x</a> <a id="10992" class="Symbol">:</a> <a id="10994" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10998" href="Assignment2.html#10978" class="Bound">A</a><a id="10999" class="Symbol">)</a> <a id="11001" class="Symbol">(</a><a id="11002" href="Assignment2.html#11002" class="Bound">y</a> <a id="11004" class="Symbol">:</a> <a id="11006" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11010" href="Assignment2.html#10980" class="Bound">B</a><a id="11011" class="Symbol">)</a> <a id="11013" class="Symbol">→</a> <a id="11015" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11017" href="Assignment2.html#10990" class="Bound">x</a> <a id="11019" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11021" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="11023" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11025" href="Assignment2.html#11002" class="Bound">y</a> <a id="11027" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11029" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11031" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11033" href="Assignment2.html#10990" class="Bound">x</a> <a id="11035" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="11041" href="Assignment2.html#11002" class="Bound">y</a> <a id="11043" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="11047" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11047" class="Postulate">not-¬</a> <a id="11053" class="Symbol">:</a> <a id="11055" class="Symbol">∀</a> <a id="11057" class="Symbol">{</a><a id="11058" href="Assignment2.html#11058" class="Bound">A</a> <a id="11060" class="Symbol">:</a> <a id="11062" class="PrimitiveType">Set</a><a id="11065" class="Symbol">}</a> <a id="11067" class="Symbol">(</a><a id="11068" href="Assignment2.html#11068" class="Bound">x</a> <a id="11070" class="Symbol">:</a> <a id="11072" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11076" href="Assignment2.html#11058" class="Bound">A</a><a id="11077" class="Symbol">)</a> <a id="11079" class="Symbol">→</a> <a id="11081" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="11085" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11087" href="Assignment2.html#11068" class="Bound">x</a> <a id="11089" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11091" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11093" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11095" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="11098" href="Assignment2.html#11068" class="Bound">x</a> <a id="11100" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism]({{ site.baseurl }}/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
{% raw %}<pre class="Agda"><a id="11336" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="11348" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11348" class="Postulate Operator">_iff_</a> <a id="11354" class="Symbol">:</a> <a id="11356" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="11361" class="Symbol">→</a> <a id="11363" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="11368" class="Symbol">→</a> <a id="11370" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="11377" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11377" class="Postulate Operator">_⇔-dec_</a> <a id="11385" class="Symbol">:</a> <a id="11387" class="Symbol">∀</a> <a id="11389" class="Symbol">{</a><a id="11390" href="Assignment2.html#11390" class="Bound">A</a> <a id="11392" href="Assignment2.html#11392" class="Bound">B</a> <a id="11394" class="Symbol">:</a> <a id="11396" class="PrimitiveType">Set</a><a id="11399" class="Symbol">}</a> <a id="11401" class="Symbol">→</a> <a id="11403" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11407" href="Assignment2.html#11390" class="Bound">A</a> <a id="11409" class="Symbol">→</a> <a id="11411" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11415" href="Assignment2.html#11392" class="Bound">B</a> <a id="11417" class="Symbol">→</a> <a id="11419" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11423" class="Symbol">(</a><a id="11424" href="Assignment2.html#11390" class="Bound">A</a> <a id="11426" href="Assignment2.html#3523" class="Record Operator">⇔</a> <a id="11428" href="Assignment2.html#11392" class="Bound">B</a><a id="11429" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="11433" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11433" class="Postulate">iff-⇔</a> <a id="11439" class="Symbol">:</a> <a id="11441" class="Symbol">∀</a> <a id="11443" class="Symbol">{</a><a id="11444" href="Assignment2.html#11444" class="Bound">A</a> <a id="11446" href="Assignment2.html#11446" class="Bound">B</a> <a id="11448" class="Symbol">:</a> <a id="11450" class="PrimitiveType">Set</a><a id="11453" class="Symbol">}</a> <a id="11455" class="Symbol">(</a><a id="11456" href="Assignment2.html#11456" class="Bound">x</a> <a id="11458" class="Symbol">:</a> <a id="11460" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11464" href="Assignment2.html#11444" class="Bound">A</a><a id="11465" class="Symbol">)</a> <a id="11467" class="Symbol">(</a><a id="11468" href="Assignment2.html#11468" class="Bound">y</a> <a id="11470" class="Symbol">:</a> <a id="11472" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11476" href="Assignment2.html#11446" class="Bound">B</a><a id="11477" class="Symbol">)</a> <a id="11479" class="Symbol">→</a> <a id="11481" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11483" href="Assignment2.html#11456" class="Bound">x</a> <a id="11485" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11487" href="Assignment2.html#11348" class="Postulate Operator">iff</a> <a id="11491" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11493" href="Assignment2.html#11468" class="Bound">y</a> <a id="11495" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11497" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11499" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11501" href="Assignment2.html#11456" class="Bound">x</a> <a id="11503" href="Assignment2.html#11377" class="Postulate Operator">⇔-dec</a> <a id="11509" href="Assignment2.html#11468" class="Bound">y</a> <a id="11511" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="11522" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
