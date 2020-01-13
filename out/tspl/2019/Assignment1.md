---
src       : "courses/tspl/2019/Assignment1.lagda.md"
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /TSPL/2019/Assignment1/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}" class="Module">Assignment1</a> <a id="131" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
```bash
submit tspl cw1 Assignment1.lagda.md
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

{% raw %}<pre class="Agda"><a id="1249" class="Keyword">import</a> <a id="1256" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1294" class="Symbol">as</a> <a id="1297" class="Module">Eq</a>
<a id="1300" class="Keyword">open</a> <a id="1305" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1308" class="Keyword">using</a> <a id="1314" class="Symbol">(</a><a id="1315" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1318" class="Symbol">;</a> <a id="1320" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1324" class="Symbol">;</a> <a id="1326" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1330" class="Symbol">;</a> <a id="1332" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1335" class="Symbol">)</a>
<a id="1337" class="Keyword">open</a> <a id="1342" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1357" class="Keyword">using</a> <a id="1363" class="Symbol">(</a><a id="1364" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1370" class="Symbol">;</a> <a id="1372" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1377" class="Symbol">;</a> <a id="1379" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1385" class="Symbol">;</a> <a id="1387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1389" class="Symbol">)</a>
<a id="1391" class="Keyword">open</a> <a id="1396" class="Keyword">import</a> <a id="1403" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1412" class="Keyword">using</a> <a id="1418" class="Symbol">(</a><a id="1419" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1420" class="Symbol">;</a> <a id="1422" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1426" class="Symbol">;</a> <a id="1428" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1431" class="Symbol">;</a> <a id="1433" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1436" class="Symbol">;</a> <a id="1438" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1441" class="Symbol">;</a> <a id="1443" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1446" class="Symbol">;</a> <a id="1448" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="1451" class="Symbol">;</a> <a id="1453" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="1456" class="Symbol">;</a> <a id="1458" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="1461" class="Symbol">)</a>
<a id="1463" class="Keyword">open</a> <a id="1468" class="Keyword">import</a> <a id="1475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="1495" class="Keyword">using</a> <a id="1501" class="Symbol">(</a><a id="1502" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="1509" class="Symbol">;</a> <a id="1511" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="1522" class="Symbol">;</a> <a id="1524" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="1529" class="Symbol">;</a> <a id="1531" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="1537" class="Symbol">;</a>
  <a id="1541" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="1547" class="Symbol">;</a> <a id="1549" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="1556" class="Symbol">;</a> <a id="1558" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1567" class="Symbol">;</a> <a id="1569" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1576" class="Symbol">;</a> <a id="1578" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1587" class="Symbol">;</a> <a id="1589" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1598" class="Symbol">;</a> <a id="1600" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1608" class="Symbol">)</a>
<a id="1610" class="Keyword">open</a> <a id="1615" class="Keyword">import</a> <a id="1622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1643" class="Keyword">using</a> <a id="1649" class="Symbol">(</a><a id="1650" href="plfa.part1.Relations.html#26539" class="Datatype Operator">_&lt;_</a><a id="1653" class="Symbol">;</a> <a id="1655" href="plfa.part1.Relations.html#26566" class="InductiveConstructor">z&lt;s</a><a id="1658" class="Symbol">;</a> <a id="1660" href="plfa.part1.Relations.html#26623" class="InductiveConstructor">s&lt;s</a><a id="1663" class="Symbol">;</a> <a id="1665" href="plfa.part1.Relations.html#30894" class="InductiveConstructor">zero</a><a id="1669" class="Symbol">;</a> <a id="1671" href="plfa.part1.Relations.html#30936" class="InductiveConstructor">suc</a><a id="1674" class="Symbol">;</a> <a id="1676" href="plfa.part1.Relations.html#30839" class="Datatype">even</a><a id="1680" class="Symbol">;</a> <a id="1682" href="plfa.part1.Relations.html#30859" class="Datatype">odd</a><a id="1685" class="Symbol">)</a>
</pre>{% endraw %}
## Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
{% raw %}<pre class="Agda"><a id="2541" class="Keyword">data</a> <a id="Bin"></a><a id="2546" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2546" class="Datatype">Bin</a> <a id="2550" class="Symbol">:</a> <a id="2552" class="PrimitiveType">Set</a> <a id="2556" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="2564" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2564" class="InductiveConstructor">nil</a> <a id="2568" class="Symbol">:</a> <a id="2570" href="Assignment1.html#2546" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="2576" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2576" class="InductiveConstructor Operator">x0_</a> <a id="2580" class="Symbol">:</a> <a id="2582" href="Assignment1.html#2546" class="Datatype">Bin</a> <a id="2586" class="Symbol">→</a> <a id="2588" href="Assignment1.html#2546" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="2594" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2594" class="InductiveConstructor Operator">x1_</a> <a id="2598" class="Symbol">:</a> <a id="2600" href="Assignment1.html#2546" class="Datatype">Bin</a> <a id="2604" class="Symbol">→</a> <a id="2606" href="Assignment1.html#2546" class="Datatype">Bin</a>
</pre>{% endraw %}For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

## Induction

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
