## `arith_ss`

``` hol4
bossLib.arith_ss : simpset
```

------------------------------------------------------------------------

Simplification set for arithmetic.

The simplification set `arith_ss` is a version of `std_ss` enhanced for
arithmetic. It includes many arithmetic rewrites, an evaluation
mechanism for ground arithmetic terms, and a decision procedure for
linear arithmetic. It also incorporates a cache of successfully solved
conditions proved when conditional rewrite rules are successfully
applied.

The following rewrites are currently used to augment those already
present from `std_ss`:

``` hol4
   |- !m n. (m * n = 0) = (m = 0) \/ (n = 0)
   |- !m n. (0 = m * n) = (m = 0) \/ (n = 0)
   |- !m n. (m + n = 0) = (m = 0) /\ (n = 0)
   |- !m n. (0 = m + n) = (m = 0) /\ (n = 0)
   |- !x y. (x * y = 1) = (x = 1) /\ (y = 1)
   |- !x y. (1 = x * y) = (x = 1) /\ (y = 1)
   |- !m. m * 0 = 0
   |- !m. 0 * m = 0
   |- !x y. (x * y = SUC 0) = (x = SUC 0) /\ (y = SUC 0)
   |- !x y. (SUC 0 = x * y) = (x = SUC 0) /\ (y = SUC 0)
   |- !m. m * 1 = m
   |- !m. 1 * m = m
   |- !x.((SUC x = 1) = (x = 0)) /\ ((1 = SUC x) = (x = 0))
   |- !x.((SUC x = 2) = (x = 1)) /\ ((2 = SUC x) = (x = 1))
   |- !m n. (m + n = m) = (n = 0)
   |- !m n. (n + m = m) = (n = 0)
   |- !c. c - c = 0
   |- !m. SUC m - 1 = m
   |- !m. (0 - m = 0) /\ (m - 0 = m)
   |- !a c. a + c - c = a
   |- !m n. (m - n = 0) = m <= n
   |- !m n. (0 = m - n) = m <= n
   |- !n m. n - m <= n
   |- !n m. SUC n - SUC m = n - m
   |- !m n p. m - n > p = m > n + p
   |- !m n p. m - n < p = m < n + p /\ 0 < p
   |- !m n p. m - n >= p = m >= n + p \/ 0 >= p
   |- !m n p. m - n <= p = m <= n + p
   |- !n. n <= 0 = (n = 0)
   |- !m n p. m + p < n + p = m < n
   |- !m n p. p + m < p + n = m < n
   |- !m n p. m + n <= m + p = n <= p
   |- !m n p. n + m <= p + m = n <= p
   |- !m n p. (m + p = n + p) = (m = n)
   |- !m n p. (p + m = p + n) = (m = n)
   |- !x y w. x + y < w + x = y < w
   |- !x y w. y + x < x + w = y < w
   |- !m n. (SUC m = SUC n) = (m = n)
   |- !m n. SUC m < SUC n = m < n
   |- !n m. SUC n <= SUC m = n <= m
   |- !m i n. SUC n * m < SUC n * i = m < i
   |- !p m n. (n * SUC p = m * SUC p) = (n = m)
   |- !m i n. (SUC n * m = SUC n * i) = (m = i)
   |- !n m. ~(SUC n <= m) = m <= n
   |- !p q n m. (n * SUC q ** p = m * SUC q ** p) = (n = m)
   |- !m n. ~(SUC n ** m = 0)
   |- !n m. ~(SUC (n + n) = m + m)
   |- !m n. ~(SUC (m + n) <= m)
   |- !n. ~(SUC n <= 0)
   |- !n. ~(n < 0)
   |- !n. (MIN n 0 = 0) /\ (MIN 0 n = 0)
   |- !n. (MAX n 0 = n) /\ (MAX 0 n = n)
   |- !n. MIN n n = n
   |- !n. MAX n n = n
   |- !n m. MIN m n <= m /\ MIN m n <= n
   |- !n m. m <= MAX m n /\ n <= MAX m n
   |- !n m. (MIN m n < m = ~(m = n) /\ (MIN m n = n)) /\
            (MIN m n < n = ~(m = n) /\ (MIN m n = m)) /\
            (m < MIN m n = F) /\ (n < MIN m n = F)
   |- !n m. (m < MAX m n = ~(m = n) /\ (MAX m n = n)) /\
            (n < MAX m n = ~(m = n) /\ (MAX m n = m)) /\
            (MAX m n < m = F) /\ (MAX m n < n = F)
   |- !m n. (MIN m n = MAX m n) = (m = n)
   |- !m n. MIN m n < MAX m n = ~(m = n)
```

The decision procedure proves valid purely univeral formulas constructed
using variables and the operators `SUC,PRE,+,-,<,>,<=,>=`.
Multiplication by constants is accomodated by translation to repeated
addition. An attempt is made to generalize sub-formulas of type `num`
not fitting into this syntax.

### Comments

The philosophy behind this simpset is fairly conservative. For example,
some potential rewrite rules, e.g., the recursive clauses for addition
and multiplication, are not included, since it was felt that their
incorporation too often resulted in formulas becoming more complex
rather than simpler. Also, transitivity theorems are avoided because
they tend to make simplification diverge.

### See also

[`BasicProvers.RW_TAC`](#BasicProvers.RW_TAC),
[`BasicProvers.SRW_TAC`](#BasicProvers.SRW_TAC),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE),
[`BasicProvers.bool_ss`](#BasicProvers.bool_ss),
[`bossLib.std_ss`](#bossLib.std_ss),
[`bossLib.list_ss`](#bossLib.list_ss)
