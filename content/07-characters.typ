#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/07-springer.typ": *

#chapter[Characters] <ch:characters>

#source(106)
From the Character Formula @eq:lusztig-deligne-character-formula we see that in
order to be able to write down the characters of the $R_T^(G)(theta)$ we have to
know the Green functions $Q_T^(G)(u)$. So far we only know that $Q_T^(G)(u)$ is
an integer. Except in the case of some groups of low rank where character tables
are known (@bib:Enomoto1976, @bib:Enomoto1972, @bib:Ennola1963, @bib:Nozawa1972,
@bib:Chang1974, @bib:Srinivasan1968, @bib:Ward1966), in the case of $GL_n$ (see
@bib:Green1955, @bib:Morris1977) where there is a recursive formula to determine
the functions, and in the case where $T$ is a "Coxeter torus" in a classical
group (see @bib:Lusztig1976b), no explicit formulae are known for the Green
functions in general. In this chapter we describe the work of Springer
@bib:Springer1976a and Kazhdan @bib:Kazhdan1977 which enable us to write down,
for sufficiently large $p$, expressions for the $Q_T^(G)(u)$ as "trigonometric
sums" on the Lie algebra of the group.

Consider the case when $T = T_0$. In this case we have a geometric
interpretation of the $Q_(T_0)^(G)(u)$, since $R_(T_0)^(G)(1)$ is the
permutation representation of $G^F$ on the cosets of $B_0^F$.

#definition[
  If $u$ is a unipotent element of $G$, $cal(B)_u$ is the variety of all Borel
  subgroups of $G$ containing $u$. We denote $cal(B)_1$ by $cal(B)$.
]

We note that $cal(B)_u$ is a projective variety since it is a subvariety of the
variety $cal(B)$ of all Borel subgroups of $G$. (See @bib:Steinberg1974, where
this variety is studied.) For example, if $G = GL_n$, $cal(B)_u$ is the variety
of all flags (in the vector space #source(107) $V$ on which $GL_n$ acts) fixed
by $u$. Now if $u$ is fixed by $F$ we have an action of $F$ on $cal(B)_u$ and
hence on $H_c^(i)(cal(B)_u)$. We then see that $Q_(T_0)^(G)(u) = |cal(B)_u^F| =
sum_i (-1)^i op("Tr")(F, H_c^(i)(cal(B)_u))$ by @th:grothendieck-trace-formula.
This is a cohomological interpretation for $Q_(T_0)^(G)(u)$, and we would like
to have a similar interpretation for $Q_T^(G)(u)$ for any $T$. This is done by
defining an action of $W = W(T_0)$ on $H_c^(i)(cal(B)_u)$ (although $W$ does not
act on $cal(B)_u$ itself) and then, if $T$ corresponds to $w in W$ (in the sense
of @cor:rational-tori), by obtaining $Q_T^(G)(u)$ as the alternating trace of
"$F$ twisted by $w$" on $⊕ H_c^(i)(cal(B)_u)$. There are three steps in this
process, the first two being due to Springer (@bib:Springer1971,
@bib:Springer1976a) and the third, for sufficiently large $p$, due to Kazhdan
@bib:Kazhdan1977. They are as follows. We assume that we have a fixed $F$-stable
maximal torus $T$. As before, $K = overline(bb(F)_q)$.

#enum(
  numbering: "(i)",
  [Let $A$ be an $F$-stable nilpotent element in the Lie algebra $frak(g)$ of
    $G$. We write down a "trigonometric function" on $frak(g)$ corresponding to
    $A$.],
  [Express this trigonometric sum as the alternating trace of an operator on the
    cohomology of $cal(B)_A$, where $cal(B)_A$ is the variety of all Borel
    subgroups of $G$ whose Lie algebras contain $A$.],
  [Lift the function so obtained on the $F$-stable nilpotent elements of
    $frak(g)$ to a function on the $F$-stable unipotent elements #source(108) of
    $G$, by using an exponential map. Prove that the function thus obtained on
    the unipotent elements of $G^F$ is (up to a constant) the Green function
    $Q_T^G$.],
)

We start with some preliminaries on the Lie algebra of $G$ (see eg.
@bib:Borel1969, p.~117 or @bib:Humphreys1975, p.~65).

#definition[
  The Lie algebra $frak(g)$ of $G$ is the $K$-space of all left-invariant
  derivations of $K[G]$ made into a Lie algebra by the rule
  $[delta_1, delta_2] = delta_1 delta_2 - delta_2 delta_1$. In other words,
  $frak(g) = {delta | delta "is a derivation of" K[G] "and"
    delta lambda_x = lambda_x delta "for all" x in G}$.
]

The group $G$ acts on $frak(g)$ by the Adjoint representation which can be
described as $op("Ad") g: delta -> rho_g delta rho_g^(-1)$ (@bib:Humphreys1975,
p.~66). For example, if $G = GL_n$, $frak(g)$ is the Lie algebra of all
$n times n$ matrices over $K$ and for $g in G$, $op("Ad") g$ is the map
$X -> g X g^(-1)$.

Let $B = T U$ be a Borel subgroup of $G$. Then we have a decomposition
$frak(g) = frak(t) + frak(n) + frak(n)^-$, where $frak(t), frak(n), frak(n)^-$
are the Lie algebras of $T, U, U^-$ respectively. We have
$frak(n) = sum_(alpha in Phi, alpha > 0) K X_alpha$,
$frak(n)^- = sum_(alpha in Phi, alpha < 0) K X_alpha$, where the $X_alpha$ are
"root vectors" and $K X_alpha$ is the Lie algebra of the root subgroup $U_alpha$
in $G$.

Let $frak(g)'$ be the vector space dual of $frak(g)$ and $⟨, ⟩$ the pairing
between $frak(g)$ and $frak(g)'$. If $G$ is an algebraic group over $CC$,
$frak(g)$ and $frak(g)'$ can be identified by a non-degenerate invariant
symmetric bilinear form on $frak(g)$. For large $p$ we have this also in
characteristic $p$. For example, if #source(109) $G = GL_n$, the form given by
$⟨ X, Y ⟩ = op("Tr") X Y$ has the above properties.

#definition[
  If $A$ is a nilpotent element in $frak(g)$, $cal(B)_A$ is the variety of all
  Borel subgroups of $G$ whose Lie algebras contain $A$.
]

We observe that there is a natural action of $F$ on $frak(g)$, and we denote the
set of $F$-fixed points by $frak(g)^F$. We have morphisms
$op("Ad"): G -> op("End") frak(g)$, $op("Ad")': G -> op("End") frak(g)'$, and it
can be shown, using their definitions, that they are defined over $bb(F)_q$. Let
$frak(t)'$ be the subspace of $frak(g)'$ which is orthogonal to
$frak(n) + frak(n)^-$. Then $frak(t)'$ is isomorphic to the dual of $frak(t)$.

#definition[
  $A' in frak(t)'$ is strongly regular if $C_(G)(A') = T$.
]

We now fix a non-trivial additive character
$psi: bb(F)_q -> overline(QQ)_ell^*$.

#definition[
  If $A$ is a nilpotent element of $frak(g)^F$ and $A'$ is a strongly regular
  element of $frak(t)'^F$, then
  $
    S(A, A') = sum_(X in G^F "-orbit of" A') psi ⟨ A, X ⟩.
  $
  #term-entry("Trigonometric sums S(A,A')", display: [Trigonometric sums
    $S(A, A')$])
]

_Remarks._ Here the action of $G^F$ is by $op("Ad")'$. Note also that since
$A in frak(g)^F$, $X in frak(g)'^F$, we have $⟨ A, X ⟩ in bb(F)_q$. Also this
"trigonometric sum" is just
$sum_(g in G^F / C_(G^F)(A')) psi ⟨ A, (op("Ad")' g) A' ⟩ =
sum_g psi ⟨ (op("Ad") g^(-1)) A, A' ⟩$, which bears a resemblance to the value
of an induced character, since $Y -> ⟨ Y, A' ⟩$ is a linear functional on
$frak(b) = frak(n) + frak(t)$.

#source(110)
#definition[
  If $a in K$, $Y_(A, A', a) =
  {(x, X) in K times (op("Ad")' G) A' | x^q - x = ⟨ A, X ⟩ + a}$.
]

Write $Y_(A, A')$ for $Y_(A, A', 0)$. Then $F$ acts on $Y_(A, A')$ by
$(x, X) -> (x^q, F X)$ and the additive group $bb(F)_q^+$ acts on $Y_(A, A')$ by
$zeta(a): (x, X) -> (x + a, X)$ ($a in bb(F)_q^+$). Let $zeta(a)^i$ be the
induced linear map on $H_c^(i)(Y_(A, A'))$. For the following Frobenius formulas
assume $a in bb(F)_q$. If $b in K$ is such that $b^q - b = a$, the map
$f: Y_(A, A') -> Y_(A, A', a)$ given by $(x, X) -> (x + b, X)$ is an isomorphism
and $F f = f zeta(a) F$. Thus we have that
$
  op("Tr")(F, H_c^(i)(Y_(A, A', a))) =
  op("Tr")(F zeta(a)^i, H_c^(i)(Y_(A, A'))).
$

We note that $(x, X) in Y_(A, A', a)^F$ if and only if $x in bb(F)_q$ and
$X in (op("Ad")' G^F) A'$ with $⟨ A, X ⟩ = -a$. Hence we have
$
  S(A, A') & = sum_(X in (op("Ad")' G^F) A') psi ⟨ A, X ⟩ \
           & = q^(-1) sum_(a in bb(F)_q) psi(-a) |Y_(A, A', a)^F| \
           & = q^(-1) sum_(i, a) (-1)^i
             [psi(-a) op("Tr")(F zeta(a)^i, H_c^(i)(Y_(A, A')))],
$
using @th:grothendieck-trace-formula, and so

$
  S(A, A') = sum_i (-1)^i op("Tr")(F, H_c^(i)(Y_(A, A'))_psi).
$ <eq:trigonometric-sum-cohomology>

Here $H_c^(i)(Y_(A, A'))_psi$ is the subspace of $H_c^(i)(Y_(A, A'))$ consisting
of all $x in H_c^(i)(Y_(A, A'))$ such that $zeta(a)^i x = psi(a) x$. Note that
this is an $F$-stable subspace. We have also used the fact that if $phi$ is any
character of $bb(F)_q^+$ then
$
  q^(-1) sum_(a in bb(F)_q) psi(-a) phi(a) =
  cases(0 & quad phi != psi, 1 & quad phi = psi).
$

#source(111)
In general these sums are not easy to compute explicitly. We give an example
where we compute them.

#example[
  $G = SL_2$, $frak(g) = frak(s l)_2$, $p != 2$, $A = mat(0, 1; 0, 0)$,
  $A' = mat(1, 0; 0, -1)$. We identify $frak(g)$ and $frak(g)'$ by means of the
  form $⟨ X, Y ⟩ = op("Tr") X Y$ on $frak(g)$. Now, by the Bruhat decomposition,
  $G = B_0 union B_0 w B_0$ where $w = mat(0, 1; -1, 0)$. Also $T_0$ centralizes
  $A'$. If $g in B_0^F$ then $⟨ A, (op("Ad") g) A' ⟩ = 0$. If
  $g in (B_0 w B_0)^F$, let
  $g = mat(1, a; 0, 1) mat(0, 1; -1, 0) mat(1, b; 0, 1)$. Then
  $⟨ A, (op("Ad") g) A' ⟩ = 2b$. If we choose $psi: bb(F)_q^+ -> CC^*$ to be a
  non-trivial character then we get
  $S(A, A') = q + q sum_(b in bb(F)_q) psi(2b) = q$. Now suppose we take
  $A = 0$. Then we get by similar calculations that $S(A, A') = q + q^2$. So we
  get
  $
    q^(-1) S(A, A') =
    cases(1 & quad A = mat(0, 1; 0, 0), q + 1 & quad A = 0).
  $
  These are precisely the values $Q_(T_0)^(G)(u)$ for $u = mat(1, 1; 0, 1)$ and
  $u = mat(1, 0; 0, 1)$ respectively (see the character table for $GL_2$ in
  Chapter~@ch:principal-series). If we were to choose $A'$ to be an element
  whose centralizer is a non-split torus in $G$, we would end up with the values
  of the discrete series characters at the unipotent elements.
]

The next few theorems are aimed at relating the groups #source(112)
$H_c^(i)(Y_(A, A'))_psi$ with the cohomology of $cal(B)_A$, and in the process
we will define a representation of $W = W(T)$ on $H_c^(i)(cal(B)_A)$. Recall
that $T$ is a fixed $F$-stable maximal torus, and $A$ is a nilpotent element of
$frak(g)^F$.

#definition[
  $frak(t)'_0$ is the set of strongly regular elements in $frak(t)'$.
]

#remark[
  It is known that $frak(t)'_0 != emptyset$ if $p != 2$ and
  $frak(t)'_0^F != emptyset$ if $q$ is sufficiently large. We assume from now on
  that $frak(t)'_0^F != emptyset$.
]

#definition[
  $cal(Y) = {(x, g T, A') in K times G / T times frak(t)'_0 |
    x^q - x = ⟨ A, (op("Ad")' g) A' ⟩}$.
]

We have actions of $bb(F)_q$, $W = W(T)$ and $F$ on $cal(Y)$: $a in bb(F)_q$
acts by $(x, g T, A') -> (x + a, g T, A')$. $w in W$ acts by
$(x, g T, A') -> (x, g dot(w)^(-1) T, (op("Ad") dot(w)) A')$. $F$ acts by
$(x, g T, A') -> (x^q, (F g) T, F A')$. Here, as before, $dot(w)$ is a
representative in $N(T)$ for $w$. The actions of $bb(F)_q$ and $F$ commute,
whereas $F dot w = (F w) dot F$ ($w in W$).

We now choose a Borel subgroup $B = T U$ containing $T$, and note that $B$ is
not necessarily $F$-stable. Having made this choice of $B$ in $cal(B)$, the
variety of Borel subgroups of $G$, we have maps
$
  cal(Y) arrow^f cal(B) times frak(t)'_0 arrow^sigma frak(t)'_0
$
given by
$
  (x, g T, A') arrow^f (g B g^(-1), A') arrow^sigma A'.
$
Let $pi = sigma f: cal(Y) -> frak(t)'_0$. The action of $W$ on $cal(Y)$ and
$frak(t)'_0$ commutes with $pi$. The idea then is to take the constant sheaf
$overline(QQ)_ell$ on $cal(Y)$, look at the direct image sheaf
$R^i pi_! overline(QQ)_ell$ on $frak(t)'_0$, take a suitable #source(113)
constant subsheaf of it which has stalks isomorphic to the groups
$H_c^(i - 2d)(cal(B)_A)$ ($d = dim U$) and get an action of $W$ on these groups.

#theorem(title: [@bib:Springer1976a, 3.5, 4.1])[
  #enum(
    numbering: "(i)",
    [The direct image sheaf $R^i f_! overline(QQ)_ell = 0$ if $i != 2d$, where
      $d = dim cal(B)$ ($= dim U$).],
    [The sheaf $(R^(2d) f_! overline(QQ)_ell)_psi$ on $cal(B) times frak(t)'_0$
      is supported on $cal(B)_A times frak(t)'_0$ and its restriction to
      $cal(B)_A times frak(t)'_0$ is the constant sheaf
      $overline(QQ)_(ell)(-d)$.],
  )
  [Here $(R^(2d) f_! overline(QQ)_ell)_psi$ denotes the part of
  $R^(2d) f_! overline(QQ)_ell$ on which $bb(F)_q$ acts according to the
  character $psi$. We let $bb(F)_q$ act trivially on $cal(B) times frak(t)'_0$,
  so that $f$ commutes with the actions of $bb(F)_q$ on $cal(Y)$ and
  $cal(B) times frak(t)'_0$. Thus we get an action of $bb(F)_q$ on
  $R^(2d) f_! overline(QQ)_ell$.]
] <th:springer-fibre-sheaf>

#proof[
  Consider a geometric point $overline(s)$ of $cal(B) times frak(t)'_0$ centred
  at $s = (g B g^(-1), A')$. By @cor:cohomology-geometric-fibre the stalk of
  $R^i f_! overline(QQ)_ell$ at $overline(s)$ is $H_c^(i)(cal(Y)_(overline(s)))$
  where $cal(Y)_(overline(s))$ is the fibre of $f$ over $overline(s)$. In our
  case $s$ is a closed point and we are working over an algebraically closed
  field $K$. Hence the stalk of $R^i f_! overline(QQ)_ell$ at $overline(s)$ is
  isomorphic to $H_c^(i)(f^(-1) s)$ where $f^(-1) s$ is the usual fibre over $s$
  (see the remark in the section on geometric points,
  Chapter~@ch:ell-adic-cohomology and Remark~@rem:closed-point-geometric-fibre).
  Now $f^(-1) s = {(x, h T, A') | h B h^(-1) = g B g^(-1)}$. If
  $h B h^(-1) = g B g^(-1)$ then $g^(-1) h in B$ and so $g^(-1) h = u t$ where
  $t in T$, $u in U$. Thus $f^(-1) s = {(x, g u T, A') |
    x^q - x = ⟨ (op("Ad") g^(-1)) A, (op("Ad")' u) A' ⟩}$.

  Consider $(op("Ad")' U) A'$. We have
  $frak(g) = frak(t) ⊕ sum_(alpha > 0) K X_alpha
  ⊕ sum_(alpha < 0) K X_alpha$ #source(114) where
  $frak(t) ⊕ sum_(alpha > 0) K X_alpha = frak(b)$, the Lie algebra of $B$. Then
  we can write $frak(g)' = frak(t)' ⊕ sum_(alpha > 0) K X'_alpha
  ⊕ sum_(alpha < 0) K X'_alpha$ where $⟨ frak(t), X'_alpha ⟩ = 0$,
  $⟨ X_alpha, X'_beta ⟩ = delta_(-alpha, beta)$. Using the formulas for the
  adjoint representation $frak(g) -> op("End") frak(g)$ (see
  eg.~@bib:Humphreys1972, p.~96) we can compute the action of the elements
  $x_(alpha)(t) in U_alpha subset U$ in the representations $op("Ad")$,
  $op("Ad")'$ of $G$. We can see that if $u in U$,
  $(op("Ad")' u) A' in A' + frak(b)^perp$, where
  $frak(b)^perp = sum_(alpha > 0) K X'_alpha$ is the subspace of $frak(g)'$
  orthogonal to $frak(b)$.

  By a theorem of Rosenlicht (see eg.~@bib:Steinberg1974, p.~35) any orbit of a
  unipotent group acting on an affine variety is closed and hence
  $(op("Ad")' U) A'$ is a closed subvariety of $frak(g)'$. Since $A'$ is
  strongly regular, it has the same dimension $d$ as $U$, and $d$ is also equal
  to $dim frak(b)^perp$. Hence $(op("Ad")' U) A' = A' + frak(b)^perp$.

  Now suppose $s in.not cal(B)_A times frak(t)'_0$, ie.
  $g B g^(-1) in.not cal(B)_A$. This means that
  $(op("Ad") g^(-1)) A in.not frak(b)$. Consider
  $⟨ (op("Ad") g^(-1)) A, (op("Ad")' u) A' ⟩$. Since $(op("Ad")' u) A'$ covers
  all the elements of $A' + frak(b)^perp$ as $u$ runs over $U$, and $U$ is
  isomorphic to affine space $bb(A)^d$, we have that $f^(-1) s$ is isomorphic to
  a finite covering of $bb(A)^d$. The action of $bb(F)_q$ on the first
  coordinate of $f^(-1) s$ by translation can be extended to an action of $K$,
  and then we see by Theorem~@th:connected-group-trivial-cohomology that $K$,
  and hence $bb(F)_q$, acts trivially on $H_c^(i)(f^(-1) s)$. Thus the group
  $(H_c^(i)(f^(-1) s))_psi$, which is the part of $H_c^(i)(f^(-1) s)$ on which
  $bb(F)_q$ acts according to the non-trivial character $psi$, is zero for all
  $i$. If $(op("Ad") g^(-1)) A in frak(b)$, then
  $⟨ (op("Ad") g^(-1)) A, (op("Ad")' u) A' ⟩ = 0$. In this case
  $f^(-1) s tilde.eq bb(F)_q times bb(A)^d$, and $bb(F)_q$ acts on the first
  factor #source(115) by translations. Now using @eq:cohomology-affine-space we
  see that $(H_c^(i)(f^(-1) s))_psi = 0$ if $i != 2d$. So we have proved (i) and
  also that the sheaf $(R^(2d) f_! overline(QQ)_ell)_psi$ is supported on
  $cal(B)_A times frak(t)'_0$. We also note that $H_c^(2d)(f^(-1) s)$ (where
  $s in cal(B)_A times frak(t)'_0$) is isomorphic to a direct sum of $q$ copies
  of $H_c^(2d)(bb(A)^d)$ and $bb(F)_q$ permutes these factors. So
  $(H_c^(2d)(f^(-1) s))_psi$ is isomorphic to $overline(QQ)_(ell)(-d)$.

  In order to finish the proof we have to show that in fact we have a constant
  sheaf on $cal(B)_A times frak(t)'_0$. That it is the constant sheaf
  $overline(QQ)_(ell)(-d)$ will then follow from the last sentence. This will
  result from two applications of Base Change @eq:cohomology-base-change.

  Let $Z = f^(-1)(cal(B)_A times frak(t)'_0) subset cal(Y)$. We have a
  commutative diagram
  $ #springer-support-square() $
  We also have $Z = {(x, g T, A') in cal(Y) |
    (op("Ad") g^(-1)) A in frak(b), x^q - x = 0}$. Thus
  $Z tilde.eq bb(F)_q times rho^(-1)(cal(B)_A) times frak(t)'_0$, where
  $rho: G / T -> cal(B)$ is the map $g T -> g B g^(-1)$. By
  @eq:cohomology-base-change it is sufficient to show that
  $(R^(2d)(f | Z)_! overline(QQ)_ell)_psi$ is a constant sheaf on
  $cal(B)_A times frak(t)'_0$. Since we also have the commutative diagram
  $ #springer-torus-borel-square() $
  we are reduced to showing that if we consider the map $rho: G / T -> cal(B)$,
  #source(116) the sheaf $R^(2d) rho_! overline(QQ)_ell$ is a constant sheaf on
  $cal(B)$. Note that the natural map $phi: G / T -> G / B$ is locally trivial,
  ie., there is a covering of $G / B$ by (Zariski) open sets $O_i$ such that
  $phi^(-1)(O_i) tilde.eq O_i times bb(A)^d$; this follows from the cellular
  decomposition of $G / B$ (see @bib:Borel1969, p.~347). Hence $rho$ is locally
  trivial. From this it follows (again by Base Change) that there is a covering
  of $cal(B)$ by Zariski open sets such that $R^(2d) rho_! overline(QQ)_ell$ is
  a constant sheaf on each open set, ie., that $R^(2d) rho_! overline(QQ)_ell$
  is a locally constant sheaf on $cal(B)$. Now it is a deep result that if $X$
  is a connected scheme and $overline(x)$ is a geometric point of $X$, the
  category of locally constant constructible sheaves of $ZZ/(ell^n ZZ)$-modules
  on $X$ is equivalent to the category of finitely-generated
  $ZZ/(ell^n ZZ)$-modules on which the fundamental group
  $pi_(1)(X, overline(x))$ acts continuously (see @bib:Deligne1977, p.~82, 2.3;
  @bib:Murre1967, @bib:Grothendieck1971). The fundamental group of $cal(B)$ is
  trivial since it is a rational projective variety (see @bib:Grothendieck1971,
  p.~285). Thus $R^(2d) rho_! overline(QQ)_ell$ is a constant sheaf on $cal(B)$.
  This proves the theorem.
]

#remark[
  Michael Artin has pointed out to me that there is a simpler way of proving
  that $R^(2d) rho_! overline(QQ)_ell$ is a constant sheaf on $cal(B)$, once we
  have shown that it is locally constant. This follows from the fact if $X$ is a
  connected _normal_ variety and $Phi$ is a locally constant sheaf on $X$ which
  is constant on some non-empty open set $U$ of $X$ then $Phi$ is a constant
  sheaf on $X$.
]

We now consider the composite morphism $pi = sigma f: cal(Y) -> frak(t)'_0$, and
use the Grothendieck spectral sequence (see
@eq:cohomology-grothendieck-single-degree). We regard $bb(F)_q$ as acting
trivially on $frak(t)'_0$; then $pi$ commutes with the actions of $bb(F)_q$ on
$cal(Y)$ and $frak(t)'_0$. Thus we can consider the sheaf
$(R^i pi_! overline(QQ)_ell)_psi$, the part of $R^i pi_! overline(QQ)_ell$ on
which $bb(F)_q$ acts according to $psi$.

#source(117)
#theorem(title: [@bib:Springer1976a, 4.2])[
  The sheaf $(R^i pi_! overline(QQ)_ell)_psi$ is the constant sheaf
  $H_c^(i - 2d)(cal(B)_A)(-d)$ on $frak(t)'_0$, for each $i$. The action of $W$
  on $cal(Y)$ gives rise to a representation of $W$ on $H_c^(i)(cal(B)_A)$.
  #term-entry("Springer representation of W", display: [Springer representation
    of $W$])
] <th:springer-weyl-representation>

#proof[
  By the Grothendieck spectral sequence
  @eq:cohomology-grothendieck-single-degree, using the fact
  (@th:springer-fibre-sheaf (i)) that $(R^j f_! overline(QQ)_ell)_psi = 0$ if
  $j != 2d$, we get $(R^i sigma_!)(R^(2d) f_! overline(QQ)_ell)_psi tilde.eq
  (R^(i + 2d) pi_! overline(QQ)_ell)_psi$. Let $Phi$ denote the sheaf on
  $cal(B)$ supported by $cal(B)_A$, which is the constant sheaf
  $overline(QQ)_(ell)(-d)$ on $cal(B)_A$.

  We have a commutative diagram
  $ #springer-constant-sheaf-square() $
  where $pi_1$ is projection. Then Theorem~@th:springer-fibre-sheaf (ii) implies
  that $pi_1^* Phi = (R^(2d) f_! overline(QQ)_ell)_psi$. By Base Change
  @eq:cohomology-base-change it follows that $R^i sigma_!(pi_1^* Phi)$ is a
  constant sheaf on $frak(t)'_0$, and thus
  $(R^(i + 2d) pi_! overline(QQ)_ell)_psi$ is a constant sheaf on $frak(t)'_0$,
  as required. The stalk at a geometric point of $frak(t)'_0$ centred at
  $A' in frak(t)'_0$ of the sheaf $R^i sigma_!(pi_1^* Phi)$ is isomorphic to
  $H_c^(i)(sigma^(-1) A', pi_1^* Phi)$, which in turn is isomorphic to
  $H_c^(i)(cal(B)_A)(-d)$. This proves the first statement of the theorem. The
  action of $W$ on $cal(Y)$ gives rise to an action of $W$ on the constant sheaf
  $(R^(i + 2d) pi_! overline(QQ)_ell)_psi$. Thus we get an action of $W$ on
  $H_c^(i)(cal(B)_A)(-d)$, ie., a representation of $W$ on $H_c^(i)(cal(B)_A)$,
  since $H_c^(i)(cal(B)_A)$ is isomorphic to $H_c^(i)(cal(B)_A)(-d)$. This
  proves the theorem.
]

Next we make the connection between these representations and the trigonometric
sums $S(A, A')$. First we recall that in defining
$f: cal(Y) -> cal(B) times frak(t)'_0$ by $f(x, g T, A') = (g B g^(-1), A')$, we
have made #source(118) a choice of $B in cal(B)$. So we now write $f_B$ for $f$.
Then $f_(dot(w) B dot(w)^(-1)) dot w = (i, w) dot f_B$ ($w in W$). Denote by
$alpha_B^i$ the isomorphism of constant sheaves
$(R^i pi_! overline(QQ)_ell)_psi tilde(arrow.r)
H_c^(i - 2d)(cal(B)_A)(-d)$ obtained in the proof of
@th:springer-weyl-representation. Let $w -> rho^(i)(w)$ be the action of $W$ on
the constant sheaf $(R^i pi_! overline(QQ)_ell)_psi$. Then
$alpha_(dot(w) B dot(w)^(-1))^i dot rho^(i)(w) = alpha_B^i$ ($w in W$). Denote
the representation of $W$ on $H_c^(i)(cal(B)_A)(-d)$, or on $H_c^(i)(cal(B)_A)$,
by $r^i$. Then we have $r^(i - 2d) = alpha_B^i rho^i (alpha_B^i)^(-1)$.

We now consider the action of $F$. We may suppose that $B = a^(-1) B_0 a$,
$T = a^(-1) T_0 a$, for some $a in G$. Then we have an isomorphism
$n -> a^(-1) n a$ of $N(T_0)$ onto $N(T)$, which induces an isomorphism $gamma$
of $W(T_0)$ onto $W(T)$. Now $T$ corresponds to $w_1 in W(T_0)$ (in the sense of
@cor:rational-tori) where $dot(w)_1 = a (F a)^(-1) in N(T_0)$. We have
$F B = (F a)^(-1) a B a^(-1)(F a) = dot(w)_2 B dot(w)_2^(-1)$, where
$dot(w)_2 = a^(-1) dot(w)_1 a$ and thus $w_2$ corresponds to $w_1$ under
$gamma$.

#remark[
  It can be shown that the representations $rho^i$ of $W$ are independent of the
  choice of $B$ (see @bib:Springer1976a, 4.6).
]

We now denote the representation of $W(T_0)$ on $H_c^(i)(cal(B)_A)$ obtained via
the isomorphism $gamma$, also by $r^i$. Then we can prove the following theorem.

#theorem(title: [@bib:Springer1976a, 4.4])[
  Let $w in W(T_0)$ correspond to the torus $T$. Then
  $S(A, A') = q^d sum_(i >= 0) (-1)^i
  op("Tr")(F dot r^(i)(w)^(-1), H_c^(i)(cal(B)_A))$.
  #term-entry(
    "Trigonometric sums S(A,A')",
    display: [Trigonometric sums $S(A, A')$],
    sub: "cohomological interpretation of",
  )
] <th:springer-trigonometric-sum>

#source(119)
#proof[
  From the commutative diagram
  $ #springer-frobenius-diagram() $
  we get an isomorphism of constant sheaves
  $F^*: (R^i pi_! overline(QQ)_ell)_psi tilde(arrow.r)
  (R^i pi_! F^* overline(QQ)_ell)_psi$ on $frak(t)'_0$, where $F^*$ denotes the
  pullback under $F$ of the appropriate sheaves. Now
  $(R^i pi_! overline(QQ)_ell)_psi$ is the constant sheaf
  $H_c^(i - 2d)(cal(B)_A)(-d)$ on $frak(t)'_0$, and it follows from the proofs
  of @th:springer-fibre-sheaf and @th:springer-weyl-representation that the
  morphism $F^*$ is given by the endomorphism $F$ of
  $H_c^(i - 2d)(cal(B)_A)(-d) tilde.eq
  H_c^(i - 2d)(cal(B)_A, overline(QQ)_(ell)(-d))$ which arises from the
  endomorphism $F$ of $cal(B)_A$. If we now make an identification of
  $H_c^(i - 2d)(cal(B)_A)(-d)$ with $H_c^(i - 2d)(cal(B)_A)$, then we have to
  replace the endomorphism $F$ of the former group by the endomorphism $q^d F$
  of $H_c^(i - 2d)(cal(B)_A)$. Hence we have a commutative diagram
  $ #springer-tate-twist-diagram() $
  #source(120) from which we get $alpha_B^i F^* = q^d F alpha_(F B)^i =
  q^d F alpha_B^i rho^(i)(w)^(-1) =
  q^d F r^(i - 2d)(w)^(-1) alpha_B^i$, where $w in W$ is given by
  $F B = dot(w) B dot(w)^(-1)$.

  Now consider the fibre over $A' in frak(t)'_0$ of $pi$. We remark that $G / T$
  is isomorphic to the $(op("Ad")' G)$-orbit of $A'$ since $A'$ is strongly
  regular. (This statement requires some proof, using @bib:Borel1969, 6.7, which
  we will omit; see @bib:Springer1976a, 2.10.) Thus the fibre of $pi$ over $A'$
  is precisely the variety $Y_(A, A')$ defined earlier. Hence we get that the
  stalk at a geometric point of $frak(t)'_0$ centred at $A'$ of the sheaf
  $(R^i pi_! overline(QQ)_ell)_psi$ is isomorphic to $H_c^(i)(Y_(A, A'))_psi$,
  and thus $H_c^(i)(Y_(A, A'))_psi tilde.eq H_c^(i - 2d)(cal(B)_A)(-d)$.
  Theorem~@th:springer-trigonometric-sum then follows from
  @eq:trigonometric-sum-cohomology.
]

_Remarks._

#enum[
  The variety $cal(B)_A$ is in general singular. For example, if $G = GL_3$,
  $A = mat(0, 1, 0; 0, 0, 0; 0, 0, 0)$, $cal(B)_A$ is the union of two
  intersecting projective lines over $K$:

  #springer-projective-lines(2)

  If $G = Sp_4$ and $A$ is the nilpotent element which has two blocks
  $mat(0, 1; 0, 0)$ along the diagonal and zeros everywhere else, $cal(B)_A$ is
  the union of three projective lines over $K$:

  #springer-projective-lines(3)

  In this case we have a standard Frobenius action on $cal(B)_A$ stabilizing
  each line, and a twisted Frobenius action on $cal(B)_A$ interchanging $ell_1$
  and $ell_2$. This corresponds to the fact that on the two unipotent #source(
    121,
  ) classes in the finite group $Sp(4, q)$ with representatives
  $
    mat(1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1; 0, 0, 0, 1)
    quad "and" quad
    mat(
      1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, -gamma;
      0, 0, 0, 1
    )
  $
  (where $gamma$ is a generator of $FF_q^*$) the principal series irreducible
  characters have values $1 + 3q$ and $1 + q$, which are equal to $|cal(B)_A^F|$
  in the two cases (see @bib:Srinivasan1968, p. 517).

  Since $cal(B)_A$ is singular we cannot use the deep theorems of Deligne (see
  @bib:Serre1975) on the eigenvalues of $F$ on the groups $H_c^(i)(cal(B)_A)$.
  However, recently P. Slodowy in Bonn has proved that there is a non-singular
  variety whose cohomology is the same as that of $cal(B)_A$, and from this it
  follows that the eigenvalues of $F$ on $H_c^(i)(cal(B)_A)$ have absolute value
  $q^(i / 2)$.

  For various results on the variety $cal(B)_A$ the reader is referred to
  @bib:Steinberg1974, @bib:Steinberg1976.

][
  Let $Z = C_(G)(A)$. Then $Z$ acts on $cal(Y)$ by
  $z(x, g T, A') = (x, z g T, A')$ ($z in Z$) and this action commutes with the
  action of $W$. Thus $Z$ acts on the constant sheaf
  $(R^i pi_! overline(QQ)_ell)_psi$ on $frak(t)'_0$ and we get a representation
  of $Z$ on $H_c^(i)(cal(B)_A)$ which commutes with the representation $r^i$ of
  $W$. Now $Z^0$ acts trivially on $H_c^(i)(cal(B)_A)$, using
  @th:connected-group-trivial-cohomology, and thus the finite group
  $C = Z / Z^0$ acts on $H_c^(i)(cal(B)_A)$. Springer (@bib:Springer1976a, 6.10)
  shows (assuming $q$ sufficiently large) that if $zeta$ is an irreducible
  representation of $C$ then the representation of $W$ on the non-zero
  multiplicity space $op("Hom")_(C)(zeta, H_c^(2e)(cal(B)_A))$, where
  $e = dim cal(B)_A$, is irreducible and each irreducible representation of $W$
  is obtained exactly once as #source(122) we vary $A$ over a set of
  representatives for the $(op("Ad") G)$-orbits of nilpotent elements in
  $frak(g)$ and $zeta$ over a set of representatives for the isomorphism classes
  of irreducible representations of $C$ with non-zero multiplicity space.

  Shoji @bib:Shoji1979 has studied this connection between nilpotent elements in
  $frak(g)$ and representations of $W$ when $G$ is classical or of type $F_4$,
  and Hotta and Springer @bib:Hotta1977 when $G = GL_n$ or when $A$ is of
  “parabolic type.”
]

#heading(level: 2, numbering: none)[Application to Green functions]

Given the $F$-stable maximal torus $T$, we fix a strongly regular element $A'$
in $frak(t)'^F$, and define the following function on the nilpotent elements of
$frak(g)^F$.

#definition(numbered: true)[
  $ Q_(T, frak(g))(A) = epsilon_G epsilon_T q^(-d) S(A, A'). $
] <def:lie-green-function>

We state without proof certain orthogonality relations satisfied by the
functions $Q_(T, frak(g))$ which are similar to the relations of
@eq:green-function-orthogonality. We note that we are justified in our notation
$Q_(T, frak(g))$ since @th:springer-trigonometric-sum shows that $S(A, A')$ is
independent of the choice of $A'$.

#theorem(numbered: false, title: [@bib:Springer1976a, 5.6])[
  Let $T, T'$ be two $F$-stable maximal tori in $G$. Then (for sufficiently
  large $q$) we have
  $
    frac(1, |G^F|) sum_(X in frak(g)^F, X "nilpotent")
    Q_(T, frak(g))(X) Q_(T', frak(g))(X)
    = frac(|N(T, T')^F|, |T^F| |T'^F|).
  $
  <eq:lie-green-orthogonality>
]

We will now sketch a proof that if $G = GL_n$ and $F$ is the standard Frobenius,
so that $G^F = GL(n, q)$, then $Q_(T, frak(g))(A)$ is a polynomial in $q$. We
can assume $A$ is in Jordan form. The variety $cal(B)$ can be identified with
the variety of complete flags #source(123)
$
  0 subset V_1 subset V_2 subset dots subset V_n = V,
  quad dim V_(i + 1) / V_i = 1,
$
where $V$ is the vector space over $K$ on which $G$ acts. Then $cal(B)_A$ is the
subvariety of flags such that $V_(i + 1) / V_i$ is annihilated by $A$. Let
$cal(P)_A$ be the variety of lines (i.e., one-dimensional subspaces) of $V$
annihilated by $A$. Then $cal(P)_A tilde.eq bb(P)(M)$, where $M = ker A$.

We have a map $pi: cal(B)_A arrow.r cal(P)_A$ which takes the flag
$0 subset V_1 dots$ to $V_1$. If $v in M$, $A$ induces a nilpotent
transformation $overline(A)$ on $V / ⟨v⟩$, so $overline(A)$ can be regarded as
an element of the Lie algebra of $GL_(n - 1)$. The fibre of $pi$ over $⟨v⟩$ is
isomorphic to $cal(B)_(overline(A))$. We have a filtration
$M = M_0 supset M_1 supset dots supset M_d = 0$, where $M_i = M ∩ op("Im") A^i$.
For all $v in M_i - M_(i + 1)$, the fibres of $pi$ are isomorphic as varieties
over $FF_q$. Let $Y_i = pi^(-1)(bb(P)(M_i) - bb(P)(M_(i + 1)))$ (making an
identification of $cal(P)_A$ with $bb(P)(M)$). Then one can show (see
@bib:Spaltenstein1976 for details) that the map
$pi: Y_i arrow.r bb(P)(M_i) - bb(P)(M_(i + 1))$ is locally trivial, and thus
locally $H_c^(i)(Y_i)$ looks like
$
  op("⊕", limits: #true)_(j + k = i) {H_c^(j)(bb(P)(M_i) - bb(P)(M_(i + 1)))
    ⊗ H_c^(k)(cal(B)_(overline(A)))}.
$
Now $bb(P)(M_i) - bb(P)(M_(i + 1))$ is a union of affine spaces, and by
induction we can assume that the eigenvalues of $F$ on
$H_c^(k)(cal(B)_(overline(A)))$ are integral powers of $q$. Furthermore the
representations of $W$ ($tilde.eq S_n$ in this case) are integral. Using
@th:springer-trigonometric-sum we see that $Q_(T, frak(g))(A)$ is a polynomial
in $q$ with integer coefficients.

The fibration of $cal(B)_A$ described above has been given by Spaltenstein in
[loc. cit.]. Similar results for classical groups, #source(124) showing that the
$Q_(T, frak(g))(A)$ are polynomials in $q$ also in that case, can be found in
@bib:Srinivasan1977.

We would now like to connect the functions $Q_(T, frak(g))$ on the nilpotent
elements of $frak(g)^F$ with the Green functions $Q_T^G$ on the unipotent
elements of $G$ introduced in @ch:lusztig-deligne. We describe the work of
Kazhdan @bib:Kazhdan1977 which gives this connection. We start with a brief
description of the Kirillov theory of orbits for nilpotent Lie algebras over
$RR$ (see e.g., @bib:Lipsman1974, p. 87).

Let $N$ be a connected, simply connected, nilpotent Lie group over $RR$ and
$frak(n)$ its Lie algebra. Then $frak(n)$ is a nilpotent Lie algebra over $RR$.
Let $frak(n)'$ be the dual of $frak(n)$, i.e.,
$frak(n)' = op("Hom")_(RR)(frak(n), RR)$.

#definition[
  Let $lambda in frak(n)'$. Then $B_lambda$ is the bilinear alternating form on
  $frak(n)$ given by
  $B_(lambda)(x_1, x_2) = lambda [x_1, x_2]$
  ($x_1, x_2 in frak(n)$).
]

#definition[
  A subalgebra $frak(h)$ of $frak(n)$ which is a maximal isotropic subspace for
  $B_lambda$ is called a polarization for $lambda$.
]

For a general discussion of polarizations the reader is referred to
@bib:Dixmier1977. Such subalgebras exist in the nilpotent case and the following
construction is due to M. Vergne. Let
$frak(n) = frak(n)_0 supset frak(n)_1 supset dots supset frak(n)_k = 0$
be a series of subspaces of $frak(n)$ such that
$dim frak(n)_i / frak(n)_(i + 1) = 1$. Let $frak(h)_i$ be the kernel of the
restriction of $B_lambda$ to $frak(n)_i$, and let
$frak(h) = sum_(i = 0)^k frak(h)_i$. Then $frak(h)$ is a maximal isotropic
subspace of $B_lambda$. If the $frak(n)_i$ are also ideals, then $frak(h)$ is a
subalgebra. Hence we can always find polarizations for $lambda$ if #source(125)
$frak(n)$ is nilpotent. The idea in finding polarizations is that $lambda$ is
only a linear functional on $frak(n)$, but it is a representation of $frak(h)$.
So we are finding a maximal subalgebra $frak(h)$ of $frak(n)$ which has $lambda$
as a representation. (Note, however, that $frak(h)$ is not uniquely determined
by $lambda$.)

Now let $H = exp frak(h)$, and define a character of $H$ by
$chi_(lambda)(exp x) = e^(i lambda(x))$ ($x in frak(h)$). Let
$rho(lambda, frak(h)) = op("Ind")_H^(N)(chi_lambda)$. Then Kirillov showed that
the representations $rho(lambda, frak(h))$ of $N$ are irreducible and that there
is a bijection $frak(n)' / N arrow.r epsilon(N)$, where $epsilon(N)$ is the set
of unitary equivalence classes of irreducible unitary representations of $N$.

We now return to our group $G$ and give a similar description of the characters
of $U^F subset G^F$, where $U$ is an $F$-stable maximal unipotent subgroup of
$G$, provided $p$ is sufficiently large. Let $V$ be the variety of unipotent
elements of $G$ and $frak(V)$ the variety of nilpotent elements of $frak(g)$. We
assume, for the rest of this chapter, that $p$ is large enough so that the maps
$exp: frak(V) arrow.r V$ and $ln: V arrow.r frak(V)$ are defined as in
characteristic $0$ and the Campbell–Hausdorff formulas (see e.g.,
@bib:Hochschild1965) hold, and that a non-degenerate invariant symmetric
bilinear form exists on the Lie algebras of reductive subgroups of $G$. (For
example if $G = GL_n$, $p > n$ will do.)

Let $frak(n) subset frak(g)$ be the Lie algebra of $U$, $frak(n)'$ the linear
dual (over $K$) of $frak(n)$. $U$ acts on $frak(n), frak(n)'$ by
$op("Ad"), op("Ad")'$ respectively, and $F$ acts on $frak(n)$ and $frak(n)'$.
Let $lambda in frak(n)'^F$. We find a polarization #source(126)
$frak(h) subset frak(n)$ for $lambda$, just as in the real case. In other words
we define $B_lambda$ as before and imitate the construction given to find a
polarization. Then we have a corresponding subgroup $H = exp frak(h)$ of $U$,
which is fixed by $F$.

We fix a non-trivial character $psi: FF_q arrow.r overline(QQ)_ell^*$. Let the
character $phi_lambda: H^F arrow.r overline(QQ)_ell^*$ be given by
$phi_(lambda)(exp x) = psi(lambda(x))$ ($x in frak(h)^F$). Then define
$chi_lambda = op("Ind")_(H^F)^(U^F)(phi_lambda)$, so that $chi_lambda$ is a
character of $U^F$.

#theorem(title: [@bib:Kazhdan1977, Propositions 1 and 2])[
  #enum(numbering: "(i)")[
    $
      chi_(lambda)(v) = q^(-dim Omega_lambda / 2)
      sum_(mu in Omega_lambda^F) psi(mu(ln v)) quad (v in U^F),
    $
    where $Omega_lambda = (op("Ad")' U) lambda$ is the $U$-orbit of $lambda$.
  ][
    $chi_lambda$ is irreducible for every $lambda$.
  ][
    $chi_lambda = chi_(lambda')$ if and only if
    $Omega_lambda = Omega_(lambda')$.
  ][
    Every irreducible character of $U^F$ is equal to $chi_lambda$.
  ][
    $dim chi_lambda = |Omega_lambda^F|^(1 / 2)
    = q^(dim Omega_lambda / 2)$.
  ]
] <th:finite-kirillov-orbits>

#proof[
  (i). Let $v in U^F$, $v = exp w$ where $w in frak(n)$. Then, by definition,
  $chi_(lambda)(v) = frac(1, |H^F|)
  sum_(u in U^F) a_(lambda)((op("Ad") u) w)$, where
  $
    a_(lambda)(x) = cases(
      psi(lambda(x)) & "if" x in frak(h)^F,
      0 & "otherwise".
    )
  $
  Let $frak(l)$ be the affine subspace of $frak(n)'$ consisting of all linear
  functionals $nu$ such that $nu | frak(h) = lambda$, i.e.,
  $frak(l) = frak(h)^perp + lambda$ where $frak(h)^perp$ is the annihilator of
  $frak(h)$ in $frak(n)'$. Then we have $a_(lambda)(x) = frac(1, |frak(l)^F|)
  sum_(nu in frak(l)^F) psi(nu(x))$: for if $x in frak(h)^F$, then
  $nu(x) = lambda(x)$ for all $nu$

  #source(127)
  in $frak(l)^F$ and we just get $psi(lambda(x))$, and if $x in.not frak(h)^F$
  then as $nu$ varies over $frak(h)^perp + lambda$ we get
  $sum_nu psi(nu(x)) = 0$ since $psi$ is a non-trivial character of $FF_q$.
  Hence we get
  $
    chi_(lambda)(v) & = frac(1, |H^F|) frac(1, |frak(l)^F|)
                      sum_(u in U^F, nu in frak(l)^F) psi(nu(op("Ad") u)(w)) \
                    & = frac(1, |H^F|) frac(1, |frak(l)^F|)
                      sum_(u, nu) psi(((op("Ad")' u)^(-1) nu)(w)).
  $

  Next, we see that $frak(l)$ is $(op("Ad") H)$-stable, and we show that in fact
  $H$ acts transitively on $frak(l)$. Let $H_0 subset H$ be the stabilizer of
  $lambda$ in $U$, and let $frak(h)_0$ be the kernel of the form $B_lambda$ on
  $frak(n)$, i.e., $frak(h)_0 = {x in frak(n) | lambda [x, y] = 0
    "for all" y "in" frak(n)}$. Now (transferring $exp$ to $op("ad") frak(n)$)
  we have $lambda((op("ad") x)y) = 0$ for all $y$ in $frak(n)$ if and only if
  $lambda(exp(op("ad") x)(y)) = lambda(y)$ for all $y$ in $frak(n)$. Just as in
  characteristic $0$ (see, e.g., @bib:Hochschild1965, p. 116, Ex. 3) it follows
  that $H_0 = exp frak(h)_0$ and, in particular, $H_0$ is connected.

  By Witt's Theorem we can write
  $frak(n) = frak(h)_0 ⊕ frak(a) ⊕ frak(a)'$
  where $frak(h) = frak(h)_0 ⊕ frak(a)$ and $dim frak(a) = dim frak(a)'$. So
  $op("codim") frak(h) = dim H - dim H_0$,
  $dim Omega_lambda = dim U - dim H_0 = 2 op("codim") frak(h)$,
  $dim frak(l) = dim frak(h)^perp = op("codim") frak(h)
  = 1 / 2 dim Omega_lambda$. Consider the map $sigma: H/H_0 arrow.r frak(l)$
  given by $sigma(x) = (op("Ad") x) lambda$. This is injective, and its image is
  a closed orbit of the unipotent group $H$ in the affine space $frak(l)$. The
  above remarks on dimensions therefore show that $sigma$ is surjective.
  <passage:kirillov-polarization-orbit>
  #ed-note[
    Equality of dimensions needs the closedness of unipotent orbits on an affine
    variety. See #cite(
      <MilneGroups2017>,
      form: "full",
    ), Theorem 17.64, p. 374.
  ]
  Thus $H$ acts transitively on $frak(l)$. Now the $H^F$-orbits in $frak(l)^F$
  are classified by the $F$-conjugacy classes of $H_0 / (H_0)^0$, as in
  @prop:f-stable-conjugacy. Since $H_0$ is connected, we also have that $H^F$ is
  transitive on $frak(l)^F$.

  #source(128)
  Now it follows that $chi_(lambda)(v) = frac(1, |frak(l)^F|)
  sum_(nu in Omega_lambda^F) psi(nu(w))$, i.e.,
  $chi_(lambda)(v) = q^(-dim Omega_lambda / 2)
  sum_(nu in Omega_lambda^F) psi(nu(w))$, where $w = ln v$, which proves (i).

  (ii) We compute $(chi_lambda, chi_lambda)$ using (i). We get
  $
    (chi_lambda, chi_lambda) = q^(-dim Omega_lambda)
    frac(1, |frak(n)^F|) sum_(x in frak(n)^F)
    |sum_mu psi(mu(x))|^2,
  $
  where $mu$ runs over $|Omega_lambda^F|$ linear maps of the $FF_q$-vector space
  $frak(n)^F$. Now
  $|Omega_lambda^F| = frac(|U^F|, |H_0^F|) = q^(dim Omega_lambda)$
  since $U$ is unipotent and hence $U/H_0$ is isomorphic to affine space (see
  e.g., @bib:Demazure1970, p. 535). This proves that
  $(chi_lambda, chi_lambda) = 1$.

  (iii) is proved analogously to (ii) since we can compute
  $(chi_lambda, chi_(lambda'))$ in the same way. Also (v) follows from (i).

  (iv) We have $sum_lambda (dim chi_lambda)^2 = sum_lambda |Omega_lambda^F|
  = q^(dim frak(n)) = |U^F|$, where $lambda$ runs over a set of representatives
  from the $op("Ad")' U^F$-orbits on $frak(n)'^F$. This proves (iv), and hence
  the theorem.
]

As before let $T$ be an $F$-stable maximal torus of $G$ and let
$frak(t) subset frak(g)$ be the Lie algebra of $T$. We identify $frak(t)$ and
its dual $frak(t)'$ by means of a non-degenerate invariant symmetric bilinear
form. Let $A'$ be a strongly regular semisimple element in $frak(t)^F$: i.e.,
$C_(G)(A') = T$. Let $Omega(A') = (op("Ad") G) A'$ be the $G$-orbit of $A'$.
Since $C_(G)(A')$ is connected, we see as in the proof of
@prop:f-stable-conjugacy that $Omega(A')^F = (op("Ad") G^F) A'$. Now we can
write the function $Q_(T, frak(g))$ on $frak(V)^F$ defined in
@def:lie-green-function as
$
  Q_(T, frak(g))(x) = frac(epsilon_G epsilon_T, |U^F|)
  sum_(y in Omega(A')^F) psi(⟨x, y⟩) quad (x in frak(V)^F),
$

#source(129)
where $⟨ , ⟩$ denotes the invariant bilinear form. We define a function $Phi$ on
$V^F$ as follows:
$ Phi(v) = epsilon_G epsilon_T Q_(T, frak(g))(ln v). $
The following theorem is a crucial result in Kazhdan's paper.

#theorem(title: [@bib:Kazhdan1977, Theorem 1])[
  The function $Phi$ is a (proper) character of $U^F$.
] <th:kazhdan-unipotent-character>

#proof[
  By @th:finite-kirillov-orbits it is sufficient to show that the scalar product
  of $Phi$ with any $chi_lambda$ is a non-negative integer. Since
  $chi_lambda = op("Ind")_(H^F)^(U^F)(phi_lambda)$ for some
  $lambda in frak(n)'^F$, we have
  $
    (Phi, chi_lambda)_(U^F) & = (Phi, phi_lambda)_(H^F) \
                            & = frac(1, |H^F|) sum_(u in H^F)
                              epsilon_G epsilon_T Q_(T, frak(g))(ln u)
                              overline(phi_(lambda)(u)) \
                            & = frac(1, |H^F|) sum_(x in frak(h)^F)
                              epsilon_G epsilon_T Q_(T, frak(g))(x)
                              psi(-lambda(x)) \
                            & = frac(1, |H^F|) frac(1, |U^F|)
                              sum_(y in Omega(A')^F, x in frak(h)^F)
                              psi{⟨x, y⟩ - lambda(x)} \
                            & = frac(1, |U^F|) |X^F|,
  $
  where $X subset Omega(A')$ is the variety of all $y in Omega(A')$ such that
  the linear functional $x arrow.r ⟨x, y⟩$ on $frak(h)$ coincides with $lambda$.
  So in order to prove the theorem we have to show that $|U^F|$ divides $|X^F|$.

  The variety $X$ has been defined with reference to the strongly regular
  element $A'$ whose centralizer is $T$ and the $F$-stable unipotent subgroup
  $U$. Keeping $U$ fixed, we conjugate $T$

  #source(130)
  over $K$ and assume now that $T$ normalizes $U$. We can no longer assume $T$
  (or $A'$) $F$-stable. Thus we will now essentially consider a variety which is
  isomorphic over $K$ to $X$, and define a partition of this variety into
  locally closed subvarieties.

  By the Bruhat decomposition we have
  $G = union_w T U dot(w) U_(w^(-1))^- = union_w U dot(w) U_(w^(-1))^- T$, where
  $w$ runs over $W(T)$. Let $g in G_w = U dot(w) U_(w^(-1))^- T$, and consider
  $(op("Ad") g) A'$. We have $(op("Ad") T) A' = A'$,
  $(op("Ad") U_(w^(-1))^-) A' = A' + frak(n)_(w^(-1))^-$, where
  $frak(n)_(w^(-1))^-$ is the Lie algebra of $U_(w^(-1))^-$. Then
  $(op("Ad") U)(op("Ad") dot(w))(A' + frak(n)_(w^(-1))^-)
  = (op("Ad") U)((op("Ad") dot(w)) A'
    + (op("Ad") dot(w)) frak(n)_(w^(-1))^-)$. Since
  $(op("Ad") U)(op("Ad") dot(w)) A' in
  frak(t) ⊕ frak(n)$, and $frak(t) ⊕ frak(n)$ is orthogonal to $frak(n)$ in the
  invariant bilinear form we see that we have to consider functionals induced on
  $frak(n)$ (via the invariant bilinear form) by elements of
  $(op("Ad") U)(op("Ad") dot(w)) frak(n)_(w^(-1))^- subset frak(g)$. Now
  $frak(n) = frak(n)_(w^(-1))^- ⊕ frak(n)_(w^(-1))$, where $frak(n)_(w^(-1))$ is
  the Lie algebra of $U_(w^(-1)) = U ∩ dot(w)^(-1) U dot(w)$. So the linear
  functionals induced on $frak(n)$ by $(op("Ad") dot(w)) frak(n)_(w^(-1))^-$ are
  precisely those linear functionals on $frak(n)$ which vanish on
  $(op("Ad") dot(w)) frak(n)_(w^(-1)) subset frak(n)$, since the invariant
  bilinear form is $(op("Ad") G)$-invariant. So we have to consider the variety
  $union_(w in W) X_w$, where $X_w = {(mu, u) in frak(n)' times U |
    mu | (op("Ad") dot(w)) frak(n)_(w^(-1)) = 0,
    (op("Ad") u) mu | frak(h) = lambda}$.
  <passage:kazhdan-bruhat-reduction>

  We can now describe our situation as follows. Suppose we have two subalgebras
  $frak(l), frak(h)$ of $frak(n)$ and corresponding subgroups $L = exp frak(l)$,
  $H = exp frak(h)$ of $U$. Consider then the variety
  $Z subset frak(n)' times U$ defined by
  $
    Z & = {(mu, u) | mu | frak(l) = 0,
          (op("Ad") u) mu | frak(h) = lambda} \
      & = {(mu, u) | mu in frak(l)^perp ∩
          (op("Ad") u)^(-1)(frak(h)^perp + lambda)}.
  $
  Consider the action of $H times L$ on $U$ given by $(h, l) u = h^(-1) u l$. By
  a result of Rosenlicht @bib:Rosenlicht1963 a quotient variety exists #source(
    131,
  ) on an open set of $U$. Applying induction on the dimension to the complement
  we see that there is a partition of $U$ into a finite number of locally closed
  subsets $U_i$ such that the quotient space $Y_i$ of $U_i$ with respect to the
  action of $H times L$ exists. Let $Z_i = Z ∩ (frak(n)' times U_i)$ and let
  $f: Z_i arrow.r Y_i$ be given by $f(mu, u) = phi(u)$, where $phi$ is the
  quotient morphism $U_i arrow.r Y_i$.

  Consider the fibres of $f$. We show that these fibres are either empty or
  isomorphic to affine space of dimension $d$ ($= dim U$). Let $y in Y_i$,
  $u in phi^(-1)(y)$. Then $phi^(-1)(y)$, which is the double coset $H u L$, is
  isomorphic to the quotient space of $H times (u L)$ by $u L u^(-1) ∩ H$. Since
  a quotient space of a unipotent group is isomorphic to affine space
  (@bib:Demazure1970, p. 535) we see that $phi^(-1)(y)$ is isomorphic to affine
  space of dimension $ell + h - m$ where $ell = dim L$, $h = dim H$,
  $m = dim(u L u^(-1) ∩ H)$. Let
  $Psi = frak(l)^perp ∩ (op("Ad") u)^(-1)(frak(h)^perp + lambda)$. If $Psi$ is
  non-empty it is isomorphic to affine space of dimension
  $(d - ell) + (d - h) - (d - m) = d + m - ell - h$. Choose a regular section of
  $H times L arrow.r H u L$ and use its representatives $h, l$ to set up a map
  $alpha: Psi times phi^(-1)(y) arrow.r f^(-1)(y)$ as follows:
  $alpha(mu, h u l) = ((op("Ad") l^(-1)) mu, h u l)$
  ($h in H$, $l in L$). Then $alpha(mu, h u l) in Z_i$, since
  $mu in frak(l)^perp$ implies that $(op("Ad") l^(-1)) mu in frak(l)^perp$, and
  $(op("Ad") h u l)(op("Ad") l^(-1)) mu
  = (op("Ad") h)(op("Ad") u) mu in frak(h)^perp + lambda$
  since $frak(h)^perp + lambda$ is $op("Ad") H$-invariant. We can check that
  $alpha$ is an isomorphism of $Psi times phi^(-1)(y)$ onto $f^(-1)(y)$. Thus
  $f^(-1)(y)$, if non-empty, is isomorphic to affine space of dimension $d$.
  <passage:kazhdan-affine-fibre>
  #ed-note[
    The representatives $h, l$ must come from a regular section; the displayed
    map otherwise depends on their choice. Under the exponential hypotheses the
    stabilizer is connected split unipotent. Its torsor over the affine space
    $H u L$ is trivial: use a series with additive quotients and the vanishing
    of additive torsors on an affine scheme. See #cite(
      <MilneGroups2017>,
      form: "full",
    ), Example 2.72, p. 61; 14.63 and 14.66, p. 299.
  ]

  Our original variety $X$ is then isomorphic over $K$ to a variety which is the
  disjoint union of locally closed subvarieties which are like the variety $Z$
  considered above. Thus @th:kazhdan-unipotent-character will follow from the
  following proposition.
]

#source(132)
#proposition(title: [@bib:Kazhdan1977, Proposition 3])[
  Let $X_0$ be a scheme over $FF_q$, and suppose
  $X = X_0 times_(FF_q) op("Spec") K$. Suppose $X$ is the disjoint union of
  locally closed subschemes $X_i$ such that for each $i$ there is a morphism
  $f_i: X_i arrow.r Y_i$ whose fibres are either empty or isomorphic to $AA^d$.
  Then $|X^F|$ is divisible by $q^d$.
] <prop:affine-fibre-divisibility>

#proof[
  It is sufficient to show, by the Trace Formula @th:grothendieck-trace-formula
  and the additivity property @eq:lefschetz-additivity that the eigenvalues of
  $F$ on each $H_c^(j)(X_i)$ are divisible by $q^d$. (We note that the schemes
  $X_i$, and the morphisms $f_i$ may not be defined over $FF_q$. But they are
  defined over some finite extension $FF_(q^n)$ of $FF_q$, and since the
  corresponding result about $F^n$ would imply the result we want, we may as
  well assume that they are defined over $FF_q$.)

  By the Leray spectral sequence @eq:cohomology-leray-single-degree, since the
  fibres of $f_i$ are isomorphic to $AA^d$, we get
  $H_c^(j)(Y_i, R^(2d) f_(i!) overline(QQ)_ell)
  tilde.eq H_c^(j + 2d)(X_i)$, and by @cor:cohomology-geometric-fibre the stalks
  of $R^(2d) f_(i!) overline(QQ)_ell$ at any geometric point of $Y_i$ centred at
  a closed point are isomorphic to $overline(QQ)_(ell)(-d)$. Since $F$ acts on
  $overline(QQ)_(ell)(-d)$ as multiplication by $q^d$, the proposition, and
  hence @th:kazhdan-unipotent-character, follows from
  @cor:cohomology-frobenius-divisibility.
]

#remark[
  Deligne gives a proof of this proposition in a special case in
  @bib:Deligne1977, p. 175, as an application of cohomological methods.
]

We now denote the function $Phi = epsilon_G epsilon_T Q_(T, frak(g)) ln$ on
$V^F$ by $Phi_T^G$. Thus we have a class function on the set of unipotent
elements of $G^F$ which is a character of $U^F$ and we now extend it to a
#source(133) class function on all of $G^F$, bringing into play the characters
of $T^F$. Let $g in G^F$ and let $g = s u$ be its Jordan decomposition. Let
$theta in hat(T^F)$. We define the function $X_(G, T, theta)$ on $G^F$ as
follows.

#definition[
  $X_(G, T, theta)(g) = 0$ if $s$ is not conjugate to any element of $T^F$.
  Otherwise,
  $
    X_(G, T, theta)(g) = epsilon_G epsilon_(C^(0)(s))
    frac(1, |C^(0)(s)^F|) sum_(x in G^F, x s x^(-1) in T^F)
    Phi_(x^(-1) T x)^(C^(0)(s))(u) theta(x s x^(-1)).
  $
]

_Remarks._

+ $X_(G, T, theta)(g)$ is an algebraic integer, for the term
  $frac(1, |C^(0)(s)^F|)$ will not appear if we sum only over representatives of
  conjugacy classes of tori in $C^(0)(s)$.
+ It turns out in the end that $Phi_T^G$ is (up to sign) equal to $Q_T^G$ and
  $X_(G, T, theta)$ is the trace of $epsilon_G epsilon_T R_T^(G)(theta)$.

It is our aim to show that $X_(G, T, theta)$ is a virtual (generalized)
character of $G^F$.

#definition[
  $cal(H)$ is the set of connected reductive $F$-stable subgroups $H$ of $G$
  such that $H$ is the connected centralizer of some subset of $T$.
]

#definition[
  Define the Möbius function $mu$ on $cal(H)$ recursively by (i) $mu(G) = 1$;
  (ii) If $C in cal(H)$, $C != G$, $sum_(C' in cal(H), C' supset C) mu(C') = 0$.
]

#definition[
  $
    kappa_T^(G)(theta) = sum_(H in cal(H)) epsilon_H mu(H)
    op("Ind")_(H^F)^(G^F)(X_(H, T, theta)).
  $
]

Using the formula for $X_(H, T, theta)$ and properties of the Möbius function we
can prove the following proposition. The proof is #source(134) omitted.

#proposition(title: [@bib:Kazhdan1977, Proposition 4])[
  The function $kappa_T^(G)(theta)$ has its support on $Z(G^F) times V^F$. In
  fact, we have
  $
    (kappa_T^(G)(theta))(s u) = cases(
      theta(s) (kappa_T^(G)(theta))(u) & "if" s in Z(G^F),
      0 & "otherwise".
    )
  $
  <eq:kazhdan-central-support>
] <prop:kazhdan-central-support>

#remark[
  Class functions on finite groups which are alternating sums of induced
  characters appear, for example, in the work of Dade (see @bib:Feit1967, 33.8).
]

Next we state, also without proof, the following proposition. The main step in
this proposition (@bib:Kazhdan1977, Proposition 6) relies essentially on a
counting argument in the Tits building of $G^F$.

#proposition(title: [@bib:Kazhdan1977, Proposition 5])[
  For every unipotent element $u$,
  $frac(|Z(G^F)| kappa_T^(G)(theta)(u), |C(u)^F|_(p'))$ lies in the ring
  $ZZ[q^(-1)]$.
] <prop:kazhdan-centralizer-integrality>

#example[
  Consider the characters of $GL(2, q)$ given in @ch:principal-series. If
  $theta = theta_(m, n)$, a character of the split torus $T_0^F$, we have
  $kappa_(T_0)^(G)(theta) = op("Ind")_(T_0^F)^(G^F)(theta)
  - phi_(m, n)$ and takes the values $q^2 - 1$ and $-1$ at $1$ and
  $mat(1, 1; 0, 1)$ respectively. A less trivial example is given by
  $G^F = GL(3, q)$,
  $T_0^F = {mat(gamma^a, 0, 0; 0, gamma^b, 0; 0, 0, gamma^c)}$
  where $gamma$ as before is a generator of $FF_q^*$. We define the following
  subgroups in $cal(H)$:

  #source(135)
  $
    H_1 = T_0, quad
    H_2 = C_(G)(mat(gamma, 0, 0; 0, gamma, 0; 0, 0, 1)), quad
    H_3 = C_(G)(mat(1, 0, 0; 0, gamma, 0; 0, 0, gamma)),
  $
  $
    H_4 = C_(G)(mat(gamma, 0, 0; 0, 1, 0; 0, 0, gamma)),
    quad H_5 = G.
  $
  Let $theta in hat(T_0^F)$. Then it turns out that
  $
    kappa_(T_0)^(G)(theta) & = 2 op("Ind")_(T_0^F)^(G^F)(theta)
                             - op("Ind")_(H_2^F)^(G^F)(R_(T_0)^(H_2)(theta)) \
                           & quad - op("Ind")_(H_3^F)^(G^F)
                             (R_(T_0)^(H_3)(theta))
                             - op("Ind")_(H_4^F)^(G^F)(R_(T_0)^(H_4)(theta))
                             + R_(T_0)^(G)(theta).
  $
  It can be checked that
  $dim kappa_(T_0)^(G)(theta) = (q^2 - 1)(q^3 - 1)(2q + 1)$, whereas
  $|G^F|_(p') = (q - 1)(q^2 - 1)(q^3 - 1)$.
]

We now prove the main theorem.
#term-entry("Kazhdan's Theorem")

#theorem(title: [@bib:Kazhdan1977, p. 278])[
  The class function $X_(G, T, theta)$ on $G^F$ is a virtual (i.e., generalized)
  character of $G^F$.
] <th:kazhdan-generalized-character>

#proof[
  By induction on the semisimple rank of $G$ we can assume that
  $X_(H, T, theta)$ is a virtual character of $H^F$ for any $H in cal(H)$,
  $H != G$. Thus it is sufficient to show that $kappa_T^(G)(theta)$ is a virtual
  character of $G^F$. By @prop:kazhdan-central-support $kappa_T^(G)(theta)$ has
  its support on $Z(G^F) V^F$. By Brauer's characterization of characters (see
  @bib:Feit1967, 15.3; @bib:Serre1977a, p. 82, or @bib:Curtis1962, 40.8) it is
  sufficient to show that $kappa_T^(G)(theta)$ is a virtual character on
  subgroups of the form $S times R$ where $S, R$ are subgroups of $G^F$
  consisting of semisimple elements and unipotent elements respectively. We can
  assume that $Z = Z(G^F) subset S$. Then the support of $kappa_T^(G)(theta)$ on
  $S R$ is contained in $Z R$. So the restriction of $kappa_T^(G)(theta)$ to
  $S R$ is $frac(|Z|, |S|) op("Ind")_(Z R)^(S R)(kappa_T^(G)(theta))$.

  #source(136)
  By @th:kazhdan-unipotent-character, and the definition of
  $kappa_T^(G)(theta)$, $kappa_T^(G)(theta)$ is a virtual character on $R$. Then
  @prop:kazhdan-centralizer-integrality shows that $|Z| (kappa_T^(G)(theta)(u))$
  is an integer and that it is divisible by $|C(u)^F|_(p')$. Thus
  $frac(|Z| (kappa_T^(G)(theta)(u)), |S|)$ is an integer. Now for any finite
  group $Q$, if $O$ is the ring of integers in an algebraic number field which
  is a splitting field for $Q$, and $f$ is an $O$-valued class function on $Q$,
  then $|Q| f$ belongs to the ring of virtual characters of $Q$ with
  coefficients in $O$ (see e.g., @bib:Serre1977a, Theorem 23′) and thus the
  quotient of the $O$-module of $O$-valued class functions on $Q$ by the
  $O$-module of virtual characters of $Q$ with coefficients in $O$ is
  annihilated by $|Q|$. Put $f = frac(|Z|, |S|) kappa_T^(G)(theta)$ on $R$. Both
  $|R| f$ and $|S| f$ lie in the $O$-character module. Since $|R|$ and $|S|$ are
  coprime, Bézout's identity shows that $f$ does also. Its character
  coefficients are rational and algebraic integers, hence integers. Thus $f$ is
  a virtual character on $R$, and $theta(s) f(u)$ is a virtual character on
  $Z R$ (using @eq:kazhdan-central-support). Thus the restriction of
  $kappa_T^(G)(theta)$ to $S R$ is a virtual character and this proves the
  theorem.
  <passage:kazhdan-brauer-integrality>
]

Finally we show (@bib:Kazhdan1977, Theorem 3) that the functions
$X_(G, T, theta)$ and $op("Tr")(epsilon_T epsilon_G R_T^(G)(theta))$ on $G^F$
coincide. We can make an induction assumption that $X_(G, T, theta)$ and
$epsilon_T epsilon_G op("Tr")(R_T^(G)(theta))$ coincide on subgroups of the form
$C^(0)(s)^F$ where $s in.not Z$. Thus
$X_(G, T, theta) - epsilon_G epsilon_T op("Tr")(R_T^(G)(theta))$ has its support
on $Z V^F$, and furthermore
$X_(G, T, theta)(s u)
- epsilon_G epsilon_T op("Tr")(s u, R_T^G theta)
= theta(s)(Phi_T^(G)(u) - epsilon_G epsilon_T Q_T^(G)(u))$
($s in Z$, $u in V^F$). Hence we have
$
  frac(1, |G^F|) sum_(s in Z, u in V^F)
  |X_(G, T, theta)(s u)
  - epsilon_G epsilon_T op("Tr")(s u, R_T^(G)(theta))|^2
$

#source(137)
$
  = frac(|Z|, |G^F|) sum_u
  |Phi_T^(G)(u) - epsilon_G epsilon_T Q_T^(G)(u)|^2
  <= 4 frac(|Z| |W(T)^F|, |T^F|),
$
using @eq:lie-green-orthogonality and @eq:green-function-orthogonality. But the
left hand side is an integer since
$X_(G, T, theta) - epsilon_G epsilon_T op("Tr")(R_T^(G)(theta))$ is a virtual
character of $G^F$. By our assumption on $p$ being large, the left hand side
must then be zero. (See @th:torus-order, which describes how $|T^F|$ can be
computed; $|W(T)^F|$ is independent of $q$.)

_Remarks._

+ Kazhdan's theorem can be interpreted, for large $p$, as providing an
  alternative approach to the work of Lusztig–Deligne at the level of characters
  by constructing families of virtual characters corresponding to tori of $G^F$.
  We note, however, that étale cohomology is used here also in the proof of the
  crucial result @th:kazhdan-unipotent-character. We refer the reader to
  @bib:Lusztig1978, Remark 2.14, where the connection between the
  $kappa_T^(G)(theta)$ and the $R_T^(G)(theta)$ is made and $kappa_T^(G)(theta)$
  is interpreted as the alternating trace of $G^F$ on the cohomology of a
  certain variety.
+ There are certain results in the literature about the values of unipotent
  characters (these will be defined in @ch:classification-of-representations) at
  semisimple elements of $G^F$. See @bib:Curtis1974, @bib:Curtis1979, and the
  references given there.
