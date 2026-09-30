#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/06-connected-action.typ": *
#import "diagrams/06-torus-norm.typ": *

#chapter[The Construction of Lusztig–Deligne] <ch:lusztig-deligne>

#source(70)
References for this chapter are [@bib:Deligne1976], [@bib:Lusztig1978], and
[@bib:Serre1977b]. From now on $K$ will be an algebraic closure of $FF_q$.

We first recall the principal series representations of $G^F$
(Chapter~@ch:principal-series). The subgroups $T_0, B_0, U_0$ are as in
Chapters~@ch:classification-of-tori and~@ch:principal-series. If $lambda$ is a
complex character of $T_0^F$ which is lifted to a character $tilde(lambda)$ of
$B_0^F$, then $Ind_(B_0^F)^(G^F) tilde(lambda)$ is a character of $G^F$ which is
irreducible if $lambda$ is regular. We would now like to generalize this to the
case of any torus $T^F$. In other words, we would like to construct a family of
virtual representations (i.e., elements of the Grothendieck group) of $G^F$
parametrized by the characters of $T^F$ and having certain nice properties,
e.g., that a virtual representation is irreducible (up to sign) if it
corresponds to a regular character of $T^F$, and that the absolute value of the
virtual dimension of each is $abs(G^F) / (abs(T^F) abs(U_0^F))$, even though
$T^F$ may not be contained in any subgroup of order $abs(T^F) abs(U_0^F)$. The
construction of Lusztig–Deligne achieves exactly this.

Let us view the principal series representations as being constituents of
$Ind_(U_0^F)^(G^F) (1)$. Thus we can construct them by taking the space
$G^F / U_0^F$, and letting $T_0^F$ act on the right and $G^F$ on the left on
this space. We can decompose the space by means of the characters of $T_0^F$ and
each subspace corresponding to a fixed character of $T_0^F$ is $G^F$-stable.
Thus we get representations of $G^F$ indexed by the characters of $T_0^F$. Now
we #source(71) have $G^F / U_0^F tilde.eq (G / U_0)^F$ by
Lemma~@lem:fixed-points-quotient. Thus $G^F / U_0^F$ is isomorphic to the
subvariety of the variety $G / U_0$ given by
${g U_0 | g in G, g^(-1) (F g) in U_0}$.

Now suppose $T$ is any $F$-stable maximal torus. Let $B = T U$ where the Borel
subgroup $B$ (and hence $U$) is not necessarily $F$-stable. We define the _Lang
covering_#term-entry(
  "Lang covering L^-1(U)",
  target: <def:lang-covering>,
  display: [Lang covering
    $L^(-1) (U)$],
) $L^(-1) (U)$ of $U$ as follows.

#definition[
  $L^(-1) (U) = {g in G | g^(-1) (F g) in U}$.
] <def:lang-covering>

Then $L^(-1) (U)$ is a closed subset of $G$ and hence is an affine variety. We
see that $G^F times T^F$ acts on $L^(-1) (U)$ by $(g, t) h = g h t$ ($g in G^F$,
$t in T^F$, $h in L^(-1) (U)$). Now in order to exploit this and get a linear
representation of $G^F times T^F$ in characteristic $0$ we go over to the
$ell$-adic cohomology of $L^(-1) (U)$. _Let $ell$ be a prime different from
$p$._ By functoriality we get an action of $G^F times T^F$ on the cohomology
groups $H_C^(i)(L^(-1) (U), overline(QQ)_ell)$. From now on we let $hat(T)^F$
denote the group of characters $Hom(T^F, overline(QQ)_ell^*)$. For any
$theta in hat(T)^F$, and any $T^F$-module $M$ over $overline(QQ)_ell$, let
$M_theta$ denote the $theta$-isotypic part of $M$. We see that the subspace
$H_C^(i)(L^(-1) (U), overline(QQ)_ell)_theta$ of
$H_C^(i)(L^(-1) (U), overline(QQ)_ell)$ is $G^F$-stable.

#definition[
  $R_T^(G)(theta)$ is the virtual representation
  $sum_(i >= 0) (-1)^i H_C^(i)(L^(-1) (U), overline(QQ)_ell)_theta$ of $G^F$.
] <def:lusztig-deligne-representation>
#term-entry(
  "Lusztig-Deligne virtual representation R_T^(G)(θ)",
  target: <def:lusztig-deligne-representation>,
  display: [Lusztig–Deligne virtual representation $R_T^(G)(theta)$],
)

Thus we have a map $theta |-> R_T^(G)(theta)$ from $hat(T)^F$ into the
Grothendieck group $cal(R) (G^F)$ of $G^F$. It will be shown later
(@cor:independence-unipotent-choice) that $R_T^(G)(theta)$ depends only on $T$
and not on the choice of $U$, and so #source(72) we are justified in omitting
$U$ from the notation. We will also denote the variety $L^(-1) (U)$ by
$tilde(X)$.

#example[
  (See [@bib:Lusztig1978], p.~17.) $G = SL_2$, $G^F = SL(2, q)$. Let $T^F$ be a
  “non-split” torus of $G^F$ of order $q + 1$ (see
  Chapter~@ch:classification-of-tori for the case of $GL_2$). Then $T^F$ is
  isomorphic to the group of elements of norm $1$ in $FF_(q^2)^*$. It can be
  checked that $tilde(X) = L^(-1) (U)$ is the affine curve $x y^q - y x^q = 1$
  on which $G^F$ acts according to its natural action on $(x, y) in K^2$ and
  $T^F$ acts as $lambda(x, y) = (lambda x, lambda y)$ ($lambda in FF_(q^2)^*$,
  $lambda^(q + 1) = 1$). Then $H_C^(0)(tilde(X), overline(QQ)_ell) = 0$,
  $dim H_C^(2)(tilde(X), overline(QQ)_ell) = 1$, and $T^F$ acts trivially on
  this space. If $theta in hat(T)^F$ is not trivial, then $-R_T^(G)(theta)$ is
  realized as the $theta$-isotypic component of
  $H_C^(1)(tilde(X), overline(QQ)_ell)$. If $theta^2 != 1$, $-R_T^(G)(theta)$ is
  irreducible of dimension $q - 1$ and this is the family of discrete series
  representations. Let $theta^2 = 1$, $theta != 1$. The $theta$-component in
  $H_C^(1)(tilde(X), overline(QQ)_ell)$ then splits into two representations of
  $G^F$ of dimension $1 / 2 (q - 1)$.

  We briefly sketch how the dimensions of the cohomology groups can be computed.
  We embed the affine curve $A$ defined by $x y^q - y x^q = 1$ in the
  non-singular projective curve $C$ given by $x y^q - y x^q - z^(q + 1) = 0$ in
  the projective space $PP^2$ over $K$. $A$ is the open subset of $C$ given by
  $z != 0$. We use the long exact sequence
  @eq:cohomology-open-closed-exact-sequence with respect to $C$, $A$, and
  $C - A$.

  By a vanishing theorem for cohomology of affine schemes [@bib:Deligne1977],
  p.~51 we see that $H_C^(0)(A, overline(QQ)_ell) = 0$. Since $C$ is a #source(
    73,
  ) projective non-singular curve, we get
  $dim H_C^(0)(C, overline(QQ)_ell) = dim H_C^(2)(C, overline(QQ)_ell) = 1$
  and $dim H_C^(1)(C, overline(QQ)_ell) = 2 g$ where $g$ is the genus of $C$
  (see [@bib:Deligne1977], p.~35), and in this case $g = q (q - 1) / 2$. [The
  groups given there are the $H^(i)(C, QQ_ell)$. To get the
  $H_C^(i)(C, overline(QQ)_ell)$, we use duality; see [@bib:Deligne1977],
  p.~71.] From these facts and the fact that
  $dim H_C^(0)(C - A, overline(QQ)_ell) = q + 1$,
  $dim H_C^(i)(C - A, overline(QQ)_ell) = 0$ ($i = 1, 2$), we get that
  $dim H_C^(1)(A, overline(QQ)_ell) = q^2$ and
  $dim H_C^(2)(A, overline(QQ)_ell) = 1$.

  We also remark (see loc. cit.) that the two representations of dimension
  $1 / 2 (q - 1)$ (the so-called Hecke representations of $SL(2, q)$) can be
  realized in $H_C^(1)(C, overline(QQ)_ell)$ where $C$ is the hyperelliptic
  curve $y^2 = x^q - x$, on which $SL(2, q)$ acts. Allan Adler has pointed out
  to me that this is a curve which in characteristic $p$ provides a
  counterexample to the theorem of Hurwitz that a curve of genus $g >= 2$ over a
  field of characteristic $0$ has at most $84 (g - 1)$ automorphisms (see
  [@bib:Hartshorne1977], p.~306).

  For other examples in classical groups, see [@bib:Deligne1976], p.~116. The
  variety $tilde(X) (w)$ mentioned there is a quotient of our variety
  $tilde(X)$, if our torus $T$ corresponds to $w in W(T_0)$ in the sense of
  Chapter~@ch:classification-of-tori, @cor:rational-tori. The cohomology of
  $tilde(X) (w)$ is the same as that of our $tilde(X)$.
] <exm:sl-two-lusztig-deligne-curve>

Before developing the main properties of the $R_T^(G)(theta)$ we discuss some
general results on schemes which have automorphisms of finite order, and on the
induced morphisms on cohomology. As in Chapter~@ch:ell-adic-cohomology, let $X$
be a scheme which is separated and of #source(74) finite type over $K$. Let $g$
be an automorphism of $X$ of finite order. We then have an action of $g$ on
$H_C^(i)(X, overline(QQ)_ell)$. From now on we will always denote
$H_C^(i)(X, overline(QQ)_ell)$ by simply $H_C^(i)(X)$ when there is no danger of
ambiguity. We now define the _Lefschetz number_ #term-entry(
  "Lefschetz number L(g,X)",
  target: <def:lefschetz-number>,
  display: [Lefschetz number $cal(L) (g, X)$],
) $cal(L) (g, X)$ of $g$ as the alternating trace of $g$ on the cohomology of
$X$.

#definition[
  $cal(L) (g, X) = sum_(i)(-1)^i tr(g, H_C^(i)(X))$.
] <def:lefschetz-number>

We have the following additivity property of the Lefschetz number.

#formula-item[
  Suppose $X$ is a finite disjoint union of locally closed subschemes
  $brace(X_i)$ which are stable under $g$. Then
  $cal(L) (g, X) = sum_i cal(L) (g, X_i)$. This can be proved using the Long
  Exact Sequence @eq:cohomology-open-closed-exact-sequence.
] <eq:lefschetz-additivity>

We remark that $X$ can be written as a finite disjoint union of locally closed
quasiprojective schemes which are stable under $g$. (This follows from the fact
that $X$ is of finite type and $g$ is of finite order.)

#proposition(title: [[@bib:Deligne1976], 3.3; [@bib:Serre1977b], Proposition
  1])[
  $cal(L) (g, X)$ is an integer which is independent of $ell$.
] <prop:lefschetz-integral-independent-ell>

#proof[
  By @eq:lefschetz-additivity and the above remark we can assume that $X$ is
  quasiprojective. We can also assume that $X$ and $g$ are defined over $FF_q$
  for some $q$, and that $F: X -> X$ is the associated Frobenius morphism. Then
  by (@prop:twisted-frobenius) we have that $F^n g$ is also a Frobenius morphism
  for some way of defining $X$ over $FF_(q^n)$. By the trace formula
  (@th:grothendieck-trace-formula) we then have
  $cal(L) (F^n g, X) = abs(X^(F^n g))$. Thus
  $abs(X^(F^n g)) = sum_lambda a_lambda lambda^n$ where $a_lambda$ is the
  alternating trace of $g$ #source(75) on the generalized $lambda$-eigenspace of
  $F$ on $⨁_i H_C^(i)(X)$ and $lambda$ runs over the eigenvalues of $F$ on
  $⨁_i H_C^(i)(X)$. Thus $sum_lambda a_lambda lambda^n$ is an integer which is
  independent of $ell$.

  Now the functions $n |-> lambda^n$ from $ZZ^+ -> overline(QQ)_ell^*$ are
  linearly independent; this can be seen, for example, by extending them to
  characters of $ZZ$, and using Dedekind's theorem. Let
  $sigma in G(overline(QQ)_ell, QQ)$. Then
  $sigma(sum_lambda a_lambda lambda^n) = sum_lambda a_lambda lambda^n$. On the
  other hand, $sum_lambda sigma(a_lambda) sigma(lambda)^n =
  sum_lambda sigma(a_(sigma^(-1) (lambda))) lambda^n$, and thus
  $sigma^(-1) (a_lambda) = a_(sigma^(-1) (lambda))$ for any $sigma$. Thus
  $sum_lambda a_lambda in QQ$, but this is just $cal(L) (g, X)$. But
  $cal(L) (g, X)$ is a character value of the finite group $⟨g⟩$ and so it is an
  algebraic integer. Thus $cal(L) (g, X)$ is an integer.

  To show that $cal(L) (g, X)$ does not depend on $ell$, let us denote for the
  moment by $cal(L) (g, X)_ell$ the alternating trace of $g$ on
  $⨁_i H_C^(i)(X, overline(QQ)_ell)$. Let $ell'$ be another prime ($!= p$) and
  let $tau: overline(QQ)_ell -> overline(QQ)_(ell')$ be an isomorphism. The same
  argument as above shows that $tau(cal(L) (g, X)_ell) = cal(L) (g, X)_(ell')$,
  and this proves the result.
]

We now state an important theorem, one of the central theorems in the work of
Lusztig–Deligne ([@bib:Deligne1976], Theorem 3.2). We will give the main ideas
of the proof but some of the details will be omitted.

#theorem[
  Suppose the automorphism $g$ of finite order of the scheme $X$ can be written
  as $g = s u = u s$ where $u$ is of order a power of $p$ and $s$ is of order
  prime to $p$. Then $cal(L) (g, X) = cal(L) (u, X^s)$, where $X^s$ is the
  subscheme of $X$ of fixed points of $s$.
] <th:lefschetz-jordan-decomposition>

#source(76)
#proof(head: [_Sketch of proof._])[
  As in (@prop:lefschetz-integral-independent-ell) we can assume that $X$ is
  quasiprojective. Furthermore we can assume that the cyclic group $⟨g⟩$ acts
  freely on $X$. (For we can write $X$ as a disjoint union of subschemes $X_i$
  where each element of $X_i$ has the same stabilizer $H_i$. The quotient group
  $⟨g⟩ / H_i$ acts freely on $X_i$; on each stratum we replace $g$ by its image
  in this quotient.)

  Now suppose that $g$ is a $p$-element. Then $s = 1$, $u = g$ and there is
  nothing to prove. So we can assume that the order of $g$ is divisible by some
  prime different from $p$, and since $cal(L) (g, X)$ is independent of $ell$ we
  can assume that this prime is $ell$. Since $s$ has no fixed points on $X$ we
  have to show that $cal(L) (g, X) = 0$. Thus the theorem will follow from the
  following proposition.

  #formula-item[
    If $H$ is a finite group acting freely on $X$, the function
    $h |-> cal(L) (h, X)$ ($h in H$) is the character of a virtual projective
    $ZZ_ell[H]$-module.
  ] <eq:free-action-projective-character>

  The theorem then follows from @eq:free-action-projective-character since it is
  well-known that the character of the representation of $H$ on a projective
  $ZZ_ell[H]$-module vanishes on elements of order divisible by $ell$ (see e.g.,
  [@bib:Serre1977a], p.~133).

  We sketch a proof of @eq:free-action-projective-character. Let $pi: X -> Y$ be
  the natural map, where $Y = X / H$. (Since $X$ is quasiprojective, the
  quotient exists.) Since the fibres of $pi$ are finite, by
  @eq:cohomology-leray-single-degree we have
  $H_C^(i)(X, ZZ / (ell^n ZZ)) tilde.eq H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$. Let
  $A = (ZZ / (ell^n ZZ))[H]$ so that $A$ is a noetherian ring. An argument
  similar to that of @eq:cohomology-finite-quotient #source(77) shows that
  $pi ! ZZ / (ell^n ZZ)$ is a sheaf of free $A$-modules of rank $1$ on $Y$.
  However, the difficulty now is that $H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$ need
  not be free or projective $A$-modules. Thus it does not make sense to talk of
  the trace of an element of $H$ on the $H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$.
  However, since $A$ is noetherian, they are finitely generated $A$-modules and
  they vanish unless $0 <= i <= 2 dim Y$ (see [@bib:Artin1972], XVII, 5.2.8.1
  for the vanishing and 5.3.6 for the finiteness).

  We can compute the $H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$ by taking a suitable
  resolution of $j ! pi ! ZZ / (ell^n ZZ)$ on a proper compactification
  $j: Y -> overline(Y)$. We could take the Godement resolution by a complex
  $cal(T): cal(T)^0 -> cal(T)^1 -> cal(T)^2 -> dots$ of flasque sheaves (see
  [@bib:Godement1958], p.~167 for the classical case and [@bib:Artin1972], XVII,
  4.2 for the étale case). This is defined by taking, for any étale
  $U -> overline(Y)$,
  $cal(T)^(0)(U) = product (j ! pi ! ZZ / (ell^n ZZ))_(overline(x))$ where the
  product is over geometric points $overline(x)$ of $U$. Then we proceed
  analogously to construct $cal(T)^1, cal(T)^2, dots$ and so on. Taking global
  sections on $overline(Y)$ gives $dot(C): C^0 -> C^1 -> C^2 -> dots$, a complex
  of $A$-modules which are flat $A$-modules in our case, since each stalk is a
  free $A$-module or zero and the direct product of flat $A$-modules is flat if
  $A$ is noetherian (see e.g., [@bib:Faith1973], pp.~439, 440). The cohomology
  groups of the complex $C^0 -> C^1 -> C^2 -> dots$ are the groups
  $H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$. The $A$-modules $C^i$ need not be finitely
  generated; however, we can replace $dot(C)$ by another complex with the same
  cohomology such that the terms of the complex are finitely generated flat
  $A$-modules. The projection formula and the cohomological-dimension bound give
  Tor amplitude $[0, 2 dim Y]$, so we may first replace $dot(C)$ by a bounded
  flat complex in those degrees. We then apply the following lemma. A proof of
  this lemma is given in [@bib:Mumford1970], p.~47 (see also
  [@bib:Hartshorne1977], p.~283).

  #source(78)
  #lemma(numbered: false)[
    Let $A$ be a noetherian ring. Let $dot(C)$ be a complex of $A$-modules such
    that the $H^(i)(dot(C))$ are finitely generated $A$-modules and such that
    $C^p != 0$ only if $0 <= p <= m$. Then there is a complex $dot(K)$ of
    finitely generated $A$-modules such that $K^p != 0$ only if $0 <= p <= m$
    and $K^p$ is free if $1 <= p <= m$, and a homomorphism of complexes
    $phi: dot(K) -> dot(C)$ such that $phi$ induces isomorphisms
    $H^(i)(dot(K)) -> H^(i)(dot(C))$ for all $i$. Moreover, if the $C^i$ are
    $A$-flat, then $K^0$ is also $A$-flat.
  ] <lem:finite-flat-cohomology-complex>

  Applying this to our situation we find that the
  $H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$ are the cohomology groups of a complex
  $dot(K)_n$ such that (i) $K_n^p$ are finitely generated $A$-modules which are
  zero unless $0 <= p <= 2 dim Y$ (ii) $K_n^p$ is free if $p >= 1$ (iii) $K_n^0$
  is $A$-flat and finitely generated, hence projective.#ed-note[
    Compact support is computed on a proper compactification using extension by
    zero. The bounded replacement also requires finite Tor amplitude; cohomology
    vanishing alone is insufficient. See #cite(<Milne1980>, form: "full"), VI,
    Proposition 8.15 and Theorem 13.13.
  ]

  We need one more fact, namely that once the complex $dot(K)_n$ is chosen, we
  can choose $dot(K)_(n + 1)$ in such a way that $dot(K)_n$ is the reduction mod
  $ell^n$ of $dot(K)_(n + 1)$. We omit the proof of this. (See
  [@bib:Deligne1977], p.~97, 4.12, and [@bib:Grothendieck1977], XV, p.~473.)
  Then, taking projective limits we get a complex $dot(K)_infinity$ of
  projective $ZZ_ell[H]$-modules such that
  $lim_(<- n) H_C^(i)(Y, pi ! ZZ / (ell^n ZZ)) = H^(i)(dot(K)_infinity)$, and
  thus $H_C^(i)(X, ZZ_ell) tilde.eq H^(i)(dot(K)_infinity)$ since
  $H_C^(i)(X, ZZ / (ell^n ZZ)) tilde.eq H_C^(i)(Y, pi ! ZZ / (ell^n ZZ))$ for
  each $n$. Moreover, this isomorphism is $H$-equivariant.

  Let $h in H$. We now see that $cal(L) (h, X)$, the alternating trace of $h$ on
  $⨁_i H_C^(i)(X, QQ_ell)$, is equal to the alternating trace of $h$ on
  $dot(K)_infinity$, a complex of projective $ZZ_ell[H]$-modules. This proves
  @eq:free-action-projective-character and hence
  Theorem~@th:lefschetz-jordan-decomposition.
]

#source(79)
#remark[
  The proof in [@bib:Deligne1976], Theorem 3.2 uses the language of derived
  categories, which we have avoided in order not to introduce too much
  machinery. However, it may be worthwhile making a few remarks about them as
  they are a valuable tool in the theory; for example, Deligne's proof of the
  Trace Formula in [@bib:Deligne1977] makes essential use of them. There, also,
  we run into the problem that certain cohomology groups are not free modules.

  Let $cal(A)$ be an abelian category. The derived category $D cal(A)$ is
  constructed in two steps: (i) Take the category whose objects are chain
  complexes of objects of $cal(A)$ and morphisms are homotopy classes of maps of
  chain complexes; (ii) “Invert” all quasi-isomorphisms (i.e., morphisms of
  complexes which induce isomorphisms of cohomology). This is done by the
  “Calculus of Fractions” and is roughly analogous to constructing a quotient
  ring of a ring with respect to a multiplicative subset.

  Thus $D cal(A)$ is the localization of the homotopy category of complexes of
  objects of $cal(A)$, such that a map $dot(C)_1 -> dot(C)_2$ of complexes which
  induces an isomorphism of cohomology, is an isomorphism in $D cal(A)$. If
  $F: cal(A) -> cal(B)$ is a left exact functor from an abelian category
  $cal(A)$ to another abelian category $cal(B)$ then the derived functor $R F$
  can be defined as a functor from $D cal(A)$ to $D cal(B)$. The use of derived
  categories makes it easier to talk of cohomology, derived functors, spectral
  sequences, etc. (See [@bib:Hartshorne1966]).
] <rem:derived-categories>

We now prove a theorem on trivial action of a connected #source(80) group on
cohomology, which will be used at several points in this and the next chapters.

#theorem(title: [[@bib:Deligne1976], Theorem 6.4])[
  Let $H$ be a connected algebraic group acting on a scheme $Y$, separated and
  of finite type over $K$. Then, if $h in H$, the action of $h$ on
  $H_C^(i)(Y, ZZ / (ell^n ZZ))$ (and hence on $H_C^(i)(Y, QQ_ell)$) is trivial.
] <th:connected-group-trivial-cohomology>

#proof[
  Let $f: H times Y -> H times Y$ be the morphism defined by
  $f(h, y) = (h, h y)$ ($h in H$, $y in Y$) and $pi$ the projection of
  $H times Y$ on $H$. We have the following commutative triangle.

  $ #connected-action-triangle() $

  We apply Base Change (@eq:cohomology-base-change and
  (@cor:cohomology-geometric-fibre)) to the commutative diagram

  $ #connected-action-base-change() $

  where the top arrow is projection. Then we see that
  $R^i pi ! (ZZ / (ell^n ZZ))$ is the constant sheaf
  $H_C^(i)(Y, ZZ / (ell^n ZZ))$ on $H$. Since $f$ preserves the fibres of $pi$
  we get an induced morphism, also denoted by $f$, of this constant sheaf on
  $H$. The action of $H$ on $Y$ gives rise to an action of $H$ on
  $H_C^(i)(Y, ZZ / (ell^n ZZ))$. Since $f(h, y) = (h, h y)$, $f$ acts on the
  stalk of the constant sheaf $H_C^(i)(Y, ZZ / (ell^n ZZ))$ at a geometric point
  centered at $h in H$ in exactly the same way as the action of $h$ on
  $H_C^(i)(Y, ZZ / (ell^n ZZ))$ #source(81) induced from the action of $h$ on
  $Y$. If $h = 1$, the action is trivial. We have a sheaf of endomorphisms of
  the constant sheaf $H_C^(i)(Y, ZZ / (ell^n ZZ))$ on the connected space $H$,
  and this itself is a constant sheaf. This means that the action of $f$ is
  trivial at all $h in H$, as required.
]

#remark(numbered: true)[
  We are looking at closed points $h$ of $H$ and $K$ is algebraically closed.
  Thus we can think of the fibre of $pi$ over a geometric point centered at $h$
  as just being isomorphic to $Y$; cf. the remark below our discussion of
  geometric points.
] <rem:closed-point-geometric-fibre>

We now return to the virtual representations $R_T^(G)(theta)$, corresponding to
an $F$-stable maximal torus $T$ of $G$ and $theta in hat(T)^F$, which are
realized on the cohomology of a scheme $tilde(X) = L^(-1) U$, where $T U$ is a
Borel subgroup of $G$. The rest of this chapter will be devoted to proving
various properties of the $R_T^(G)(theta)$. We first show that if $u in G^F$ is
unipotent, then $tr(u, R_T^(G)(theta))$ is independent of $theta$. For,

$
  tr(u, R_T^(G)(theta))
  &= 1 / abs(T^F) sum_(t in T^F) cal(L) ((u, t^(-1)), tilde(X)) theta(t) \
  &= 1 / abs(T^F) sum_t cal(L) (u, tilde(X)^t) theta(t),
  quad "from" #[@th:lefschetz-jordan-decomposition] \
  &= 1 / abs(T^F) cal(L) (u, tilde(X)),
  quad "since" t "acts"
$

fixed point freely on $tilde(X)$ if $t != 1$. By
(@prop:lefschetz-integral-independent-ell), $cal(L) (u, tilde(X))$ is an integer
and thus $tr(u, R_T^(G)(theta))$ is rational. Since it is an algebraic integer,
it is an integer independent of $theta$.

#source(82)
#definition(numbered: true)[
  $Q_T^(G)(u) = tr(u, R_T^(G)(1))$.
] <def:green-function>
#term-entry(
  "Green functions Q_T^G",
  display: [Green functions $Q_T^G$],
  target: <def:green-function>,
)

The function $Q_T^G$ on the unipotent elements of $G^F$ is called a _Green
function_, after Green [@bib:Green1955] who studied them in the case of $GL_n$.

We now prove an important character formula#term-entry(
  "Character formula",
  target: <th:lusztig-deligne-character-formula>,
) ([@bib:Deligne1976], 4.2). We first state some facts about centralizers of
semisimple elements in $G^F$ (see [@bib:Borel1970], E-35, E-38).

Let $s in G^F$, and let $s$ be semisimple. Then $C^(0)(s)$ is a connected
reductive group which is generated by a maximal torus $T$ such that $s in T$ and
all root subgroups $U_alpha$ with respect to $T$ such that $alpha(s) = 1$. (For
example, this follows from the Bruhat decomposition.) If $B = T U$ (where $U$ is
generated by the $U_alpha$ with $alpha$ positive), then $B ∩ C^(0)(s)$ is a
Borel subgroup of $C^(0)(s)$ with unipotent radical $U ∩ C^(0)(s)$. Any
unipotent element in $C(s)$ lies in $C^(0)(s)$.

#example[
  $G = GL_3$,

  $ s = mat(a, 0, 0; 0, a, 0; 0, 0, b), quad "where" a, b in FF_q^*, a != b. $

  Then $C(s) = C^(0)(s)$ and $C(s)$ is generated by the diagonal torus $T_0$ and
  the two root subgroups $U_alpha$ and $U_(-alpha)$, where

  $
    U_alpha = {mat(1, t, 0; 0, 1, 0; 0, 0, 1) | t in K},
    quad U_(-alpha) = U_alpha^top.
  $
] <exm:gl-three-semisimple-centralizer>

#theorem(title: [Character Formula])[
  Let $g in G^F$ and let $g = s u$ be the Jordan decomposition of $g$. Then
  #source(83)

  $
    tr(g, R_T^(G)(theta)) = 1 / abs(C^(0)(s)^F)
    sum_(x in G^F, x s x^(-1) in T^F)
    Q_(x^(-1) T x)^(C^(0)(s)) (u) theta(x s x^(-1)).
  $
  <eq:lusztig-deligne-character-formula>
] <th:lusztig-deligne-character-formula>

#proof[
  First we note that the formula on the right hand side makes sense since
  $x s x^(-1) in T^F$ implies $s in x^(-1) T x$ and thus
  $x^(-1) T x subset C^(0)(s)$; however, $T$ and $x^(-1) T x$ need not be
  conjugate in $C^(0)(s)$. Since $C^(0)(s)$ is a reductive group we can talk of
  a virtual representation $R_(x^(-1) T x)^(C^(0)(s)) (theta)$ (and hence a
  Green function $Q_(x^(-1) T x)^(C^(0)(s)))$ of $C^(0)(s)^F$.

  The left hand side of @eq:lusztig-deligne-character-formula is

  $
    1 / abs(T^F) sum_(t in T^F) cal(L) ((s u, t^(-1)), tilde(X)) theta(t)
    = 1 / abs(T^F) sum_(t in T^F)
    cal(L) (u, tilde(X)^((s, t^(-1)))) theta(t)
    quad "by" #[@th:lefschetz-jordan-decomposition].
  $

  Consider, for a fixed $t$, the scheme
  $tilde(X)^((s, t^(-1))) = {g' in G | g'^(-1) (F g') in U,
    s g' t^(-1) = g'}$. Let $g' in tilde(X)^((s, t^(-1)))$. Suppose
  $g'^(-1) (F g') = v$, so that $F g' = g' v$. Since $s g' t^(-1) = g'$ and
  $s, t in G^F$ we get $s(F g') t^(-1) = F g' = s(g' v) t^(-1) = g' t v t^(-1)$.
  Thus $g' v = g' t v t^(-1)$ and $v in C(t)$. Since $v in U$, $v in C^(0)(t)$.
  By Lang's Theorem (@th:lang) we can write $v = z^(-1) (F z)$ where
  $z in C^(0)(t)$. Now we see that $g' z^(-1) in G^F$, for
  $(F g') (F z)^(-1) = g' v (z v)^(-1) = g' z^(-1)$. Thus $g' = h z$ where
  $h in G^F$, $z in C^(0)(t)$.

  #source(84)
  Next we note that $h z = g' = s g' t^(-1) = s h z t^(-1) = s h t^(-1) z$ and
  thus $h = s h t^(-1)$. Now consider the map

  $
    {h in G^F | h^(-1) s h = t} times
    {z in C^(0)(t) | z^(-1) (F z) in U ∩ C^(0)(t)}
    -> tilde(X)^((s, t^(-1)))
  $

  given by $(h, z) |-> h z$.

  This map is surjective by the above remarks. Also, if $h_1 z_1 = h_2 z_2$ then
  $h_2^(-1) h_1 = z_2 z_1^(-1) in G^F ∩ C^(0)(t) = C^(0)(t)^F$. Hence if we
  factor out the product on the left hand side by the action of $C^(0)(t)^F$
  (which acts on the first factor on the right, and on the second factor, which
  we denote by $tilde(Y)_t$, on the left) we see that the map

  $
    {h in G^F | h^(-1) s h = t} times_(C^(0)(t)^F) tilde(Y)_t
    -> tilde(X)^((s, t^(-1)))
  $

  is a bijection. Thus we see that we have a partition of
  $tilde(X)^((s, t^(-1)))$ into a finite number of subschemes
  ${h} times tilde(Y)_t$, where, on ${h} times tilde(Y)_t$, $u$ acts as
  $h z |-> u h z = h (h^(-1) u h) z$. We also note that $tilde(Y)_t$ is
  analogous to $tilde(X)$, for the group $C^(0)(t)$. We then get

  $
    & cal(L) (u, tilde(X)^((s, t^(-1)))) \
    & = 1 / abs(C^(0)(t)^F) sum_(h in G^F, h^(-1) s h = t)
      cal(L) (h^(-1) u h, tilde(Y)_t)
      quad "(using" #[@eq:lefschetz-additivity] ")" \
    & = 1 / abs(C^(0)(t)^F) sum_(h in G^F, h^(-1) s h = t)
      abs(T^F) Q_T^(C^(0)(t)) (h^(-1) u h).
  $

  Thus the left hand side of @eq:lusztig-deligne-character-formula becomes
  #source(85)

  $
    1 / abs(C^(0)(s)^F)
    sum_(h in G^F, h^(-1) s h in T^F)
    Q_(h T h^(-1))^(C^(0)(s)) (u) theta(h^(-1) s h)
  $

  which is the right hand side of @eq:lusztig-deligne-character-formula. This
  proves the theorem.
]

#remark[
  This character formula enables us to express the value of the character of
  $R_T^(G)(theta)$ at $g$, in terms of functions on the semisimple elements and
  on the unipotent elements. It is not possible to compute the $Q_T^(G)(u)$
  explicitly from the definition of $R_T^(G)(theta)$ and even the computation of
  $Q_T^(G)(1)$ (i.e., the dimension of $R_T^(G)(theta)$) involves the existence
  and properties of the Steinberg character. The problem of describing the Green
  functions $Q_T^(G)(u)$ will be studied in Chapter~@ch:characters.
] <rem:character-formula-green-functions>

From now on, for any scheme $X$, we will denote $H_C^(i)(X, overline(QQ)_ell)$
by $H_C^(i)(X)$.

Our aim now is to prove an orthogonality theorem for the $R_T^(G)(theta)$. We
first introduce certain definitions. Recall (Chapter~@ch:classification-of-tori)
that for any $F$-stable maximal torus $T$, $X(T)$ denotes the group of
characters of $T$. Let $Y(T) = Hom(K^*, T)$. Then $Y(T)$ is called the group of
one-parameter subgroups of $T$. Both $X(T)$ and $Y(T)$ are free abelian groups
of rank $ell$ where $ell$ is the dimension of $T$ and we have a non-singular
pairing $X(T) times Y(T) -> ZZ$ given by $(chi, phi) = n$ if $chi phi(t) = t^n$
($t in K^*$) which make them dual to each other (see [@bib:Borel1969], §8). Now
$F$ acts on $X(T)$ and hence on $Y(T) = Hom(X(T), ZZ)$. There is a positive
integer $n$ such that $F^n$ acts on $T$ as $t |-> t^(q^n)$; #source(86) this
follows by choosing a finite basis of $X(T)$ and a common finite field of
definition of its characters. Then $F^n chi = chi^(q^n)$ for every $chi in X(T)$
(see the proof of Theorem~@th:torus-order), and $T$ is split over $FF_(q^n)$.

We now choose a fixed generator $gamma$ of the group of $(q - 1)$st roots of
unity in $K^*$. If $T$ is split over $FF_q$, we have an exact sequence

$ 0 -> Y(T) arrow.r.long^(F - 1) Y(T) -> T^F -> 0, $
<eq:torus-cocharacter-exact-sequence>

given as follows: the map $Y(T) -> T^F$ is given by $phi |-> phi(gamma)$. We
note that $phi(gamma) in T^F$ since
$F(phi(gamma)) = phi(gamma)^q = phi(gamma^q) = phi(gamma)$. The kernel of this
map is $(F - 1) Y(T)$. The map is surjective since it is known that the images
of the one-parameter subgroups generate $T$, i.e., the map $Y(T) ⊗ K^* -> T$
given by $(phi, x) |-> phi(x)$ is an isomorphism.

If $T$ is split over $FF_(q^n)$ we take the map $Y(T) -> T^(F^n)$ as above and
compose it with the “norm” map $N = 1 + F + dots + F^(n - 1): T^(F^n) -> T^F$.
Note that we have a commutative diagram

$ #torus-norm-diagram() $ <eq:torus-norm-diagram>

So in any case we have an exact sequence of the form
@eq:torus-cocharacter-exact-sequence and thus we can regard any
$theta in hat(T)^F$ as a character (i.e., a #source(87) homomorphism
$Y(T) -> overline(QQ)_ell^*$) of $Y(T)$.

#lemma(title: [[@bib:Deligne1976], 5.4])[
  Let $theta in hat(T)^F$, $theta' in hat(T')^F$, where $T, T'$ are $F$-stable
  maximal tori. Then the following conditions are equivalent.

  + $attach(T, tl: x) = T'$ for some $x in G$, such that the induced map
    $Y(T) -> Y(T')$ takes $theta$ to $theta'$.
  + For some $n$, there exists $x in G^(F^n)$ such that
    $attach(T^(F^n), tl: x) = T'^(F^n)$ and
    $attach((theta dot N), tl: x) = theta' dot N$.
] <lem:geometric-conjugacy-equivalences>

#proof[
  From the commutative diagram @eq:torus-norm-diagram it is clear that if
  $theta in hat(T)^F$, then $theta$ and $theta dot N in hat(T)^(F^n)$ give rise
  to the same character of $Y(T)$ and so (i) is not changed if we replace
  $theta$ by $theta dot N$. So we can assume $T, T'$ split over $FF_q$, in which
  case the Lemma is clear.
]

#definition(title: [[@bib:Deligne1976], 5.5])[
  The pairs $(T, theta)$, $(T', theta')$ are said to be _geometrically
  conjugate_#term-entry(
    "Geometric conjugacy",
    target: <def:geometric-conjugacy>,
  ) if either of the two above conditions holds.
] <def:geometric-conjugacy>

#example[
  $G = GL_2$, $F$ the standard Frobenius. We have two subgroups:

  $
    T_1 = T_0^F = {mat(gamma^a, 0; 0, gamma^b)} quad "and"
    T_2 = {mat(zeta^a, 0; 0, zeta^(a q))} quad ("where" zeta^(q + 1)
      = gamma)
  $

  such that $T_1 subset G^F$ and $T_2$ is conjugate in $G$ to a subgroup of
  $G^F$. If $S = T_0^(F^2) = {mat(zeta^a, 0; 0, zeta^b)}$, we have two norm maps
  $N_1: S -> T_1$, $N_2: S -> T_2$ given by

  $ N_1: mat(zeta^a, 0; 0, zeta^b) |-> mat(gamma^a, 0; 0, gamma^b) $

  and #source(88)

  $
    N_2: mat(zeta^a, 0; 0, zeta^b) |->
    mat(zeta^(a + b q), 0; 0, zeta^(b + a q)).
  $

  (For $N_2$, we use the twisted Frobenius map
  $mat(zeta^a, 0; 0, zeta^b) |-> mat(zeta^(b q), 0; 0, zeta^(a q))$ of $S$.) Any
  character of $T_1$ is given by

  $ theta_(m, n): mat(gamma^a, 0; 0, gamma^b) |-> gamma^(m a + n b) $

  ($gamma$ also denotes a primitive $(q - 1)$st root of unity in
  $overline(QQ)_ell^*$ here) and any character of $T_2$ is given by

  $ tau_n: mat(zeta^a, 0; 0, zeta^(a q)) |-> zeta^(n a) $

  (see also Chapter~@ch:principal-series). Then the characters $theta_(m, m)$ of
  $T_1$ and $tau_(m (q + 1))$ of $T_2$ are geometrically conjugate. In
  particular, $1 in hat(T)_1$, $1 in hat(T)_2$ are geometrically conjugate.
] <exm:gl-two-geometric-conjugacy>

#definition[
  $N_(G)(T, T') = {g in G | g^(-1) T g = T'}$ and $W_(G)(T, T')$ is the orbit
  set $T ∖ N(T, T') tilde.eq N(T, T') / T'$. We also write $W(T, T')$ for
  $W_(G)(T, T')$, and $W(T)$ for $W(T, T)$ (which agrees with our previous
  notation).
] <def:transporter-weyl-set>

We have a variant of the Bruhat decomposition for $G$. Choose representatives
$dot(w) in N(T, T')$ for the elements $w in W(T, T')$. Any element $g in G$ can
be written as $g = u_g n_g u'_g$, where $u_g in U ∩ n_g U'^- n_g^(-1)$,
$n_g in N(T, T')$, $u'_g in U'$. We have $G = ⊔_(w in W(T, T')) G_w$, where
$G_w$ is the set of all $g$ such that $n_g in T dot(w)$.

We also note that $F$ acts on $W(T, T')$ and we have #source(89)
$W(T, T')^F tilde.eq T^F \ N(T, T')^F tilde.eq N(T, T')^F / T'^F$, using Lang's
Theorem, as in the proof of Lemma~@lem:fixed-points-quotient.

#theorem(title: [Strong orthogonality; [@bib:Deligne1976], Theorem 6.2])[
  Let $T, T'$ be two $F$-stable maximal tori in $G$. If $(T, theta^(-1))$,
  $(T', theta')$ ($theta in hat(T)^F$, $theta' in hat(T')^F$), are not
  geometrically conjugate, then
  $(H_C^(i)(tilde(X))_theta ⊗ H_C^(j)(tilde(X)')_(theta'))^(G^F) = 0$. [Here
  $tilde(X), tilde(X)'$ denote the schemes $L^(-1) U$, $L^(-1) U'$ with respect
  to some $U, U'$ chosen such that $T U, T' U'$ are Borel subgroups.]
] <th:strong-orthogonality>
#term-entry(
  "Strong orthogonality (of the R_T^(G)(θ))",
  display: [Strong orthogonality (of the $R_T^(G)(theta)$)],
  target: <th:strong-orthogonality>,
)

#corollary(title: [[@bib:Deligne1976], p.~136])[
  If $(T, theta)$, $(T', theta')$ are not geometrically conjugate then the
  virtual representations $R_T^(G)(theta)$, $R_(T')^(G)(theta')$ are disjoint,
  i.e., have no irreducible constituents in common.
] <cor:geometrically-distinct-disjoint>

#proof(head: [_Proof of Corollary._])[
  This follows from the fact that $R_T^(G)(theta^(-1))$ is the dual of
  $R_T^(G)(theta)$; this follows, e.g., from the Character Formula
  (@th:lusztig-deligne-character-formula).
]

#proof(head: [_Proof of Theorem._])[
  By the Künneth Formula @eq:cohomology-kunneth we have that

  $
    H_C^(k)(tilde(X) times tilde(X)')_(theta, theta')
    tilde.eq sum_(i + j = k)
    H_C^(i)(tilde(X))_theta ⊗ H_C^(j)(tilde(X)')_(theta'),
  $

  where $H_C^(k)(tilde(X) times tilde(X)')_(theta, theta')$ is the subspace of
  $H_C^(k)(tilde(X) times tilde(X)')$ on which $T^F times T'^F$ acts on the
  right according to the character $theta times theta'$. Thus we have to show
  that $(H_C^(k)(tilde(X) times tilde(X)')_(theta, theta'))^(G^F) = 0$ if
  $(T, theta^(-1))$, $(T', theta')$ are not geometrically conjugate. (Note that
  $G^F$ acts #source(90) diagonally on the left on $tilde(X) times tilde(X)'$
  and hence on $H_C^(i)(tilde(X) times tilde(X)')$.) This means, by
  @eq:cohomology-finite-quotient, that we have to show that
  $H_C^(i)((tilde(X) times tilde(X)') / G^F)_(theta, theta') = 0$.

  Now we have an isomorphism

  $
    (tilde(X) times tilde(X)') / G^F ->
    Y = {(x, x', y) in U times U' times G | x (F y) = y x'}
  $

  given by $(g, g') |-> (g^(-1) (F g), (g')^(-1) (F g'), g^(-1) g')$, and
  $T^F times T'^F$ acts on $Y$ as

  $ (x, x', y) |-> (t^(-1) x t, t'^(-1) x' t', t^(-1) y t'). $

  Let $Y_w = {(x, x', y) | y in G_w}$; then $Y_w$ is a locally closed subset of
  $Y$. Now there is a filtration of $G$ defined by the closures of the $G_w$
  (see e.g. A. Borel and J. Tits, Publ. Math. IHES 41 (1972), §3) and this leads
  to a filtration of $Y$. Using the long exact sequence
  @eq:cohomology-open-closed-exact-sequence repeatedly, we see that it is
  sufficient to show that $H_C^(i)(Y_w)_(theta, theta') = 0$ for all $w$.

  Now we embed $T^F times T'^F$ in a diagonalizable group $H_w$ which acts on
  $Y_w$ as follows. Let

  $
    H_w = {(t, t') in T times T' | t' (F t')^(-1)
      = (F dot(w))^(-1) t (F t)^(-1) (F dot(w))}.
  $

  Then $T^F times T'^F subset H_w subset T times T'$. Define an action of $H_w$
  on $Y_w$ by the following rule. If $(t, t') in H_w$,
  $f_(t, t') (x, x', y) = (tilde(x), tilde(x)', tilde(y))$, where

  $
     tilde(x) & = t^(-1) x (F u_y) t (F(t^(-1) u_y^(-1) t)) \
    tilde(x)' & = t'^(-1) x' (F u'_y)^(-1) t' F(t'^(-1) u'_y t') \
     tilde(y) & = t^(-1) y t'.
  $

  Then we can check that $(tilde(x), tilde(x)', tilde(y)) in Y_w$ and that
  $f_(t_1, t'_1) f_(t_2, t'_2) = f_(t_1 t_2, t'_1 t'_2)$. Thus $H_w$ acts on
  $Y_w$ and then by Theorem~@th:connected-group-trivial-cohomology #source(91)
  the action of $H_w^0$ on $H_C^(i)(Y_w)$ is trivial. Suppose that
  $H_C^(i)(Y_w)_(theta, theta')$ is non-zero for some $w$. Then it follows that
  the restriction of the character $theta theta'$ of $T^F times T'^F$ to
  $H_w^0 ∩ (T^F times T'^F)$ is trivial. From this we will deduce that
  $(T, theta^(-1))$ and $(T', theta')$ are geometrically conjugate.

  Now $H_w$ is the kernel of the composite map $T times T' -> T times T' -> T$
  given by

  $
    (t, t') |-> ((F t) t^(-1), (F t') t'^(-1)) |->
    (F dot(w)) (F t') t'^(-1) (F dot(w))^(-1) t(F t)^(-1).
  $

  Hence $Y(H_w^0)$, the group of one-parameter subgroups of $H_w^0$, is the
  kernel of the composite map $Y(T) times Y(T') -> Y(T) times Y(T') -> Y(T)$
  given by

  $
    (x, x') |-> ((F - 1)x, (F - 1)x') |->
    (F dot(w)) (F - 1)x' - (F - 1)x.
  $

  [Note that the mapping $F dot(w): T' -> T$ given by
  $t' |-> (F dot(w)) t' (F dot(w))^(-1)$ induces a mapping
  $F dot(w): Y(T') -> Y(T)$.]

  Now we make the following remark. Let $S, S'$ be two tori of $G$ with
  $S' subset S$, and suppose $S$ is $F$-stable. Then if $theta in hat(S)^F$ is
  trivial on $S' ∩ S^F$ then, regarded as a character of $Y(S)$ it is trivial on
  $((F - 1)Y(S') ⊗ QQ) ∩ Y(S)$. This comes from looking at the inverse image of
  $S' ∩ S^F$ under the map $Y(S) -> S^F$ given by
  @eq:torus-cocharacter-exact-sequence.

  Using this we see that $theta theta'$ is trivial on
  $((F - 1)Y(H_w^0) ⊗ QQ) ∩ (Y(T) times Y(T'))$. Now $F - 1$ is injective and
  $Y(T) times Y(T') / (F - 1) (Y(T) times Y(T'))$ is a torsion group. So the
  kernel $M$ of #source(92) the map $Y(T) times Y(T') -> Y(T)$ given by
  $(x, x') |-> (F dot(w))x' - x$ must be contained in the above intersection.
  Hence $theta theta'$ is trivial on $M$ and this says that for all $x in Y(T)$,
  $theta(x) theta'((F dot(w))^(-1) (x)) = 1$. Thus
  $theta dot attach(theta', tl: F dot(w)) = 1$ as characters of $Y(T)$ and
  $theta^(-1)$ and $theta'$ are geometrically conjugate, as required.
]

#theorem(title: [Weak orthogonality; [@bib:Deligne1976], Theorem 6.8;
  [@bib:Lusztig1978], Theorem 2.3])[
  Let $theta in hat(T)^F$, $theta' in hat(T')^F$. Then
  $(R_T^(G)(theta), R_(T')^(G)(theta')) =
  abs({w in W(T, T')^F | attach(theta', tl: dot(w)) = theta})$. In particular,
  $(R_T^(G)(theta), R_(T')^(G)(theta')) = 0$ (but $R_T^(G)(theta)$,
  $R_(T')^(G)(theta')$ need not be disjoint) if $T$ and $T'$ are not
  $G^F$-conjugate.
] <th:weak-orthogonality>
#term-entry(
  "Weak orthogonality (of the R_T^(G)(θ))",
  display: [Weak orthogonality (of the $R_T^(G)(theta)$)],
  target: <th:weak-orthogonality>,
)

#theorem(title: [Orthogonality relations for Green functions;
  [@bib:Deligne1976], Theorem 6.9])[
  We have the following relations for the functions $Q_T^G$ on the unipotent
  elements of $G^F$.

  $
    1 / abs(G^F) sum_(u in G^F, u "unipotent") Q_T^(G)(u) Q_(T')^(G)(u)
    = abs(N(T, T')^F) / (abs(T^F) abs(T'^F)).
  $
  <eq:green-function-orthogonality>
] <th:green-function-orthogonality>
#term-entry(
  "Orthogonality of Green functions",
  target: <th:green-function-orthogonality>,
)

#proof(head: [_Proofs of Theorems_~@th:weak-orthogonality _and_
  @th:green-function-orthogonality.])[
  The proofs are by formal computation using the character formula
  @eq:lusztig-deligne-character-formula. The strong orthogonality theorem
  (@th:strong-orthogonality) also enters into the proof at the end. We make an
  assumption (by induction on the semisimple rank of $G$) that
  @eq:green-function-orthogonality holds for the groups $C^(0)(s)^F$, where $s$
  does not lie in $Z(G^F)$, the center of $G^F$. Then #source(93)

  $
    (R_T^(G)(theta), R_(T')^(G)(theta'))
    &= 1 / abs(G^F) sum_(h in G^F)
    tr(h, R_T^(G)(theta)) tr(h^(-1), R_(T')^(G)(theta')) \
    &= 1 / abs(G^F) sum_(s in G^F, s "semisimple")
    1 / abs(C^(0)(s)^F)^2
    sum_(g, g' in G^F, g^(-1) s g in T^F, g'^(-1) s g' in T'^F)
    theta(g^(-1) s g) overline(theta'(g'^(-1) s g')) \
    & quad dot sum_(u in C^(0)(s)^F, u "unipotent")
    Q_(g T g^(-1))^(C^(0)(s)) (u) Q_(g' T' g'^(-1))^(C^(0)(s)) (u),
    quad "using" #[@eq:lusztig-deligne-character-formula],
  $

  $
    & = 1 / abs(G^F) sum_(s in G^F, s "semisimple", s in.not Z(G^F))
      1 / abs(C^(0)(s)^F) sum_(g, g')
      theta(g^(-1) s g) overline(theta'(g'^(-1) s g')) \
    & quad dot
      abs(N_(C^(0)(s)) (g T g^(-1), g' T' g'^(-1))^F)
      / (abs(T^F) abs(T'^F)) \
    & + sum_(s in G^F, s in Z(G^F)) theta(s) overline(theta'(s))
      (1 / abs(G^F) sum_(u "unipotent") Q_T^(G)(u) Q_(T')^(G)(u)) \
    & = 1 / abs(G^F) sum_(s in G^F, s "semisimple")
      1 / abs(C^(0)(s)^F) sum_(g, g')
      theta(g^(-1) s g) overline(theta'(g'^(-1) s g')) \
    & quad dot
      abs(N_(C^(0)(s)) (g T g^(-1), g' T' g'^(-1))^F)
      / (abs(T^F) abs(T'^F)) + A,
  $

  where the sum is over all semisimple elements $s$ including the central
  elements of $G^F$, and

  $
    A = sum_(s in Z(G^F)) theta(s) overline(theta'(s))
    {1 / abs(G^F) sum_(u "unipotent") Q_T^(G)(u) Q_(T')^(G)(u)
      - abs(N(T, T')^F) / (abs(T^F) abs(T'^F))}.
  $

  #source(94)
  Now the set

  $
    {(g, g', n_1) in G^F times G^F times G^F |
      g^(-1) s g in T^F, g'^(-1) s g' in T'^F, \
      n_1 in N_(C^(0)(s)) (g T g^(-1), g' T' g'^(-1))^F}
  $

  is in bijection with the set

  $
    {(g, n, x) in G^F times N(T, T')^F times C^(0)(s)^F |
      g^(-1) s g in T^F}
  $

  under the map $(g, g', n_1) |-> (g, n, n_1)$ where $n = g^(-1) n_1 g'$, for
  $n in N(T, T')^F$ is equivalent to
  $n_1 in N_(C^(0)(s)) (g T g^(-1), g' T' g'^(-1))^F$. Hence

  $
    (R_T^(G)(theta), R_(T')^(G)(theta'))
    &= A + 1 / abs(G^F) sum_(s in G^F, s "semisimple")
    1 / abs(C^(0)(s)^F) \
    & quad dot sum_(g in G^F, g^(-1) s g in T^F, n in N(T, T')^F)
    theta(g^(-1) s g) overline(theta'(n^(-1) g^(-1) s g n))
    abs(C^(0)(s)^F) / (abs(T^F) abs(T'^F)) \
    &= A + 1 / abs(G^F) sum_(t in T^F, n in N(T, T')^F)
    abs(G^F) / (abs(T^F) abs(T'^F))
    theta(t) overline(theta'(n^(-1) t n)) \
    &= A + abs({w in W(T, T')^F | attach(theta, tl: dot(w)) = theta'}),
  $

  since

  $
    1 / abs(T^F) sum_(t in T^F) theta(t) overline(theta'(n^(-1) t n))
    = cases(
      0 & "if" theta != attach(theta', tl: n),
      1 & "if" theta = attach(theta', tl: n)
    ).
  $

  By (@cor:geometrically-distinct-disjoint) we have
  $(R_T^(G)(theta), R_(T')^(G)(1)) = 0$ if $theta != 1$, since the only
  character of $T^F$ geometrically conjugate to $1 in hat(T')^F$ is
  $1 in hat(T)^F$. So if $T^F$ has a non-trivial character which #source(95)
  restricts to $1$ on $Z(G^F)$ then we have $A = 0$, and
  $sum_(s in Z(G^F)) theta(s) theta'(s^(-1)) != 0$, so that
  @eq:green-function-orthogonality holds. Then $A = 0$ in general and so
  Theorem~@th:weak-orthogonality holds. Similarly our conclusions hold if $T'^F$
  has such a character. In the remaining case, @eq:green-function-orthogonality
  follows from the Green-function orthogonality theorem of Deligne and Lusztig
  [@bib:Deligne1976], 6.9. Their proof first passes to the adjoint group: Green
  functions on corresponding unipotent elements are unchanged, and both sides of
  the orthogonality formula are unchanged. The case of a torus with only one
  rational point is treated after this reduction. Thus $A = 0$, and
  Theorem~@th:weak-orthogonality follows in this case also.
  #ed-note[
    The equality $T^F = Z(G)^F$ does not imply that $T$ is split. For example, a
    Coxeter torus of $SU(3, 2)$ has order $2^2 - 2 + 1 = 3$, equal to the order
    of the centre. The central reduction is essential; see #cite(
      <DeligneLusztig1976>,
      form: "full",
    ), §4.1 and the proof of Theorem 6.9.
  ]
]

*Remarks.*

+ The construction of the virtual representations $R_T^(G)(theta)$ of $G^F$
  gives us a map $theta |-> R_T^(G)(theta)$ from $cal(R) (T^F)$ into
  $cal(R) (G^F)$ where $cal(R) (G^F)$ is the Grothendieck group of $G^F$. Let
  $theta, phi in hat(T)^F$. Using (@th:mackey) and (@th:weak-orthogonality) we
  see that $(Ind_(T^F)^(N(T)^F) (theta), Ind_(T^F)^(N(T)^F) (phi))_(N(T)^F) =
  (R_T^(G)(theta), R_T^(G)(phi))_(G^F)$. Taking characters we get an isometry
  from the space of class functions on $N(T)^F$ vanishing outside $T^F$ into the
  space of class functions on $G^F$. This is a familiar situation in the
  character theory of finite groups; see e.g. [@bib:Feit1967], p.~172. We also
  remark that if $T$ and $T'$ are not $G^F$-conjugate, so that
  $(R_T^(G)(theta), R_(T')^(G)(phi)) = 0$ for $theta in hat(T)^F$,
  $phi in hat(T')^F$ then in fact we have
  $sum_g tr(g, R_T^(G)(theta)) tr(g^(-1), R_(T')^(G)(phi)) = 0$, where the sum
  runs #source(96) over all $g = s u$ where $s$ is conjugate to a fixed
  semisimple element $s_0$. This follows from the character formula
  @eq:lusztig-deligne-character-formula and the orthogonality of Green functions
  (@th:green-function-orthogonality). In other words, we have
  “section-by-section orthogonality” among the $R_T^(G)(theta)$, where by a
  section we mean a $p'$-section.

+ Green [@bib:Green1955] and Kilmoyer (unpublished) have defined the notion of
  the _principal part_ at $T$ of a class function $f$ on $G^F$. This is defined
  by

  $
    f_((T)) (t) = abs(T^F) / abs(C^(0)(t)^F)
    sum_(u in C(t)^F, u "unipotent") f(t u) Q_T^(C^(0)(t)) (u)
    quad (t in T^F).
  $

  The mapping $theta |-> tr R_T^(G)(theta)$ ($theta in hat(T)^F$) extends by
  linearity to a map from the space of class functions on $T^F$ into the space
  of class functions on $G^F$. If $phi$ is a class function on $T^F$ and the
  class function $phi^*$ on $G^F$ corresponds to $phi$ under this map we have
  $(phi^*, f)_(G^F) = (phi, f_((T)))_(T^F)$. Furthermore, if $f$ is a linear
  combination of the $R_T^(G)(theta)$, we have
  $f = sum_((T)) 1 / abs(W(T)^F) (f_((T)))^*$ where the summation is over a set
  of representatives for the conjugacy classes of tori in $G^F$.#ed-note[
    For an arbitrary class function, the displayed sum gives its orthogonal
    projection onto the span of the Deligne–Lusztig characters. The identity
    holds for functions in that span. See #cite(<Digne2020>, form: "full"),
    Definition 10.2.3 and Proposition 10.2.4.
  ] The maps $theta |-> tr R_T^(G)(theta)$ and $f |-> f_((T))$ can be regarded
  as twisted versions of the induction and restriction maps for class functions.



#definition[
  The character $theta in hat(T)^F$ is regular if it is not fixed by any
  non-trivial element of $W(T)$.
] <def:regular-torus-character>

#corollary[
  If $theta in hat(T)^F$ is regular then $±R_T^(G)(theta)$ is irreducible.
] <cor:regular-lusztig-deligne-irreducible>

#source(97)
#proof[
  This is clear from (@th:weak-orthogonality).
]

#corollary(title: [[@bib:Lusztig1978], 2.4])[
  The virtual representation $R_T^(G)(theta)$ is independent of the choice of
  $U$ which defines the variety $tilde(X) = L^(-1) U$.
] <cor:independence-unipotent-choice>

#proof[
  Suppose $f, f'$ are two class functions on $G^F$ such that
  $(f, f) = (f, f') = (f', f')$. Then $(f - f', f - f') = 0$ and hence $f = f'$.
  If we have $B = T U$, $B' = T U'$, we apply this remark to
  $f = R_(T, U)^(G)(theta)$, $f' = R_(T, U')^(G)(theta)$ and use
  Theorem~@th:weak-orthogonality.
]

#remark[
  We will show later (@th:regular-representation-decomposition) that every
  irreducible character of $G^F$ occurs as a constituent of some
  $R_T^(G)(theta)$. Corollary~@cor:regular-lusztig-deligne-irreducible and an
  asymptotic result on the number of regular characters of tori of $G^F$ (see
  [@bib:Springer1975], pp.~638, 640) show that the $±R_T^(G)(theta)$, for
  $theta$ regular, give “most” of the irreducible characters of $G^F$, in some
  sense.
] <rem:most-irreducible-characters>

Next we determine the dimensions of the $R_T^(G)(theta)$. The ubiquitous
Steinberg representation enters into this calculation. We first define this
representation and review some of its properties. Any $F$-stable maximal torus
$T$ of $G$ has a decomposition $T = T_d T_a$, where $T_d$ is a maximal
$FF_q$-split subtorus of $T$ (see e.g. [@bib:Borel1969], p.~218). Let
$sigma(G) = dim (T_0)_d$. We define $epsilon_G = (-1)^(sigma(G))$.

The _Tits building_ of $G^F$ is the simplicial complex $cal(J)$ whose simplices
are indexed by the proper parabolic subgroups of $G^F$. We denote the simplex
corresponding to $P^F$ by $S_P$. We say $S_P$ is a face of $S_Q$ if
$Q subset P$. Then $G^F$ acts on $cal(J)$ (by conjugation) and hence on the
(classical) cohomology groups $H^(i)(cal(J), ZZ)$. The representation of $G^F$
on the top reduced cohomology of $cal(J)$ is called the _Steinberg
representation_#term-entry("Steinberg representation") $op("St")_G$. Its
dimension is $abs(U_0^F) = abs(G^F)_p$. For the properties of this
representation see [@bib:Springer1974], §5, and [@bib:Curtis1979], 4.2.8. In
particular, #source(98)

$
  (Ind_(B_0^F)^(G^F) (1), op("St")_G) = 1.
$ <eq:steinberg-principal-series-multiplicity>

The character of $op("St")_G$ vanishes on elements which are not semisimple,
and, for a semisimple element $s$,

$
  op("St")_(G)(s) = epsilon_G epsilon_(C^(0)(s)) op("St")_(C^(0)(s)) (1).
$ <eq:steinberg-character>

#theorem[
  ([@bib:Deligne1976], 7.1; [@bib:Lusztig1978], 2.9.)
  $
    dim R_T^(G)(theta) = Q_T^(G)(1)
    = epsilon_G epsilon_T abs(G^F) / (abs(U_0^F) abs(T^F))
    = epsilon_G epsilon_T abs(G^F) / (op("St")_(G)(1) abs(T^F)).
  $
] <th:lusztig-deligne-dimension>

Thus the dimension is what it would be if we were inducing a character of $T^F$
from a Borel subgroup containing $T^F$, even though such a Borel subgroup need
not exist.

#proof[
  First suppose there is a nontrivial character $theta$ of $T^F$ which is
  trivial on $Z(G)^F$. Then by Corollary~@cor:geometrically-distinct-disjoint,
  $R_T^(G)(theta)$ and $R_(T_0)^(G)(1) = Ind_(B_0^F)^(G^F) (1)$ are disjoint.
  Hence, by @eq:steinberg-principal-series-multiplicity,
  $(R_T^(G)(theta), op("St")_G) = 0$. Using
  @eq:lusztig-deligne-character-formula and @eq:steinberg-character, we obtain
  #source(99)
  $
    sum_(s in G^F, s " semisimple")
    (epsilon_G epsilon_(C^(0)(s)) op("St")_(C^(0)(s)) (1)) / abs(C^(0)(s)^F)
    sum_(g in G^F, g^(-1) s g in T^F)
    Q_(g T g^(-1))^(C^(0)(s)) (1) theta(g^(-1) s g) = 0.
  $
  By induction, for $s$ noncentral,
  $
    Q_(g T g^(-1))^(C^(0)(s)) (1)
    = epsilon_(C^(0)(s)) epsilon_T abs(C^(0)(s)^F)
    / (op("St")_(C^(0)(s)) (1) abs(T^F)).
  $
  We therefore have
  $
    & epsilon_G epsilon_T / abs(T^F)
      sum_(s in G^F, s " semisimple noncentral")
      sum_(g in G^F, g^(-1) s g in T^F) theta(g^(-1) s g) \
    & + sum_(s in Z(G)^F) op("St")_(G)(1) / abs(G^F)
      sum_(g in G^F) Q_T^(G)(1) theta(s) = 0,
  $
  that is,
  $
    epsilon_G epsilon_T abs(G^F) / abs(T^F)
    sum_(t in T^F, t in.not Z(G)^F) theta(t)
    + sum_(z in Z(G)^F) op("St")_(G)(1) Q_T^(G)(1) theta(z) = 0.
  $
  Since
  $
    sum_(t in T^F, t in.not Z(G)^F) theta(t)
    = -sum_(z in Z(G)^F) theta(z) != 0,
  $
  we obtain
  $ op("St")_(G)(1) Q_T^(G)(1) = epsilon_G epsilon_T abs(G^F) / abs(T^F). $
  If no such character $theta$ exists, the remaining case follows from
  [@bib:Deligne1976], Theorem 7.1. Its proof makes the same adjoint-group
  reduction as the proof of Theorem~@th:weak-orthogonality before treating a
  torus with only one rational point.
]

#source(100)
#corollary[
  ([@bib:Deligne1976], 7.3.)
  $
    Ind_(T^F)^(G^F) theta
    = epsilon_G epsilon_T R_T^(G)(theta) ⊗ op("St")_G.
  $
] <cor:steinberg-tensor-induction>

#proof[
  By @eq:steinberg-character it is enough to compare the characters on
  semisimple elements. For such an element $s$,
  $
    tr(s, R_T^(G)(theta)) & = 1 / abs(C^(0)(s)^F)
                            sum_(g in G^F, g^(-1) s g in T^F)
                            Q_(g T g^(-1))^(C^(0)(s)) (1) theta(g^(-1) s g) \
                          & = epsilon_(C^(0)(s)) epsilon_T
                            / (op("St")_(C^(0)(s)) (1) abs(T^F))
                            sum_(g in G^F, g^(-1) s g in T^F) theta(g^(-1) s g).
  $
  Hence
  $
    tr(s, epsilon_G epsilon_T R_T^(G)(theta) ⊗ op("St")_G)
    &= 1 / abs(T^F)
    sum_(g in G^F, g^(-1) s g in T^F) theta(g^(-1) s g)
    \
    &= tr(s, Ind_(T^F)^(G^F) theta).
  $
]

The next theorem shows that every irreducible representation occurs as a
constituent of some $R_T^(G)(theta)$.

#theorem[
  ([@bib:Deligne1976], 2.11.) The regular representation of $G^F$ is
  $
    1 / abs(G^F)_p sum_T sum_(theta in hat(T)^F)
    epsilon_T epsilon_G R_T^(G)(theta),
  $
  where the first sum is over all $F$-stable maximal tori of $G$.
] <th:regular-representation-decomposition>

#proof[
  The expression on the right is an element of $R(G^F) ⊗_ZZ QQ$; denote it by
  $phi$. By Theorem~@th:weak-orthogonality,
  #source(101)
  $
    (phi, phi) & = 1 / abs(G^F)_p^2 sum_(T, T')
                 sum_(theta in hat(T)^F, theta' in hat(T')^F)
                 epsilon_T epsilon_(T')
                 abs({n in N(T, T')^F | attach(theta, tl: n) = theta'})
                 / abs(T'^F) \
               & = 1 / abs(G^F)_p^2 sum_(T, T', theta, theta')
                 epsilon_T epsilon_(T')
                 abs(
                   {g in G^F | g T g^(-1) = T',
                     attach(theta, tl: g) = theta'}
                 )
                 / abs(T'^F) \
               & = 1 / abs(G^F)_p^2 sum_(T, theta, g in G^F)
                 epsilon_T epsilon_(g T g^(-1)) / abs(T^F) \
               & = 1 / abs(G^F)_p^2 abs(G^F) abs(G^F)_p^2 \
               & = abs(G^F).
  $
  Here we have used the fact that the number of $F$-stable maximal tori is
  $abs(G^F)_p^2$ (Theorem~@th:steinberg-representation). If $rho$ denotes the
  regular representation, then $(rho, R_T^(G)(theta)) = dim R_T^(G)(theta)$, so
  that
  $
    (rho, phi) = 1 / abs(G^F)_p sum_(T, theta)
    epsilon_T epsilon_G epsilon_G epsilon_T
    abs(G^F)_(p') / abs(T^F) = abs(G^F).
  $
  Since $(rho, rho) = abs(G^F)$, we have $(rho - phi, rho - phi) = 0$, and hence
  $rho = phi$.
]

#remark[
  The characters $R_T^(G)(theta)$ do not, in general, span the space of all
  class functions on $G^F$. They do so for $G L_n$, but not for $S L_2$. The
  class functions in the subspace spanned by them are called _uniform
  functions_.
]

#source(102)
We now consider the connections between the $R_T^(G)(theta)$ and the
Harish–Chandra theory described in Chapter~@ch:harish-chandra.

#theorem[
  ([@bib:Deligne1976], 8.2; [@bib:Lusztig1978], 2.6.) Suppose the $F$-stable
  maximal torus $T$ is contained in an $F$-stable parabolic subgroup $P$ of $G$.
  Let $P = L V$, where $L$ is an $F$-stable Levi subgroup. Let
  $theta in hat(T)^F$. Then
  $ R_T^(G)(theta) = Ind_(P^F)^(G^F) (tilde(R)_T^(L)(theta)). $
  Here, as in Chapter~@ch:harish-chandra, if $M$ is an $L^F$-module, $tilde(M)$
  denotes its lift to $P^F$.
] <th:lusztig-deligne-parabolic-induction>

#proof[
  Choose a Borel subgroup $B = T U$ where $T subset B subset P$, and $B$ is not
  necessarily $F$-stable. As before, let $tilde(X) = L^(-1) U$. If
  $g in tilde(X)$, then $F g = g u$ for some $u in U subset P$. Hence
  $F(g P g^(-1)) = g P g^(-1)$, so that $g P g^(-1)$ is $F$-stable.

  Let $cal(P)$ be the finite set of all $F$-stable conjugates of $P$. This is
  also the set of $G^F$-conjugates of $P$, by
  Proposition~@prop:f-stable-conjugacy, since $N_(G)(P) = P$. We have a map
  $phi: g arrow.r g P g^(-1)$ of $tilde(X)$ onto $cal(P)$. If
  $P' = g_1 P g_1^(-1)$, where $g_1 in G^F$, its fibre is
  $
    tilde(X)_(P') = {g in tilde(X) | g P g^(-1) = g_1 P g_1^(-1)}
    = {g_1^(-1) g in P | (g_1^(-1) g)^(-1) F(g_1^(-1) g) in U}.
  $
  There is a natural map
  $
    tilde(X)_(P') arrow.r overline(tilde(X))_(P')
    := {overline(g_1^(-1) g) in L |
      overline(g_1^(-1) g)^(-1) F(overline(g_1^(-1) g)) in overline(U)},
  $
  where, for a subset $Y subset P$, $overline(Y)$ denotes its image under the
  canonical map $P arrow.r L$. The target is a variety $L^(-1) overline(U)$ for
  $L$. The fibres are all isomorphic to $V$, and hence to affine space of some
  dimension $s$. Thus by the cohomology formulas of
  Chapter~@ch:ell-adic-cohomology,
  $
    H_C^(i)(tilde(X)_(P')) tilde.eq
    H_C^(i - 2s) (overline(tilde(X))_(P')).
  $
  We disregard the Tate twist here; it matters only when calculating the action
  of Frobenius on cohomology.

  #source(103)
  Now $tilde(X) = union_(P' in cal(P)) tilde(X)_(P')$. The group $G^F$ acts
  transitively on $cal(P)$ by conjugation, and therefore permutes the schemes
  $tilde(X)_(P')$ and their cohomology groups $H_C^(i)(tilde(X)_(P'))$
  transitively. The stabilizer of the fibre corresponding to $P$ is $P^F$.

  We use the following simple observation. Let $Q < H$ be finite groups, $M$ an
  $H$-module, and $N$ a $Q$-submodule of $M$ such that
  $M = x_1 N ⊕ x_2 N ⊕ dots.c ⊕ x_r N$, where the $x_i$ form a set of left coset
  representatives for $H$ over $Q$. Then $M = Ind_Q^(H)(N)$. This extends
  immediately to virtual representations. Together with the additivity formula
  @eq:lefschetz-additivity for the alternating traces on the direct sum of the
  $H_C^(i)(tilde(X)_(P'))$, it proves the theorem.
]

#definition[
  An $F$-stable maximal torus $T$ is _minisotropic_#term-entry(
    "Minisotropic torus",
    target: <def:minisotropic-torus>,
  ) if it is not contained in any $F$-stable proper parabolic subgroup of $G$.
] <def:minisotropic-torus>

#example[
  If $G = G L_n$ and $F$ is the standard Frobenius map, the maximal torus
  corresponding to the Coxeter element of $W(T_0)$, that is, to an $n$-cycle in
  $S_n$, is minisotropic. It is the only such torus up to conjugacy by $G^F$.
] <exm:gl-minisotropic-torus>

#theorem[
  ([@bib:Deligne1976], 8.3; [@bib:Lusztig1978], 2.18.) Let $mu$ be a
  representation of $G^F$. Then $mu$ is cuspidal if and only if
  $(mu, R_T^(G)(theta))_(G^F) = 0$ whenever $T$ is not minisotropic, for every
  $theta in hat(T)^F$.
] <th:lusztig-deligne-cuspidality>

#proof[
  Suppose $(mu, R_T^(G)(theta))_(G^F) = 0$ for every $F$-stable maximal torus
  $T$ contained in $L$, where $P = L V$ is an $F$-stable #source(104) proper
  parabolic subgroup of $G$ and $L$ an $F$-stable Levi subgroup. If $rho_L$ is
  the regular representation of $L^F$, then
  $
    Ind_(V^F)^(G^F) (1) & = Ind_(P^F)^(G^F) (tilde(rho)_L) \
                        & = Ind_(P^F)^(G^F) (1 / abs(L^F)_p
                            sum_(T subset L, theta in hat(T)^F)
                            epsilon_L epsilon_T tilde(R)_T^(L)(theta)) \
                        & = 1 / abs(L^F)_p sum_(T subset L, theta in hat(T)^F)
                          epsilon_L epsilon_T R_T^(G)(theta),
  $
  by Theorems~@th:regular-representation-decomposition and
  @th:lusztig-deligne-parabolic-induction. Hence
  $(mu, Ind_(V^F)^(G^F) (1)) = 0$, which shows that $mu$ is cuspidal.

  Conversely, suppose $(mu, R_T^(G)(theta)) != 0$ for some $T subset L$,
  $P = L V$, and $theta in hat(T)^F$. Then
  $
    (mu, R_T^(G)(theta))_(G^F)
    = (mu, Ind_(P^F)^(G^F) (tilde(R)_T^(L)(theta)))_(G^F)
    = (mu, tilde(R)_T^(L)(theta))_(P^F) != 0.
  $
  Write $mu = mu' + mu''$, where $mu'$ is the representation of $P^F$ on the
  space of $V^F$-fixed vectors. Since $V^F$ acts trivially on
  $tilde(R)_T^(L)(theta)$, $(mu'', tilde(R)_T^(L)(theta))_(P^F) = 0$. Thus
  $(mu', tilde(R)_T^(L)(theta))_(P^F) != 0$. There are nonzero $V^F$-fixed
  vectors in $mu$, so $mu$ is not cuspidal.
]

In the light of Theorems~@th:lusztig-deligne-parabolic-induction and
@th:lusztig-deligne-cuspidality we make the following remarks. For an $F$-stable
proper parabolic subgroup $P = L V$, with $L$ $F$-stable, the cuspidal
representations of $L^F$ occur as constituents of some $R_T^(L)(theta)$ with $T$
minisotropic in $L$. We lift them to $P^F$ and induce them to $G^F$. The
irreducible representations of $G^F$ which do not arise in this way are the
cuspidal representations #source(105) of $G^F$, and they occur as constituents
of the $R_T^(G)(theta)$ with $T$ minisotropic in $G$. Of particular interest are
the cuspidal representations which occur as constituents of some $R_T^(G)(1)$.
We study these further in Chapter~@ch:classification-of-representations.
