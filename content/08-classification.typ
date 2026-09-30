#import "main-defs.typ": *
#import "statements.typ": *

#chapter[Classification of
  Representations] <ch:classification-of-representations>

#source(138)
In this chapter we turn to the classification of all the irreducible
representations of a group of the form $G^F$. We will describe the
classification of the representations of $GL(n, q)$ and $U(n, q)$
[@bib:Lusztig1977b] and of certain versions of the other classical groups
([@bib:Lusztig1977a], [@bib:Lusztig1978]). In the case of $GL(n, q)$ there is a
recursive method of obtaining the Green functions and hence in principle we have
the character table. By work of Hotta and Springer [@bib:Hotta1977], along with
the classification of the representations of $U(n, q)$, the same is true for
$U(n, q)$ for large $p$. However, in the case of Lusztig's classification of the
representations of the other classical groups, we have only the dimensions but
not the characters of the representations.

In some sense the so-called unipotent representations of $G^F$ are the most
important ones to obtain. Lusztig has classified the unipotent representations
in all cases, i.e., also in the case of the exceptional groups (see
[@bib:Lusztig1978], [@bib:Lusztig1979]), and given their dimensions.

#definition[
  An irreducible representation of $G^F$ is _unipotent_#term-entry(
    "Unipotent representation",
  ) if it occurs as a constituent of $R_T^(G)(1)$ for some $F$-stable maximal
  torus $T$ of $G$.
] <def:unipotent-representation>

We note that the irreducible constituents of
$Ind_(B_0^F)^(G^F)(1) = R_(T_0)^(G)(1)$ are unipotent; in particular the
representations $1$ and $op("St")_G$ are unipotent. But there may be other
unipotent #source(139) representations of $G^F$ (e.g., $theta_10$ of
[@bib:Srinivasan1968], which is in fact a cuspidal unipotent representation, and
therefore cannot occur in $R_(T_0)^(G)(1)$ by
Theorem~@th:lusztig-deligne-cuspidality). The first proposition gives $1$ as a
linear combination of the $R_T^(G)(1)$.

_Notation._ $sum_((T))$ stands for the sum over a set of representatives of
$G^F$-conjugacy classes of $F$-stable maximal tori of $G$.

#proposition[
  ([@bib:Deligne1976], Corollary 7.14; [@bib:Lusztig1978], 2.7.) We have
  $ 1 = sum_((T)) 1 / abs(W(T)^F) R_T^(G)(1). $
] <prop:trivial-representation-torus-average>

#proof[
  It is sufficient to show that $(R_T^(G)(1), 1)_(G^F) = 1$ for every $T$, since
  $R_T^(G)(1)$ and $R_(T')^(G)(theta)$ are disjoint if $theta in hat(T')^F$,
  $theta != 1$, by Theorem~@th:strong-orthogonality, and
  $(R_T^(G)(1), R_T^(G)(1)) = abs(W(T)^F)$ by Theorem~@th:weak-orthogonality.

  As before let $tilde(X)$ denote the variety from which $R_T^(G)(1)$ is
  constructed. We have
  $
    (R_T^(G)(1), 1) & = sum_i (-1)^i dim((H_C^(i)(tilde(X))_1)^(G^F)) \
                    & = sum_i (-1)^i 1 / abs(T^F)
                      sum_(t in T^F) tr(t, lr(H_C^(i)(tilde(X)))^(G^F)) \
                    & = sum_i (-1)^i 1 / abs(T^F)
                      sum_(t in T^F) tr(t, H_C^(i)(G^F ∖ tilde(X))),
  $
  by @eq:cohomology-finite-quotient. The map $g |-> g^(-1)(F g)$ gives an
  isomorphism $G^F ∖ tilde(X) -> U$, where $tilde(X) = L^(-1) U$, and the action
  $g |-> g t$ of $T^F$ on $tilde(X)$ corresponds to the action
  $u |-> t^(-1) u t$ on $U$. #source(140) This is just conjugation, so the
  action of $T^F$ extends to an action of $T$ on $U$. The action of $T$ on
  $H_C^(i)(U)$ is trivial by Theorem~@th:connected-group-trivial-cohomology.
  Thus $cal(L)(t, U)$ is constant for all $t$. Choose a regular element $t_0$ of
  $T$, i.e., $C^(0)(t_0) = T$, so that $t_0$ has only the identity as a fixed
  point on $U$. Then $cal(L)(t_0, U) = cal(L)(1, U^(t_0)) = 1$ by
  Theorem~@th:lefschetz-jordan-decomposition. Hence $cal(L)(t, U) = 1$ for all
  $t$, and
  $ (R_T^(G)(1), 1) = 1 / abs(T^F) sum_(t in T^F) cal(L)(t, U) = 1. $
]

#corollary[
  For any unipotent element $u$,
  $ sum_((T)) 1 / abs(W(T)^F) Q_T^(G)(u) = 1. $
] <cor:green-functions-torus-average>

#remark(numbered: true)[
  It can also be shown ([@bib:Deligne1976], 7.14) that
  $
    sum_((T)) (epsilon_G epsilon_T) / abs(W(T)^F) R_T^(G)(1)
    = op("St")_G.
  $
] <rem:steinberg-torus-average>

By the classification of tori (@cor:rational-tori), each $F$-stable maximal
torus $T$ corresponds to an $F$-conjugacy class of $W = W(T_0)$. We write $R_w$
for $R_T^(G)(1)$ if $T$ corresponds to $w in W$. By
@prop:rational-tori-weyl-classes, $abs(W(T)^F) = abs(C'(w))$. Thus we can write
@prop:trivial-representation-torus-average as

$ 1 / abs(W) sum_(w in W) R_w = 1. $ <eq:trivial-representation-weyl-average>

Let $cal(E)(W)$ denote the set of isomorphism classes of irreducible
representations of $W$. Then $F$ acts on $cal(E)(W)$. Let $E in cal(E)(W)^F$,
and we can ask whether, in analogy with @rem:steinberg-torus-average and
@eq:trivial-representation-weyl-average, $1 / abs(W) sum_(w in W) tr(w, E) R_w$
is a unipotent representation of $G^F$. This is true if $G^F = GL(n, q)$ or
$U(n, q)$ (with a #source(141) slight modification, i.e., “twisting by $w_0$”)
and furthermore in these cases all unipotent representations are obtained this
way. But it is not true in general.

At this stage we need to generalize the construction of $R_T^(G)(theta)$ to an
$F$-stable reductive subgroup $L$ of $G$ which is a Levi subgroup of a parabolic
subgroup, and a character of $L^F$ (see [@bib:Lusztig1976a]).

Let $P = L V$ be the Levi decomposition of a parabolic subgroup $P$ of $G$, with
$L$ $F$-stable but $P$ not necessarily $F$-stable. We call $L$ a
_regular_#term-entry("Regular subgroup") subgroup of $G$ (see
[@bib:Lusztig1977a], 7.2).

#definition(numbered: true)[
  Let $L$ be a regular subgroup of $G$. Then
  $ S_(L subset P, G) = {g in G | g^(-1)(F g) in V}. $
] <def:levi-induction-variety>

We also denote $S_(L subset P, G)$ by $S$ when the context is clear. The group
$G^F times L^F$ acts on $S$ by $(g_0, l): g |-> g_0 g l^(-1)$, and hence on
$H_C^(i)(S)$. Let $Pi$ be any $L^F$-module over $overline(QQ)_ell$. Then
$H_C^(i)(S) ⊗ Pi$ is a $G^F times L^F$-module if $G^F$ acts trivially on $Pi$.
Thus $(H_C^(i)(S) ⊗ Pi)^(L^F)$ is $G^F$-stable.

#definition[
  ([@bib:Lusztig1976a], p.~203.)
  $ R_L^(G)(Pi) = sum_i (-1)^i (H_C^(i)(S) ⊗ Pi)^(L^F). $
] <def:lusztig-induction>

This is a virtual representation of $G^F$, and we obtain a map
$Pi |-> R_L^(G)(Pi)$ from $R(L^F)$ to $R(G^F)$. If $L = T$ is a torus and
$Pi = theta in hat(T)^F$, we recover $R_T^(G)(theta)$, for the action of $T^F$
on $S$ considered here is the inverse of the action on $tilde(X)$ considered
earlier.

#source(142)
#proposition[
  ([@bib:Lusztig1976a], p.~204.) Let $T$ be an $F$-stable maximal torus
  contained in a regular subgroup $L$. Let $theta in hat(T)^F$. Then
  $ R_L^G R_T^(L)(theta) = R_T^(G)(theta). $
] <prop:lusztig-induction-transitivity>

#proof[
  Choose a Borel subgroup $B$ of $G$ such that $T subset B subset P$, where
  $P = L V$. Let $B_1 = B ∩ L$, $B_1 = T V_1$, and $B = T U$, with $V_1, U$
  unipotent. Then $U = V_1 V$, a semidirect product, and $B_1$ is a Borel
  subgroup of $L$. We construct an isomorphism
  $
    L^F ∖ (S_(L subset P, G) times S_(T subset B_1, L))
    -> S_(T subset B, G)
  $
  by $(g, g') |-> g g'$, where $L^F$ acts on the product by
  $(g, g') |-> (g l^(-1), l g')$ ($l in L^F$). If $g in S_(L subset P, G)$ and
  $g' in S_(T subset B_1, L)$, it is easy to check that
  $g g' in S_(T subset B, G)$. Conversely, if $g'' in S_(T subset B, G)$, write
  $g''^(-1)(F g'') = u_1 u_2$ with $u_1 in V_1$, $u_2 in V$. By Lang's
  Theorem~@th:lang write $u_1 = g'^(-1)(F g')$ with $g' in L$. Set
  $g = g'' g'^(-1)$; then $g in S_(L subset P, G)$. If instead we choose
  $g_0 in L$ with $g_0^(-1)(F g_0) = u_1$, then $g_0 = l g'$ for some $l in L^F$
  and $g$ is replaced by $g l^(-1)$. This gives the required isomorphism.

  By the Künneth Formula~@eq:cohomology-kunneth and
  @eq:cohomology-finite-quotient, for every nonnegative integer $r$,
  $
    H_C^(r)(S_(T subset B, G)) tilde.eq
    ⨁_(i + j = r)
    (H_C^(i)(S_(L subset P, G)) ⊗
      H_C^(j)(S_(T subset B_1, L)))^(L^F).
  $
  This isomorphism is compatible with the action of $G^F times T^F$.

  #source(143)
  For $theta in hat(T)^F$ we therefore have
  $
    H_C^(r)(S_(T subset B, G))_(theta^(-1)) tilde.eq
    ⨁_(i + j = r)
    (H_C^(i)(S_(L subset P, G)) ⊗
      H_C^(j)(S_(T subset B_1, L))_(theta^(-1)))^(L^F).
  $
  Taking alternating sums over $r$ gives
  $
    R_T^(G)(theta) & = sum_r (-1)^r H_C^(r)(S_(T subset B, G))_(theta^(-1)) \
                   & = sum_(i, j) (-1)^(i + j)
                     (H_C^(i)(S_(L subset P, G)) ⊗
                       H_C^(j)(S_(T subset B_1, L))_(theta^(-1)))^(L^F) \
                   & = sum_j (-1)^j
                     R_L^(G)(H_C^(j)(S_(T subset B_1, L))_(theta^(-1))) \
                   & = R_L^G R_T^(L)(theta),
  $
  as required.
]

#remark[
  It can be shown ([@bib:Lusztig1976a], p.~208) that
  $
    dim(epsilon_G epsilon_L R_L^(G)(Pi))
    = abs(G^F)_(p') abs(L^F)_(p')^(-1) dim Pi.
  $
] <rem:lusztig-induction-dimension>

_Examples._

+ $G = GL_3$, with $tilde(F)$ the twisted Frobenius morphism, so that
  $G^(tilde(F)) = U(3, q)$. Let $P$ be the parabolic subgroup consisting of
  matrices of the form
  $ mat(*, *, *; 0, *, *; 0, *, *), $
  with the obvious Levi subgroup
  $ L = {mat(*, 0, 0; 0, *, *; 0, *, *)}. $
  Then $L$, but not $P$, is $tilde(F)$-stable, and
  $L^(tilde(F)) tilde.eq U(1, q) times U(2, q)$. There are two tori $T_0, T_1$
  in $L$ such that $abs(T_0^(tilde(F))) = (q + 1)(q^2 - 1)$ and
  $abs(T_1^(tilde(F))) = (q + 1)^3$. A typical element of $L^(tilde(F))$
  #source(144) is of the form
  $ mat(eta^a, 0; 0, A), $
  where $eta$ is a primitive $(q + 1)$st root of unity in $K$ and
  $A in U(2, q)$. Let $phi_(l, m)$ be the character of $L^(tilde(F))$ taking
  this element to $(det A)^m eta^(l a)$, interpreted in $overline(QQ)_ell$ by
  choosing an embedding of $K^*$ into $overline(QQ)_ell^*$, with
  $1 <= l, m <= q + 1$. We obtain a family ${R_L^(G)(phi_(l, m))}$ of virtual
  representations of $G^(tilde(F))$ of dimension $q^2 - q + 1$, irreducible if
  $l, m$ are distinct. There is also a family
  ${R_L^(G)(op("St")_L dot phi_(l, m))}$ of dimension $q(q^2 - q + 1)$,
  irreducible if $l != m$. In fact, writing $phi = phi_(l, m)$, we have
  $ R_L^(G)(phi) = 1 / 2 [R_(T_0)^(G)(phi) + R_(T_1)^(G)(phi)], $
  $
    R_L^(G)(op("St")_L dot phi)
    = 1 / 2 [R_(T_0)^(G)(phi) - R_(T_1)^(G)(phi)].
  $
  Here $phi$ is restricted to $T_0^(tilde(F))$ and $T_1^(tilde(F))$. Similar
  representations exist for $GL(3, q)$, but are less interesting since both $L$
  and $P$ are stable under the standard Frobenius morphism.

+ $G = GL_4$, with $F$ the standard Frobenius, so $G^F = GL(4, q)$. Let
  $ L = {mat(A, 0; 0, B)} tilde.eq GL_2 times GL_2, $
  and consider $w = mat(0, I; I, 0)$ in $N(L)$. If $w = a(F a)^(-1)$ with
  $a in G$, then $(a^(-1) L a)^F subset G^F$ is isomorphic to $GL(2, q^2)$ and
  is not contained in a #source(145) parabolic subgroup of $G^F$ as a Levi
  subgroup. For a linear character $theta$ of $(a^(-1) L a)^F$ we have a virtual
  representation $R_(a^(-1) L a)^(G)(theta)$ of $G^F$ of dimension
  $(q - 1)(q^3 - 1)$, irreducible if $theta$ is not fixed by a nontrivial
  element of $N(a^(-1) L a)^F / (a^(-1) L a)^F$. This gives a family of virtual
  representations of $GL(4, q)$ of dimension $(q - 1)(q^3 - 1)$; using
  $op("St")_(a^(-1) L a) dot theta$ gives another family of dimension
  $q^2(q - 1)(q^3 - 1)$. With the twisted Frobenius morphism $tilde(F)$ on $G$,
  so that $G^(tilde(F)) tilde.eq U(4, q)$, and the same $L$, we obtain families
  of dimensions $(q + 1)(q^3 + 1)$ and $q^2(q + 1)(q^3 + 1)$ (see
  [@bib:Nozawa1972], where these are denoted $chi_3(k)$ and $chi_4(k)$).

+ The first example generalizes as follows. Let $G = GL_n$ and let $tilde(F)$ be
  the twisted Frobenius morphism, with $G^(tilde(F)) = U(n, q)$. Let
  $ L = {mat(a, 0; 0, A)} tilde.eq GL_1 times GL_(n - 1), $
  so that $L^(tilde(F)) tilde.eq U(1, q) times U(n - 1, q)$. For any character
  $theta$ of $L^(tilde(F))$ we can construct $R_L^(G)(theta)$. The virtual
  representation $R_L^(G)(1)$ is the sum of the trivial representation and a
  virtual representation $Psi$ which is irreducible up to sign. The
  representation $Psi$, when $n$ is even, was constructed by Tate and Thompson
  [@bib:Tate1965] and is historically the first example of a representation of a
  finite classical group constructed using étale cohomology. See
  [@bib:Hotta1978] for more details, including its character.

#source(146)
#heading(level: 2, numbering: none)[Representations of $GL(n, q)$ and
  $U(n, q)$] <sec:general-linear-unitary-representations>

We now describe the classification of representations of $GL(n, q)$ and
$U(n, q)$. The unipotent representations of $GL(n, q)$ were constructed by
Steinberg [@bib:Steinberg1951a]. The classification of all the representations
of $GL(n, q)$ was given by Green [@bib:Green1955]. The classification for
$U(n, q)$ was given by the author and Lusztig in [@bib:Lusztig1977b]. Their
method treats both cases simultaneously and will be described below. A
long-standing conjecture of Ennola [@bib:Ennola1963] stated that the Green
functions of $U(n, q)$ could be obtained from those of $GL(n, q)$ by changing
$q$ to $-q$. This has been proved for large $p$ (see [@bib:Hotta1977]). Thus in
principle we can construct the character table of $U(n, q)$ for large $p$.

Let $G = GL_n$ and let $F$ be either the standard Frobenius morphism (Case 1) or
the twisted Frobenius morphism (Case 2). Thus $G^F$ is $GL(n, q)$ in Case 1 and
$U(n, q)$ in Case 2. Recall that $B_0$ is the group of upper triangular
matrices, $T_0$ the group of diagonal matrices, and $W = W(T_0) tilde.eq S_n$,
the symmetric group of degree $n$. The torus $T_0$ is $F$-stable in both cases,
whereas $B_0$ is $F$-stable only in Case 1.

Let $w_0$ be the element of maximal length in $W$ (see [@bib:Bourbaki1968],
p.~43). We may take as $dot(w)_0$ the matrix with ones on the antidiagonal and
zeros elsewhere, in $N(T_0)$. Put $e = 0$ in Case 1 and $e = 1$ in Case 2. Then
$w_0^(-e) w w_0^e = F w$ for every $w in W$. Let $Delta subset Phi^+$ be the
simple #source(147) roots determining $B_0$. For $J subset Delta$, let $W_J$ be
generated by the reflections in the hyperplanes orthogonal to the roots in $J$,
in $V = X(T_0) ⊗_ZZ RR$. The subgroups $P_J = B_0 W_J B_0$ are the standard
parabolic subgroups containing $B_0$. Their Levi decompositions are
$P_J = L_J V_J$, with $T_0 subset L_J$ (see [@bib:Humphreys1972], p.~183). Here
each $L_J$ is a product of groups $GL_k$ for $k <= n$. For every $J$,
$dot(w)_0^(-e) L_J dot(w)_0^e = F L_J$. If $dot(w)_0^e = y^(-1)(F y)$ with
$y in G$, then $L = y L_J y^(-1)$ is $F$-stable. In Case 1 we may take $y = 1$;
in Case 2, $L^F$ is a direct product of finite unitary groups and need not be
contained in a parabolic subgroup of $G^F$.

#proposition[
  For every $J subset Delta$,
  $ 1 / abs(W_J) sum_(w in W_J) R_(w w_0^e) $
  is a virtual representation of $G^F$. Here $R_w$ is as in
  @eq:trivial-representation-weyl-average.
] <prop:parabolic-weyl-average>

#proof[
  We have $dot(w)_0^(-e) B_0 dot(w)_0^e = F B_0$, and hence $y B_0 y^(-1)$ is
  $F$-stable. Thus the canonical torus in $L$, the analogue of $T_0$, may be
  taken to be $T_1 = y T_0 y^(-1)$. Also $N_(L)(T_1) = y N_(L_J)(T_0) y^(-1)$,
  and representatives in $N_(L)(T_1)$ for $W_L = N_(L)(T_1) / T_1$ may be taken
  to be ${y dot(w) y^(-1) | w in W_J}$. Suppose $a^(-1) T_1 a$ with $a in L$ is
  $F$-stable, so that $a^(-1) y T_0 y^(-1) a$ is $F$-stable. Then
  $y^(-1) a(F a)^(-1)(F y) in N(T_0)$. Since $a(F a)^(-1) = y dot(w) y^(-1)$ for
  some $w in W_J$, #source(148) we have
  $y^(-1) a(F a)^(-1)(F y) = dot(w) dot(w)_0^e$. By
  @eq:trivial-representation-weyl-average,
  $ 1 / abs(W_L) sum_(x in W_L) R_(T_x)^(L)(1) = 1_L, $
  where $T_x$ is a maximal torus of $L$ corresponding to $x in W_L$. By
  Proposition~@prop:lusztig-induction-transitivity,
  $1 / abs(W_L) sum_(x in W_L) R_(T_x)^(G)(1)$ is a virtual representation of
  $G^F$. The preceding remarks show that it equals
  $1 / abs(W_J) sum_(w in W_J) R_(w w_0^e)$.
]

#theorem[
  Let $E in cal(E)(W)$. Then
  $ 1 / abs(W) sum_(w in W) tr(w w_0^e, E) R_w $
  is a unipotent representation, up to sign, of $G^F$. All unipotent
  representations of $G^F$ arise this way.
] <th:general-linear-unitary-unipotent-characters>

#proof[
  By a theorem of Frobenius [@bib:Frobenius1900], every irreducible
  representation $E$ of $W$ is an integral linear combination of representations
  $Ind_(W_J)^(W)(1)$ for $J subset Delta$. For $E = Ind_(W_J)^(W)(1)$,
  $
    1 / abs(W) sum_(w in W) tr(w w_0^e, E) R_w
    &= 1 / abs(W) sum_(w in W) tr(w, E) R_(w w_0^e) \
    &= 1 / abs(W_J) sum_(w in W_J) R_(w w_0^e).
  $
  By Proposition~@prop:parabolic-weyl-average, this is a virtual representation,
  and therefore the same is true for every $E$. To show it is irreducible up to
  sign, use Theorem~@th:weak-orthogonality and
  Proposition~@prop:rational-tori-weyl-classes. #source(149) They give
  $(R_w, R_w) = abs(C'(w))$. Since $w_0^(-e) w w_0^e = F w$, we have
  $C'(w w_0^e) = C(w)$. Character orthogonality in $W$ now shows that
  $1 / abs(W) sum_(w in W) tr(w, E) R_(w w_0^e)$ has norm $1$.

  We have obtained as many unipotent representations as there are conjugacy
  classes of $W$. Here this also equals the number of $F$-conjugacy classes, and
  hence the number of distinct $R_w$. Inverting the equations expresses the
  $R_w$ in terms of these unipotent representations. Thus we have constructed
  all unipotent representations of $G^F$.
]

#remark[
  The number of unipotent representations also equals the number of unipotent
  conjugacy classes of $G^F$: both equal the number of partitions of $n$.
] <rem:unipotent-partitions>

We now describe how all the representations of $GL(n, q)$ and $U(n, q)$ are
constructed. For details and proofs see [@bib:Lusztig1977b]. Choose
representatives ${L}$ for the $G^F$-conjugacy classes of centralizers of
$F$-stable semisimple elements of $G$. Consider linear characters $theta$ of
$L^F$ trivial on $D(L)^F$, where $D(L)$ is the derived group. We call $theta$
regular if it is fixed by no nontrivial element of $N(L)^F / L^F$. Choose a set
$cal(S)$ of representatives for the $N(L)^F / L^F$-orbits of such regular
characters of $L^F$, and let $Pi in cal(E)(L)$ have the form $Pi = theta phi$,
with $theta in cal(S)$ and $phi$ a unipotent #source(150) representation of
$L^F$. As $(L, Pi)$ varies over all these pairs, the virtual representations
$R_L^(G)(Pi)$ vary over all irreducible representations of $G^F$, up to sign.

#remark[
  We have shown that the unipotent representations of $G^F$, up to sign, are
  given by $1 / abs(W) sum_(w in W) chi(w) R_(w w_0^e)$, with $chi$ an
  irreducible character of $W tilde.eq S_n$. We now discuss when they are
  cuspidal.

  _Case 1: $GL(n, q)$._ For $n > 1$, all these representations occur in
  $Ind_(B_0^F)^(G^F)(1)$, and by Theorem~@th:lusztig-deligne-cuspidality they
  are not cuspidal.

  _Case 2: $U(n, q)$._ See [@bib:Lusztig1977a], §9. Suppose such a
  representation is cuspidal. By Theorem~@th:lusztig-deligne-cuspidality, if
  $w w_0$ corresponds to a non-minisotropic torus, then $chi(w) = 0$.
  Equivalently, $chi(w) = 0$ whenever $w$ has eigenvalue $-1$ in the natural
  representation on $X(T_0) ⊗_ZZ RR$. Thus $chi$ vanishes on all elements of
  even order. By a theorem of Brauer and Nesbitt (see [@bib:Curtis1962], §86),
  $dim chi$ is divisible by the highest power of $2$ dividing $abs(W)$. The
  hook-length formula is
  $ dim chi = n! / product_(i, j) h_(i j), $
  where $h_(i j)$ is the hook length of the square $(i, j)$ in the Young diagram
  of $chi$. All $h_(i j)$ must therefore be odd. The only possible such Young
  diagram corresponds to $n = 1 + 2 + dots + k$ for some $k$, so
  $n = k(k + 1) / 2$. Conversely, if $n$ has this #source(151) form and $chi$
  corresponds to that partition, it gives a unipotent cuspidal representation of
  $G^F$. This is the unique unipotent cuspidal representation of $G^F$.
] <rem:general-linear-unitary-cuspidality>

#example[
  $U(3, q)$ has a unipotent cuspidal representation of dimension $q^2 - q$. Here
  $Ind_(B^F)^(G^F)(1)$, where $B$ is an $F$-stable Borel subgroup, has two
  constituents whereas $W$ has three irreducible representations; this accounts
  for the extra unipotent representation.
] <exm:unitary-three-unipotent-cuspidal>

The description given for $GL(n, q)$ and $U(n, q)$ does not hold in general. One
reason it works here is that $G = GL_n$ is “self-dual”. We introduce the idea of
a dual group of $G$, which is also related to Langlands's notion of an
$L$-group.

#heading(level: 2, numbering: none)[Dual group] <sec:dual-group>
#term-entry("Dual group")

See [@bib:Lusztig1977a], §7. Let $G, F$ be as usual, and $T$ an $F$-stable
maximal torus. Recall from Chapter~@ch:lusztig-deligne that
$X = X(T) = Hom(T, K^*)$ and $Y = Y(T) = Hom(K^*, T)$ are $ZZ$-duals. The roots
$Phi$ form a subset of $X$. A subset $Phi^∨$ of $Y$ defines the dual root system
to $Phi$ (see [@bib:Bourbaki1968], p.~277), and its elements are called coroots.
The data ${X, Y, Phi, Phi^∨}$ determine $G$ up to isomorphism (see
[@bib:Grothendieck1970], Exposé XXV). The morphism $F$ acts on $X$ and $Y$. The
group $G^F$ is determined by the actions of $F$ and $q^(-1) F$, which has finite
order, on $Y$. Reversing $X$ and $Y$ and replacing the root system by its dual
gives the data ${Y, X, Phi^∨, Phi}$ determining a connected reductive group
$G^*$, the dual of $G$.

#source(152)
Then $G^*$ is defined over $FF_q$ and has an $F$-stable maximal torus $T^*$ dual
to $T$, so $X(T^*) = Y(T)$ and $Y(T^*) = X(T)$. Their Weyl groups are
identified. There is a natural correspondence between characters of $T^F$ and
elements of $T^(* F)$, since $hat(T)^F tilde.eq X(T) / (F - 1) X(T)$ and
$T^(* F) tilde.eq Y(T^*) / (F - 1) Y(T^*)$
(see @eq:torus-cocharacter-exact-sequence). A similar exact sequence
$ 0 -> X(T) arrow.r.long^(F - 1) X(T) -> hat(T)^F -> 0 $
is obtained by restricting characters to $T^F$ and composing with a fixed
isomorphism of $K^*$ into $overline(QQ)_ell^*$. For $theta in hat(T)^F$ we
obtain $s in T^(* F)$, well-defined up to conjugacy by an element of $N(T^*)^F$.
Instead of $R_T^(G)(theta)$ we can speak of $R_(T^*)^(G)(s)$ for $s in G^(* F)$.
The Strong Orthogonality Theorem (@cor:geometrically-distinct-disjoint) may then
be restated as follows.

#theorem[
  ([@bib:Curtis1975], 5.21; [@bib:Lusztig1977a], 7.5.2.) The virtual
  representations $R_(T_1^*)^(G)(s_1)$ and $R_(T_2^*)^(G)(s_2)$ are disjoint
  unless $s_1$ and $s_2$ are $G^(* F)$-conjugate.
] <th:dual-semisimple-disjointness>

The finite groups $G^F$ and $G^(* F)$ are also called duals. There is a
bijection between $G^F$-conjugacy classes of regular subgroups of $G$ and
$G^(* F)$-conjugacy classes of regular subgroups of $G^*$.

#source(153)
#heading(level: 3, numbering: none)[Examples of dual
  groups] <ss:dual-group-examples>

#table(
  columns: 2,
  align: center,
  table.header([$G$], [$G^*$]),
  [$SL_n$], [$PGL_n$],
  [$GL_n$], [$GL_n$],
  [$Sp_(2n)$], [$SO_(2n + 1)$],
  [$SO_(2n)^±$], [$SO_(2n)^±$],
  [$op("CSp")_(2n)$], [$G_(2n + 1)^circle$],
  [$op("CO")_(2n)^(±, circle)$], [$G_(2n)^(±, circle)$],
)

#table(
  columns: 2,
  align: center,
  table.header([$G^F$], [$G^(* F)$]),
  [$SL(n, q)$], [$PGL(n, q)$],
  [$GL(n, q)$], [$GL(n, q)$],
  [$U(n, q)$], [$U(n, q)$],
  [$Sp(2n, q)$], [$SO(2n + 1, q)$],
  [$SO^(±)(2n, q)$], [$SO^(±)(2n, q)$],
)

Here $op("CSp")_(2n)$ is the group of symplectic similitudes and
$op("CO")_(2n)^(±, circle)$ is the identity component of the group of
similitudes of a quadratic form over $FF_q$, split $(+)$ or nonsplit $(-)$. The
groups $G_(2n + 1)^circle$ and $G_(2n)^(±, circle)$ are the special Clifford
groups of quadratic forms over $FF_q$ in dimensions $2n + 1$ and $2n$. The
homomorphisms $G_(2n + 1)^circle -> SO_(2n + 1)$ and
$G_(2n)^(±, circle) -> SO_(2n)^±$ induce surjective homomorphisms of finite
groups $(G_(2n + 1)^circle)^F -> (SO_(2n + 1))^F$ and
$(G_(2n)^(±, circle))^F -> (SO_(2n)^±)^F$, with central kernels of order $q - 1$
(see [@bib:Lusztig1977a], p.~154).

The next section describes centralizer algebras of representations of $G^F$
induced from certain representations of parabolic subgroups. These algebras are
also called Hecke algebras in the literature. #source(154)

#heading(level: 2, numbering: none)[Centralizer
  algebras] <sec:centralizer-algebras>
#term-entry("Centralizer algebras")

References for this section are [@bib:Curtis1979], §3; [@bib:Curtis1972];
[@bib:Lusztig1975], §5; [@bib:Lusztig1977a], §5; and [@bib:Bourbaki1968],
pp.~54–55.

In this section $B_0$ and $T_0$ denote an $F$-stable Borel subgroup and an
$F$-stable maximal torus contained in it, as in
Chapter~@ch:classification-of-tori.

Recall from the Harish–Chandra theory of Chapter~@ch:harish-chandra that one of
our problems is to decompose $Ind_(P^F)^(G^F)(tilde(rho))$, where $tilde(rho)$
is the lift to $P^F$ of a cuspidal representation $rho$ of $L^F$. Every
irreducible representation of $G^F$ occurs as a constituent of such a
representation.

In particular, $Ind_(B_0^F)^(G^F)(1)$, and more generally
$Ind_(B_0^F)^(G^F)(tilde(lambda))$ for $lambda in hat(T)_0^F$, give the
principal series of $G^F$. The former was studied by Curtis, Iwahori, and
Kilmoyer [@bib:Curtis1972]; the latter by Kilmoyer [@bib:Kilmoyer1978] for $G$
of adjoint type, and by Kilmoyer and Howlett [@bib:Howlett1980] in general, in
fact for finite groups with a split $B N$-pair. We begin with the centralizer
algebra of $Ind_(B_0^F)^(G^F)(1)$.

Let $(W, S)$ be a finite Coxeter group (see [@bib:Bourbaki1968]). Thus $W$ has
distinguished generators #source(155) ${w_i}$, with $w_i in S$, and defining
relations $(w_i w_j)^(m_(i j)) = 1$, where $m_(i i) = 1$ for every $i$. For
$w in W$, $ell(w)$ is the minimum number of generators in an expression for $w$
as a product of distinguished generators.

Let $R = QQ[X_1, X_2, dots, X_n]$ be the polynomial ring over $QQ$ in
indeterminates $X_i$ corresponding to the $w_i$, with $X_i = X_j$ whenever $w_i$
and $w_j$ are conjugate in $W$. For example, when $W$ is the Weyl group of an
indecomposable root system, $R$ is a polynomial ring in one or two generators.
The _generic algebra_#term-entry("Generic algebra") $A_W$ over $R$ has basis
${T_w | w in W}$, with $T_1 = 1$, and multiplication

$
  T_(w_i) T_w = cases(
    T_(w_i w) & "if" ell(w_i w) >= ell(w),
    X_i T_(w_i w) + (X_i - 1) T_w & "if" ell(w_i w) < ell(w),
  ).
$ <eq:generic-hecke-multiplication>

It can be shown ([@bib:Curtis1972], 1.8) that $A_W$ has a presentation with
relations

$
  T_(w_i)^2 &= X_i 1 + (X_i - 1) T_(w_i), \
  underbrace(T_(w_i) T_(w_j) T_(w_i) dots, m_(i j))
  &= underbrace(T_(w_j) T_(w_i) T_(w_j) dots, m_(i j))
  quad (i != j).
$

A _specialization_ of $R$ is a homomorphism $f: R -> QQ$ with
$X_i |-> q_i in QQ$. It gives an algebra $A_f$ over $QQ$ with basis
${T_w^- | w in W}$ and multiplication defined by
@eq:generic-hecke-multiplication with $X_i$ replaced by $q_i$.

#source(156)
For a group $G^F$, the centralizer algebra of $Ind_(B_0^F)^(G^F)(1)$ is
isomorphic to $A_f$ for a suitable specialization, with Coxeter group
$W(T_0)^F$. This follows from Iwahori and Matsumoto's presentation of that
centralizer algebra (see [@bib:Curtis1972], 1.6). If $G$ is split over $FF_q$,
i.e., $T_0$ is split, and $F$ is standard, then $f(X_i) = q$ for every $i$. If
$G = GL_n$ and $F$ is twisted, so $G^F = U(n, q)$, we may take
$R = QQ[X_1, X_2]$, with $f(X_1) = q$, $f(X_2) = q^2$ for even $n$, and
$f(X_1) = q^2$, $f(X_2) = q^3$ for odd $n$. Kilmoyer [@bib:Kilmoyer1978]
similarly showed that for adjoint $G$ and any $lambda in hat(T)_0^F$, the
centralizer algebra of $Ind_(B_0^F)^(G^F)(tilde(lambda))$ is $A_f$ for a
suitable generic algebra $A_W$.

Let $frak(J)$ be the quotient field of $R$, $overline(frak(J))$ an algebraic
closure, and $overline(R)$ the integral closure of $R$ in it. For an irreducible
character $chi$ of $A_W ⊗_R overline(frak(J))$, we have
$chi(T_w) in overline(R)$ for every $w in W$. Under the specialization $f$ above
we obtain an irreducible character of $A_f ⊗_QQ CC$ corresponding to a
constituent of $Ind_(B_0^F)^(G^F)(1)$. There is also an element
$d_chi in overline(frak(J))$, the _generic degree_ corresponding to $chi$, given
by #source(157)

$
  d_chi = (dim chi sum_(w in W) Ind T_w)
  / (sum_(w in W) (Ind T_w)^(-1) chi(T_w) chi(T_(w^(-1)))).
$

Here $Ind$ is the homomorphism $A_W -> R$ defined by $Ind(T_(w_i)) = X_i$. The
crucial point is that, under $f$, or more precisely an extension of $f$ to
$overline(R) -> CC$, $d_chi$ becomes the dimension of the constituent $phi$ of
$Ind_(B_0^F)^(G^F)(1)$ corresponding to $chi$. Thus explicit expressions for
$d_chi$ in terms of the $X_i$ compute the dimensions of principal series
representations. Generic degrees have been computed for all indecomposable Weyl
groups except type $F_4$ with $R = QQ[X_1, X_2]$; even there most are known. For
classical groups this was done by Hoefsmit [@bib:Hoefsmit1974], and for
exceptional groups by Benson, Grove, and Surowski [@bib:Benson1975] and by
Benson [@bib:Benson1979].

We now turn to Lusztig's more recent work ([@bib:Lusztig1975],
[@bib:Lusztig1977a], [@bib:Lusztig1978]) on centralizer algebras of
$Ind_(P^F)^(G^F)(tilde(rho))$ for unipotent cuspidal representations $rho$ of
$L^F$. First we describe specializations of the generic algebra in another way.
Let $(W, S)$ be a Coxeter group and $phi: S -> overline(QQ)_ell$ satisfy
$phi(s) = phi(s')$ whenever $s, s'$ are conjugate in $W$. Let $cal(H)(W, phi)$
be the $overline(QQ)_ell$-algebra with basis ${T_w | w in W}$ and multiplication
defined by

$
  T_w T_(w') = T_(w w') quad "if" quad
  ell(w w') = ell(w) + ell(w'),
$
$ (T_s + 1)(T_s - phi(s)) = 0 quad "for all" quad s in S. $

Next, we note that if $rho$ is a unipotent cuspidal representation of $L^F$ then
$Ind_(P^F)^(G^F)(tilde(rho))$ contains only unipotent representations, and
conversely if $rho$ is a unipotent representation of $G^F$ which corresponds to
an $F$-stable parabolic subgroup $P$ in the Harish-Chandra classification then
$rho$ is a constituent of $Ind_(P^F)^(G^F)(tilde(rho)_0)$ where $rho_0$ is a
unipotent cuspidal representation of $L^F$ (see e.g. [@bib:Curtis1976], 1.2).
The following theorem follows from Lusztig's work. #source(158)

#theorem[
  Let $P$ be an $F$-stable parabolic subgroup of $G$ and let $P = L V$ where $L$
  is $F$-stable. Let $rho_0$ be a cuspidal unipotent representation of $L^F$.
  Then the centralizer algebra of $E = Ind_(P^F)^(G^F)(tilde(rho)_0)$ is
  isomorphic to $cal(H)(W_0, phi)$ where $(W_0, S)$ is a suitable Coxeter group
  and $phi: S -> overline(QQ)_ell$ is a suitable function. The isomorphism is
  _special_ in the sense that the basis elements $T_w$ ($w != 1$) of
  $cal(H)(W_0, phi)$ correspond to endomorphisms of $E$ of trace zero.
] <th:unipotent-centralizer-algebra>

We give a brief discussion of this theorem. Suppose $G$ has a connected Dynkin
graph $Gamma$. Suppose we are given a unipotent non-cuspidal representation
$rho$ of $G^F$. We can find a suitable $F$-stable parabolic subgroup $P_1$,
where $P_1 = L_1 V_1$ and $L_1$ is $F$-stable, such that $rho$ is a constituent
of $Ind_(P_1^F)^(G^F)(tilde(rho)_1)$ and $rho_1$ is a unipotent cuspidal
representation of $L_1^F$. Then $L_1$ also has a connected Dynkin graph $Gamma'$
and it can be shown that $rho_1$ is uniquely determined by $rho$. (In most
cases, this follows from the fact that $L_1^F$ has a unique unipotent cuspidal
representation.) Moreover, $Gamma'$ is the unique $F$-stable subgraph of its
type of $Gamma$. #source(159)

Conversely, suppose $P$ is $F$-stable and $L$ has a Dynkin graph $Gamma'$ which
is an $F$-stable subgraph of $Gamma$. Suppose $rho_0$ is a unipotent cuspidal
representation of $L^F$. Let $overline(Gamma)$ be a graph whose vertices are in
bijection with the orbits of $F$ on $Gamma - Gamma'$. For two such orbits
$gamma, gamma'$ we define

$
  m_(gamma, gamma') =
  (2(abs(Phi_(Gamma' ∪ gamma ∪ gamma')) - abs(Phi_(Gamma'))))
  / (abs(Phi_(Gamma' ∪ gamma)) + abs(Phi_(Gamma' ∪ gamma'))
  - 2 abs(Phi_(Gamma'))),
$

where $Phi_(Gamma'), dots$ denote the set of roots of a root system of type
$Gamma', dots$. Then $m_(gamma, gamma') = 2, 3, 4$ or $6$, and, as usual, we
join the vertices of $overline(Gamma)$ corresponding to $gamma$ and $gamma'$ by
$0, 1, 2$ or $3$ bonds in the four cases. The resulting graph is a graph of a
Coxeter group $W_0$. A suitable function $phi$ is then defined on the set $S$ of
simple reflections of $W_0$ and the centralizer algebra of $E$ is shown to be
isomorphic to $cal(H)(W_0, phi)$. For a case-by-case list of
$Gamma, Gamma', overline(Gamma)$ and $phi$ see [@bib:Lusztig1978], p. 35. A
discussion of the above results is also on pp. 33–34, loc. cit.

In fact, the group $W_0$ is isomorphic to $(N(L) / L)^F$. It is not usually the
case that this group turns out to be a Coxeter group (it is a section of the
Weyl group $W(T_0)$ of $G$). Lusztig ([@bib:Lusztig1975], 5.9) proves that it is
a Coxeter group if the Weyl group of $L$ satisfies a certain assumption
([@bib:Lusztig1975], 5.7.1) on subsets of the set of simple reflections being
stable under conjugation by the longest element. This assumption is satisfied in
all the cases when $L^F$ has a unipotent cuspidal representation. (For example,
if $L$ is of type $A$ and $G$ is of type $D$ it is not satisfied, but untwisted
groups of type $A$ have no unipotent cuspidal representations. Another such
example is when $L$ is of type $D_5$ and $G$ is of type $E_6$; again $L^F$ has
no unipotent cuspidal representations.) #source(160)

Theorem~@th:unipotent-centralizer-algebra is proved when $G$ is classical in
[@bib:Lusztig1977a], §5 (see especially 5.15). When $G$ is exceptional it is
proved in [@bib:Lusztig1975], §5; here it is assumed that the unipotent cuspidal
representation $rho$ is contained in $R_T^(L)(1)$ where $T$ is a “Coxeter
torus.” However, for $E_6$ and $E_7$ all unipotent cuspidal representations are
of this form, whereas the other groups do not appear in the form of a subgroup
$L$ inside a bigger group $G$. Another assumption on $rho$ needed for the
theorem is that it is extendible to a representation of $N(L)^F$. This is also
true in all the cases; in most cases it follows because it is the only unipotent
cuspidal representation. If this is not so, it follows from [@bib:Lusztig1975],
Lemma 6.6.

#heading(level: 2, numbering: none)[Representations of classical
  groups] <sec:classical-group-representations>

([@bib:Lusztig1977a], [@bib:Lusztig1978]). We have seen that in the case of
$GL(n, q)$ and $U(n, q)$ the unipotent representations are parametrized by
partitions of $n$.

Thus it would appear as a first guess that in the case of groups of types
$B, C, D$ (i.e., the classical groups), pairs of partitions have to be used
since they parametrize the conjugacy classes of the Weyl group of type $B$.
However, this does not work, and neither do we get formulas for the unipotent
representations as in @th:general-linear-unitary-unipotent-characters (except
for the trivial or Steinberg representations). In fact, the number of unipotent
representations is not equal to the number of $F$-conjugacy classes of the Weyl
group, in general. Lusztig has introduced certain combinatorial objects called
“symbols” and shown that these parametrize the unipotent representations of
finite classical groups. We will now describe this result. #source(161)

The idea is this: a partition of $n$ can either be thought of as a decreasing
sequence of integers $alpha_1 >= alpha_2 >= dots >= alpha_m$ with
$alpha_1 + alpha_2 + dots + alpha_m = n$, or, taking
$lambda_i = alpha_i - i + m$ ($1 <= i <= m$) as an array of integers
$lambda_1 > lambda_2 > dots > lambda_m$. This is generalized as follows. A
_symbol_#term-entry("Symbol") is an array of the form

$
  Lambda = mat(
    lambda_1 > lambda_2 > dots > lambda_a;
    mu_1 > mu_2 > dots > mu_b
  )
$

where the $lambda_i, mu_i$ are non-negative integers. We say that $Lambda$ is
equivalent to

$
  mat(
    lambda_1 + 1 > lambda_2 + 1 > dots > lambda_a + 1 > 0;
    mu_1 + 1 > mu_2 + 1 > dots > mu_b + 1 > 0
  )
$

or to

$
  mat(
    mu_1 > mu_2 > dots > mu_b;
    lambda_1 > lambda_2 > dots > lambda_a
  ).
$

#definition[
  #enum(
    numbering: "(i)",
    [$op("def") Lambda = abs(a - b)$ is the _defect_ of $Lambda$.],
    [$rk Lambda = sum_i lambda_i + sum_i mu_i
      - floor(((a + b - 1) / 2)^2)$ is the _rank_ of $Lambda$.],
  )
] <def:symbol-defect-rank>

The defect and rank are functions on the set of equivalence classes of symbols.
#source(162)

#definition[
  $Phi_(n, d)$ is the set of equivalence classes of symbols of rank $n$ and
  defect $d$.
] <def:symbol-classes>

#definition[
  If $Lambda = mat(
    lambda_1 > lambda_2 > dots > lambda_a;
    mu_1 > mu_2 > dots > mu_b
  )$, then

  $
    D_(Lambda)(q) & =
                    (product_(i < j)(q^(lambda_i) - q^(lambda_j))
                    product_(i < j)(q^(mu_i) - q^(mu_j)))
                    / ((product_(i=1)^a (q^2 - 1) dots (q^(2 lambda_i) - 1))
                    (product_(i=1)^b (q^2 - 1) dots (q^(2 mu_i) - 1))) \
                  & quad dot (product_(1 <= i <= a, 1 <= j <= b)
                    (q^(lambda_i) + q^(mu_j)))
                    / (2^c q^(binom(a+b-2, 2)+binom(a+b-4, 2)+dots)),
  $

  where

  $
    c = cases(
      floor((a+b-1)/2) & "if" quad
      {lambda_1, lambda_2, dots, lambda_a} != {mu_1, mu_2, dots, mu_b},
      a = b & "otherwise."
    )
  $
] <def:symbol-degree>

#theorem[
  ([@bib:Lusztig1977a], 8.2). There exists a bijection between the unipotent
  representations of the groups

  #enum(
    numbering: "(i)",
    [$Sp(2n, q)$ and equivalence classes of symbols of rank $n$ and odd
      defect;],
    [$SO(2n + 1, q)$ and equivalence classes of symbols of rank $n$ and odd
      defect;],
    [$SO^+(2n, q)$ and equivalence classes of symbols of rank $n$ and defect
      $equiv 0 (mod 4)$;],
    [$SO^-(2n, q)$ and equivalence classes of symbols of rank $n$ and defect
      $equiv 2 (mod 4)$, with symbols having equal rows counted twice in Case
      (iii).],
  )

  If the correspondence is ${Lambda} -> rho_Lambda$ where $Lambda$ is a symbol
  and $rho_Lambda$ is a unipotent representation of the group in question,
  $rho_Lambda$ is cuspidal if and only if
  $rk Lambda = n = floor((op("def") Lambda / 2)^2)$, and there is at most one
  such representation. Cuspidal representations occur precisely when
  $n = k^2 + k$ for some $k$ in Cases (i) and (ii), $n = k^2$ for some even $k$
  in Case (iii), and $n = k^2$ for some odd $k$ in Case (iv). Finally we have
  #source(163)

  $ dim rho_Lambda = D_(Lambda)(q) abs(G^F)_(p'), $ <eq:unipotent-symbol-degree>

  where $G^F$ is a group as in (i), (ii), (iii) or (iv).
] <th:classical-unipotent-symbols>

We will return to this theorem after stating another theorem
(@th:classical-jordan-decomposition), which brings out the importance of knowing
the unipotent representations. As before we let $G^*$ denote the dual group of
$G$. We can write $cal(E)(G) = ⨆_((s)) cal(E)(G, (s))$ where $s$ runs over a set
of representatives of $G^(*F)$-conjugacy classes of semisimple elements of
$G^(*F)$, and

$
  cal(E)(G, (s)) = {rho in cal(E)(G) |
    chevron.l rho, R_(T^*)^(G)(s) chevron.r != 0}
$

for some $F$-stable maximal torus $T^* subset G^*$, $s in T^(*F)$.

Note that $cal(E)(G, (1))$ is the set of unipotent representations of $G^F$.

#theorem[
  ([@bib:Lusztig1977a], 8.2). Let $G$ be one of the following groups.

  (a) $G = Sp_(2n)$, $q$ even, $n >= 1$; $G^* = SO_(2n+1)$.

  (b) $G = SO_(2n)^±$, $q$ even, $n >= 2$; $G^* = SO_(2n)$.

  (c) $G = SO_(2n+1)$, $q$ odd, $n >= 1$; $G^* = Sp_(2n)$.

  (d) $G = op("CSp")_(2n)$, $q$ odd, $n >= 1$; $G^* = G_(2n+1)^0$. #source(164)

  (e) $G = op("CO")_(2n)^(±,0)$, $q$ odd, $n >= 2$; $G^* = G_(2n)^(±,0)$.

  Then there is a bijection, for each $s in G^(*F)$,
  $alpha: cal(E)(lr(C_(G^*)(s))^*, (1)) -> cal(E)(G, (s))$, such that

  $
    dim alpha(rho) = (abs(G^(*F))_(p'))
    / (abs(lr(C_(G^*)(s))^F)_(p')) (dim rho).
  $ <eq:jordan-decomposition-degree>
] <th:classical-jordan-decomposition>

#remark[
  This theorem can be regarded as giving a “Jordan decomposition” for
  representations of $G^F$ in the sense that each irreducible representation of
  $G^F$ is associated with a semisimple element $s$ of $G^(*F)$ and a unipotent
  representation of $lr(C_(G^*)(s))^(*F)$. Lusztig has conjectured that such a
  theorem holds in general for all $G$ and not just for classical groups.
] <rem:jordan-decomposition>

At this point we prove a result about dimensions of unipotent representations
which will be used later. By @th:regular-representation-decomposition, if $rho$
denotes the regular representation of $G^F$ we have

$
  rho = 1 / abs(G^F)_p sum_T sum_(theta in hat(T))
  epsilon_G epsilon_T R_T^(G)(theta), quad "and hence"
$

$
  & sum_(phi in cal(E)(G), phi "unipotent") (dim phi) phi
    + sum_(phi in cal(E)(G), phi "non-unipotent") (dim phi) phi \
  & = 1 / abs(G^F)_p
    (sum_T epsilon_T epsilon_G R_T^(G)(1)
      + sum_(T, theta, theta != 1) epsilon_T epsilon_G R_T^(G)(theta)).
$

Hence, using @cor:geometrically-distinct-disjoint we have

$
  sum_(phi "unipotent") (dim phi) phi
  = 1 / abs(G^F)_p sum_T epsilon_T epsilon_G R_T^(G)(1).
$

Using the dimension formula @th:lusztig-deligne-dimension we then get

$
  sum_(phi "unipotent") (dim phi)^2
  &= 1 / abs(G^F)_p sum_T (abs(G^F)_(p')) / abs(T^F) \
  &= 1 / abs(G^F)_p sum_((T)) abs(G^F)
  / (abs(T^F) abs(W(T)^F)) dot (abs(G^F)_(p')) / abs(T^F).
$

Thus, using @th:torus-order we get #source(165)

$
  sum_(phi "unipotent") (dim phi)^2
  = 1 / abs(W) sum_(w in W) (abs(G^F)_(p'))^2
  / abs(det(w F - 1))^2.
$ <eq:unipotent-degrees-square-sum>

The rest of this section will be devoted to a discussion of the proofs of
@th:classical-unipotent-symbols and @th:classical-jordan-decomposition.

Consider a classical Weyl group, i.e., of type $A, B$ or $D$. Denote by
$cal(H)_(n)(q, y)$ the algebra $cal(H)(W_n, phi)$ where $W_n$ is the Weyl group
of type $B_n$ and $phi(w_j) = q$ ($1 <= j <= n-1$), $phi(w_n) = y$ for some $y$
in $overline(QQ)_ell$, $w_1, w_2, dots, w_n$ being the fundamental reflections,
i.e., the elements of $S$, where $w_n$ corresponds to the short root. Let
$tilde(cal(H))_(n)(q)$ be the algebra $cal(H)(tilde(W)_n, phi)$ where
$tilde(W)_n$ is of type $D_n$ and $phi(s) = q$ for all $s$. Hoefsmit
[@bib:Hoefsmit1974] has described the representations of $cal(H)_(n)(q, y)$ and
$tilde(cal(H))_(n)(q)$. Lusztig gives an alternative description of the
representations in terms of symbols, rather than pairs of partitions, and proves
the following proposition.

#proposition[
  ([@bib:Lusztig1977a], 4.6.2). There exists a bijection between the set
  $cal(H)_(n)(q, q^d)^∨$ of irreducible representations over $overline(QQ)_ell$
  of $cal(H)_(n)(q, q^d)$ and the set $Phi_(n', d)$ of equivalence classes of
  symbols of rank $n'$ and defect $d$, where $n' = n + floor((d/2)^2)$. Suppose
  there is a _special_ (see @th:unipotent-centralizer-algebra) homomorphism
  $cal(H)_(n)(q, q^d) -> End E$, where $E$ is a finite-dimensional
  $overline(QQ)_ell$-vector space. If $E_0 in cal(H)_(n)(q, q^d)^∨$ corresponds
  to $(Lambda) in Phi_(n', d)$, the multiplicity of $E_0$ in the
  $cal(H)_(n)(q, q^d)$-module $E$ is given by #source(166)

  $ (dim E) D_(Lambda)(q) D_(([0,d-1],emptyset))(q)^(-1) (q-1)^n. $

  Here $([0,d-1], emptyset)$ stands for the symbol whose two rows are
  ${d-1 > dots > 0}$ and $emptyset$.
] <prop:hecke-symbol-multiplicity>

A similar proposition ([@bib:Lusztig1977a], 4.7.1) holds for the algebra
$tilde(cal(H))_(n)(q)$.

We will mainly describe the easiest case of @th:classical-unipotent-symbols and
@th:classical-jordan-decomposition, i.e., $G = Sp(2n, q)$, $G^* = SO(2n+1, q)$,
$n >= 1$, $q$ even. Then we wish to show the following.

#proof-claim[
  There is a bijection $(Lambda) <-> rho_Lambda$ between
  $Phi_n = ⨆_(d "odd") Phi_(n, d)$ and $cal(E)(G, (1))$ and the dimension of
  $rho_Lambda$ is given by @eq:unipotent-symbol-degree.
] <claim:unipotent-symbol-induction>

#proof-claim[
  If $(s)$ is a semisimple class of $G^*$, there is a bijection
  $alpha: cal(E)(lr(C_(G^*)(s))^*, (1)) <-> cal(E)(G, (s))$ such that
  $dim alpha(rho)$ is given by @eq:jordan-decomposition-degree.
] <claim:jordan-series-induction>

We first check that the theorem is true for $n = 1$ and assume that it is true
for $n' < n$. Now let $s in G^(*F)$, where $s != 1$ is semisimple. We choose a
regular subgroup $L'$ of $G^*$ such that $C_(G^*)(s) subset L'$. (This can
always be done in the case when $q$ is even; in classical groups the only
semisimple elements for which this fails to hold are elements with eigenvalues
$±1$ in the natural representation.) Then there is a regular subgroup $L$ of $G$
corresponding to $L'$. To prove @claim:jordan-series-induction it is then enough
to show that the conjugacy class of $s$ in $L'^F$ has the property
@claim:jordan-series-induction with respect to $L'$, i.e., that we have a
bijection $cal(E)(lr(C_(L')(s))^*, (1)) -> cal(E)(L, (s))$. For, composing this
with the bijection $cal(E)(L, (s)) <-> cal(E)(G, (s))$ obtained from the map
$rho -> epsilon_G epsilon_L R_L^(G)(rho)$ ($rho in cal(E)(L, (s))$) and noting
that $C_(L')(s) approx C_(G^*)(s)$, we have @claim:jordan-series-induction. If
all the semisimple components of $L'$ (and hence of $L$) are of type $A$ then we
are done, by the description of the representations of $GL(n, q)$ and $U(n, q)$
given earlier. If not, $L$ has a component isomorphic to $Sp_(2m)$ for some
$m < n$ and we can use the induction hypothesis. Thus
@claim:jordan-series-induction holds. #source(167)

We now consider @claim:unipotent-symbol-induction. We make the following
definitions:

#definition[
  #enum(
    numbering: "(i)",
    [$B(G^F)$ is the number of conjugacy classes of $G^F$.],
    [$B_1(G^F)$ is the number of unipotent conjugacy classes of $G^F$.],
  )
] <def:conjugacy-class-counts>

We show that in fact $B_1(G^F) = abs(cal(E)(G, (1)))$. (This is false if $q$ is
odd.) Since $q$ is even, we have an isogeny $SO_(2n+1) -> Sp_(2n)$ which leads
to a bijection $(s) <-> (s')$ between classes of semisimple elements of $G^F$
and $G^(*F)$ such that $C_(G)(s) approx lr(C_(G^*)(s'))^*$. Thus

$
  abs(cal(E)(G)) & = sum_((s')) abs(cal(E)(lr(C_(G^*)(s'))^*, (1))),
                   quad "by" #[@claim:jordan-series-induction] \
                 & = sum_((s)) abs(cal(E)(C_(G)(s), (1))).
$

Now the groups $lr(C_(G)(s))^F$ are products of symplectic groups, general
linear groups, or unitary groups (possibly over extensions of $FF_q$ in the last
two cases). For general linear groups or unitary groups, the number of unipotent
representations is equal to the number of unipotent conjugacy classes, as we
have seen. Using this fact and induction on $n$ we may assume that
$abs(cal(E)(C_(G)(s), (1))) = B_1(lr(C_(G)(s))^F)$ whenever $s != 1$. But we
have $B(G^F) = sum_((s)) B_1(lr(C_(G)(s))^F)$ by the Jordan decomposition for
elements of $G^F$. This shows that $B_1(G^F) = abs(cal(E)(G, (1)))$, as claimed.
Thus it is sufficient to show that $B_1(G^F) = abs(Phi_n)$. Lusztig proves
([@bib:Lusztig1977a], 3.4.1) that #source(168)

$
  sum_(n=0)^infinity abs(Phi_n) t^n
  = product_(i=1)^infinity (1-t^i)^(-2)
  sum_(j=0)^infinity t^(j(j+1)).
$

Then it follows from a formula of Wall [@bib:Wall1963] for the number of
unipotent classes of $Sp(2n, q)$ ($q$ even) and an identity of Andrews
[@bib:Andrews1977] that the right hand side of this identity is also
$sum_(n=0)^infinity B_1(G^F) t^n$. This proves the first part of
@claim:unipotent-symbol-induction.

Next we consider the second part of @claim:unipotent-symbol-induction and also
when unipotent cuspidal representations occur in this case. The idea is to
induce unipotent cuspidal representations from parabolic subgroups, consider
their constituents which are non-cuspidal unipotent representations of $G^F$,
and see what unipotent representations remain, if any.

Let $L' != G^*$ be a regular subgroup of $G^*$ which is contained in an
$F$-stable parabolic subgroup. Corresponding to $L'$ we have a regular subgroup
$L$ of $G$ which is contained in an $F$-stable parabolic subgroup $P$ of $G$.
Suppose $cal(E)(L, (1))$ contains some cuspidal representation; then no
component of $L$ can be of type $A$ since $GL(n, q)$ has no unipotent cuspidal
representations. Thus $L$ is isomorphic over $FF_q$ to $S times G_1$ where $S$
is a torus and $G_1 approx Sp_(2m)$ for some $m < n$. By the induction
hypothesis we must have $m = floor((d/2)^2)$ for some odd integer $d$ and
$G_1^F$ has a unique unipotent cuspidal representation. By combining it with the
trivial representation of $S$ we get a unipotent representation $rho$ of $L^F$.
We then consider $E = Ind_(P^F)^(G^F)(tilde(rho))$ and use
@prop:hecke-symbol-multiplicity to study the constituents of $E$. The discussion
following @th:unipotent-centralizer-algebra shows that the centralizer algebra
of $E$ is of the form $cal(H)_(n-m)(q, y)$ for some $y$. In order to pin down
$y$ we make the following induction assumption. #source(169)

#formula-item[
  If $cal(E)(G, (1))$ contains _subcuspidal_ representations, i.e.,
  representations which are constituents of representations induced from a
  _maximal_ parabolic subgroup whose inducing representation is cuspidal on its
  Levi factor, then there are exactly two of these and the ratio of their
  dimensions is $q^t$ where $floor((t/2)^2) = floor((dim V'' - 2) / 2)$. Here
  $V''$ is the $FF_q$-space on which $G^*$ acts in its natural representation.
] <eq:subcuspidal-induction-assumption>

Now suppose $m <= n-2$. Then $P^F$ is not a maximal parabolic subgroup of $G^F$
and there is a proper subgroup of $G^F$ containing $P^F$ as a maximal parabolic
subgroup to which @eq:subcuspidal-induction-assumption applies. The power of $q$
appearing there is then $q^d$, where $m = floor((d/2)^2)$. Then it can be shown
([@bib:Lusztig1977a], 5.15) that this is exactly the parameter $y$, i.e., that
the centralizer algebra of $E$ is isomorphic to $cal(H)_(n-m)(q, q^d)$. The
constituents of $E$ are in bijection with the elements of
$cal(H)_(n-m)(q, q^d)^∨$ and thus with the elements of $Phi_(n, d)$, by
@prop:hecke-symbol-multiplicity. Moreover, using @prop:hecke-symbol-multiplicity
we can also show that if $(Lambda) in Phi_(n, d)$ corresponds to a constituent
$rho_Lambda$ of $E$, then $dim rho_Lambda = D_(Lambda)(q) abs(G^F)_(p')$.
#source(
  170,
)

If $m = n-1$, then we know that the centralizer algebra of $E$ is isomorphic to
$cal(H)_1(q, y)$ for some $y$ which is not known. But in this case
$cal(H)_1(q, y)$ is of dimension $2$ and $E$ has two irreducible constituents.
These correspond to the two classes of symbols of rank $floor((d/2)^2) + 1$ and
defect $d$, namely, the classes of

$
  mat(d > d-1 > dots > 0; 1) quad "and" quad
  mat(d > d-2 > d-3 > dots > 1 > 0; emptyset).
$

The sum of $D_(Lambda)(q)$ for these two $(Lambda)$ is checked to be
$D_(lambda_0)(q) (q-1)^(-1)$ where
$lambda_0 = mat(d-1 > d-2 > dots > 0; emptyset)$, and thus we get, in this case

$
  sum_((Lambda) in Phi_(n, d)) dim rho_Lambda
  = sum_((Lambda)) D_(Lambda)(q) abs(G^F)_(p').
$ <eq:subcuspidal-degree-sum>

(Here $floor((d/2)^2) = n-1$.)

Now we have shown that the number of unipotent representations is $abs(Phi_n)$,
and $abs(Phi_n) = sum_(floor((d/2)^2) <= n, d "odd") abs(Phi_(n, d))$. Now all
the non-cuspidal unipotent representations have been accounted for and they are
in bijection with $union.big_(floor((d/2)^2) <= n-1) Phi_(n, d)$. Also we have
$abs(Phi_(n, d)) = 1$ if $n = floor((d/2)^2)$ since the only symbol of rank
$floor((d/2)^2)$ and defect $d$, up to equivalence, is $lambda_0$ defined above.
Thus the number of unipotent cuspidal representations is $1$ if
$n = floor((d/2)^2)$ for some odd $d >= 1$ and $0$ otherwise. If
$n = floor((d/2)^2)$ we associate a unipotent cuspidal representation
$rho_(lambda_0)$ to $lambda_0$. We get a correspondence $(Lambda) -> rho_Lambda$
from $Phi_n$ onto $cal(E)(G, (1))$. It remains to prove the dimension formula
for cuspidal and subcuspidal $rho_Lambda$, and to prove
@eq:subcuspidal-induction-assumption for $G$.
#source(171)

Now we consider the formula @eq:unipotent-degrees-square-sum for
$sum_((Lambda) in Phi_n) (dim rho_Lambda)^2$.

It can be shown ([@bib:Lusztig1977a], 3.5) that

$
  sum_((Lambda) in Phi_n) D_(Lambda)(q)^2
  = 1 / abs(W_n) sum_(w in W_n) 1 / abs(det(w F - 1))^2,
$

and thus we have

$
  sum_((Lambda) in Phi_n) (dim rho_Lambda)^2
  = sum_((Lambda) in Phi_n) D_(Lambda)(q)^2 (abs(G^F)_(p'))^2.
$ <eq:symbol-degrees-square-sum>

If $n = floor((d/2)^2)$ there are no subcuspidal representations since both $n$
and $n-1$ cannot be of the form $t^2 + t$. Similarly if $n-1 = floor((d/2)^2)$
there are no cuspidal representations. So from @eq:subcuspidal-degree-sum and
@eq:symbol-degrees-square-sum and the fact that we have
@eq:unipotent-symbol-degree if $rho_Lambda$ is not cuspidal or subcuspidal, we
get one equation for $dim rho_Lambda$ if $rho_Lambda$ is cuspidal or two
equations for the dimensions of the two subcuspidal $rho_Lambda$. In each case
we find @eq:unipotent-symbol-degree holds. Furthermore in the subcuspidal case
the ratio of the two dimensions is $q^d$ and thus
@eq:subcuspidal-induction-assumption also holds. Thus we have the theorems in
Case (a).

Case (a) is the simplest of all the cases, and although many of the arguments
are similar in the other cases, some new difficulties appear when $q$ is odd. We
will briefly mention these. #source(172)

A semisimple element $s in G^(*F)$ is said to be _exceptional_ if its
centralizer $C_(G^*)(s)$ has the same semisimple rank as $G^*$. On $V''$ (this
is the $FF_q$-space on which $G^*$ acts) an element $s$ of this form has
eigenvalues $1$ or $-1$. For example, if $G^* = Sp_(2n), SO_(2n)$ or
$SO_(2n+1)$, and $s = diag(1, dots, 1, -1, dots, -1)$ then the connected
centralizer of $s$ in $G^*$ is a product of two symplectic groups in the first
case and a product of two orthogonal groups in the other two cases. Such a
centralizer cannot be embedded inside a regular subgroup $L'$, and this is a
source of difficulties in constructing the representations of $G$ in
$cal(E)(G, (s))$.

#example[
  In the character table of $Sp(4, q)$, $q$ odd (see [@bib:Srinivasan1968]), the
  characters denoted by $Phi_9, theta_1, theta_2, theta_3, theta_4$ correspond
  to an exceptional semisimple element in the dual group.
] <exm:exceptional-semisimple-characters>

Suppose, for example, we are in Case (c) of @th:classical-jordan-decomposition
and let $s$ be a semisimple element of $G^(*F)$ whose only eigenvalues on $V''$
are $±1$. In this case we can still embed $s$ in a proper regular subgroup $L'$
of $G^*$ which is contained in an $F$-stable parabolic subgroup, but we might
not have $C_(G^*)(s) subset L'$. We have a corresponding regular subgroup $L$ of
$G$ which is contained in an $F$-stable parabolic subgroup $P$ of $G$. Suppose
$cal(E)(L, (s))$ contains a cuspidal representation. Then $L$ is again of the
form $S times G_1$ where $S$ is a torus and $G_1$ is a special orthogonal group.
Then $cal(E)(L, (s))$ will contain a unique cuspidal representation $rho$ and as
before we would like to decompose $E = Ind_(P^F)^(G^F)(tilde(rho))$. #source(
  173,
)

Now $L'$ is of the form $S' times G'_1$ where $S'$ is a torus and $G'_1$ is a
symplectic group. So we have an orthogonal decomposition of $V''$ as
$V'' = V_0 ⊕ tilde(V)''$ where $G'_1$ is the group of isometries of
$tilde(V)''$. Let $tilde(V)''_1, tilde(V)''_(-1)$ be the $(±1)$-eigenspaces of
$s$ on $tilde(V)''$. Using the fact that $cal(E)(L, (s))$ has a cuspidal
representation which corresponds to a cuspidal representation in
$cal(E)(lr(C_(L')(s))^*, (1))$ we see that there exist odd integers
$d, d^- >= 1$ such that

$
  1/2 dim tilde(V)''_1 = floor((d/2)^2), quad
  1/2 dim tilde(V)''_(-1) = floor((d^-/2)^2).
$

Let $tau = floor(1/2 dim V''_1)$, $tau^- = floor(1/2 dim V''_(-1))$ where
$V''_1, V''_(-1)$ are the $1$ and $(-1)$-eigenspaces of $s$ on $V''$. Then it
can be shown that the centralizer algebra of $E$ is isomorphic to
$cal(H)_(ell)(q, y) ⊗ cal(H)_(m)(q, y')$ for some $y, y'$ where
$ell = tau - floor((d/2)^2)$, $m = tau^- - floor((d^-/2)^2)$. After this, the
analysis proceeds as in Case (a).

#remark[
  We have seen that in two cases, when $E = Ind_(B_0^F)^(G^F)(1)$ or
  $E = Ind_(P^F)^(G^F)(tilde(rho))$ where $rho$ is a unipotent cuspidal
  representation, $End E approx cal(H)(W, phi)$ for a suitable $W$ and $phi$. If
  $rho$ is an arbitrary cuspidal representation of $L^F$ and
  $E = Ind_(P^F)^(G^F)(tilde(rho))$, Springer (see [@bib:Borel1970], C-12)
  conjectured that $End E$ is isomorphic to the group algebra of the stabilizer
  of $rho$ in $N(L)^F / L^F$, twisted by a certain $2$-cocycle. Recently R. B.
  Howlett and G. L. Lehrer have announced a proof of this conjecture. They show
  that the cocycle is trivial if $G$ has a connected center. #source(174)
] <rem:howlett-lehrer-centralizer>

#heading(level: 2, numbering: none)[Exceptional
  groups] <sec:exceptional-group-representations>

([@bib:Lusztig1975], [@bib:Lusztig1979], [@bib:Lusztig1978]). In the classical
groups we have seen that there is at most one unipotent cuspidal representation
in each case. It is this miraculous fact that enables us to classify them using
the dimension equation @eq:unipotent-degrees-square-sum once the non-cuspidal
unipotent representations are known. However, this is not true in the case of
the exceptional groups and the number of unipotent cuspidal representations in
each case is as follows. We also include some twisted groups here.

#table(
  columns: (auto, 1fr, auto),
  table.header([Type], [Number of unipotent cuspidal representations], []),
  [$G_2$], [4], [],
  [$F_4$], [7], [($q$ large)],
  [$E_6$], [2], [],
  [$E_7$], [2], [],
  [$E_8$], [13], [($q$ large)],
  [$attach(D_4, tl: 3)$], [2], [($q$ large)],
  [$attach(E_6, tl: 2)$], [3], [($q$ large)],
  [$attach(B_2, tl: 2)$], [2], [],
  [$attach(G_2, tl: 2)$], [4], [],
  [$attach(F_4, tl: 2)$], [10], [($q$ large)],
) <passage:exceptional-unipotent-cuspidal-counts>

In the case of the exceptional groups Lusztig used another technique to
construct unipotent cuspidal representations (see [@bib:Lusztig1975]). First we
describe, for any $G$, an alternative way of realizing the virtual
representations $R_T^(G)(1)$ ([@bib:Deligne1976], 1.4). We say two Borel
subgroups $B_1, B_2$ of $G$ are in relative position $w$, for some
$w in W(T_0) = W$, if $B_1 = g B_0 g^(-1)$,
$B_2 = g dot(w) B_0 dot(w)^(-1) g^(-1)$ for some $g in G$. Let $X_w$#term-entry(
  "The variety X_w",
  display: [The variety $X_w$],
) be the scheme of all Borel subgroups $B$ such that $B$ and $F B$ are in
relative position $w$. Then $G^F$ acts on $X_w$ by conjugation and hence on
$H_C^(i)(X_w)$. The virtual representation of $G^F$ on
$sum_i (-1)^i H_C^(i)(X_w)$ is the representation $R_w$. So the idea is to try
and decompose the $H_C^(i)(X_w)$ into irreducible constituents. Now $F^delta$
acts on these spaces, where $delta$ is the smallest integer such that $F^delta$
acts trivially on $W$ (thus $delta = 1$ if $G$ is split over $FF_q$). One can
thus consider the eigenspaces of $F^delta$ on $H_C^(i)(X_w)$. #source(175)

#definition[
  The element $f in W$ is a _Coxeter element_ if $f = s_1 s_2 dots s_r$ where
  $r = ell(f)$, each $s_i in S$ (a set of fundamental reflections in $W$) and
  ${s_i}$ is a set of representatives for the orbits of $F$ on $S$. The order of
  the $F$-centralizer of $f$ is denoted by $h_0$.
] <def:twisted-coxeter-element>

#theorem[
  ([@bib:Lusztig1975], 6.1). Suppose the Dynkin diagram of $G$ is connected. The
  action of $F^delta$ on $⨁_i H_C^(i)(X_f)$ is semisimple and $F^delta$ has
  precisely $h_0$ distinct eigenvalues $lambda_i$ ($i = 1, 2, dots, h_0$) with
  multiplicities $>= 1$. The $lambda_i$-eigenspaces are mutually non-isomorphic
  irreducible $G^F$-modules. #source(176)
] <th:coxeter-variety-eigenspaces>

Thus one realizes unipotent representations of $G^F$ on the eigenspaces of
$F^delta$. The cases where cuspidal representations occur are listed in
[@bib:Lusztig1978], Table I, p. 32. The eigenvalues of $F^delta$ are products of
a root of unity and a power of $q^delta$. This power is of the form
$q^(n delta)$ where $n$ is an integer except when $G$ is of type $E_7$ or $E_8$,
when $n$ could be a half-integer.

#remark[
  In this theorem only the constituents of $⨁_i H_C^(i)(X_f)$ are considered. In
  [@bib:Lusztig1978], 3.9 it is shown that if $rho$ is any unipotent
  representation of $G^F$, it occurs as a constituent of the generalized
  $mu$-eigenspace of $F^delta$ on some $H_C^(i)(X_w)$ and $mu$ is uniquely
  determined by $rho$ up to a factor $q^(n delta)$ where $n$ is an integer. (See
  also [@bib:Lusztig1979], §1, 2.)
] <rem:unipotent-frobenius-eigenvalues>

If $G$ is of type $E_6$ or $E_7$ the two cuspidal unipotent representations of
$G^F$ occur as constituents of $H_C^(i)(X_f)$ as described in
@th:coxeter-variety-eigenspaces. (See [@bib:Lusztig1978], 3.27.) In the case of
$G_2$ ($p != 2, 3$) the unipotent cuspidal representations (or rather, their
characters) are the ones listed as $X_17, X_18, X_19, overline(X)_19$ by Chang
and Ree [@bib:Chang1974]. If $G$ is of type $F_4$, there are $7$ unipotent
cuspidal representations and they are classified in ([@bib:Lusztig1978], 3.29).
Finally if $G$ is of type $E_8$, the $13$ unipotent cuspidal representations are
described in [@bib:Lusztig1979].

The dimensions of the unipotent representations are known in all cases and they
are polynomials in $q$ with rational coefficients. There is an interesting
pattern to the denominators which occur in these rational coefficients, which
has led Lusztig to propose a classification of unipotent representations into
families, each family being associated with a certain finite group. In the case
of classical groups these finite groups are elementary abelian $2$-groups and in
the case of exceptional groups they are the symmetric groups
$S_1, S_2, S_3, S_4$ or $S_5$. For details the reader is referred to
[@bib:Lusztig1979]. #source(177)
