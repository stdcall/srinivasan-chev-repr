#import "main-defs.typ": *
#import "statements.typ": *

#chapter[
  Discrete Series Representations and Harish-Chandra Theory
] <ch:harish-chandra>

#source(35)
We recall (Chapter~@ch:algebraic-groups) that if $P$ is a parabolic subgroup of
$G$ then we have a Levi decomposition $P = L V$. If $P$ is $F$-stable then so is
$V$ and we can choose $L$ to be $F$-stable by choosing it to contain an
$F$-stable maximal torus $T$. Then we have $P^F = L^F V^F$ and
$V^F = upright("O")_(p)(P^F)$. By a parabolic subgroup of $G^F$ we mean a
subgroup of the form $P^F$; we will refer to $V^F$ as its unipotent radical and
to $L^F$ as a Levi subgroup. We will also denote the lift of a representation
$rho$ of $L^F$ to $P^F$ by $tilde(rho)$. The representations of $L^F$ which are
best suited for lifting to $P^F$ and inducing to $G^F$ are those which "do not
come from below", ie.~the so-called cuspidal or discrete series representations.

The results to be described here are due to Harish-Chandra, and can be found in
@bib:Curtis1975, @bib:Borel1970, or @bib:Springer1975.

#definition[
  Let $zeta$ be an irreducible representation (or character) of $G^F$. We say
  $zeta$ is _cuspidal_ or is in the _discrete series_, if for any $P^F != G^F$,
  $zeta | V^F$ does not contain the trivial representation (or character) of
  $V^F$.
  #term-entry("Cuspidal representation", target: <def:cuspidal-representation>)
  #term-entry("Discrete series", target: <def:cuspidal-representation>)
] <def:cuspidal-representation>

#remark[
  If $G$ is a torus, we define every irreducible representation of $G^F$ to be
  cuspidal.
]

_Notation._ $cal(E)(G)$ (resp.~$attach(cal(E), tl: circle.small)(G)$) is the set
of isomorphism classes of irreducible representations (resp.~cuspidal
representations) of $G^F$.

#lemma[
  Let $zeta$ be in $cal(E)(G)$. Then $zeta$ is cuspidal if and only if the
  following holds.
] <lem:cuspidal-character-sums>

#formula-item[
  For every $x in G^F$ we have $sum_(v in V^F) zeta(x v) = 0$ for all #source(
    36,
  ) $P^F != G^F$.
] <eq:cuspidal-character-sums>

#proof[
  Let $e = frac(1, |V^F|) sum_(v in V^F) v$. Then $e$ is an idempotent in
  $CC[V^F]$ affording the trivial representation. So if
  @eq:cuspidal-character-sums is satisfied then $zeta(e) = 0$ and $zeta$ is
  cuspidal. Conversely, let $zeta$ be cuspidal. Then $zeta(e) = 0$, hence
  $zeta(x e) = 0$ for all $x in G^F$ and @eq:cuspidal-character-sums holds.
]

#remark[
  More generally a class function $f$ on $G^F$ is said to be cuspidal if
  @eq:cuspidal-character-sums holds. In this case it is not enough to check that
  $f(e) = 0$ to show that $f$ is cuspidal.
]

#proposition[
  Let $zeta in cal(E)(G)$. Then there is a parabolic subgroup $P^F$ of $G^F$ and
  $psi in attach(cal(E), tl: circle.small)(L)$ such that $zeta$ is a constituent
  of $Ind_(P^F)^(G^F)(tilde(psi))$.
] <prop:cuspidal-support-existence>

#proof[
  There exist parabolics $P$ such that $zeta$ occurs in $Ind_(V^F)^(G^F)(1)$;
  for example, we could take $P = G$, in which case $V = 1$. Take a minimal such
  $P$, and consider $zeta | P^F$. Let $M$ be a $G^F$-module affording $zeta$ and
  let $N$ be the $P^F$-submodule of $M$ consisting of the fixed points under
  $V^F$. By Frobenius reciprocity $N != 0$. Consider the representation $cal(G)$
  of $P^F$ on $N$. This is the direct sum of irreducible representations which
  must all be lifts of cuspidal representations of $L^F$; otherwise, there would
  be a proper parabolic subgroup of $L^F$ whose unipotent radical has a fixed
  point on $N$, and this would lead to a parabolic subgroup of $G^F$ which is
  #source(37) properly contained in $P^F$, and such that $zeta$ restricted to
  its unipotent radical contains 1, contradicting the minimality of $P$. Since
  $zeta$ occurs in $Ind_(V^F)^(G^F)(1)$ it follows now that it occurs in some
  $Ind_(P^F)^(G^F)(tilde(tau))$ where $tau$ is a cuspidal representation of
  $L^F$.
]

#remark[
  In @prop:cuspidal-support-existence we could have $P^F = G^F$, in which case
  $zeta in attach(cal(E), tl: circle.small)(G)$. If $P$ is an $F$-stable
  parabolic subgroup of $G$, let $cal(E)(G, P)$ be the set of all $phi$ in
  $cal(E)(G)$ which occur as constituents of $Ind_(P^F)^(G^F)(tilde(psi))$ for
  some $psi$ in $attach(cal(E), tl: circle.small)(L)$. Now it follows that if we
  choose representatives ${P_i}$ for the conjugacy classes of $F$-stable
  parabolic subgroups of $G$ then $cal(E)(G) = union_i cal(E)(G, P_i)$. We would
  like to refine this decomposition and get a disjoint union.
]

#definition[
  Two $F$-stable parabolic subgroups $P$ and $P'$ are said to be _associated_ if
  there exist $F$-stable Levi subgroups $L, L'$ of $P, P'$ and $x in G^F$ such
  that $conj(x, L^F) = L'^F$.
]

Our aim is to show that $(Ind_(P^F)^(G^F)(tilde(zeta)),
  Ind_(P'^F)^(G^F)(tilde(zeta)'))_(G^F) = 0$ unless $P$ and $P'$ are associated,
where $zeta, zeta'$ are in $attach(cal(E), tl: circle.small)(L)$,
$attach(cal(E), tl: circle.small)(L')$ respectively.

#example[
  Let $G = GL_n$. Then two $F$-stable parabolic subgroups $P$ and $P'$ are
  associated if and only if their Levi subgroups are both isomorphic to
  $GL_(n_1) times GL_(n_2) times dots times GL_(n_k)$ for the same set of
  positive integers $n_1, n_2, dots, n_k$. The next lemma #source(38) is rather
  technical and we will omit the proof. A proof can be found in @bib:Curtis1975,
  where the finite group $G^F$ is considered throughout without any reference to
  the algebraic group (the BN-pair axioms serving as a substitute). This lemma
  is proved there for two parabolics $P_1^F, P_2^F$ which contain a common Borel
  subgroup $B^F$. Since any two $F$-stable Borel subgroups are conjugate by an
  element of $G^F$ (see @cor:rational-tori) there is no loss of generality in
  assuming that the two parabolic subgroups of $G$ that we are considering do in
  fact contain a common $F$-stable Borel subgroup.
]

#lemma[
  Let $P_1, P_2$ be $F$-stable parabolic subgroups containing $T_0$ with
  $P_i = L_i V_i$ ($i = 1, 2$), the $L_i$ being $F$-stable and containing $T_0$.
  #ed-note[
    Fixing the torus chooses compatible Levi complements. The intersection
    decomposition also applies after conjugating the second parabolic by a
    Weyl-group representative, as required below; see #cite(
      <Digne2020>,
      form: "full",
    ), Proposition 3.4.8.
  ] Then we have the following.

  #enum(
    numbering: "(i)",
    [$P_1^F ∩ P_2^F = (L_1^F ∩ L_2^F)(L_1^F ∩ V_2^F)
      (L_2^F ∩ V_1^F)(V_1^F ∩ V_2^F)$. Furthermore, we have uniqueness of
      expression for elements of $P_1^F ∩ P_2^F$.],
    [The unipotent radical of $L_1^F ∩ P_2^F$ is $L_1^F ∩ V_2^F$ and the
      unipotent radical of $L_2^F ∩ P_1^F$ is $L_2^F ∩ V_1^F$.],
    [$P_1^F ∩ V_2^F subset V_1^F$ implies $L_1^F subset L_2^F$.],
  )
] <lem:parabolic-intersection>

#theorem[
  Let $P_1, P_2$ be as in Lemma~@lem:parabolic-intersection and let
  $W = W(T_0)$. Let $psi_i in attach(cal(E), tl: circle.small)(L_i)$
  ($i = 1, 2$). Then $(Ind_(P_1^F)^(G^F)(tilde(psi)_1),
    Ind_(P_2^F)^(G^F)(tilde(psi)_2))_(G^F) = 0$ unless
  $L_1^F = conj(dot(w), L_2^F)$ and $psi_1 = conj(dot(w), psi_2)$ for some
  $w in W^F$ (in particular, unless $P_1, P_2$ are associated).
  #term-entry("Harish-Chandra's Theorem", target: <th:harish-chandra>)
] <th:harish-chandra>

#source(39)
#proof[
  By the Bruhat decomposition @prop:finite-bruhat and Mackey's
  Theorem~@th:mackey we have
  $
    (Ind_(P_1^F)^(G^F)(tilde(psi)_1),
      Ind_(P_2^F)^(G^F)(tilde(psi)_2))_(G^F) =
    sum_w
    (tilde(psi)_1, conj(dot(w), tilde(psi)_2))_(P_1^F ∩ conj(dot(w), P_2^F)),
  $
  where $w$ runs over a subset of $W^F$. Now consider
  $
    (tilde(psi)_1, conj(dot(w), tilde(psi)_2)) =
    frac(1, |P_1^F ∩ conj(dot(w), P_2^F)|)
    sum_(x, y, z, v) tilde(psi)_(1)(x y z v)
    overline(conj(dot(w), tilde(psi)_2)(x y z v)),
  $
  the sum being over all $x in L_1^F ∩ conj(dot(w), L_2^F)$,
  $y in L_1^F ∩ conj(dot(w), V_2^F)$, $z in V_1^F ∩ conj(dot(w), L_2^F)$,
  $v in V_1^F ∩ conj(dot(w), V_2^F)$
  (using @lem:parabolic-intersection (i)). Now since $tilde(psi)_1$ and
  $conj(dot(w), tilde(psi)_2)$ are trivial on $V_1^F ∩ conj(dot(w), V_2^F)$, the
  above expression is a multiple of $sum_(x, y, z) tilde(psi)_(1)(x y z)
  overline(conj(dot(w), tilde(psi)_2)(x y z))$, and hence of
  $sum_(x, y, z) tilde(psi)_(1)(x y)
  overline(conj(dot(w), tilde(psi)_2)(x z))$
  (writing $x y z = x z(z^(-1) y z)$ and noting that
  $z^(-1) y z in conj(dot(w), V_2^F)$, $z in V_1^F$). Now using
  @lem:parabolic-intersection (ii), @eq:cuspidal-character-sums and the fact
  that $psi_1 in attach(cal(E), tl: circle.small)(L_1)$ we see that
  $sum_y tilde(psi)_(1)(x y) = 0$ unless $L_1^F ∩ conj(dot(w), V_2^F) = 1$.
  Similarly $sum_z conj(dot(w), tilde(psi)_2)(x z) = 0$ unless
  $V_1^F ∩ conj(dot(w), L_2^F) = 1$. Hence we have
  $(Ind_(P_1^F)^(G^F)(tilde(psi)_1),
    Ind_(P_2^F)^(G^F)(tilde(psi)_2)) = 0$ unless for some $w in W^F$,
  $L_1^F ∩ conj(dot(w), V_2^F)$ and $V_1^F ∩ conj(dot(w), L_2^F)$ are both
  trivial. But then $P_1^F ∩ conj(dot(w), V_2^F) subset V_1^F$ and
  $conj(dot(w)^(-1), V_1^F) ∩ P_2^F subset V_2^F$. By
  @lem:parabolic-intersection (iii) this implies #source(40) that
  $L_1^F subset conj(dot(w), L_2^F)$ and $L_2^F subset conj(dot(w)^(-1), L_1^F)$
  and thus $L_1^F = conj(dot(w), L_2^F)$, as required. Also it now follows that
  $psi_1 = conj(dot(w), psi_2)$, as otherwise
  $
    (tilde(psi)_1, conj(dot(w), tilde(psi)_2))_(P_1^F ∩ conj(dot(w), P_2^F)) = 0
  $.
]

#remark[
  In fact @lem:parabolic-intersection (iii) can be sharpened to: if
  $P_1^F ∩ V_2^F subset V_1^F$, then $L_1 subset L_2$ (see @bib:Springer1975,
  p.~627). So in Theorem~@th:harish-chandra we can prove the scalar product is
  zero unless $L_1 = conj(dot(w), L_2)$.
]

Now we have shown that

$ cal(E)(G) = union_P cal(E)(G, P), $ <eq:harish-chandra-series>

where the union is disjoint and $P$ runs over a set of representatives for the
associativity classes of $F$-stable parabolic subgroups of $G$. Thus the problem
of determining $cal(E)(G)$ is reduced to two problems.
#enum(
  [Find $attach(cal(E), tl: circle.small)(G)$.],
  [Decompose $Ind_(P^F)^(G^F)(tilde(psi))$ where
    $psi in attach(cal(E), tl: circle.small)(L)$.],
)
These two problems will be discussed in subsequent chapters. Neither of them is
completely solved, but a large number of the representations in
$attach(cal(E), tl: circle.small)(G)$ have been constructed by Lusztig and
Deligne @bib:Deligne1976 and by Lusztig in @bib:Lusztig1975. The centralizer
algebra of $Ind_(P^F)^(G^F)(tilde(psi))$ has been studied in some cases and this
will be discussed in Chapter~@ch:classification-of-representations.
