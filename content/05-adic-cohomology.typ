#import "main-defs.typ": *
#import "statements.typ": *

#source(41)
#chapter[The $ell$-adic cohomology] <ch:ell-adic-cohomology>

In this chapter we will first give a review of the definitions and elementary
properties of sheaves on a topological space. This material is introduced so
that one knows what to expect in the case of $ell$-adic sheaves. Then we define
schemes and the sheaf cohomology of schemes. After this we describe $ell$-adic
sheaves and $ell$-adic cohomology and give a survey of the main properties of
$ell$-adic cohomology groups of a scheme which is separated and of finite type
over an algebraically closed field. We point out the analogous results in the
classical case and give references to the results in both the $ell$-adic and the
classical cases.

== Sheaves (Classical theory) <sec:classical-sheaves>
#term-entry("Sheaf", sub: "classical")

(See @bib:Godement1958, @bib:Hartshorne1977 or @bib:Macdonald1968.)

Let $X$ be a topological space. A presheaf $Phi$ of abelian groups (or sets,
rings, etc.) consists of the following data. For every open subset $U$ of $X$ we
have an abelian group (or set, ring, etc.) $Phi(U)$, together with (restriction)
homomorphisms $rho_(U V): Phi(U) arrow.r Phi(V)$ whenever $V subset U$, subject
to the conditions #enum(
  numbering: "(1)",
  [$Phi(emptyset) = 0$],
  [$rho_(U U)$ is the identity map of $Phi(U)$],
  [if $U supset V supset W$, then $rho_(U W) = rho_(V W) rho_(U V)$.],
)

The presheaf $Phi$ is said to be a _sheaf_ if it also satisfies:

#formula-item[
  For each open set $U$ in $X$ and each open covering $\{U_alpha\}$ of $U$, and
  each family $\{s_alpha\}$ such that $s_alpha in Phi(U_alpha)$ and $s_alpha$,
  $s_beta$ have the same restriction to $Phi(U_alpha inter U_beta)$ for all
  $alpha, beta$, there is a unique $s in Phi(U)$ whose restriction to $U_alpha$
  is $s_alpha$ for all $alpha$.
] <eq:sheaf-gluing>

#source(42)
If $x in X$, the _stalk_ of $Phi$ at $x$ is defined to be
$lim_(arrow.r, x in U, U "open") Phi(U)$, and is denoted by $Phi_x$.

We define a morphism $phi: Phi arrow.r cal(G)$ of presheaves or sheaves on $X$
as a family of homomorphisms $phi(U): Phi(U) arrow.r cal(G)(U)$ ($U$ open in
$X$) commuting with the restriction homomorphisms. Then $phi$ induces a
homomorphism $phi_x: Phi_x arrow.r cal(G)_x$ for each $x in X$.

Given a presheaf $Phi$ on $X$, there is a canonical sheaf $tilde(Phi)$, called
its _sheafification_, and a morphism $Phi arrow.r tilde(Phi)$ (of presheaves)
through which all morphisms from $Phi$ into sheaves factor uniquely. We can
construct this as follows (@bib:Macdonald1968, p. 30). Let $E$ be the disjoint
union of the stalks $Phi_x$ for all $x in X$. Given $s in Phi(U)$, define
$tilde(s): U arrow.r E$ by $tilde(s)(x) = s_x$, where, in the canonical map
$Phi(U) arrow.r Phi_x$, $s$ maps on $s_x$. Thus $tilde(s)$ is a section of $E$
over $U$. Give $E$ the finest topology such that all the maps $tilde(s)$ are
continuous. Define, for each open $U$, $tilde(Phi)(U)$ to be the set of
continuous sections of $E$ over $U$. Then $tilde(Phi)$ is the required sheaf. If
we had started with a presheaf $Phi$ which was already a sheaf, $tilde(Phi)$
would be isomorphic to $Phi$. Because of this way of viewing a sheaf on $X$, the
elements of $Phi(U)$ for any sheaf $Phi$ are called the sections of $Phi$ over
$U$. The elements of $Phi(X)$ are called global sections, and often $Phi(X)$ is
denoted by $Gamma(X, Phi)$.

Another way of thinking of a presheaf is as a contravariant functor from the
category $cal(C)(X)$ whose objects are the open sets in $X$ and morphisms are
inclusions of open sets, into
#source(43)
the category of abelian groups (or sets, rings, etc.). This is the point of view
which will be useful later.

#heading(level: 3, numbering: none)[Direct and inverse images of sheaves]
#term-entry("Direct and inverse images of sheaves", sub: "classical")

(@bib:Hartshorne1977, p. 65.)

Let $f: X arrow.r Y$ be a continuous map and $Phi$ a sheaf on $X$. Then the
direct image $f_* Phi$ is the sheaf on $Y$ defined by
$(f_* Phi)(V) = Phi(f^(-1)(V))$ for any open set $V$ of $Y$. If $cal(G)$ is a
sheaf on $Y$, the inverse image $f^* cal(G)$ is the sheaf on $X$ associated with
the presheaf $p$ where
$p(U) = lim_(arrow.r, V supset f(U), V "open") cal(G)(V)$, for an open set $U$
in $X$. We then have $"Hom"_(Y)(cal(G), f_* Phi) = "Hom"_(X)(f^* cal(G), Phi)$,
i.e. the functor $f^*$ from the category of sheaves of abelian groups on $Y$ to
the category of sheaves of abelian groups on $X$ is the left adjoint of the
functor $f_*$ from the category of sheaves of abelian groups on $X$ to the
category of sheaves of abelian groups on $Y$.

We also note that subsheaves and quotient sheaves can be defined for sheaves of
abelian groups on $X$ (@bib:Hartshorne1977, p. 64).

#heading(level: 3, numbering: none)[Restriction]

(@bib:Hartshorne1977, p. 65.)

Let $Z$ be a subspace of $X$ with the induced topology and let $i: Z arrow.r X$
be the inclusion map. If $Phi$ is a sheaf on $X$, the sheaf $i^* Phi$ on $Z$ is
called the restriction of $Phi$ to $Z$ and denoted by $Phi|_Z$. We note that the
stalk of $Phi|_Z$ at any $x in Z$ is just $Phi_x$.

#heading(level: 3, numbering: none)[Extension by zero]

(@bib:Hartshorne1977, p. 68.)

Let $j: U arrow.r X$ be an open immersion (i.e., $j$ is an isomorphism of $U$
with an open subset of $X$). If $Phi$ is a sheaf on
#source(44)
$U$, the sheaf on $X$ associated with the presheaf which attaches $Phi(V)$ to
$V$ if $V subset U$ or $0$ to $V$ if $V subset.not U$ is called the extension of
$Phi$ by zero and is denoted by $j_! Phi$. If $Z = X - U$ and $i: Z arrow.r X$
is inclusion, we have an exact sequence
$0 arrow.r j_(!)(Phi|_U) arrow.r Phi arrow.r i_(*)(Phi|_Z) arrow.r 0$ of sheaves
on $X$ for any sheaf $Phi$ on $X$.

#heading(level: 3, numbering: none)[Examples]


+ _Constant sheaf._ Let $A$ be an abelian group, given the discrete topology.
  The constant sheaf $A$ on $X$ is defined by
  $A(U) = \{"Continuous maps of" U "into" A\}$. So if $U$ is connected
  $A(U) = A$. In fact, $A$ is the sheafification of the presheaf which assigns
  $A$ to every open set $U$ of $X$.

+ _Locally constant sheaf._ $Phi$ is a locally constant sheaf on $X$ if there is
  a covering of $X$ by open sets $\{U_i\}$ such that $Phi|_(U_i)$ is a constant
  sheaf for each $i$.

+ Let $X$ be an affine variety over the algebraically closed field $K$, as in
  Chapter @ch:algebraic-groups. We say a function $f: X arrow.r K$ is regular at
  $a in X$ if there is a neighborhood $V$ of $a$ in which $f = g/h$ where
  $g, h in K[X]$ and $h != 0$ in $V$. We say $f$ is regular if it is regular at
  all $a in X$. If $U$ is open in $X$, let $Phi(U)$ be the set of all regular
  functions on $U$. Then $Phi$ is a sheaf of rings on $X$. Similarly we have a
  naturally defined sheaf on any quasiprojective variety $X$
  (@bib:Hartshorne1977, p. 62).

#heading(level: 3, numbering: none)[Sheaf cohomology]
#term-entry("Sheaf cohomology")

(@bib:Hartshorne1977, pp. 202–208.)

The category of sheaves of abelian groups on a topological space $X$ is an
abelian category which has enough injectives;
#source(45)
hence every sheaf $Phi$ on $X$ has an injective resolution.

Furthermore, the global section functor
$Gamma: Phi arrow.r Gamma(X, Phi) = Phi(X)$ is left exact from this category
into the category of abelian groups. Thus we can take the derived functors of
$Gamma$ and define the cohomology groups of $X$ with coefficients in $Phi$. In
other words, if
$
  0 arrow.r Phi arrow.r C^0 arrow.r C^1 arrow.r dots arrow.r C^i arrow.r
  C^(i+1) arrow.r dots
$
is an injective resolution of $Phi$, we consider the complex
$
  0 arrow.r Gamma(X, C^0) arrow.r Gamma(X, C^1) arrow.r
  dots arrow.r Gamma(X, C^i) arrow.r^(d_i) Gamma(X, C^(i+1)) arrow.r dots
$
and define $H^(i)(X, Phi) = (ker d_i) / ("Im" d_(i-1))$. (Note that
$H^(0)(X, Phi) = Gamma(X, Phi)$.)

The sequence of functors $R^i Gamma: Phi arrow.r H^(i)(X, Phi)$ from the
category of sheaves of abelian groups on $X$ into the category of abelian groups
forms a “$delta$-functor” in the sense that given any short exact sequence
$0 arrow.r Phi' arrow.r Phi arrow.r Phi'' arrow.r 0$ of sheaves we have a long
exact sequence
$
  0 arrow.r H^(0)(X, Phi') arrow.r H^(0)(X, Phi) arrow.r H^(0)(X, Phi'')
  arrow.r^(delta_1) H^(1)(X, Phi') arrow.r H^(1)(X, Phi) arrow.r H^(1)(X,
    Phi'') arrow.r^(delta_2) dots
$
Furthermore, it is a “universal $delta$-functor” in the sense that given any
other sequence of functors $(T_i)$ with the above property, and a morphism of
functors $f^0: Gamma arrow.r T_0$, there is a unique sequence of morphisms
$f^i: R^i Gamma arrow.r T_i$ for each $i$, starting with the given $f^0$, which
commute with the $delta_i$ for each short exact sequence.

#heading(level: 3, numbering: none)[Higher direct images of a sheaf]

(@bib:Hartshorne1977, p. 250.)

Let $f: X arrow.r Y$ be a continuous map and $Phi$ a sheaf on $X$.
#source(46)
Then the $i^"th"$ direct image sheaf $R^i f_* Phi$ on $Y$ is the sheafification
of the presheaf on $Y$ which assigns to any open set $V$ in $Y$ the abelian
group $H^(i)(f^(-1)(V), Phi|_(f^(-1)(V)))$.

== Schemes <sec:schemes>
#term-entry("Scheme")

(@bib:Macdonald1968, Ch. 6; @bib:Hartshorne1977, Chapter II; @bib:Mumford1967,
Ch. 2.)

In this section we define and give a brief review of schemes, without too many
technical details.

A _ringed space_ is a pair $(X, cal(O)_X)$ consisting of a topological space $X$
and a sheaf of rings $cal(O)_X$ (called the structure sheaf) on $X$. A morphism
$(X, cal(O)_X) arrow.r (Y, cal(O)_Y)$ consists of a continuous map $f$ from $X$
to $Y$ and a morphism of sheaves $cal(O)_Y arrow.r f_* cal(O)_X$. Thus for each
open set $V$ in $Y$ we have a ring homomorphism
$cal(O)_(Y)(V) arrow.r cal(O)_(X)(f^(-1)(V))$, compatible with restrictions, and
hence an induced homomorphism of stalks $cal(O)_(Y, f(x)) arrow.r cal(O)_(X, x)$
for any $x in X$. A _locally ringed space_ is a ringed space $(X, cal(O)_X)$ in
which for each $x in X$ the stalk $cal(O)_(X,x)$ is a local ring, and a morphism
of locally ringed spaces is one in which the homomorphism of stalks mentioned
above is a local homomorphism of local rings, i.e., the inverse of the maximal
ideal of $cal(O)_(X,x)$ is the maximal ideal of $cal(O)_(Y,f(x))$. (See
@bib:Macdonald1968, p. 34, or @bib:Hartshorne1977, p. 72.)

Let $A$ be a commutative ring with $1$. Let $X = "Spec" A$ be the set of all
prime ideals of $A$. For any $E subset A$ we let $V(E) subset X$ be the set of
all prime ideals containing $E$. We define a topology (the Zariski topology) on
$X$ by letting the sets $V(E)$ be the closed sets. One can define a sheaf of
rings $cal(O)_X$ on $X$ in such a way that the stalk $cal(O)_(X,x)$ of
$cal(O)_X$
#source(47)
at $x in X$ is the local ring of $A$ corresponding to the prime ideal $x$ of
$A$. Then $"Spec" A$ is a locally ringed space. (See @bib:Macdonald1968, p. 36;
@bib:Hartshorne1977, p. 70.)

An _affine scheme_ is a locally ringed space which is isomorphic to $"Spec" A$
for some $A$. Finally a _scheme_ is a locally ringed space $(X, cal(O)_X)$ in
which every point has an open neighborhood $U$ such that the pair
$(U, cal(O)_X|_U)$ is an affine scheme. A morphism of schemes is a morphism
regarding them as locally ringed spaces. (See @bib:Macdonald1968, p. 43 or
@bib:Hartshorne1977, p. 74, where there are also several examples of schemes.)

If $S$ is a fixed scheme, a _scheme over_ $S$ is a scheme $X$ together with a
morphism $X arrow.r S$. Often one considers the category of schemes over a fixed
base scheme $S$, the morphisms from $X$ to $Y$ being given by commutative
triangles
#import "diagrams/05-schemes.typ": fibre-product, scheme-triangle
#align(center, scheme-triangle())
If $S = "Spec" A$, we talk of a scheme over $A$. Any scheme $X$ can be regarded
as a scheme over $ZZ$; it is enough to show this for affine schemes, and given
any ring $A$ with $1$ the natural map $ZZ arrow.r A$ gives rise to a morphism
$"Spec" A arrow.r "Spec" ZZ$.

In the category of schemes over $S$, products exist. In other words, given
$X arrow.r S$, $Y arrow.r S$ we have a product scheme $X times_S Y$ over $S$ and
a commutative diagram
#align(center, fibre-product())
such that given any scheme $Z$ over $S$ and morphisms $f: Z arrow.r X$,
$g: Z arrow.r Y$ which make a commutative diagram with the given morphisms
$X arrow.r S$ and $Y arrow.r S$, there is a unique morphism
#source(48)
$theta: Z arrow.r X times_S Y$ such that $f = p_1 dot theta$ and
$g = p_2 dot theta$. If $S = "Spec" ZZ$ we write $X times Y$ for $X times_ZZ Y$.
(See @bib:Hartshorne1977, p. 87.)

#remark[

  + In the category of sets, if $X arrow.r S$, $Y arrow.r S$ are inclusions,
    then $X times_S Y$ is just $X inter Y$. Thus when we introduce “generalized
    topologies” (e.g., the étale topology) on a scheme $X$, the product
    $X times_S Y$ will take the place of $X inter Y$.

  + If $X, Y$ are schemes over $S$, the map $X times_S Y arrow.r Y$ makes
    $X times_S Y$ a scheme over $Y$, and we say it is obtained from $X$ by base
    extension.
]

#example[
  Let $X_0$ be an irreducible affine variety over the algebraically closed field
  $K$, as in Chapter @ch:algebraic-groups. Then $X_0$ can be enlarged to an
  affine scheme $X$ over $K$; in fact, $X = "Spec" A$ where $A = K[X_0]$. The
  idea is that $X$ consists of not only the points of $X_0$ (which correspond to
  maximal ideals of $A$ and represent the _closed points_ of $X$) but also of
  points corresponding to each irreducible subvariety of $X_0$. The morphism
  $X arrow.r "Spec" K$ consists of mapping $X$ onto $"Spec" K$ (which consists
  of a single point) and $K$ into $A$ in the natural way. Similarly we can
  associate a scheme with any quasi-projective variety. (See
  @bib:Hartshorne1977, p. 78.) We will call such a scheme a quasiprojective
  scheme.
]

_Notation._ If $x in X$, where $X$ is a scheme, the stalk of $cal(O)_X$ at $x$
is a local ring whose residue field will be denoted by $k(x)$.

#heading(level: 3, numbering: none)[Fibres of a morphism]
#term-entry("Fibres of a morphism")

Suppose we have a morphism $f: X arrow.r Y$ of schemes and $y in Y$. Then the
fibre of $f$ over $y$ is defined to be the
#source(49)
scheme $X times_Y "Spec" k(y)$. (Note that there is a natural morphism
$"Spec" k(y) arrow.r Y$, which takes $"Spec" k(y)$ onto $y$ and the stalk
$cal(O)_(Y,y)$ onto $k(y)$.) This is a scheme over $k(y)$ whose underlying
topological space is homeomorphic to $f^(-1)(y)$, the usual fibre over $y$
(@bib:Hartshorne1977, p. 89, or @bib:Murre1967, p. 16). We sometimes denote the
fibre of $f$ over $y$ by $X_y$.

#heading(level: 3, numbering: none)[“Points,” geometric points and geometric
  fibres]
#term-entry("Point", sub: "geometric")
#term-entry("Geometric fibres")

If $X_0$ is an affine variety over an algebraically closed field $K$, the points
of $X_0$ are in bijection with the $K$-homomorphisms of $A = K[X_0]$ into $K$.
If $X, Y$ are schemes over $S$ we define a $Y$-valued point of $X$ to be a
morphism (over $S$) from $Y$ into $X$. In particular, a _geometric point_ of a
scheme $X$ is a morphism $"Spec" tilde(K) arrow.r X$ where $tilde(K)$ is an
algebraically closed field. The image of this morphism is called the _center_ of
the geometric point. If $x in X$ then we have a morphism
$"Spec" overline(k(x)) arrow.r X$ which is a geometric point centered at $x$.
Conversely, any geometric point centered at $x in X$ is a morphism of the form
$"Spec" tilde(K) arrow.r X$ where $tilde(K) supset overline(k(x))$. [For a
discussion of points and the motivation for defining them in this way, see
@bib:Mumford1967, p. 218.]

Suppose we have a morphism $f: X arrow.r Y$ and $overline(x)$ is a geometric
point of $Y$, i.e., we have a morphism $overline(x): "Spec" tilde(K) arrow.r Y$.
Then the “geometric fibre” of $f$ over $overline(x)$ is defined to be
$X times_Y "Spec" tilde(K)$, and denoted by $X_(overline(x))$. Suppose
$overline(x)$ is centered at $x in Y$. Then the connection between
$X_(overline(x))$ and the usual fibre $X_x$ is that there is an action of a
Galois group (essentially, of $overline(k(x))$ over $k(x)$) and $X_x$ is
essentially a quotient of $X_(overline(x))$
#source(50)
under this action.

We now define some important kinds of morphisms of schemes.

#definition[
  Let $f: X arrow.r Y$ be a morphism of schemes. Let $Delta$ be the “diagonal
  morphism” $X arrow.r X times_Y X$ whose composition with both the projection
  maps $X times_Y X arrow.r X$ is the identity map $X arrow.r X$. We say $f$ is
  _separated_ (or $X$ is separated over $Y$) if $Delta$ is a closed immersion.
  (See @bib:Hartshorne1977, p. 96.)
]

This is the analogue of the Hausdorff axiom for topological spaces. For example,
any morphism $X arrow.r Y$ of affine schemes is separated.

#definition[
  A morphism $f: X arrow.r Y$ of schemes is of _finite type_ (or $X$ is of
  finite type over $Y$) if there is a covering of $Y$ by open affine subsets
  $V_i = "Spec" B_i$ such that each $f^(-1)(V_i)$ can be covered by a finite
  number of open affine subsets $U_(i j) = "Spec" A_(i j)$, such that each
  $A_(i j)$ is a finitely generated $B_i$-algebra. If each $f^(-1)(V_i)$ is
  itself affine and equal to $"Spec" A_i$, where $A_i$ is integral over $B_i$
  then we say $f$ is finite. (See @bib:Hartshorne1977, p. 84; cf. the definition
  of a finite morphism in Chapter @ch:algebraic-groups.)
]

#definition[
  A morphism $f: X arrow.r Y$ is _universally closed_ if it is closed (i.e., the
  image under $f$ of any closed subset of $X$ is closed) and for any morphism
  $Y' arrow.r Y$, the corresponding morphism $X times_Y Y' arrow.r Y'$ is
  closed.
]

#definition[
  A morphism $f: X arrow.r Y$ is _proper_ if it is separated, of finite type,
  and universally closed. We also say $X$ is proper over $Y$. For example, the
  affine line over a field $k$ is not proper over $k$, but the projective line
  is
  #source(51)
  proper over $k$. More generally, any projective variety is proper over $k$.
  Thus “proper” is the analogue of compactness in the classical case. (See
  @bib:Hartshorne1977, p. 100.)
]

#heading(level: 3, numbering: none)[Functoriality of Sheaf Cohomology]
#term-entry("Functoriality of cohomology")

Let $X$ be a scheme, $Phi$ a sheaf of abelian groups on $X$. Regarding $Phi$ as
a sheaf on the underlying (Zariski) topological space of $X$, we can form the
cohomology groups $H^(i)(X, Phi)$ as described earlier.

Suppose we have a morphism $f: X arrow.r X'$ of schemes and $Phi$ is a sheaf on
$X'$. By the definition of the inverse image sheaf $f^* Phi$ on $X$, we have a
map $Gamma(X', Phi) arrow.r Gamma(X, f^* Phi)$, i.e., a map
$H^(0)(X', Phi) arrow.r H^(0)(X, f^* Phi)$. Also the functor
$Phi arrow.r H^(i)(X, f^* Phi)$ is a $delta$-functor from the category of
sheaves on $X'$ into the category of abelian groups. Thus, since the $R^i Gamma$
form a universal $delta$-functor from the category of sheaves on $X'$ into the
category of abelian groups, we have a sequence of morphisms
$H^(i)(X', Phi) arrow.r H^(i)(X, f^* Phi)$. In other words, the morphism
$f: X arrow.r X'$ of schemes induces a homomorphism
$H^(i)(X', Phi) arrow.r H^(i)(X, f^* Phi)$ for each $i$.

== Étale cohomology <sec:etale-cohomology>

(@bib:Artin1972, Exposé XVII; @bib:Deligne1977; @bib:Grothendieck1977, Exposé
VI.)

#heading(level: 3, numbering: none)[The étale topology]

(See @bib:Mumford1965, @bib:Artin1962, or @bib:Deligne1977.)

Let $X$ be a set. To give a topology on $X$ is equivalent to giving a category
$cal(C)(X)$ whose objects are the open sets in $X$ and morphisms are inclusions
of open sets. Grothendieck's idea is to generalize this notion; thus a
generalized topological space in his sense is given by a category whose objects
are
#source(52)
morphisms of the form $U arrow.r X$ in some category $cal(C)$, where $X$ is a
fixed object of $cal(C)$, and morphisms are commutative triangles
#import "diagrams/05-schemes.typ": (
  neighbourhood-triangle, set-equalizer, sheaf-equalizer, site-triangle,
)
#align(center, site-triangle())
One such “topology” is the étale topology, where $cal(C)$ is the category of
schemes, which will be described below.

_From now on, unless otherwise stated, we will consider only schemes which are
separated and of finite type over an algebraically closed field $K$._ We can
think of such a scheme as obtained by gluing together a finite number of affine
schemes of the form $"Spec" A$ where $A$ is a finitely generated $K$-algebra.

#term-entry("Étale morphism")

We introduce the concept of an étale morphism. Let $f: X arrow.r Y$ be a
morphism of schemes. Then we have a morphism of sheaves
$cal(O)_Y arrow.r f_* cal(O)_X$, and, for each $x in X$, we have an induced map
of stalks $cal(O)_(Y,f(x)) arrow.r cal(O)_(X,x)$ which is a map of local rings.

#definition[
  $f$ is étale if for each closed point $y$ of $Y$, $f^(-1)(y)$ is finite and
  for each $x in f^(-1)(y)$ the morphism of stalks
  $cal(O)_(Y,y) arrow.r cal(O)_(X,x)$ gives rise to an isomorphism of the
  completions (with respect to their maximal ideals)
  $tilde(cal(O))_(Y,y) arrow.r tilde(cal(O))_(X,x)$.
]

Roughly, an étale morphism is analogous to a local homeomorphism for analytic
spaces over $CC$.

Given a scheme $X$, the category $X_"et"$ is the category whose objects are
étale morphisms $U arrow.r X$ where $U$ is a scheme, and morphisms are
commutative triangles
#align(center, site-triangle())
Then “coverings” in this “étale topology” on $X$ consist of finite sets of
morphisms $U_alpha arrow.r^(P_alpha) U$ such that $U$ is the union of the
$P_(alpha)(U_alpha)$.

#source(53)
#term-entry("Sheaf", sub: "étale")
#term-entry("Étale cohomology")
A presheaf of abelian groups (sets, rings, etc.) on $X_"et"$ is a contravariant
functor $Phi$ from $X_"et"$ into the category of abelian groups (sets, rings,
etc.). Then $Phi$ is a sheaf if it satisfies a formal analogue of
@eq:sheaf-gluing, where, for any $U_alpha, U_beta$, the intersection
$U_alpha inter U_beta$ is replaced by $U_alpha times_U U_beta$. In other words,
for any covering $\{U_alpha arrow.r U\}$, the diagram
#align(center, sheaf-equalizer())
is exact.

(Here a diagram
#align(center, set-equalizer())
of sets and mappings is said to be exact if $f$ maps $A$ bijectively on the set
of all $x in B$ such that $g(x) = h(x)$.) The maps in the diagram are obtained
from using the functor $Phi$ on the morphisms $U_alpha arrow.r U$,
$U_alpha times_U U_beta arrow.r U_alpha$,
$U_alpha times_U U_beta arrow.r U_beta$. By abuse of language we will from now
on talk of a sheaf on $X$.

Now we consider the global section functor $Gamma: Phi arrow.r Phi(X)$ from the
category of sheaves of abelian groups on $X$ into the category of abelian groups
and denote its $i^"th"$ derived functor by $R^i Gamma$ or $H^(i)(X, dot)$. Then
$H^(i)(X, Phi)$ is the _étale cohomology group_ of $X$ with coefficients in the
sheaf $Phi$.

#heading(level: 3, numbering: none)[Cohomology with compact support]
#term-entry("Cohomology with compact support")

(@bib:Deligne1977, p. 47.)

By a theorem of Nagata, there exists a “compactification” $tilde(X)$ of the
scheme $X$; i.e., a scheme $tilde(X)$ proper over $K$ and an open immersion
$j: X arrow.r tilde(X)$. (For example, such a situation arises when $X$ is a
quasiprojective variety embedded in a projective variety $tilde(X)$.)

Let $Phi$ be a sheaf of torsion abelian groups on $X$. As in the classical case,
we can define a sheaf $j_! Phi$ on $tilde(X)$, the
#source(54)
extension of $Phi$ by $0$. This is defined as follows:
$"Hom"_(tilde(X))(j_! Phi, cal(G)) = "Hom"_(X)(Phi, j^* cal(G))$, where $cal(G)$
is any sheaf on $tilde(X)$.

#definition[
  $H_c^(i)(X, Phi) = H^(i)(tilde(X), j_! Phi)$.
]

The $H_c^(i)(X, Phi)$ are the étale cohomology groups with compact support of
$X$ with coefficients in $Phi$. It is a deep theorem that these groups are
independent of the choice of $tilde(X)$.

#heading(level: 3, numbering: none)[Direct and inverse images of sheaves]
#term-entry("Direct and inverse images of sheaves", sub: "étale")

(See @bib:Deligne1977, pp. 22, 49.)

Suppose we have a geometric point $overline(x): "Spec" tilde(K) arrow.r X$. Then
an _étale neighborhood_ of $overline(x)$ consists of a commutative diagram
#align(center, neighbourhood-triangle())
where $U arrow.r X$ is an étale morphism. If $Phi$ is a sheaf on $X$, the stalk
$Phi_(overline(x))$ of $Phi$ at the geometric point $overline(x)$ is defined to
be $lim_(arrow.r, U) Phi(U)$, the limit being over all étale neighborhoods of
$overline(x)$.

Let $f: X arrow.r Y$ be a morphism of schemes and $Phi$ a sheaf on $X$. The
direct image sheaf $f_* Phi$ on $Y$ is defined by
$(f_* Phi)(V) = Phi(X times_Y V)$ for every étale morphism $V arrow.r Y$. Thus
$f_*$ is a left exact functor from the category of sheaves of abelian groups on
$X$ into the category of sheaves of abelian groups on $Y$. The $i^"th"$ derived
functor of $f_*$ is denoted by $R^i f_*$. If $overline(y)$ is a geometric point
of $Y$ then the stalk $(R^i f_* Phi)_(overline(y))$ is isomorphic to
$lim_(arrow.r, V) H^(i)(X times_Y V, Phi)$, the limit being over all étale
neighborhoods $V$ of $overline(y)$.

By analogy with the classical case we then define the inverse image functor
$f^*$ from the category of sheaves of abelian groups on $Y$ into the category of
sheaves of abelian
#source(55)
groups on $X$ as the left adjoint of $f_*$. Then if $overline(x)$ is a geometric
point of $X$ and $Phi$ is a sheaf on $Y$ the stalk $(f^* Phi)_(overline(x))$ is
isomorphic to the stalk $Phi_(f(overline(x)))$, where $f(overline(x))$ is the
geometric point $"Spec" tilde(K) arrow.r X arrow.r^f Y$.

We now define direct images of sheaves in the “compact support” case as follows.
Given $f: X arrow.r Y$ it can be shown that we have a commutative diagram
#import "diagrams/05-schemes.typ": adic-transition, compactification-triangle
#align(center, compactification-triangle())
where $tilde(f)$ is proper. Then we define
$(R^i f_!)(Phi) = R^(i)(tilde(f)_*)(j_! Phi)$, where $Phi$ is a torsion sheaf on
$X$. (Note the notation $f_!$, rather than $f_*$, in the compact support case.)
Again it can be shown that this definition is independent of the choice of
$tilde(X)$.

#heading(level: 3, numbering: none)[$ell$-adic sheaves]

(@bib:Deligne1977, p. 82.)

For any prime $ell$ different from $"char" K$, let $ZZ_ell, QQ_ell$ denote the
ring of $ell$-adic integers and the field of $ell$-adic numbers, respectively.

An _étale covering_ of a scheme $X$ is a scheme $Y$, and a finite étale
surjective morphism $f: Y arrow.r X$.

#definition[
  A sheaf $Phi$ on $X$ is said to be _locally constant_ if there is an étale
  covering $f: Y arrow.r X$ such that $f^* Phi$ is a constant sheaf on $Y$.
]

#definition[
  A sheaf $Phi$ on $X$ is said to be _constructible_ if it has finite stalks and
  $X$ is the union of a finite number of locally closed sets on each of which
  $Phi$ is locally constant. (Recall that a subset of a topological space is
  locally closed if it is the intersection
  #source(56)
  of an open set and a closed set.)
]

#term-entry("Sheaf", sub: "ℓ-adic", sub-display: [$ell$-adic])

We now define an $ell$-adic sheaf on $X$, and note that it is _not_ a sheaf on
$X$ in the sense that we have defined earlier.

#definition[
  A $ZZ_ell$-sheaf (or $ell$-adic sheaf) $Phi$ on $X$ is a projective system of
  sheaves $Phi_n$, when $Phi_n$ is a constructible sheaf of
  $ZZ/(ell^(n+1) ZZ)$-modules such that the morphisms $Phi_n arrow.r Phi_(n-1)$
  factor through an isomorphism as in the commutative diagram below.
  #align(center, adic-transition())
]

The stalk $Phi_(overline(x))$ of a $ZZ_ell$-sheaf $Phi$ on $X$ at a geometric
point $overline(x)$ of $X$ is defined to be the $ZZ_ell$-module
$lim_(arrow.l, n) (Phi_n)_(overline(x))$.

#heading(level: 3, numbering: none)[Examples of $ZZ_ell$-sheaves]


+ $Phi_n$ is the constant sheaf $ZZ/(ell^(n+1) ZZ)$. Then $Phi$ is the constant
  $ZZ_ell$-sheaf $ZZ_ell$.

+ $Phi_n$ is the sheaf $mu_(ell^(n+1))$ of $ell^(n+1)"th"$ roots of unity (see
  below).

#definition[
  $ H^(i)(X, Phi) = lim_(arrow.l) H^(i)(X, Phi_n), $
  where $Phi$ is a $ZZ_ell$-sheaf.
  $ H_c^(i)(X, Phi) = lim_(arrow.l) H_c^(i)(X, Phi_n). $
]

#remark[
  The groups $H^(i)(X, Phi_n)$, $H_c^(i)(X, Phi_n)$ are finite, and so there is
  a good definition of $lim_(arrow.l)$.
]

In particular, we have by definition
$H_c^(i)(X, ZZ_ell) = lim_(arrow.l) H_c^(i)(X, ZZ/(ell^n ZZ))$.

#source(57)
#term-entry(
  "ℓ-adic cohomology groups H_c^(i)(X,Q_ℓ)",
  display: [$ell$-adic cohomology groups $H_c^(i)(X, QQ_ell)$],
  sort: "l-adic cohomology",
)
#heading(level: 3, numbering: none)[$QQ_ell$-sheaves]

The category of $QQ_ell$-sheaves on $X$ is defined to be the quotient of the
category of $ZZ_ell$-sheaves on $X$ by the Serre subcategory of torsion
$ZZ_ell$-sheaves (see e.g., @bib:Faith1973, Chapter 15).

Given a $ZZ_ell$-sheaf $Phi$ we denote the corresponding $QQ_ell$-sheaf by
$Phi ⊗ QQ_ell$, and its stalk at the geometric point $overline(x)$ of $X$ is
defined to be $Phi_(overline(x)) ⊗_(ZZ_ell) QQ_ell$. Suppose $Phi$ is a
$QQ_ell$-sheaf on $X$ which is represented by a $ZZ_ell$-sheaf $Phi'$, i.e.,
$Phi = Phi' ⊗ QQ_ell$. Then we define
$
  H_c^(i)(X, Phi) = (lim_(arrow.l) H_c^(i)(X, Phi' ⊗ ZZ/(ell^n ZZ))) ⊗_(ZZ_ell)
  QQ_ell.
$
In particular, $H_c^(i)(X, QQ_ell) = H_c^(i)(X, ZZ_ell) ⊗_(ZZ_ell) QQ_ell$.

We will be mostly concerned with the cohomology groups $H_c^(i)(X, QQ_ell)$, or
with the (finite-dimensional) $overline(QQ)_ell$-spaces
$H_c^(i)(X, overline(QQ)_ell) = H_c^(i)(X, QQ_ell) ⊗_(QQ_ell) overline(QQ)_ell$,
where $overline(QQ)_ell$ is an algebraic closure of $QQ_ell$.

#heading(level: 3, numbering: none)[Tate twists]

(@bib:Tate1965, p. 96.)

For every integer $n > 0$, the group of $n^"th"$ roots of unity in
$K = overline(FF)_q$ is denoted by $mu_n$. Let $ell$ be a prime not equal to
$p = "char" K$. Then the groups $mu_(ell^n)$ form a projective system (with
homomorphisms $mu_(ell^n) arrow.r mu_(ell^(n-1))$) and we let
$H = QQ_ell ⊗_(ZZ_ell) lim_(arrow.l) mu_(ell^n)$. The Galois group $G(K, FF_q)$
acts on $mu_(ell^n)$ for each $n$, and thus
#source(58)
it acts on the one-dimensional $QQ_ell$-vector space $H$. For any vector space
$V$ over $QQ_ell$, we define the _Tate twists_ of $V$ by
$V(m) = V ⊗_(QQ_ell) H^(⊗ m)$, where, if $m < 0$, $H^(⊗ m)$ is defined as
$"Hom"(H^(⊗ (-m)), QQ_ell)$. Then if $G(K, FF_q)$ acts on $V$, it acts on
$V(m)$. Similarly we define the twists of a vector space $V$ over
$overline(QQ)_ell$.

As an example of a $QQ_ell$-space $V$ on which $G(K, FF_q)$ acts, consider a
scheme $X_0$ over $FF_q$ and let $X = X_0 times_(FF_q) "Spec" K$ be the scheme
over $K$ obtained by base extension. Then $G(K, FF_q)$ acts on the second
factor, hence on $X$, and hence on $V = H_c^(i)(X, QQ_ell)$ (see
§~@sec:compact-support-properties). Then, in fact, we have
$V(m) = H_c^(i)(X, QQ_(ell)(m))$.

We note that if $Phi$ is a $QQ_ell$-sheaf then we can also talk of the twists
$Phi(m)$ of $Phi$.

== Properties of $ell$-adic cohomology with compact support
<sec:compact-support-properties>

As before, $X$ is a scheme which is separated and of finite type over an
algebraically closed field $K$. If $X$ is projective the groups
$H^(i)(X, QQ_ell)$ and $H_c^(i)(X, QQ_ell)$ coincide. Some of the properties
stated below will be stated for torsion abelian sheaves on $X$. Then by taking
the torsion sheaves $ZZ/(ell^n ZZ)$, taking inverse limits and tensoring with
$QQ_ell$ we get the corresponding statements for the $H_c^(i)(X, QQ_ell)$.

#heading(level: 3, numbering: none)[Base change]
#term-entry("Base change")

(@bib:Deligne1977, p. 49; @bib:Artin1972, XII, §5.)

#formula-item[
  Suppose we have a cartesian diagram of schemes
  #source(59)
  #import "diagrams/05-schemes.typ": base-change-square
  #align(center, base-change-square())
  and $Phi$ is a torsion abelian sheaf on $X$. Then
  $g^(*)(R^i f_!)(Phi) tilde.eq (R^i f'_!)(g'^* Phi)$, for all $i >= 0$.
] <eq:cohomology-base-change>

In the classical case, the analogous result holds for paracompact spaces (see
@bib:Godement1958, 4.17.1).

#corollary[
  Let $overline(s)$ be a geometric point of $S$. Then the stalk
  $(R^i f_! Phi)_(overline(s))$ at $overline(s)$ of the direct image sheaf
  $R^i f_! Phi$ is isomorphic to $H_c^(i)(X_(overline(s)), tilde(Phi))$, where
  $X_(overline(s))$ is the geometric fibre of $f$ over $overline(s)$, and
  $tilde(Phi)$ is the pullback of $Phi$ to $X_(overline(s))$, from the map
  $X_(overline(s)) arrow.r X$.
] <cor:cohomology-geometric-fibre>

#remark[
  If $overline(s)$ is centered at a generic point of $S$, the theorem follows
  essentially as it does in the classical case, i.e., by taking smaller and
  smaller étale neighborhoods of $overline(s)$. So the theorem has content
  mainly for non-generic points of $S$, e.g., closed points.
]

#heading(level: 3, numbering: none)[Finiteness of cohomology]

(@bib:Artin1972, XVII, 5.2.8.1, 5.3.8; @bib:Deligne1977, p. 84, 2.10.)

#formula-item[
  Let $Phi$ be a torsion constructible sheaf on $X$. Then the groups
  $H_c^(i)(X, Phi)$ are finite and they are zero except when
  $0 <= i <= 2 dim X$.
] <eq:cohomology-finiteness>

The groups $H_c^(i)(X, QQ_ell)$ are finite-dimensional vector spaces over
$QQ_ell$.

#source(60)
#heading(level: 3, numbering: none)[Leray Spectral Sequence and Grothendieck
  Spectral Sequence]
#term-entry("Spectral sequences of Leray and Grothendieck")

(@bib:Deligne1977, p. 23; @bib:Artin1972, XVII, 5.1.8.1.)

Let $Phi$ be a torsion sheaf on $X$. Let $f: X arrow.r Y$ be a morphism of
schemes. Then we have a Leray spectral sequence
$ E_2^(p q) = H_c^(p)(Y, R^q f_! Phi) arrow.r.double H_c^(p+q)(X, Phi). $
The way we use this is as follows.

#formula-item[
  Suppose that all the fibres of $f$ are isomorphic to a fixed scheme $Z$ such
  that $H_c^(q)(Z, Phi) = 0$ except for $q = q_0$. Then
  $H_c^(p)(Y, R^(q_0) f_! Phi) tilde.eq H_c^(p+q_0)(X, Phi)$.
] <eq:cohomology-leray-single-degree>

Let $X arrow.r^f Y arrow.r^g Z$ be morphisms of schemes. Then we have a
Grothendieck spectral sequence
$ E_2^(p q) = (R^p g_!)(R^q f_! Phi) arrow.r.double R^(p+q)((g f)_! Phi). $
(For the classical case, see @bib:Hilton1971, p. 299). The way we use this is as
follows.

#formula-item[
  If $R^q f_! Phi = 0$ except for $q = q_0$, then
  $ (R^p g_!)(R^(q_0) f_! Phi) tilde.eq R^(p+q_0)((g f)_! Phi). $
] <eq:cohomology-grothendieck-single-degree>

In most cases in @eq:cohomology-leray-single-degree we will be taking
$Z = AA^d$, affine space of dimension $d$. Then we use the following result on
the cohomology groups of $AA^d$. Let $ell != p$, where $p = "char" K$.

$
  H_c^(i)(AA^d, QQ_ell) = cases(0 & i != 2 d, QQ_(ell)(-d) & i = 2 d).
$ <eq:cohomology-affine-space>

The fact that $H_c^(i)(AA^d, QQ_ell) = 0$ for $i != 2 d$ can be seen, for
example, by using the Comparison Theorem @th:cohomology-comparison which enables
us in some cases to compute $ell$-adic cohomology groups of varieties by looking
at corresponding varieties in characteristic $0$ and
#source(61)
computing classical cohomology. A reference for the fact that the top cohomology
is $QQ_(ell)(-d)$ is @bib:Tate1965, p. 96. We note that it is very important to
keep track of the Tate twist here, as this tells us that if $F$ is the Frobenius
morphism of $AA^d$, the induced action on $H_c^(i)(AA^d, QQ_ell)$ is
multiplication by $q^d$.

#heading(level: 3, numbering: none)[Functoriality of cohomology groups]
#term-entry("Functoriality of cohomology")

Suppose we have a morphism $f: X arrow.r Y$ of schemes and $Phi$ is a sheaf on
$Y$. As in the case of classical sheaf cohomology, we have an induced morphism
$H^(i)(Y, Phi) arrow.r H^(i)(X, f^* Phi)$. In the compact support case, we have
the following. Suppose $f: X arrow.r Y$ is a _finite_ morphism. It can be shown
that we can embed $X, Y$ in proper varieties $tilde(X), tilde(Y)$ with morphisms
$j: X arrow.r tilde(X)$, $j': Y arrow.r tilde(Y)$ and
$tilde(f): tilde(X) arrow.r tilde(Y)$ such that $tilde(f)$ maps $tilde(X) - X$
into $tilde(Y) - Y$. Then, by definition,
$H^(i)(tilde(X), j_! f^* Phi) = H_c^(i)(X, f^* Phi)$ and
$H^(i)(tilde(Y), j'_! Phi) = H_c^(i)(Y, Phi)$. But then by the definitions of
$j_!$ and $j'_!$ we have $tilde(f)^(*)(j'_! Phi) = j_(!)(f^* Phi)$. Hence we
have a homomorphism $H_c^(i)(Y, Phi) arrow.r H_c^(i)(X, f^* Phi)$.

We will also come across the following situation. Let $f: X arrow.r Y$ be a
morphism of schemes. Let $g$ be an automorphism of $X$ (e.g., $g$ belongs to a
group acting on $X$) such that each fibre of $f$ is stable under $g$. Let $Phi$
be a constant sheaf on $X$. Then $g^* Phi$ is a constant sheaf on $X$,
canonically isomorphic to $Phi$. Thus we have a morphism $g^* Phi arrow.r Phi$
which leads to a morphism $tilde(g): (R^i f_!)(g^* Phi) arrow.r R^i f_! Phi$ of
sheaves on $Y$. By Base Change @eq:cohomology-base-change $(R^i f_!)(g^* Phi)$
is isomorphic to $R^i f_! Phi$. Thus we have an induced action $tilde(g)$ on the
sheaf $(R^i f_! Phi)$ on $Y$.

#source(62)
More generally, let $g, g'$ be automorphisms of $X, Y$ respectively such that
#import "diagrams/05-schemes.typ": automorphism-square
#align(center, automorphism-square())
is commutative. Let $Phi$ be a constant sheaf on $X$. Then we have an induced
morphism $tilde(g): g'^(*)(R^i f_! Phi) arrow.r R^i f_! Phi$. If $R^i f_! Phi$
is also a constant sheaf on $Y$, then we have a morphism of $R^i f_! Phi$. (As
an example, see Theorem @th:springer-weyl-representation, Chapter
@ch:characters.)

#heading(level: 3, numbering: none)[Long exact sequence]
#term-entry("Long exact sequence")

(@bib:Artin1972, XVII, p. 350, 5.1.16.3.)

If we have a short exact sequence of torsion abelian sheaves
$0 arrow.r Phi arrow.r cal(G) arrow.r cal(H) arrow.r 0$, where
$Phi, cal(G), cal(H)$ are sheaves on $X$, we have a long exact sequence of
cohomology
$0 arrow.r dots arrow.r H^(i-1)(X, cal(H)) arrow.r H^(i)(X, Phi) arrow.r
H^(i)(X, cal(G)) arrow.r H^(i)(X, cal(H)) arrow.r H^(i+1)(X, Phi) arrow.r
dots$, since the functors $\{R^i Gamma\}$ form a $delta$-functor. Now suppose we
have a closed subscheme $X'$ of $X$ and let $Y = X - X'$. If $Phi$ is a torsion
sheaf on $X$ and $i: X' arrow.r X$, $j: Y arrow.r X$ are inclusions, then the
exact sequence
$0 arrow.r j_(!)(Phi|_Y) arrow.r Phi arrow.r i_(*)(Phi|_(X')) arrow.r 0$ of
sheaves on $X$ gives rise to a long exact sequence
$
  dots arrow.r H_c^(i)(Y, Phi) arrow.r H_c^(i)(X, Phi) arrow.r H_c^(i)(X',
    Phi) arrow.r dots.
$ <eq:cohomology-open-closed-exact-sequence>

#heading(level: 3, numbering: none)[Künneth formula]
#term-entry("Künneth Formula")

(@bib:Artin1972, XVII, p. 368, 5.4.3.)

Let $X_1, X_2$ be schemes. Then there is an isomorphism
$
  H_c^(k)(X_1 times X_2, QQ_ell) tilde.eq ⊕_(i+j=k) \{H_c^(i)(X_1, QQ_ell) ⊗
  H_c^(j)(X_2, QQ_ell)\}.
$ <eq:cohomology-kunneth>

#source(63)
#heading(level: 3, numbering: none)[Cohomology of a quotient of a scheme by a
  finite group]

#formula-item[
  Suppose $G$ is a finite group which acts on a scheme $X$, and suppose the
  quotient $Y = X/G$ exists. (This is always the case, for example, if $X$ is
  quasiprojective; see e.g. @bib:Serre1959, p. 59.) Then
  $H_c^(i)(Y, QQ_ell) tilde.eq H_c^(i)(X, QQ_ell)^G$.

  [Note that $G$ acts on $H_c^(i)(X, QQ_ell)$; the right hand side denotes the
  $G$-invariants in $H_c^(i)(X, QQ_ell)$.]
] <eq:cohomology-finite-quotient>

There is a classical analogue of this theorem for a locally compact space which
has a finite group acting on it and one proves this by means of a _transfer_
map. (See @bib:Borel1960, p. 37.) In the étale case also such a transfer map
exists (@bib:Artin1972, XVII, p. 426, 6.2.5). We will sketch a proof of
@eq:cohomology-finite-quotient based on @bib:Borel1960, loc. cit.

Let $f = pi: X arrow.r Y$ be the canonical map. Let $Phi$ be a constant torsion
sheaf on $Y$, then $f^* Phi$ is a constant sheaf on $X$ and there is a morphism
(morphism of adjunction; see e.g. @bib:Faith1973, p. 232)
$Phi arrow.r f_! f^* Phi$ of sheaves on $Y$. Since each fibre of $pi$ is finite
we have by @eq:cohomology-leray-single-degree that
$H_c^(i)(Y, f_! f^* Phi) tilde.eq H_c^(i)(X, f^* Phi)$. Now the action of $G$ on
$X$ leads to an action of $G$ on the sheaf $(f_! f^* Phi)$ on $Y$. At any
geometric point $overline(y)$ of $Y$ the stalk $(f_! f^* Phi)_(overline(y))$ is
a sum of copies of $Phi_(overline(y))$, labeled by the geometric points of the
fibre, and $G$ permutes these abelian groups transitively. Then the group of
fixed points under $G$ of this stalk is just $Phi_(overline(y))$ which is
embedded in $(f_! f^* Phi)_(overline(y))$. We see that $(f_! f^* Phi)^G = Phi$.
Now the inclusion $Phi arrow.r (f_! f^* Phi)^G$ and the map
$(f_! f^* Phi) arrow.r Phi$
#source(64)
given by $x arrow.r sum_(g in G) g x$ (the transfer map) give rise to maps
$
  mu: H_c^(i)(X, f^* Phi) arrow.r H_c^(i)(Y, f_! f^* Phi) arrow.r H_c^(i)(Y,
    Phi),
$
$
  sigma: H_c^(i)(Y, Phi) arrow.r H_c^(i)(Y, (f_! f^* Phi)^G) arrow.r
  H_c^(i)(Y, f_! f^* Phi) arrow.r H_c^(i)(X, f^* Phi)
$
and we can check that $mu sigma$ is multiplication by $|G|$ and $sigma mu$ is
action by $sum_(g in G) g$. Furthermore $sigma$ is just the map
$H_c^(i)(Y, Phi) arrow.r H_c^(i)(X, f^* Phi)$ induced by functoriality from
$pi$, and since $pi$ commutes with the action of $G$ (regarding $G$ as acting
trivially on $Y$) $sigma$ maps $H_c^(i)(Y, Phi)$ into $H_c^(i)(X, f^* Phi)^G$.
Then $sigma mu$ is multiplication by $|G|$ on $H_c^(i)(X, f^* Phi)^G$.

Now we take $Phi_n = ZZ/(ell^n ZZ)$, take projective limits of cohomology groups
and tensor with $QQ_ell$, so that our cohomology groups are then vector spaces
over $QQ_ell$. We then see that we have an isomorphism
$H_c^(i)(Y, QQ_ell) arrow.r H_c^(i)(X, QQ_ell)^G$, as required.

The following two theorems are useful in computing cohomology. An example will
be given at the end.

#heading(level: 3, numbering: none)[Specialization Theorem]

(@bib:Artin1972, XVI, Theorem 2.1 and Corollary 2.5.)

Let $R$ be a discrete valuation ring with residue field $k$ and quotient field
$tilde(k)$. Then $"Spec" R$ has exactly two points: a closed point $x_0$ with
$k(x_0) = k$ and a generic point $x_1$ with $k(x_1) = tilde(k)$ (see
@bib:Hartshorne1977, p. 74). Let $overline(x)_j$ be a geometric point of
$"Spec" R$ centered at $x_j$ ($j = 0, 1$). Let $X$ be a scheme over $R$, i.e.,
let $f: X arrow.r "Spec" R$ be a morphism, and let $Phi$ be a torsion abelian
sheaf on $X$. By Base Change @cor:cohomology-geometric-fibre
#source(65)
we have that the stalk $((R^i f_!)(Phi))_(overline(x)_j)$ of $(R^i f_!)(Phi)$ at
$overline(x)_j$ is isomorphic to $H_c^(i)(X_(overline(x)_j), Phi_j)$
($j = 0, 1$) where $Phi_j$ is the pullback of $Phi$ to $X_(overline(x)_j)$. Now
if in addition we have $f$ proper and smooth (see @bib:Hartshorne1977, p. 268
for the definition of a smooth morphism of schemes) and $Phi$ is a constructible
locally constant $p'$-torsion abelian sheaf where $p = "char" k$, then the
Specialization Theorem says that the stalks at both points are isomorphic, i.e.,
$
  H_c^(i)(X_(overline(x)_0), Phi_0) tilde.eq H_c^(i)(X_(overline(x)_1), Phi_1).
$

#heading(level: 3, numbering: none)[Comparison Theorem]

(@bib:Artin1972, XI, 4.4; @bib:Deligne1977, p. 51.)

#theorem[
  Let $X$ be a scheme (separated, finite type) over $CC$. Then
  $H_c^(i)(X, ZZ/(n ZZ)) tilde.eq H_c^(i)(X^"an", ZZ/(n ZZ))$ for any $n$, where
  $X^"an"$ is the space $X$ with its classical topology and the cohomology group
  on the right is the usual cohomology group with compact support.
] <th:cohomology-comparison>

#heading(level: 3, numbering: none)[The Frobenius morphism]
#term-entry("Frobenius morphism")

(@bib:Tate1965, p. 100; @bib:Deligne1977, pp. 79, 80.)

Suppose we have a scheme $X_0$ which is separated and of finite type over
$FF_q$. Let $K = overline(FF)_q$. Then $X = X_0 times_(FF_q) "Spec" K$ is
obtained from $X_0$ by base extension and is a scheme over $K$.

The Frobenius morphism $F_0$ of $X_0$ is the morphism of ringed spaces
$(X_0, cal(O)_(X_0))$ which is the identity on the underlying topological space
$X_0$, whereas on any $alpha in cal(O)_(X_0)(U)$ where $U$ is a (Zariski) open
set of $X_0$, it acts as $alpha arrow.r alpha^q$. Since $F_0$
#source(66)
acts trivially on $(X_0)_"et"$ it induces the identity on
$H_c^(i)(X_0, QQ_ell)$.

We now have a morphism $F_0 times sigma$ of $X$, where $sigma$ is the element of
the Galois group $G(K, FF_q)$ given by $x arrow.r x^q$. Again $F_0 times sigma$
induces the identity on $H_c^(i)(X, QQ_ell)$ and hence $F_0 times 1$ and
$1 times sigma$ act as inverses on $H_c^(i)(X, QQ_ell)$. The morphism
$F = F_0 times 1$ is called the geometric Frobenius morphism and $1 times sigma$
is called the arithmetic Frobenius morphism of $X$.

#remark[
  Compare the geometric and arithmetic Frobenius morphisms introduced in Chapter
  @ch:algebraic-groups for affine varieties defined over $FF_q$.
]

Let $Phi$ be any sheaf on $X_0$. Then $F$ induces an action on the stalk
$Phi_(overline(x))$ of $Phi$ at any geometric point of $X_0$ centered at a
closed point $x$ of $X_0$, as follows. Suppose we have a morphism
$overline(x): "Spec" overline(k(x)) arrow.r X_0$ with image $x$; then the
inverse image of $Phi$ is precisely the constant sheaf $Phi_(overline(x))$ on
$"Spec" overline(k(x))$. The morphism
$sigma_x = sigma^([k(x):FF_q]): "Spec" overline(k(x)) arrow.r "Spec"
overline(k(x))$
gives rise by functoriality to a morphism of
$Gamma("Spec" overline(k(x)), Phi_(overline(x)))$ onto
$Gamma("Spec" overline(k(x)), sigma_x^* Phi_(overline(x)))$, i.e., an
endomorphism of $Phi_(overline(x))$. We define the _local Frobenius_ morphism
$F_x$ of $Phi_(overline(x))$ to be the inverse of this.

We now state the important fixed point formula of Grothendieck (see
@bib:Deligne1977, p. 86, Theorem 3.2; @bib:Serre1975, §1;
@bib:Grothendieck1966).

#term-entry("Trace formula of Grothendieck")

#theorem(title: [Trace Formula])[
  $ |X^F| = sum_(i >= 0) (-1)^i "Tr"(F, H_c^(i)(X, QQ_ell)). $
] <th:grothendieck-trace-formula>

Here $X^F$ is the set of closed points of $X$ fixed by $F$. If $X$ is an affine
variety defined over $FF_q$ (as in Chapter @ch:algebraic-groups) this
#source(67)
formula enables us to compute the number of $FF_q$-rational points of $X$.

The following theorem (@bib:Grothendieck1972, XXI, Theorem 5.2.2), which will be
used in Chapter @ch:characters, gives a connection between the local Frobenius
morphisms and the action of $F$ on cohomology.

#definition[
  A $QQ_ell$-sheaf $Phi$ on $X_0$ is called integral if, for every geometric
  point $overline(x)$ centered at a closed point $x$ of $X_0$, $F_x$ has
  eigenvalues on $Phi_(overline(x))$ which are algebraic integers.
]

#theorem(numbered: false)[
  If $Phi$ is integral, then the eigenvalues of $F$ on $H_c^(i)(X, Phi)$ are
  algebraic integers.
] <th:cohomology-integrality>

#corollary[
  Let $Phi$ be a $QQ_ell$-sheaf on $X_0$ such that for all geometric points
  centered at closed points the eigenvalues of $F_x$ on the stalks are all
  divisible by $q^(n [k(x):FF_q])$. Then the eigenvalues of $F$ on
  $H_c^(i)(X, Phi)$ are divisible by $q^n$.
] <cor:cohomology-frobenius-divisibility>

#proof[
  Apply the above theorem to $Phi(n)$.
]

#remark[
  This theorem is proved for $d = 1$ (where $d = dim X_0$) by using two
  expressions for the “$L$-function” $Z(X_0, Phi, t)$ (see @bib:Serre1975, p. 2)
  and then by induction on $d$ by fibering $X_0$ over a curve.
]

We now make some remarks about reductive group schemes. For the definition of a
group scheme, see e.g., @bib:Hartshorne1977, p. 324. Roughly, a group scheme
$cal(G)$ over $ZZ$ is a scheme together with multiplication, identity and
inverse morphisms satisfying certain axioms.

Consider the reductive linear algebraic group $G$ defined over $FF_q$ that we
have studied in Chapters @ch:algebraic-groups through @ch:harish-chandra. Assume
#source(68)
that $G$ is split over $FF_q$ (see @rem:split-group). Grothendieck and Demazure
@bib:Grothendieck1970 have shown that there is a reductive group scheme $cal(G)$
over $ZZ$ from which we can recover $G$. In other words, there is a scheme
$cal(G) arrow.r "Spec" ZZ$ such that we can extend the base and get a morphism
$f: cal(G) times_ZZ "Spec" A arrow.r "Spec" A$ where $A$ is a discrete valuation
ring with residue field $FF_q$, the fibre of $f$ over the closed point of
$"Spec" A$ is isomorphic to $G$, and the fibre over the generic point of
$"Spec" A$ is isomorphic to a corresponding group in characteristic $0$.
Similarly we have a scheme $cal(G)/cal(B)$ over $ZZ$ which gives rise to the
variety $G/B$ where $B$ is a Borel subgroup of $G$. For these proper flag
schemes the Specialization and Comparison theorems compare their $ell$-adic
cohomology with the classical cohomology of the corresponding varieties in
characteristic $0$. The group $W = W(T_0)$ acts on $G/T_0$. The affine-space
fibration $G/T_0 arrow.r G/B_0$ transports this action to the compactly
supported cohomology of $G/B_0$. For constant $QQ_ell$ coefficients, the
comparison isomorphisms for the proper flag schemes are compatible with this
transported action.
#ed-note[
  The transported action is the usual coinvariant action tensored with the sign
  character. The usual action is described by Chern classes; comparison for the
  proper flag schemes preserves these classes, and Poincaré duality identifies
  the transported action. Thus its invariant subspace occurs in the top degree,
  rather than degree zero. See #cite(<BGG1973>, form: "full"), §2, Theorem 3\;
  compare #cite(<Digne2020>, form: "full"), Corollary 10.2.7.
]

We now prove a theorem due to Steinberg (@bib:Steinberg1968b, 14.14) which will
be used in Chapter @ch:lusztig-deligne, as an illustration of the theorems
mentioned in this chapter.

#theorem[
  Let $G$ be a connected reductive algebraic group defined over $FF_q$, and $F$
  the Frobenius morphism. Then the number of $F$-stable maximal tori is
  $|G^F|_p^2$.
] <th:steinberg-representation>

#source(69)
#proof[
  Let $T_0, B_0, W = W(T_0)$, $N = N(T_0)$ be as in Chapter
  @ch:classification-of-tori. Then we want to compute $|(G/N)^F|$. Now $W$ acts
  on $G/T_0$ by the rule $w(x T_0) = x T_0 dot(w)$, and
  $G/N tilde.eq (G/T_0)/W$. By the Trace Formula @th:grothendieck-trace-formula
  we have
  $
    |(G/N)^F| & = sum_i (-1)^i "Tr"(F, H_c^(i)(G/N, QQ_ell)) \
              & = sum_i (-1)^i "Tr"(F, H_c^(i)(G/T_0, QQ_ell)^W)
  $
  by @eq:cohomology-finite-quotient.

  There is a morphism $G/T_0 arrow.r G/B_0$ whose fibres are all isomorphic to
  $U_0$, and hence to affine space of dimension $d$, where $B_0 = T_0 U_0$.
  Thus, by @eq:cohomology-leray-single-degree and @eq:cohomology-affine-space we
  have
  $ H_c^(i)(G/T_0, QQ_ell) tilde.eq (H_c^(i-2d)(G/B_0, QQ_ell))(-d). $
  By the Specialization and Comparison Theorems it follows that
  $H_c^(j)(G/B_0, QQ_ell) tilde.eq H_c^(j)(tilde(G)/tilde(B), QQ_ell)$ where
  $tilde(G)$ is a group analogous to $G$ in characteristic $0$ and $tilde(B)$ is
  a Borel subgroup of $tilde(G)$.

  Moreover, this isomorphism preserves the transported action of $W$ on
  cohomology. In characteristic $0$, the direct sum
  $⊕_j H^(j)(tilde(G)/tilde(B), QQ_ell)$ with this action is the regular
  representation of $W$, and the trivial representation occurs in degree $2 d$.
  So we have the same situation for $⊕_j H_c^(j)(G/B_0, QQ_ell)$. Now just as in
  @eq:cohomology-affine-space we see that $H_c^(2d)(G/B_0, QQ_ell)$ is
  isomorphic to $QQ_(ell)(-d)$ and $F$ acts on this by multiplication by $q^d$
  (in fact, this arises from the “cell decomposition” of $G/B_0$, see e.g.,
  @bib:Borel1969, p. 347). Hence on $H_c^(2d)(G/B_0, QQ_ell)(-d)$, $F$ acts as
  multiplication by $q^(2d)$. From this it follows that $|(G/N)^F| = q^(2d)$, as
  required.
]
