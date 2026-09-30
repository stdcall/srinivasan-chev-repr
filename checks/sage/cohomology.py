"""Exact finite checks of corrections and normalizations in Chapters V and VI.

The matrix is a counterexample to the original degree-independent local
divisibility hypothesis. The curve checks cover q=3,4,5,9; they are not a
formal computation of étale cohomology. The general dimension argument
uses smooth plane-curve genus and the open/closed exact sequence.
The C_3 check tests inverse pullback and the torus-character convention.
The q=7 hyperelliptic check gives a lower bound on automorphisms.
"""
from sage.all import CyclotomicField, GF, ZZ, PolynomialRing, matrix, vector

# A Coxeter torus for SU_3(2) has cocharacter Frobenius -2 times a
# three-cycle on the A_2 lattice. Its order is det(F-1)=3 and its split
# rank is zero, although SU_3(2)'s centre also has three rational points.
# This is one root-lattice computation, not a classification of all tori.
coxeter = matrix(ZZ, [[0, -1], [1, -1]])
torus_frobenius = -2 * coxeter
assert coxeter**3 == matrix.identity(ZZ, 2)
assert (torus_frobenius - matrix.identity(ZZ, 2)).det() == 3
assert (torus_frobenius - 2 * matrix.identity(ZZ, 2)).rank() == 2


# Passage: cor:cohomology-frobenius-divisibility.
# On Spec(F_16) over F_4 a rank-one 3-adic sheaf can have local Frobenius
# eigenvalue 4. Geometric base change gives two points and global F below.
# Local divisibility by 4 does not imply global divisibility by 4.
frobenius = matrix(ZZ, [[0, 4], [1, 0]])
assert frobenius**2 == 4 * matrix.identity(ZZ, 2)
assert frobenius.charpoly() == frobenius.charpoly().parent().gen()**2 - 4
assert set(frobenius.eigenvalues()) == {-2, 2}
assert all(v % 4 != 0 for v in frobenius.eigenvalues())


for q in (3, 4, 5, 9):
    field = GF(q, 'a')
    ring = PolynomialRing(field, names=('x', 'y', 'z'))
    x, y, z = ring.gens()
    curve = x * y**q - x**q * y - z**(q + 1)
    assert curve.total_degree() == q + 1
    assert curve.derivative(x) == y**q
    assert curve.derivative(y) == -x**q
    assert curve.derivative(z) == -z**q
    # Simultaneous vanishing of these partial derivatives forces x=y=z=0,
    # which is not a projective point, also after algebraic field extension.
    boundary = [(field(1), t) for t in field
                if curve(field(1), t, field(0)) == 0]
    boundary += [(field(0), field(1))]
    assert len(boundary) == q + 1
    genus = q * (q - 1) // 2
    assert 2 * genus + (len(boundary) - 1) == q**2

print('Cohomology: exact degree-2 divisibility counterexample; '
      'smooth-curve and boundary checks for q=3,4,5,9 passed.')


# Passage: def:lusztig-deligne-representation.
# Bounded normalization check for G=T=C_3, X=T. Functions carry the usual
# inverse pullback: rho(a)f(x)=f(a^{-1}x). It does not compute cohomology
# of a positive-dimensional Deligne--Lusztig variety.
cyclotomic = CyclotomicField(3)
zeta = cyclotomic.gen()


def translation_pullback(shift):
    """Inverse pullback of the point permutation i |-> i+shift on C_3."""
    return matrix(cyclotomic, 3, 3,
                  lambda i, j: int(j == (i - shift) % 3))


left_generator = translation_pullback(1)
new_torus_generator = translation_pullback(1)  # geometric h |-> h t
old_torus_generator = translation_pullback(-1)  # geometric h |-> h t^-1
for character_power in (1, 2):
    character = zeta**character_power
    new_vector = vector(cyclotomic,
                        [zeta**(-character_power * i) for i in range(3)])
    old_vector = vector(cyclotomic,
                        [zeta**(character_power * i) for i in range(3)])
    for exponent in range(3):
        assert new_torus_generator**exponent * new_vector == (
            character**exponent * new_vector)
        assert left_generator**exponent * new_vector == (
            character**exponent * new_vector)
        assert old_torus_generator**exponent * old_vector == (
            character**exponent * old_vector)
        assert left_generator**exponent * old_vector == (
            character**(-exponent) * old_vector)
    new_projector = sum((character**(-i) * new_torus_generator**i
                         for i in range(3)), matrix.zero(cyclotomic, 3)) / 3
    old_projector = sum((character**(-i) * old_torus_generator**i
                         for i in range(3)), matrix.zero(cyclotomic, 3)) / 3
    assert new_projector.rank() == old_projector.rank() == 1
    assert new_projector * new_vector == new_vector
    assert old_projector * old_vector == old_vector

print('C_3 normalization: exact cyclotomic inverse-pullback check gives '
      'R_T^T(theta)=theta with geometric +, theta^-1 with geometric -.')


# Passage: exm:sl-two-lusztig-deligne-curve.
# For odd q, a Mobius matrix over F_q with determinant delta lifts to
# (x,y) |-> ((a*x+b)/(c*x+d), sqrt(delta)*y/(c*x+d)^((q+1)/2)).
# The identity below is checked on every PGL_2(F_7) representative.
# Over the algebraic closure both square roots exist, so each of the 336
# base transformations has two distinct lifts. This is a lower bound,
# not a claim that these are all automorphisms of the curve.
q = 7
prime_field = GF(q)
poly_ring = PolynomialRing(prime_field, 'x')
x = poly_ring.gen()
quadratic_field = GF(q**2, 'b')
projective_matrices = set()
for a in prime_field:
    for b in prime_field:
        for c in prime_field:
            for d in prime_field:
                entries = (a, b, c, d)
                if a*d - b*c == 0:
                    continue
                first = next(value for value in entries if value != 0)
                projective_matrices.add(tuple(value / first for value in entries))
for a, b, c, d in projective_matrices:
    determinant = a*d - b*c
    numerator, denominator = a*x + b, c*x + d
    assert (numerator**q * denominator - numerator * denominator**q
            == determinant * (x**q - x))
    roots = quadratic_field(determinant).sqrt(all=True)
    assert len(roots) == 2
    assert all(root**2 == quadratic_field(determinant) for root in roots)
assert len(projective_matrices) == q*(q**2 - 1) == 336
assert 2 * len(projective_matrices) == 672
assert 672 > 84 * ((q - 1)//2 - 1) == 168
print('Hyperelliptic q=7: all336 PGL_2 base transformations preserve the '
      'branch equation and have two lifts; lower bound672 exceeds168.')
