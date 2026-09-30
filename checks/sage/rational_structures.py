"""Exact finite counterexamples for the rational-structure corrections.

These calculations refute missing hypotheses. They do not establish Lang's
theorem, descent of translation spaces, or the general parabolic-intersection
theorem. The latter is Proposition 3.4.8 of Digne and Michel (2020).
"""
from sage.all import GF, PolynomialRing, matrix


# A regular function defined over F_3 need not be F_3-valued on K-points.
# Translation of t by a point outside F_3 acquires a coefficient outside F_3.
extension = GF(9, name="a")
a = extension.gen()
assert a**3 != a
assert extension(0) + a == a


# Upper triangular GL_2(F_3), with two rational Levi complements of the
# same Borel. The printed intersection formula fails if they need not
# contain the same maximal torus.
field = GF(3)
nonzero = [x for x in field if x != 0]


def key(mat):
    return tuple(mat.list())


diagonal = [matrix(field, [[r, 0], [0, s]])
            for r in nonzero for s in nonzero]
unipotent = [matrix(field, [[1, t], [0, 1]]) for t in field]
u = matrix(field, [[1, 1], [0, 1]])
conjugate = [u * d * u.inverse() for d in diagonal]
borel = {key(d * v) for d in diagonal for v in unipotent}
common_levi_keys = {key(d) for d in diagonal} & {key(d) for d in conjugate}
common_levi = [d for d in diagonal if key(d) in common_levi_keys]
right_hand_side = {key(d * v) for d in common_levi for v in unipotent}
assert len(borel) == 12
assert len(common_levi) == 2
assert len(right_hand_side) == 6
assert right_hand_side < borel

# For compatible Levi complements containing the same torus, the same
# formula reduces to the ordinary Borel decomposition, in this example.
compatible_rhs = {key(d * v) for d in diagonal for v in unipotent}
assert compatible_rhs == borel

print("ok rational_structures: F_9 translation counterexample; "
      "GL_2(F_3) incompatible-Levi counterexample and compatible example")


# Passage: prop:twisted-frobenius.
# Bounded polynomial-ring check: g cycles three coordinate variables,
# F cubes variables and fixes coefficients; phi cubes coefficients and
# fixes variables. The old partner phi*g leaves an unwanted g^2 factor.
# The inverse partner phi*g^-1 restores a |-> a^3. This is not a proof
# of general descent or of Proposition2.1 for arbitrary affine varieties.
coordinate_ring = PolynomialRing(extension, names=('x0', 'x1', 'x2'))
x0, x1, x2 = coordinate_ring.gens()
geo = coordinate_ring.hom([x0**3, x1**3, x2**3], coordinate_ring)
cycle = coordinate_ring.hom([x1, x2, x0], coordinate_ring)
cycle_inverse = coordinate_ring.hom([x2, x0, x1], coordinate_ring)


def arithmetic(poly):
    return coordinate_ring({powers: coefficient**3
                            for powers, coefficient in poly.dict().items()})


samples = [coordinate_ring(0), coordinate_ring(1), coordinate_ring(a),
           x0, x1, x2, a*x0 + x1*x2,
           (a + 1)*x0**2*x1 + a*x2**2 + x0*x1*x2]
for poly in samples:
    assert cycle(cycle(cycle(poly))) == poly
    assert cycle(cycle_inverse(poly)) == poly
    assert arithmetic(cycle(poly)) == cycle(arithmetic(poly))
    assert geo(cycle(arithmetic(cycle_inverse(poly)))) == poly**3
    # Over F_9 the arithmetic map has order2, commuting with order3 g;
    # the corrected partner therefore has order dividing6 here.
    iterated = poly
    for _ in range(6):
        iterated = arithmetic(cycle_inverse(iterated))
    assert iterated == poly
assert geo(cycle(arithmetic(cycle(x0)))) == x2**3
assert x2**3 != x0**3
print('Three-cycle rational structure: old phi*g fails on x0; '
      'phi*g^-1 restores cubing on eight polynomial samples over F_9.')
