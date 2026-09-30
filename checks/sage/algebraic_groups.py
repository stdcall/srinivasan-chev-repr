"""Exact checks for Chapter I, coordinate rings and the Bruhat refinement.

The defining ideal (x^2) has the same zero set as (x) but is not prime.
This is a counterexample to using an arbitrary defining ideal as the
coordinate ideal; it is not a proof of the Nullstellensatz.

The printed restricted factor U intersect w U^- w^-1 belongs on the
left in the Bruhat refinement. The SL3 example below disproves uniqueness
when it is placed on the right. Symbolic matrix entries additionally
verify injectivity for the corrected parametrization of that SL3 cell.
The check does not prove Bruhat decomposition for every reductive group.
"""
from sage.all import QQ, PolynomialRing, matrix, identity_matrix

R = PolynomialRing(QQ, 'x')
x = R.gen()
I = R.ideal(x**2)
assert x not in I and x*x in I
assert I.radical() == R.ideal(x)

# A three-cycle is a determinant-one representative of s1 s2.
w = matrix(QQ, [[0, 0, 1], [1, 0, 0], [0, 1, 0]])
e = identity_matrix(QQ, 3)
v = matrix(QQ, e)
v[0, 1] = 1
assert w.det() == 1
# v is in U and in w U^- w^-1, but w v w^-1 is also in U.
lower = w.inverse() * v * w
assert all(lower[i, j] == 0 for i in range(3) for j in range(i + 1, 3))
assert all(lower[i, i] == 1 for i in range(3))
u = w * v.inverse() * w.inverse()
assert all(u[i, j] == 0 for i in range(3) for j in range(i))
assert all(u[i, i] == 1 for i in range(3))
assert u != e and v != e
assert e * w * e * e == u * w * e * v

# Corrected factor order: restricted left factor, full right factor.
S = PolynomialRing(QQ, names=('a', 'b', 'c', 'd', 'e', 'r', 's'))
a, b, c, d, q, r, s = S.gens()
L = S.fraction_field()
left = matrix(L, [[1, a, b], [0, 1, 0], [0, 0, 1]])
right = matrix(L, [[1, c, d], [0, 1, q], [0, 0, 1]])
torus = matrix(L, [[r, 0, 0], [0, s, 0], [0, 0, 1/(r*s)]])
M = left * w.change_ring(L) * torus * right
assert M[1, 0] == r
assert M[2, 1] == s
assert M[0, 0] / r == a
assert M[0, 1] == a*r*c + b*s
assert (M[0, 1] - a*r*c) / s == b
assert M[1, 1] / r == c
assert M[1, 2] / r == d
assert M[2, 2] / s == q
assert M.det() == 1
print('ok algebraic_groups: defining-ideal counterexample; '
      'SL3 nonuniqueness counterexample; corrected cell parameters')
