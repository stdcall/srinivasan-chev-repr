"""Exact checks for the initial SL2 sum and Artin--Schreier maps.

Finite checks q=3,5,9 supplement the symbolic matrix computation.
They are not a proof of the formulas for all prime powers.
"""
from sage.all import GF, PolynomialRing, QQ, CyclotomicField, matrix

R = PolynomialRing(QQ, names=('a', 'b'))
a, b = R.gens()
u = lambda t: matrix(R, [[1, t], [0, 1]])
w = matrix(R, [[0, 1], [-1, 0]])
A = matrix(R, [[0, 1], [0, 0]])
Aprime = matrix(R, [[1, 0], [0, -1]])
g = u(a) * w * u(b)
assert (A * g * Aprime * g.inverse()).trace() == 2 * b

for q in (3, 5, 9):
    F = GF(q, name='t')
    p = F.characteristic()
    C = CyclotomicField(p)
    zeta = C.gen()
    psi = lambda x: zeta ** int(F(x).trace())
    big = sum((psi(2 * b) for a in F for b in F), C(0))
    assert big == q * sum((psi(2 * b) for b in F), C(0)) == 0
    assert q + big == q
    assert q + q * q == q * (q + 1)
    images = set()
    for a in F:
        for b in F:
            gf = matrix(F, [[1, a], [0, 1]]) * matrix(F, w)
            gf *= matrix(F, [[1, b], [0, 1]])
            images.add(tuple((gf * matrix(F, Aprime) * gf.inverse()).list()))
    assert len(images) == q * q

    E = GF(q ** p, name='e')
    shift = next(t for t in E if t**q - t != 0
                 and (t**q - t)**q == t**q - t)
    parameter = shift**q - shift
    assert parameter**q == parameter
    for x in list(E)[:20]:
        assert (x + shift)**q == x**q + shift + parameter
        assert ((x + shift)**q - (x + shift)) == x**q - x + parameter
    E2 = GF(q*q, name='e2')
    x = next(t for t in E2 if (t**q - t)**q != t**q - t)
    parameter2 = x**q - x
    assert (x**q)**q - x**q == parameter2**q != parameter2
    print(f'q={q}: q² distinct big-cell orbit points; exact character sum; '
          'F-stable parameter and nonstable counterexample checked')
print('Symbolic SL2 trace equals 2b; all focused checks passed.')

# A symbolic Heisenberg example detects the unchosen-section ambiguity
# in the printed product map. It does not prove the repaired torsor theorem.
S = PolynomialRing(QQ, names=('t', 'c'))
t, c = S.gens()
I = matrix.identity(S, 3)
X = matrix(S, 3, 3, {(0, 1): 1})
Y = matrix(S, 3, 3, {(0, 2): 1})
Z = matrix(S, 3, 3, {(1, 2): 1})
assert X * Z - Z * X == Y
h = I + t * X
l = I - t * X
assert h * l == I
mu = lambda v: v[0, 2] + c * v[1, 2]
assert mu(X) == 0 and mu(Y) == 1
assert mu(Z) == c
assert mu(l * Z * l.inverse()) == c - t
assert mu(l * X * l.inverse()) == 0
assert mu(l * Y * l.inverse()) == 1
print('Exact Heisenberg ambiguity: the same h*l=identity changes mu(Z) '
      'from c to c-t while retaining mu(X)=0 and mu(Y)=1.')
