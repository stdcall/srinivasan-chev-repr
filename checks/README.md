# Checks

Run the exact Sage calculations with `just check-sage` and the Lean proofs
and axiom audit with `just check-lean`.
Each calculation below concerns only its stated examples or symbolic model.
Finite checks supplement the mathematical arguments; they do not establish
the general algebraic-group or cohomological theorems.
Page references below refer to the printed 1979 edition.

## Sage

### `sage/algebraic_groups.py`

Chapter I, coordinate algebra (p. 1) and Bruhat refinement (p. 7,
`passage:bruhat-refinement`). In the polynomial ring over the rationals,
the ideals `(x²)` and `(x)` have the same zero set, but `(x²)` is not prime.
This refutes use of an arbitrary defining ideal as the coordinate ideal;
it does not prove the Nullstellensatz.

For a three-cycle Weyl representative in SL₃, exact matrices give distinct
factorizations when the restricted factor `U ∩ wU⁻w⁻¹` is placed on the
right. Symbolic matrices over a rational-function field recover all seven
parameters of the corrected cell, with nonzero torus parameters. This checks
injectivity for that cell, rather than existence or uniqueness for all groups.

### `sage/rational_structures.py`

Chapter II, rational functions in the proof of Lang's theorem (p. 11): a
function defined over the field of three elements need not take values in
that field at extension-field points. Translation by a point in the field
of nine elements need not preserve the original coefficient field.

Chapter IV, Lemma 4.4 (p. 28, `lem:parabolic-intersection`): two rational
Levi complements of the upper-triangular GL₂ over the field of three
elements give an intersection product of size six, while the Borel has
size twelve. Choosing both Levi complements to contain the same torus
recovers the Borel in this example. This demonstrates the missing hypothesis;
it does not prove the general parabolic-intersection theorem.

Chapter II, Proposition 2.1 (p. 8, `prop:twisted-frobenius`): in a
three-variable polynomial ring over the field of nine elements, geometric
Frobenius cubes variables, arithmetic Frobenius cubes coefficients, and
`g` cycles the variables. The partner `φg` fails on the first variable.
The corrected partner `φg⁻¹` restores cubing on eight explicit polynomials,
commutes with the stated maps there, and has order dividing six in this model.
This is a counterexample and bounded consistency check, not a descent proof.

### `sage/cohomology.py`

Chapter V, Corollary 5.13 (p. 57,
`cor:cohomology-frobenius-divisibility`): the integral matrix with rows
`(0,4)` and `(1,0)` squares to four times the identity but has eigenvalues
±2. It models the two geometric points of the degree-two extension of
the field of four elements and refutes a degree-independent local
divisibility hypothesis.

Chapter VI, the SL₂ curve example (pp. 62–63,
`exm:sl-two-lusztig-deligne-curve`): for `q=3,4,5,9`, the Hermitian plane
curve has degree `q+1`, the three stated partial derivatives, and `q+1`
boundary points. The dimension check uses the smooth plane-curve genus
`q(q−1)/2` and the open–closed exact sequence to obtain `q²`. Sage does not
compute étale cohomology here.

Chapter VI, the definition of the Deligne–Lusztig representation
(pp. 60–61, `def:lusztig-deligne-representation`): functions on the cyclic
group of order three over the third cyclotomic field test inverse pullback,
both nontrivial torus characters, all three generator powers, and their
rank-one projectors. The geometric right action `h ↦ ht` gives left character
`θ`, whereas `h ↦ ht⁻¹` gives `θ⁻¹`. This checks the character normalization;
it is not a proof of the general cohomological character formula.

The hyperelliptic remark in the same curve example (p. 63) is checked for
`q=7`: all 336 normalized PGL₂ matrices preserve the branch equation in
the required form, and both determinant square roots exist over the field
of 49 elements. Their two lifts give a lower bound of 672 automorphisms,
exceeding the genus-three Hurwitz bound of 168. This does not determine the
entire automorphism group. The argument assumes odd characteristic and
uses the smooth projective model of `y²=x^q−x`.

Chapter VI, the remaining central-torus case (pp. 85, 89): on the A₂
root lattice, a Coxeter element has order three and the twisted Frobenius
matrix is minus twice that element. The determinant of `F−1` is three
and `F−2` has full rank. Thus the corresponding SU₃(2) torus has three
rational points and split rank zero. This supplies a counterexample to
inferring splitness from equality with the rational centre; the general
orthogonality and dimension arguments use the cited adjoint-group reduction.

### `sage/characters_initial.py`

Chapter VII, the initial SL₂ sum (p. 101): symbolic matrices give trace
`2b`, independent of the other big-cell coordinate `a`. Exact additive
character sums and enumeration of the orbit points for `q=3,5,9` check
the missing factor `q` and the `q²` distinct points. Artin–Schreier
translations for these fields test stable parameters and a nonstable
parameter counterexample (p. 100); translation identities are checked on
at most twenty extension-field elements for each chosen parameter.

For the fibre parametrization on p. 121, a symbolic Heisenberg example
with `[X,Z]=Y` gives two representatives of the identity whose transformed
functional values at `Z` differ. It establishes the representative-choice
ambiguity, rather than the existence of a regular section or the repaired
torsor argument.

### Text identity

The Sage checks are associated with the following SHA-256 identities of
the mathematical text. These identify the text snapshot; the scripts do
not automatically verify these hashes. Recheck the correspondence and
update the identities when the mathematical text changes. The recorded
Chapter VI normalization check used the Chapter VI identity shown here.

| Text | SHA-256 |
| --- | --- |
| `content/01-algebraic-groups.typ` | `7b5702d02cf85af8f57a274b8dd1a51ac6df301a7f884ca0defc9721242106c5` |
| `content/02-tori.typ` | `882c16523ca749eb9518a870100baaac4a8f3459d7755dfb91b0976006b8bb70` |
| `content/04-harish-chandra.typ` | `f1239768c5f5246ab2cb9e92fdcaeef644779c7517af6f7a5895f0fd7f7468ef` |
| `content/05-adic-cohomology.typ` | `f899cb89adf48d827f6839cc638ffbafd7325db3a43af6188aca4c306031138b` |
| `content/06-lusztig-deligne.typ` | `5080412bc868e89abee728115214b31b56a5fa84380faeb08a1c3b9fde9d56ce` |
| `content/07-characters.typ` | `9d3b6d468ead112da0d5a16dec865b9ead8dd4055ab0e6fa9caff0aa9859292d` |

## Lean

The scope and passage labels are recorded in `lean-proofs.json`.
The proofs use the Lean toolchain and mathlib revision pinned in
`lean/lean-toolchain` and `lean/lake-manifest.json`.

- `Srinivasan.bruhat_factor_unique`, in `lean/Srinivasan/BruhatUniqueness.lean`,
  formalizes the cancellation step in the Bruhat refinement (Chapter I,
  p. 7, `passage:bruhat-refinement`). For an arbitrary group, subgroups
  `H,K`, and element `w`, assume that `h∈H` and `w⁻¹hw∈K` imply `h=1`.
  Equality `h₁wk₁=h₂wk₂` then gives equality of both factors. The structural
  intersection hypothesis, existence of the decomposition, uniqueness of
  the Weyl element, and splitting of the Borel factor are not formalized.
- `Srinivasan.lang_fibre_iff`, in `lean/Srinivasan/LangFibres.lean`,
  formalizes the fibre calculation in the proof of Lang's theorem
  (Chapter II, p. 11, `passage:lang-finite-fibres`). For an arbitrary group
  endomorphism `F`, equality `x(Fx)⁻¹=y(Fy)⁻¹` is equivalent to
  `F(y⁻¹x)=y⁻¹x`. Finiteness of rational points, the dimension argument,
  finiteness of the morphism, and surjectivity of the Lang map are not proved.

`lean/check_axioms.py` compiles every listed proof separately and rejects
compiler errors or warnings. It requires exactly the listed declarations
in the axiom output and allows only `propext`, `Classical.choice`, and
`Quot.sound`; it also checks proof inventory and root imports. The binding
to the book is by passage labels, not by a text hash. The audit verifies
that these labels exist, so a change to a labelled passage still requires
review of its correspondence to the proof. Proof files are hashed during
the run to detect a concurrent change.

## Infrastructure tests

`just test` runs `tests/test_infrastructure.py`. These tests cover the shared
numbering series and references, PDF outline destinations preserving zoom,
chapter and child destination positions, reference line wrapping, statement openings, page sequences, editor/build stage
agreement, rejection of an empty final index, and the correction-journal
schema. They do not check the mathematical claims.
