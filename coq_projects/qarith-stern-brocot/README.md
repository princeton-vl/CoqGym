# Binary Rational Numbers

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-540-24849-1_20.svg
[doi-link]: https://doi.org/10.1007/978-3-540-24849-1_20

[travis-shield]: https://travis-ci.com/coq-community/qarith-stern-brocot.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/qarith-stern-brocot/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

Development of rational numbers as finite binary lists and defining
field operations on them in two different ways: strict and lazy.


More details about the project can be found in the paper
[QArith: Coq Formalisation of Lazy Rational Arithmetic](https://hal.inria.fr/inria-00077041).

## Meta

- Author(s):
  - Milad Niqui (initial)
  - Yves Bertot (initial)
- Coq-community maintainer(s):
  - Hugo Herbelin ([**@herbelin**](https://github.com/herbelin))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: Coq 8.7 or greater (use releases for other Coq versions)
- Additional dependencies: none

## Building and installation instructions

The easiest way to install the latest released version is via
[OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-qarith-stern-brocot
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/qarith-stern-brocot
cd qarith-stern-brocot
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `QArithSternBrocot` namespace.

## Documentation

This package contains a rational arithmetic library for Coq.
This includes:

- A binary representation for positive rational numbers `Qpositive` and its
  extension to `Q` by adding sign bit (also known as Stern-Brocot
  tree encoding).
- Arithmetic operations on `Qpositive` and `Q` defined in an strict way.
- More efficient arithmetic operations on `Q` defined lazily using
  homographic and quadratic algorithms for this binary representation
  (exact rational arithmetic).
- Proof of the correctness of the homographic and quadratic algorithms
  using the strict operations.
- The files enable the user to use Coq `field` tactic on `Q` with two
  different field structures (using strict or lazy operations).
- The Haskell extraction of the lazy algorithms (`quadratic.hs`).
- A syntax for using the rational numbers as pair of integers, and writing
  simple arithmetic operations on them.
- A proof of irrationality of the square root of 2.
- A proof that `Q` is Archimedean.
- A proof that `Q` is countable.

