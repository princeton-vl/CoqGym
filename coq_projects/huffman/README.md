# Huffman

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]

[travis-shield]: https://travis-ci.com/coq-community/huffman.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/huffman/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

This projects contains a proof of correctness of the Huffman coding
algorithm, as described in the paper
[A Method for the Construction of Minimum-Redundancy Codes][paper],
Proc. IRE, pp. 1098-1101, September 1952.

[paper]: http://compression.ru/download/articles/huff/huffman_1952_minimum-redundancy-codes.pdf



## Meta

- Author(s):
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: Coq 8.7 or later
- Additional dependencies: none

## Building and installation instructions

The easiest way to install the latest released version is via
[OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-huffman
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/huffman
cd huffman
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `Huffman` namespace.

## Documentation
  
To run the algorithm, open an OCaml toplevel (`ocaml`) and do
```ocaml
#use "run_huffman.ml";;
```

To get the code that gives the frequency string:  
```ocaml
let code = huffman "abbcccddddeeeee";;
```

To code a string:
```ocaml
let c = encode code "abcde";;
```

To decode a string:
```ocaml
decode code c;;
```

Some more information on the development is available:
ftp://ftp-sop.inria.fr/marelle/Laurent.Thery/Huffman/index.html

In particular, a note in PDF format describes the formalization:
ftp://ftp-sop.inria.fr/marelle/Laurent.Thery/Huffman/Note.pdf

