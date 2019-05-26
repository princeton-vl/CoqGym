# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/ninja-48.png) Function Ninjas
Write readable code using simple functional combinators.

    download url
      |> Xml.import
      |> Xml.get_list "user"
      |> List.map (fun name => String.capitalize @@ String.trim name)
      |> String.join ", "

## Install
### With OPAM
Add the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-function-ninjas

### From source
Do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import FunctionNinjas.All.

at the beginning of your source files. It will add two notations:
* `x |> f` Like `f x`. Useful to pipe data through a list of functions.
* `f @@ x` Like `f x`, with lower priority. Will save you many parenthesis.
