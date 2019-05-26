# Notes on goal handling:

- Goals are retrieved by `Query`. It will return the whole proof
  object which is quite intimidating, but on the good side it opens up
  basically any possibility.

  For each goal, we've chosen to return the true internal
  representation of the objects, basically a `constr`. It turns out
  you really need access to it if you want to do some more advanced
  features.

  The return type comes from Coq and is::

```ocaml
type 'a pre_goals = {
  fg_goals       : 'a list;
  bg_goals       : ('a list * 'a list) list;
  shelved_goals  : 'a list;
  given_up_goals : 'a list;
}
```
  is instantiated at this lower level with::

```ocaml
'a = Constr.constr * Context.NamedList.Declaration.t list
```
  that is, type + hypotheses, where hypotheses are::
```ocaml
      Id.t list * Constr.t option * Constr.t
```
  a list of names, an (optional) definition, and the type. Typical example::
```ocaml
      f := map id : nat -> nat
```

- `Query` will take a family of filters operating on the representation. Some candidates are:

  - Filter by type of goal => This is an enumeration datatype for the fields of the record.

  - Filter by name of hypotheses/goal.

  - Filter by type/shape pattern => you provide the `constr_pattern` you want, like in search.

  - Filter by dependency.

  - *Insert your own here*

As in all queries, you may chose to get the raw representation, a pretty printed one, a rich document, etc...
