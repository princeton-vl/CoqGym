# 1.0.0

- Big rewrite

- `IO a` is now `('a -> Obj.t) -> Obj.t` (`forall r. (a -> r) -> r`)
- A single main entry point: `SimpleIO.SimpleIO` (plus optional unsafe modules)
- New functions for strings and exceptions

# 0.2

- Removed ocaml library. `IO` is now defined in OCaml by extraction simply as
  `('a -> unit) -> unit`.
- Add `delay_io`

# 0.1

Initial release
