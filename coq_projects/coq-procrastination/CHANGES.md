v1.2 2018-09-18
---------------

- Speed up defer when "Group GOAL" contains redices
  (Fabian Kunze)
- Fixed a bug when deferring conjunction right before 'end defer'
  (Fabian Kunze)
- Fixed a bug that sometimes left an '/\ True' at the end of an deferred goal
  after 'end defer'
  (Fabian Kunze)

v1.1 2018-07-09
---------------

- Fix a bug where `end defer` would not work when deferring in Type
- Make `Group` opaque to avoid having its contents being instantiated by e.g.
  `eauto`.

v1.0 2018-07-08
---------------

- First release
