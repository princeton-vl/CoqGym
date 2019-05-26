Copyright (c) 2015, Lionel Rieg

DESCRIPTION
===========

A rudimentary library for dependent maps that contain their domain in the type,
that is they have type [t A dom], where [A] is the type of elements associated
to keys and [dom] is the domain of the map.

It is nowhere near as complete as MSets/FMaps.

BUILDING
========

Simply compile all the files with:
     make
If you want a local installation, add the line "-install local" to the file _CoqProject
before compiling.
You can then install the library with:
    make install
You may need super-user privileges for installation.

You can build the documentation with:
    make html

You can then use the library with
    Require DepMap.DepMap.

LICENSE
=======

This library is available under the CeCILL-B license.
