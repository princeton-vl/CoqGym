FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby
RUN apt-get install -y ocaml-nox

# OPAM 1.2
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.0.tar.gz |tar -xz
WORKDIR opam-1.2.0
RUN ./configure
RUN make lib-ext
RUN make
RUN make install

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 4

# Coq
RUN opam install -y coq

# Tools
RUN apt-get install -y inotify-tools

# Coq repository
RUN opam repo add coq-released https://coq.inria.fr/opam/released

# Dependencies
RUN opam install -y coq-error-handlers coq-function-ninjas coq-list-string

# Build
ADD . /root/system
WORKDIR /root/system
RUN eval `opam config env`; ./configure.sh && make -j
