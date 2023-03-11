FROM nvcr.io/nvidia/pytorch:23.02-py3

WORKDIR /workspace/CoqGym
COPY . .

RUN apt-get update && apt-get install -y ruby opam lmdb-utils

RUN opam init --bare --disable-sandboxing --auto-setup
RUN opam switch create 4.07.1+flambda && eval $(opam env)

RUN python -m pip install --upgrade pip
RUN pip install lark-parser==0.6.5 lmdb pandas pexpect progressbar2 sexpdata

RUN source install.sh

ENV PATH="/workspace/CoqGym/coq/bin:/root/.opam/4.07.1+flambda/bin":$PATH

RUN cd coq_projects && make && cd ..

RUN python unzip_data.py apt-get install -y lmdb-utils

RUN python eval_env.py

WORKDIR /vampire
RUN wget https://github.com/vprover/vampire/releases/download/snakeForV4.7%2B/vampire-snake-static4starexec.zip
RUN unzip vampire-snake-static4starexec.zip
RUN mv bin/* /usr/bin/

WORKDIR /workspace
RUN git clone https://github.com/Z3Prover/z3
WORKDIR /workspace/z3
RUN python scripts/mk_make.py && cd build && make -j8 && make install

WORKDIR /workspace
RUN wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
RUN chmod u+x cvc4-1.8-x86_64-linux-opt
RUN mv cvc4-1.8-x86_64-linux-opt /usr/bin/cvc4

WORKDIR /workspace
RUN git clone https://github.com/eprover/eprover.git
WORKDIR eprover
RUN ./configure && make -j8 && make install
RUN mv PROVER/* /usr/bin 

WORKDIR /workspace/CoqGym/ASTactic
RUN python extract_proof_steps.py
