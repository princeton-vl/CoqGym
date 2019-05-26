Bootstrap: shub
From: singularityhub/ubuntu

%help
    See https://github.com/princeton-vl/CoqGym/blob/master/README.md#using-coqgym-in-a-container

%files
    data.tar.gz /data.tar.gz
    sexp_cache.tar.gz /sexp_cache.tar.gz
    projs_split.json /projs_split.json

%labels
    AUTHOR Kaiyu Yang
    EMAIL  kaiyuy@cs.princeton.edu
    GITHUB https://github.com/princeton-vl/CoqGym

%environment
    export LANGUAGE=en_US.UTF-8
    export LANG=en_US.UTF-8
    export LC_ALL=en_US.UTF-8
    export SHELL=/bin/bash
    export OPAMROOT=/.opam

%post
    locale-gen en_US.UTF-8
    dpkg-reconfigure locales

    apt-get update && apt-get -y install git wget bzip2 zip unzip build-essential m4 ruby-full
    git clone https://github.com/LMDB/lmdb
    cd /lmdb/libraries/liblmdb && make -j4 && make install && cd /

    echo "Installing Anaconda3.."
    wget https://repo.anaconda.com/archive/Anaconda3-2019.03-Linux-x86_64.sh
    bash /Anaconda3-2019.03-Linux-x86_64.sh -b -p /anaconda3
    eval "$(/anaconda3/bin/conda shell.bash hook)"
    conda init
    rm /Anaconda3-2019.03-Linux-x86_64.sh

    echo "Installing OPAM.."
    wget https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh
    printf '\n' | bash install.sh
    opam init --bare --disable-sandboxing --root /.opam
    export OPAMROOT=/.opam
    eval $(opam env)
    rm install.sh

    echo "Installing CoqGym.."
    opam switch create 4.07.1+flambda && eval $(opam env)
    opam update && eval $(opam env)
    git clone https://github.com/princeton-vl/CoqGym
    cd CoqGym && ./install.sh
    export PATH=/CoqGym/coq/bin:$PATH
    cd coq_projects && make && cd ..
    
    conda env create -f coq_gym.yml && conda activate coq_gym
    conda install pytorch-cpu torchvision-cpu -c pytorch

    mv /data.tar.gz /CoqGym/data.tar.gz
    mv /sexp_cache.tar.gz /CoqGym/sexp_cache.tar.gz
    mv /projs_split.json /CoqGym/projs_split.json
    python unzip_data.py

    cp -r /root/.bashrc /.bashrc
