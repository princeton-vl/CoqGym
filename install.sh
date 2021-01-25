#!/bin/bash

OPAM_SWITCH="4.07.1+flambda"
COQ_ROOT=$(pwd)/coq

echo "Installing Dependencies.."
opam switch $OPAM_SWITCH && eval $(opam env)
opam install --yes dune=1.10.0 cmdliner=1.0.4 ppx_sexp_conv=v0.12.0 ppx_deriving=4.3 sexplib=v0.12.0 ppx_import=1.6.2 camlp5=7.08 coq=8.9.1

if [ $? -eq 0 ]; then
    echo "Dependencies installed"
    
    echo "Installing Coq.."
    cd coq && ./configure -local -flambda-opts '-O3 -unbox-closures' && make && cd ..

    if [ $? -eq 0 ]; then
        echo "Coq installed"
        export COQBIN=$COQ_ROOT/bin/
        export PATH=$COQBIN:$PATH

        echo "Installing SerAPI.."
        cd coq-serapi && make SERAPI_COQ_HOME=$COQ_ROOT && dune install && cd ..
         
        if [ $? -eq 0 ]; then
            echo "SerAPI installed"

            echo "Installing CoqHammer.."
            cd ASTactic/coqhammer && make && make install && cd ../..

            if [ $? -eq 0 ]; then
                echo "CoqHammer installed"
            else
                echo "Failed to install CoqHammer!"
            fi

        else
            echo "Failed to install SerAPI!"
        fi

    else
        echo "Failed to install Coq!" 
    fi

else
    echo "Failed to install the dependencies!" 
fi
