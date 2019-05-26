# ASTactic

![ASTactic](/images/astactic.jpg)

Code for the paper:  

Kaiyu Yang and Jia Deng. [“Learning to Prove Theorems via Interacting with Proof Assistants.”](https://arxiv.org/) International Conference on Machine Learning (ICML). 2019.

(put bibtex here)


## Dependencies

* [CoqGym](https://github.com/princeton-vl/CoqGym): Follow the instructions to obtain the CoqGym dataset, **place ASTactic under the root directory of CoqGym, activate the `coq_gym` conda environment, make sure OPAM is in the switch `4.07.1+flambda` and `which coqc` prints `CoqGym/coq/bin/coqc`**.
* Automated theorem provers: [Vampire](https://vprover.github.io), [CVC4](http://cvc4.cs.stanford.edu/), [Eprover](http://www.eprover.org), and [Z3](https://github.com/Z3Prover/z3). Install all of them, otherwise you may see a performance degradation of the hammer baseline.


## Install CoqHammer

1. In `CoqGym/`, run: `git clone git@github.com:princeton-vl/ASTactic.git --recursive && cd ASTactic`
1. Run `source install.sh` to install CoqHammer for the hammer baselines.


## Extracting Proof Steps

The ASTactic model is trained on individual proof steps, rather than entire proofs.
After obtaining the CoqGym dataset, run `python extract_proof_steps.py`. This can take a while, and you have the option to run it in parallel, please see the source code for details.


The extracted proof steps are stored in `proof_steps/`. You can double-check the number of proof steps to make sure everything works as expected: 

Directory |  # files
------------ | -------------
proof_steps/human/train | 121,645
proof_steps/human/valid | 68,181
proof_steps/synthetic/train | 174,077


## Training

To train on training + validation proof steps, without synthetic proofs:  
`python main.py --no_validation --exp_id human`


With synthetic proofs:  
`python main.py --no_validation --include_synthetic --exp_id human+synthetic`


## Testing 

`python evaluate.py ours ours-TEST --path runs/human/checkpoints/model_003.pth --file ../data/StructTact/Assoc.json --proof "get_set_same"`

`python -u evaluate.py auto auto-TEST --file ../data/StructTact/Assoc.json --proof "get_set_same"`

It is normal to have a small fraction of out-of-memory error and other errors during testing, these proofs are counted as failures.


*Caveat*: Testing is computationally expensive, but the workloads are embarrassingly parallel, which means you can run them in parallel in any order. We do not provide the code for that because it depends on a particular HPC infrastructure.
