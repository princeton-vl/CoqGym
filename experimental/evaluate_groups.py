import os
import sys
sys.path.append(os.path.normpath(os.path.dirname(os.path.realpath(__file__))))
sys.path.append(
    os.path.normpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../"))
)
import argparse
import json
from utils import log
from progressbar import ProgressBar
from agent import Agent
from experimental.gast_tactic_groups.prover import Prover
import torch
import glob, pickle


if __name__ == "__main__":
    # argument setup
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=str)
    parser.add_argument("--datapath", type=str, default="./proof_steps/test")
    parser.add_argument("--modelpath", type=str)
    parser.add_argument("--batchsize", type=int, default=1)
    parser.add_argument("--term_embedding_dim", type=int, default=1024)
    parser.add_argument("--dropout_rate", type=float, default=0.4)
    parser.add_argument("--hops", type=int, default=4)
    parser.add_argument("--projs_split", type=str, default="../projs_split.json")
    opts = parser.parse_args()
    log(opts)
    opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    if opts.device.type == "cpu":
        log("using CPU", "WARNING")

    # all file paths
    files = []
    for filename in os.listdir(opts.datapath):
        if filename.endswith(".pickle"): 
            files.append(os.path.join(opts.datapath, filename))
        else:
            continue
    
    # initialize model
    model = Prover(opts)
    log("loading model checkpoint from %s ..." % opts.modelpath)
    if opts.device.type == "cpu":
        checkpoint = torch.load(opts.modelpath, map_location="cpu")
    else:
        checkpoint = torch.load(opts.modelpath)
    model.load_state_dict(checkpoint["state_dict"])
    model.to(opts.device)
    agent = Agent(model, None, None, opts)
    
    # prediction
    bar = ProgressBar(max_value=len(files))
    res = []
    for i, f in enumerate(files):
        try:
            pred, true = agent.evaluate_proxy(f)
            res.append([pred, true])
        except:
            res.append(["FAILED", "BIG F"])
        bar.update(i)
    
    # save result and calculate accuracy
    with open(opts.output, 'w') as f:
        num_correct = 0
        for i, r in enumerate(res):
            if r[0] == r[1]:
                num_correct += 1
            if i == len(res)-1:
                f.write(f"{r[0]},{r[1]}")
            else:
                f.write(f"{r[0]},{r[1]}\n")
    print(f"\nAccuarcy: {num_correct/len(res)}")




