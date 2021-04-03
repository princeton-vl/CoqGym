import argparse, os, sys, torch
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))
from agent import Agent
import numpy as np
import random

if __name__ == "__main__":
    
    parser = argparse.ArgumentParser()
    
    # paths
    parser.add_argument("--tacmodel", type=str, default="./models/dummy.pth")
    parser.add_argument("--argmodel", type=str, default="./models/dummy.pth")
    parser.add_argument("--model", type=str, default="ffn")
    parser.add_argument("--datapath", type=str, default="../data")
    parser.add_argument("--nonterminals", type=str, default="./jsons/nonterminals.json")
    parser.add_argument("--tactics", type=str, default="./jsons/tactics.json")
    parser.add_argument("--split", type=str, default="../projs_split.json")
    parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")
    
    # run env
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--num_tactics", type=int, default=10)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--lm", type=int, default=-1)
    
    # model parameters
    parser.add_argument("--dropout", type=str, default=0.0)
    opts = parser.parse_args()
    opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    # set run env
    torch.manual_seed(opts.seed)
    np.random.seed(opts.seed)
    random.seed(opts.seed)
                     
    # agent
    agent = Agent(opts, model=None)
    agent.test()
    
