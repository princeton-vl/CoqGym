import os, json, pickle
import multiprocessing as mp

proof_steps = '../proof_steps'
with open('../_SL/jsons/tactics.json') as f: all_tactics = json.load(f)


def freq(files):
    total = 0
    res = {}
    for tac in all_tactics:
        res[tac] = 0

    for i, file_name in enumerate(files):
        current_file_path = f"../proof_steps/train/{file_name}"
        with open(current_file_path, 'rb') as f:
            example = pickle.load(f)
            is_synthetic = example['is_synthetic']
            if is_synthetic:
                continue
            
            total += 1
            print(total)
            tactic_app = example['tactic']['text']

            if tactic_app.startswith('simple induction'):
                tactic = 'simple induction'
            else:
                for tac in all_tactics:
                    if tactic_app.startswith(tac):
                        tactic = tac
            
            res[tactic] += 1

    return res, total


def tactic_freq():

    files = os.listdir("../proof_steps/train")
    print(files)

    with mp.Pool(processes=4) as pool:
        res, total = pool.map(freq, files)
        print(res)
        print(total)


if __name__ == "__main__":
    freq = tactic_freq()
