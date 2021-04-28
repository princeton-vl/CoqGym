import os, json, pickle

proof_steps = '../proof_steps'
with open('../_SL/jsons/tactics.json') as f: all_tactics = json.load(f)
with open('../_SL/jsons/generic_args.json') as f: generic_args = json.load(f)

def freq(files, path):
    total = 0
    res = {}
    for tac in all_tactics:
        res[tac] = 0

    for i, file_name in enumerate(files):
        current_file_path = f"{path}/{file_name}"
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

    train = f'{proof_steps}/train'
    valid = f'{proof_steps}/valid'

    train_files = os.listdir(train)
    valid_files = os.listdir(valid)

    valid_freq, valid_count = freq(valid_files, valid)
    print(f'{valid_freq}, {valid_count}')

    train_freq, train_count = freq(train_files, train)
    print(f'{train_freq}, {train_count}')


def average_lc():
    train = f'{proof_steps}/train'
    files = os.listdir(train)
    for i, file_name in enumerate(files):
        current_file_path = f"{train}/{file_name}"
        with open(current_file_path, 'rb') as f:
            print(i)
            example = pickle.load(f)
            is_synthetic = example['is_synthetic']
            if is_synthetic:
                continue

            tactic = example['tactic']['text']
            lc_ids = [lc['ident'] for lc in example['local_context']]


def number_of_args():
    synthetic_lc = {}
    human_lc = {}
    synthetic_gc = {}
    human_gc = {}

    train = f'{proof_steps}/train'
    files = os.listdir(train)

    for i, file_name in enumerate(files):
        current_file_path = f"{train}/{file_name}"
        with open(current_file_path, 'rb') as f:
            print(i)
            example = pickle.load(f)
            is_synthetic = example['is_synthetic']
            tactic_app = example['tactic']['text']
            lc_ids = [lc['ident'] for lc in example['local_context']]
            lc_args = len(find_lc_args(tactic_app, lc_ids))
            gc_args = len(find_gc_args(tactic_app, lc_ids))

            if is_synthetic:
                synthetic_lc[lc_args] = synthetic_lc.get(lc_args, 0) + 1
                synthetic_gc[gc_args] = synthetic_gc.get(gc_args, 0) + 1
            else:
                human_lc[lc_args] = human_lc.get(lc_args, 0) + 1
                human_gc[gc_args] = human_gc.get(gc_args, 0) + 1
        
    print(synthetic_lc)
    print(human_lc)
    print(synthetic_gc)
    print(human_gc)
    

def find_lc_args(tactic_application, lc_ids):
    all_actions = tactic_application.split(" ")
    args = all_actions[1:]
    res = []
    for i, arg in enumerate(args):
        if arg in lc_ids:
            res.append(arg)
    return res

def find_gc_args(tactic_application, lc_ids):
    all_actions = tactic_application.split(" ")
    args = all_actions[1:]
    res = []
    for arg in args:
        if arg in generic_args:
            continue
        if arg in all_tactics:
            continue
        if arg in lc_ids:
            continue
        res.append(arg)
    return res

if __name__ == "__main__":
    number_of_args()
