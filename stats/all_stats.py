import os, json, pickle

proof_steps = '../proof_steps'
with open('../_SL/jsons/tactics.json') as f: all_tactics = json.load(f)


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

    train_freq, train_count = freq(train_files, train)
    print(f'{train_freq}, {train_count}')

    valid_freq, valid_count = freq(valid_files, valid)
    print(f'{valid_freq}, {valid_count}')


def average_lc():
    train = f'{proof_steps}/train'
    train_files = os.listdir(train)

if __name__ == "__main__":
    freq = tactic_freq()
