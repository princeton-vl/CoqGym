import os
import lmdb
from progressbar import ProgressBar
import json
from glob import glob
import pdb


def merge_lmdbs():
    'merge all the LMDB databases in data/ into one'
    db_path = 'sexp_cache'
    dst_db = lmdb.open(db_path, map_size=1e11, writemap=True, readahead=False)
    files = glob('data/**/*sexp_cache', recursive=True)

    bar = ProgressBar(max_value=len(files))
    for i, db_path in enumerate(files):
        print(db_path)
        try:
            src_db = lmdb.open(db_path, map_size=1e11, readonly=True, readahead=True, lock=False)
        except lmdb.Error as ex:
            print(ex)
            continue
        with src_db.begin() as txn1:
            cursor = txn1.cursor()
            for key, value in cursor:
                with dst_db.begin(write=True) as txn2:
                    txn2.put(key, value, dupdata=False, overwrite=False)
        src_db.close()
        os.system('rm -r "%s"' % db_path)
        bar.update(i)

    dst_db.close()


def env_diff(new_env, old_env):
    add = {'constants': [json.loads(const) for const in new_env['constants'] if const not in old_env['constants']],
           'inductives': [json.loads(induct) for induct in new_env['inductives'] if induct not in old_env['inductives']]}
    subtract = {'constants': [json.loads(const) for const in old_env['constants'] if const not in new_env['constants']],
                'inductives': [json.loads(induct) for induct in old_env['inductives'] if induct not in new_env['inductives']]}
    env_delta = {'add': add, 'subtract': subtract}
    return env_delta


def merge_proofs():
    files = [f for f in glob('data/**/*.json', recursive=True) if 'PROOFS' not in f]

    bar = ProgressBar(max_value=len(files))
    for i, f in enumerate(files):
        file_data = json.load(open(f))
        proofs = []
        env = {'constants': [], 'inductives': []}

        # merge the files for the human proofs
        for proof_name in file_data['proofs']:
            proof_file = f[:-5] + '-PROOFS/' + proof_name + '.json'
            if not os.path.exists(proof_file):
                continue
            proof_data = json.load(open(proof_file))
            for j, const in enumerate(proof_data['env']['constants']):
                proof_data['env']['constants'][j] = json.dumps(proof_data['env']['constants'][j])
            for j, const in enumerate(proof_data['env']['inductives']):
                proof_data['env']['inductives'][j] = json.dumps(proof_data['env']['inductives'][j])

            env_delta = env_diff(proof_data['env'], env)
            env = proof_data['env']

            proofs.append({'name': proof_name, 'line_nb': proof_data['line_nb'], 'env_delta': env_delta,
                           'steps': proof_data['steps'], 'goals': proof_data['goals'], 'proof_tree': proof_data['proof_tree']})

        # merge the synthetic proofs
        synthetic_proofs = {}
        for sf in glob(f[:-5] + '-SUBPROOFS/*.json'):
            proof_name = sf.split('/')[-1][:-5]
            subprf_data = json.load(open(sf))
            synthetic_proofs[proof_name] = subprf_data

        file_data['proofs'] = proofs
        file_data['synthetic_proofs'] = synthetic_proofs
        if proofs != []:
            json.dump(file_data, open(f, 'wt'))
        os.system('rm -r ' + f[:-5] + '-*PROOFS')

        bar.update(i)


def merge_synthetic_proofs():
    dirnames = glob('data/**/*-SUBPROOFS', recursive=True)

    bar = ProgressBar(max_value=len(dirnames))
    for i, d in enumerate(dirnames):
        filename = d[:-10] + '.json'
        if not os.path.exists(filename):
            continue
        file_data = json.load(open(filename))
        file_data['synthetic_proofs'] = {}
        for f in glob(os.path.join(d, '*.json')):
            proof_name = f.split('/')[-1][:-5]
            subprf_data = json.load(open(f))
            file_data['synthetic_proofs'][proof_name] = subprf_data
        json.dump(file_data, open(filename, 'wt'))
        os.system('rm %s/*.json' % d)
        bar.update(i)


if __name__ == '__main__':
    print('merging the LMDB files..')
    merge_lmdbs()
    print('merging the proof files..')
    merge_proofs()
