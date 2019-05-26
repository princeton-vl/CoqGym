import os
import re
import json
from re_patterns import *
from hashlib import sha1
from glob import glob
from progressbar import ProgressBar
from collections import defaultdict
import lmdb
import pdb


def log(msg, msg_type='INFO'):
  if msg_type == 'INFO':
    prefix = ''
  elif msg_type == 'WARNING':
    prefix = '\033[33mWARNING: '
  elif msg_type == 'ERROR':
    prefix = '\033[91mERROR: '
  suffix = '\033[0m'
  print(prefix + str(msg) + suffix)


comment_pattern = re.compile(r'(?<!")(?P<start>\(\*).*?(?P<end>(\*\))|(?=\(\*))(?!")', re.DOTALL)


def remove_comments(code):
    characters = []
    num_left = 0
    in_string = False

    i = 0
    while i < len(code) - 1:
        if code[i] == '"':
            in_string = not in_string
        if not in_string and code[i : i + 2] == '(*':
            num_left += 1
            i += 2
        elif not in_string and num_left > 0 and code[i : i + 2] == '*)':
            num_left -= 1
            i += 2
        elif num_left == 0: 
            characters.append(code[i])
            i += 1
        else:
            i += 1

    characters.append(code[-1])
    code_without_comment = ''.join(characters)

    return code_without_comment


def normalize_spaces(s):
    return re.sub(r'\s+', ' ', s, flags=re.DOTALL)


def get_code(coq_code):
    def loc2code(bp, ep):
        code = coq_code[bp : ep]
        try:
            code = code.strip().decode('utf-8')
        except UnicodeDecodeError:
            code = code.decode(chardet.detect(code)['encoding']).strip()
        code = normalize_spaces(remove_comments(code))
        return code
    return loc2code


class SexpCache:

    def __init__(self, db_path, readonly=False):
        if readonly:
            self.env = lmdb.open(db_path, map_size=1e11, readonly=True, readahead=False, lock=False, max_readers=1024)
        else:
            self.env = lmdb.open(db_path, map_size=1e11, writemap=True, readahead=False, max_readers=1024)


    def dump(self, sexp):
        sexp_bytes = sexp.encode('utf-8')
        digest = sha1(sexp_bytes).hexdigest()
        key = digest.encode('utf-8')
        with self.env.begin(write=True) as txn:
            txn.put(key, sexp_bytes, dupdata=False, overwrite=False)
        return digest

    
    def __getitem__(self, key):
        with self.env.begin() as txn:
            return txn.get(key.encode('utf-8')).decode('utf-8')


def add_ml_path(paths, serapi, sexp_cache):
    parsed_paths = [match.group() for match in ML_PATH_PATTERN.finditer(paths)]
    cmds = []
    for path in parsed_paths[::-1]:
        cmd = 'Add ML Path "%s".' % path
        _, ast = serapi.execute(cmd, return_ast=True)
        cmds.append((cmd, 'VernacAddMLPath', sexp_cache.dump(ast)))
    return cmds


def path_conflict(succ, prev):
    suffix_physical = None
    suffix_logical = None
    if succ[0].startswith(prev[0]):
        suffix_logical = succ[0][len(prev[0]):]
    if succ[1].startswith(prev[1]):
        suffix_physical = succ[1][len(prev[1]):]
    if suffix_physical is None:
        return False
    if suffix_logical is None:
        return True
    return [s for s in suffix_logical.split('.') if s != ''] != [s for s in suffix_physical.split('/') if s != '']


def add_load_path(paths, serapi, pwd, sexp_cache):
    # parse the paths
    parsed_paths = []
    built_in = False
    for match in LOAD_PATH_PATTERN.finditer(paths):
        logical_path = match['logical_path'].strip().replace('<>', '')
        physical_path = match['physical_path'].strip()
        implicit = match['implicit'].strip()
        if logical_path == '' and physical_path.endswith(pwd):
            built_in = True
        parsed_paths.append([logical_path, physical_path, implicit, built_in, False])
        # check for any conflict
        for i in range(len(parsed_paths) - 1):
            conflict = path_conflict(parsed_paths[-1], parsed_paths[i])
            assert parsed_paths[i][3] or not conflict
            parsed_paths[i][4] = conflict or parsed_paths[i][4]

    sorted_paths = [path for path in parsed_paths if not path[4]][::-1]
    cmds = []
    for logical_path, physical_path, implicit, built_in, conflict in sorted_paths:
        assert not conflict
        rec = 'Rec ' if implicit == 'true' else ''
        if logical_path == '':
            cmd = 'Add %sLoadPath "%s".' % (rec, physical_path)
        else:
            cmd = 'Add %sLoadPath "%s" as %s.' % (rec, physical_path, logical_path)
        _, ast = serapi.execute(cmd, return_ast=True)
        cmds.append((cmd, 'VernacAddLoadPath', sexp_cache.dump(ast)))
    return cmds


def set_paths(meta, serapi, sexp_cache):
    pwd = PWD_PATTERN.search(meta)['pwd']
    cmd = 'Cd "%s".' % pwd
    _, ast = serapi.execute(cmd, return_ast=True)
    vernac_cmds = []
    vernac_cmds.append((cmd, 'VernacChdir', sexp_cache.dump(ast)))
    ml_paths = ML_PATHS_PATTERN.search(meta)['ml_paths']
    for cmd in add_ml_path(ml_paths, serapi, sexp_cache):
        vernac_cmds.append(cmd)
    load_paths = LOAD_PATHS_PATTERN.search(meta)['load_paths']
    for cmd in add_load_path(load_paths, serapi, pwd, sexp_cache):
        vernac_cmds.append(cmd)
    return vernac_cmds


def extract_code(meta, loc2code):
    coq_code = []
    for match_loc in LOC_PATTERN.finditer(meta):
        tags = defaultdict(list)
        for match_tag in TAG_PATTERN.finditer(match_loc.group()):
            tag = match_tag['tag'].strip()
            content = match_tag['content'].strip()
            tags[tag].append(content)
        for tag, content in tags.items():
            if len(content) == 1:
                tags[tag] = content[0]
            else:
                pdb.set_trace()
        if tags['VERNAC_TYPE'] == 'VernacProof' and 'END_TACTIC' not in tags:
            continue
        loc = PARSE_LOC_PATTERN.search(tags['LOC'])
        code_line = loc2code(int(loc['bp']), int(loc['ep']))
        coq_code.append((code_line, tags))
    return coq_code


def dst_filename(src, data_path):
    return os.path.join(data_path, *os.path.splitext(src)[0].split(os.path.sep)[1:])


def update_env(env, env_delta):
    # add
    env['constants'].extend(env_delta['add']['constants'])
    env['inductives'].extend(env_delta['add']['inductives'])
    # subtract
    to_remove = {v['physical_path']
                  for v in env_delta['subtract']['constants'] + env_delta['subtract']['inductives']}
    env['constants'] = [const for const in env['constants'] if const['physical_path'] not in to_remove]
    env['inductives'] = [induct for induct in env['inductives'] if induct['physical_path'] not in to_remove]
    return env


def iter_proofs(data_root, callback, include_synthetic=False, show_progress=False):
    def iter_proofs_in_file(filename, file_data):
        env = {'constants': [], 'inductives': []}
        for proof_data in file_data['proofs']:
            env = update_env(env, proof_data['env_delta'])
            del proof_data['env_delta']
            proof_data['env'] = env
            callback(filename, proof_data)
            if include_synthetic and 'synthetic_proofs' in file_data and proof_data['name'] in file_data['synthetic_proofs']:
                for subprf_data in file_data['synthetic_proofs'][proof_data['name']]:
                    subprf_data['env'] = env
                    callback(filename, subprf_data)

    iter_coq_files(data_root, iter_proofs_in_file, show_progress)


def iter_coq_files(data_root, callback, show_progress=False):
    coq_files = glob(os.path.join(data_root, '**/*.json'), recursive=True)
    bar = ProgressBar(max_value=len(coq_files))
    for i, f in enumerate(coq_files):
        file_data = json.load(open(f))
        callback(f, file_data)
        if show_progress:
            bar.update(i)


def iter_sexp_cache(db_path, callback):
    env = lmdb.open(db_path, map_size=1e11, readonly=True, readahead=True, lock=False)
    bar = ProgressBar(max_value=env.stat()['entries'])
    with env.begin() as txn:
        cursor = txn.cursor()
        for i, (key, value) in enumerate(cursor):
           callback(i, key, value.decode('utf-8'))
           bar.update(i)
