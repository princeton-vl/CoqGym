import os 
import json
from glob import glob
from utils import get_code, SexpCache, set_paths, extract_code, dst_filename
from serapi import SerAPI
from time import time
import sexpdata
from proof_tree import ProofTree
from extract_proof import goal_is_prop, check_topology
import pdb


def close_proof(sexp_cache, serapi):
    fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
    assert bg_goals + shelved_goals == []
    if fg_goals == []:
        return []
    num_goals_left = len(fg_goals)
    cmds = []
    for i in range(num_goals_left):
        _, ast = serapi.execute('auto.')
        cmds.append(('auto.', 'VernacExtend', sexp_cache.dump(ast)))
        fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
        if fg_goals == []:
            return cmds
 
    return None


def subgoals2hypotheses(script, serapi):
    'Execute `script` and convert all unsolved new sub-goals into hypotheses in the context of the current goal'
    serapi.push()
    fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
    assert shelved_goals + given_up_goals == []
    assert len(fg_goals) == 1
    current_goal_id = fg_goals[0]['id']
    existing_goal_ids = set([g['id'] for g in fg_goals + bg_goals])

    local_context = []
    for hyp in fg_goals[0]['hypotheses']:
        for ident in hyp['idents'][::-1]:
            local_context.append((ident, hyp['type']))
    local_context = local_context[::-1]

    for cmd, _, _ in script:
        serapi.execute(cmd)

    fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
    assert shelved_goals + given_up_goals == []
    unsolved_goal_ids = set([g['id'] for g in fg_goals + bg_goals])
    if bg_goals != [] or not existing_goal_ids.issubset(unsolved_goal_ids.union({current_goal_id})):
        # consider only the case when there is no unfocused goal left. 
        # and no existing goal other than the current_goal was decomposed (the sub-tree of the current goal has insufficient height)
        serapi.pull()
        return None

    hypotheses = {}
    # convert the focused goals
    for n, g in enumerate(fg_goals, start=1):
        serapi.push()
        serapi.execute('Focus %d.' % n)

        local_context_g = []
        for hyp in g['hypotheses']:
            for ident in hyp['idents'][::-1]:
                local_context_g.append((ident, hyp['type']))
        local_context_g = local_context_g[::-1]
        local_context_diff = [p for p in local_context_g if p not in local_context]
        for ident, _ in local_context_diff:
            serapi.execute('generalize %s.' % ident)
        fg_goals, _, _, _ = serapi.query_goals()
        assert len(fg_goals) == 1
        hypotheses[g['id']] = fg_goals[0]['type']
        serapi.pop()

    serapi.pop()
    return hypotheses


def set_up_hypotheses(hyps, sexp_cache, serapi):
    'Set up the hypotheses converted from the subgoals'
    cmds = []
    for goal_id, hyp in hyps.items():
        H = 'assert (HYPOTHESIS_FROM_SUBGOAL_%d: %s); [> admit | idtac].' % (goal_id, hyp)
        _, ast = serapi.execute(H, return_ast=True)
        cmds.append((H, 'VernacExtend', sexp_cache.dump(ast)))
    return cmds
        

def goal2subproof(goal, length, line_nb, script, sexp_cache, serapi):
    'Extract a synthetic proof a fixed length from a goal'
    hypotheses = subgoals2hypotheses(script, serapi)
    if hypotheses is None:
        return None
    cmds = set_up_hypotheses(hypotheses, sexp_cache, serapi)

    subproof_data = {
        'goal_id': goal['id'],
        'length': length,
        'line_nb': line_nb,
        'entry_cmds': cmds,
        'steps': [],
        'goals': {},
        'proof_tree': None,
    }
    # execute the proof
    for num_executed, (cmd, cmd_type, _) in enumerate(script, start=line_nb + 1):
        # keep track of the goals
        fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
        for g in fg_goals + bg_goals:
            g['sexp'] = sexp_cache.dump(g['sexp'])
            for i, h in enumerate(g['hypotheses']):
                g['hypotheses'][i]['sexp'] = sexp_cache.dump(g['hypotheses'][i]['sexp'])
            subproof_data['goals'][g['id']] = g
        ast = sexpdata.dumps(serapi.query_ast(cmd))
        subproof_data['steps'].append({'command': (cmd, cmd_type, sexp_cache.dump(ast)),
                                       'goal_ids': {'fg': [g['id'] for g in fg_goals],
                                                    'bg': [g['id'] for g in bg_goals]}
                                      })

        # the proof ends
        if cmd_type == 'VernacEndProof':
            return None  # there is no such proof

        # run the tactic
        if args.debug:
            print('SUBPROOF-id%d-len%d %d: %s' % (goal['id'], length, num_executed, cmd))
        serapi.execute(cmd)

        if num_executed == line_nb + length:  # now, try to close the proof
            exit_cmds = close_proof(sexp_cache, serapi)
            if exit_cmds is None:
                print('failed')
                return None
            print('succeeded')
            subproof_data['exit_cmds'] = exit_cmds
            break

    assert check_topology(subproof_data['steps'])
    subproof_data['proof_tree'] = ProofTree(subproof_data['steps'], subproof_data['goals']).to_dict()
    
    return subproof_data


def record_subproofs(line_nb, script, sexp_cache, serapi):
    'For a human-written proof, extract all synthetic proofs from all goals'
    assert script[-1][1] == 'VernacEndProof'
    subproofs_data = []
    # execute the proof
    for num_executed, (cmd, cmd_type, _) in enumerate(script, start=line_nb + 1):
        # keep track of the goals
        fg_goals, bg_goals, shelved_goals, given_up_goals = serapi.query_goals()
        if fg_goals != []:
            g = fg_goals[0]
            if g['id'] in subproofs_data:
                continue
            if not goal_is_prop(g, serapi):
                continue
            serapi.push()
            serapi.execute('Focus 1.')
            for i in range(1, min(args.max_length, len(script) - 2) + 1):
                serapi.push()
                subprf = goal2subproof(g, i, num_executed - 1, script[num_executed - line_nb - 1 : num_executed - line_nb - 1 + i], 
                                       sexp_cache, serapi)
                if subprf is not None:
                    subproofs_data.append(subprf)
                serapi.pop()
            serapi.pop()

        # run the tactic
        if args.debug:
            print('PROOF %d: %s' % (num_executed, cmd))
        serapi.execute(cmd)

    return subproofs_data
   

def get_subproofs(human_proof_file, vernac_cmds, sexp_cache, args):
    prf = json.load(open(human_proof_file))
    line_nb = prf['line_nb']
    with SerAPI(args.timeout, args.debug) as serapi:
        for cmd, _, _ in vernac_cmds[:line_nb + 1]:
            serapi.execute(cmd)
        subproofs_data = record_subproofs(line_nb, vernac_cmds[line_nb + 1 : line_nb + 1 + len(prf['steps'])], 
                                          sexp_cache, serapi)

    return subproofs_data 


def dump(subproofs_data, args):
    print('%d synthetic proofs extracted' % len(subproofs_data))
    if subproofs_data == []:
        return
    for i, subprf in enumerate(subproofs_data):
        subproofs_data[i]['name'] = args.proof
    dirname = dst_filename(args.file, args.data_path) + '-SUBPROOFS/'
    json.dump(subproofs_data, open(os.path.join(dirname, args.proof + '.json'), 'wt'))
  
  
if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    import argparse
    arg_parser = argparse.ArgumentParser(description='Extract the synthetic proofs from intermediate goals')
    arg_parser.add_argument('--debug', action='store_true')
    arg_parser.add_argument('--file', type=str, help='The meta file to process')
    arg_parser.add_argument('--proof', type=str, help='The proof to extract')
    arg_parser.add_argument('--max_length', type=int, default=4, help='The maximum length for synthetic proofs')
    arg_parser.add_argument('--timeout', type=int, default=3600, help='Timeout for SerAPI')
    arg_parser.add_argument('--data_path', type=str, default='./data')
    args = arg_parser.parse_args()
    print(args)

    human_proof_file = dst_filename(args.file, args.data_path) + '-PROOFS/' + args.proof + '.json'
    if not os.path.exists(human_proof_file):
        print('%s does not exist. Exiting..' % human_proof_file)
        sys.exit(0)
    dirname = dst_filename(args.file, args.data_path) + '-SUBPROOFS/'
    try:
        os.makedirs(dirname)
    except os.error:
         pass
    db_path = os.path.join(dirname, args.proof + '_sexp_cache')
    sexp_cache = SexpCache(db_path)

    file_data = json.load(open(dst_filename(args.file, args.data_path) + '.json'))
    subproofs_data = get_subproofs(human_proof_file, file_data['vernac_cmds'], sexp_cache, args)
    dump(subproofs_data, args)
