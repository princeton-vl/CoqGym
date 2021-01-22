import os
import json
from glob import glob
from utils import get_code, SexpCache, set_paths, extract_code, dst_filename
from serapi import SerAPI
import pdb


def check_file(filename, sexp_cache, args):
    print("\n" + filename)
    coq_filename = os.path.splitext(filename)[0] + ".v"
    fields = coq_filename.split(os.path.sep)
    loc2code = get_code(open(coq_filename, "rb").read())
    file_data = {
        "filename": os.path.sep.join(fields[2:]),
        "coq_project": fields[1],
        "vernac_cmds": [],
        "num_extra_cmds": None,
        "proofs": [],
    }
    meta = open(filename).read()

    with SerAPI(args.timeout, args.debug) as serapi:
        # set the path
        file_data["vernac_cmds"].extend(set_paths(meta, serapi, sexp_cache))
        file_data["num_extra_cmds"] = len(file_data["vernac_cmds"])

        # extract the coq code
        coq_code = extract_code(meta, loc2code)

        # process the coq code
        for num_executed, (code_line, tags) in enumerate(coq_code):
            if "PROOF_NAME" in tags:
                if tags["PROOF_NAME"] not in file_data["proofs"]:
                    file_data["proofs"].append(tags["PROOF_NAME"])
            # execute until the proof editing mode starts
            if args.debug:
                print("%d: %s" % (num_executed, code_line))
            _, ast = serapi.execute(code_line, return_ast=True)
            file_data["vernac_cmds"].append(
                (code_line, tags["VERNAC_TYPE"], sexp_cache.dump(ast))
            )

    return file_data


def dump(file_data, args):
    path = os.path.join(
        args.data_path, file_data["coq_project"], file_data["filename"]
    )[:-2]
    try:
        os.makedirs(os.path.split(path)[0])
    except os.error:
        pass
    json.dump(file_data, open(path + ".json", "wt"))


def process_file(filename):
    # extract a Coq file
    db_path = dst_filename(filename, args.data_path) + "-sexp_cache"
    try:
        os.makedirs(os.path.split(db_path)[0])
    except os.error:
        pass
    sexp_cache = SexpCache(db_path)
    file_data = check_file(filename, sexp_cache, args)
    dump(file_data, args)


if __name__ == "__main__":
    import sys

    sys.setrecursionlimit(100000)
    import argparse

    arg_parser = argparse.ArgumentParser(
        description="Execute the Coq source code and locate the proofs"
    )
    arg_parser.add_argument(
        "--debug", action="store_true", help="print the executed Coq code"
    )
    arg_parser.add_argument(
        "--proj", type=str, help="The Coq project to process (default to all projects)"
    )
    arg_parser.add_argument(
        "--meta_files",
        type=str,
        help="The file containing the paths of *.meta files (default to all *.meta files)",
    )
    arg_parser.add_argument(
        "--file",
        type=str,
        help="The meta file to process (default to all *.meta files)",
    )
    arg_parser.add_argument(
        "--timeout", type=int, default=600, help="Timeout for SerAPI"
    )
    arg_parser.add_argument("--data_path", type=str, default="./data")
    args = arg_parser.parse_args()
    assert args.proj is None or args.meta_files is None

    # grab the *.meta files to process
    if args.proj:
        meta_files = list(glob("coq_projects/%s/**/*.meta" % args.proj, recursive=True))
    elif args.meta_files:
        meta_files = [line.strip() for line in open(args.meta_files)]
    elif args.file:
        meta_files = [args.file]
    else:
        meta_files = list(glob("coq_projects/**/*.meta", recursive=True))
    meta_files.sort()
    print("%d Coq files to process" % len(meta_files))

    # process each of them
    for filename in meta_files:
        process_file(filename)
