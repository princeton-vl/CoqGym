import time
import os
import shutil
from pathlib import Path
from torchvision.datasets.utils import download_file_from_google_drive, extract_archive


def download_and_unzip_coqgym_data(path):

    # path = Path('~/data_lib/coqgym/').expanduser()
    data_root_path = path.expanduser()

    # https://drive.google.com/file/d/17QTwGiDRVsDPJa5KepdcB-fi3nv-b9Ng/view?usp=sharing
    file_id = "17QTwGiDRVsDPJa5KepdcB-fi3nv-b9Ng"
    projs_split = data_root_path / Path("projs_split.json")
    # if zip not there re-download it
    if not projs_split.exists():
        download_file_from_google_drive(file_id, path, projs_split)

    # https://drive.google.com/file/d/1CGQ_XKQKlrVt-grNzVI1x3laxIJYmWft/view?usp=sharing
    file_id = "1CGQ_XKQKlrVt-grNzVI1x3laxIJYmWft"
    sexp_cache_gz = data_root_path / Path("sexp_cache.tar.gz")
    # if zip not there re-download it
    if not sexp_cache_gz.exists():
        download_file_from_google_drive(file_id, path, sexp_cache_gz)
    shutil.unpack_archive(sexp_cache_gz, path)

    # https://drive.google.com/file/d/1QSxu7U5XMtc8DkIL4TLyl2NhmmUMRgJp/view?usp=sharing
    file_id = "1QSxu7U5XMtc8DkIL4TLyl2NhmmUMRgJp"
    data_zip = data_root_path / Path("data_lib.tar.gz")
    # if zip not there re-download it
    if not data_zip.exists():
        download_file_from_google_drive(file_id, path, data_zip)
    shutil.unpack_archive(data_zip, path)

    # crease sexp database
    do_mdb_load(sexp_cache_gz, data_root_path)


def do_mdb_load(sexp_cache_gz, extract_dir, original_code=False):
    """

    command:
        mdb_load [-V] [-f file] [-n] [-s subdb] [-N] [-T]  envpath
    description:
        The mdb_load utility reads from the standard input and loads it into the LMDB environment envpath.
    Kaiyu's example:
        execute('mdb_load -f sexp_cache.lmdb sexp_cache')
    """
    import shutil

    data_root_path = path.expanduser()

    if original_code:
        # unzip('sexp_cache.tar.gz')
        # os.mkdir('sexp_cache')
        # execute('mdb_load -f sexp_cache.lmdb sexp_cache')
        # os.remove('sexp_cache.lmdb')
        assert False
    else:
        # unzip(sexp_cache_gz, extract_dir)
        shutil.unpack_archive(sexp_cache_gz, data_root_path)

        sexp_cache_dir = data_root_path / "sexp_cache"
        sexp_cache_dir.mkdir(parents=True, exist_ok=True)

        sexp_cache_lmdb = data_root_path / "sexp_cache.lmdb"
        sexp_cache = data_root_path / "sexp_cache"
        # execute creating data_lib base
        exit_code = os.system(f"mdb_load -f {sexp_cache_lmdb} {sexp_cache}")
        assert exit_code == 0

        os.remove(sexp_cache_lmdb)
    print(f"done mdb_load: {sexp_cache_gz, extract_dir}\n")


def get_coqgym_container(path):
    from torchvision.datasets.utils import (
        download_file_from_google_drive,
        extract_archive,
    )

    data_root_path = path.expanduser()

    # https://drive.google.com/file/d/1dzNR8uj5fpo9bN40xfJo_EkFR0vr1FAt/view?usp=sharing
    file_id = "1dzNR8uj5fpo9bN40xfJo_EkFR0vr1FAt"
    path_to_container = data_root_path / Path("coq_gym.simg")
    # if zip not there re-download it
    if not path_to_container.exists():
        download_file_from_google_drive(file_id, path, path_to_container)


if __name__ == "__main__":
    print("Start download..")

    path = Path('./').expanduser()
    print(f"Download path = {path}")
    download_and_unzip_coqgym_data(path)
    get_coqgym_container(path)

    print("Done")
