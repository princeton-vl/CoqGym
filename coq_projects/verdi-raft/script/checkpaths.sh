#!/usr/bin/env bash

set -e

if ! [ -f _CoqProject ]; then
    exit 0
fi

if [ "${TRAVIS}x" != "x" ]; then
    exit 0
fi


grep '\.v' _CoqProject | sort > build.files
find . -name '*.v' -not -path "./script/assumptions.v" | sed 's!^\./!!' | sort > files

comm -23 files build.files > files.missing.from.build
comm -13 files build.files > nonexistant.build.files

EXIT_CODE=0

if [ -s files.missing.from.build ]
then
    echo 'The following files are present but are missing from _CoqProject.'
    echo 'Perhaps you have added a new file and should rerun ./configure?'
    cat files.missing.from.build
    EXIT_CODE=1
fi

if [ -s nonexistant.build.files ]
then
    echo 'The following files are present in _CoqProject but do not exist.'
    echo 'Perhaps you have deleted a file and should rerun ./configure?'
    cat nonexistant.build.files
    EXIT_CODE=1
fi

rm -f files build.files files.missing.from.build nonexistant.build.files
exit $EXIT_CODE
