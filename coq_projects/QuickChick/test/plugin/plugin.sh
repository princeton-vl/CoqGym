#!/bin/sh
set -e

# Just test this compiles
coqc -Q ../../src QuickChick plugin.v
