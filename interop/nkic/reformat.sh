#!/bin/bash
set -e -u -o pipefail
trap "kill 0" SIGINT SIGTERM

clang-format -i *.h *.c
