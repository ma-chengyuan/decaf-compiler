#!/bin/bash

# for use with test_compile.py

docker run \
  --mount type=bind,source="$(pwd)",target=/mnt \
  compilers /mnt/test_program
