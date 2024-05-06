#!/bin/bash

# for use with test_compile.py

docker run \
  --mount type=bind,source="$(pwd)",target=/mnt \
  compilers gcc -O0 -no-pie /mnt/test_program.S -o /mnt/test_program
