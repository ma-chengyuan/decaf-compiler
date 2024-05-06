#!/bin/bash

# for use with test_compile.py

docker run \
  --mount type=bind,source="$(pwd)",target=/mnt \
  --mount type=bind,source="$(pwd)/../public-tests/derby/lib",target=/derby_lib \
  compilers gcc -O0 -no-pie /mnt/test_program.S -L/derby_lib -l6035_linux_x86 -o /mnt/test_program
