#!/bin/bash

# for use with test_compile.py

docker run \
  --mount type=bind,source="$(pwd)",target=/mnt \
  --mount type=bind,source="$(pwd)/../public-tests/derby",target=/derby \
  compilers /bin/bash -c "cd /derby && hyperfine --warmup 5 ../mnt/test_program"
