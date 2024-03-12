#!/bin/bash

# run docker build -t compilers .

cargo run -- "$@" -t assembly --output program.S
docker run \
  --mount type=bind,source="$(pwd)"/program.S,target=/program.S,readonly \
  compilers /bin/bash -c "gcc -O0 -no-pie /program.S -o program && ./program && echo \"Finished with exit code $?\""
