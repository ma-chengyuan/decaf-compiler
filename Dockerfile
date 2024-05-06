FROM --platform=linux/amd64 ubuntu:latest

RUN apt-get update && apt-get install -y \
    build-essential vim wget

RUN wget https://github.com/sharkdp/hyperfine/releases/download/v1.16.1/hyperfine_1.16.1_amd64.deb
RUN dpkg -i hyperfine_1.16.1_amd64.deb
