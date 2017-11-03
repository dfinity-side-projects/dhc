FROM ubuntu:xenial

ENV DEBIAN_FRONTEND noninteractive
ENV LD_LIBRARY_PATH /usr/local/lib
ENV PATH ${PATH}:/root/.local/bin

RUN apt-get update
RUN apt-get install -y asciidoc curl git libbz2-dev libncurses5-dev

### Install Stack
RUN mkdir -p /root/.local/bin
RUN curl -sSL https://get.haskellstack.org | sh

### Install Haste
WORKDIR /tmp
RUN git clone https://github.com/valderman/haste-compiler
WORKDIR /tmp/haste-compiler
RUN git checkout 0.6.0.0
RUN stack setup
RUN stack install
RUN stack install hsc2hs
RUN stack exec haste-boot -- --force --local

### Install Haste package manager
WORKDIR /root/.haste/x86_64-linux-haste-0.6.0.0-ghc-7.10.3/haste-cabal
RUN cp libgmp.so.3 ${LD_LIBRARY_PATH}
RUN cp haste-cabal.bin /root/.local/bin/haste-cabal

### Install Haste packages
RUN haste-cabal install bimap parsec

### Create workspace
RUN mkdir /workspace
WORKDIR /workspace
