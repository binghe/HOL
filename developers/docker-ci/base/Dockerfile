# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker build --push -t binghelisp/hol-dev .

# GitHub Action recommends Debian-based systems as base images
FROM debian:stable

WORKDIR /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib

# necessary packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev curl wget

# optional packages
RUN apt-get install -qy emacs-nox vim automake
RUN apt-get clean

# install Mlton
RUN wget -q https://github.com/MLton/mlton/releases/download/on-20201002-release/mlton-20201002-1.amd64-linux.tgz
RUN tar xzf mlton-20201002-1.amd64-linux.tgz
RUN make -C mlton-20201002-1.amd64-linux

# install polyml
RUN git clone https://github.com/polyml/polyml.git
RUN cd polyml && ./configure --enable-intinf-as-int
RUN make -C polyml -j4
RUN make -C polyml install

# install mosml
RUN git clone https://github.com/kfl/mosml.git
RUN make -C mosml/src world
RUN make -C mosml/src install
