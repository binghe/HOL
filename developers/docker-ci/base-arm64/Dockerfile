# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image for ARM64
#
# e.g. docker build --push -t binghelisp/hol-dev:arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM ubuntu:20.04

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib

# necessary packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev curl wget

# optional packages (IDE and others)
RUN apt-get install -qy emacs-nox vim automake procps
RUN apt-get clean

# install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-5.9.tar.gz https://github.com/polyml/polyml/archive/refs/tags/v5.9.tar.gz
RUN tar xzf polyml-5.9.tar.gz
RUN cd polyml-5.9 && ./configure --enable-intinf-as-int
RUN make -C polyml-5.9 -j4
RUN make -C polyml-5.9 compiler
RUN make -C polyml-5.9 install

# [optional] delete building directories for smaller image sizes
RUN rm -rf polyml*

# for developments using this base image with attached /ML volumes
ENV PATH=/ML/HOL/bin:$PATH
