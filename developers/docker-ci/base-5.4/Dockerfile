# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image for HOL-Omega
#
# e.g. docker build --push -t binghelisp/hol-dev:omega .

# GitHub Actions recommends Debian-based systems as base images
FROM ubuntu:16.04

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib

# necessary packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev curl wget

# optional packages (IDE and others)
RUN apt-get install -qy emacs-nox procps
RUN apt-get clean

# install polyml-5.4.1 (https://github.com/binghe/polyml)
RUN wget -q -O polyml-5.4.1.tar.gz https://github.com/binghe/polyml/archive/refs/tags/v5.4.1.tar.gz
RUN tar xzf polyml-5.4.1.tar.gz
RUN cd polyml-5.4.1 && ./configure
RUN make -C polyml-5.4.1 -j4
RUN make -C polyml-5.4.1 compiler
RUN make -C polyml-5.4.1 install

# install mosml (https://github.com/kfl/mosml.git)
RUN wget -q -O mosml-ver-2.10.1.tar.gz https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz
RUN tar xzf mosml-ver-2.10.1.tar.gz
RUN make -C mosml-ver-2.10.1/src world
RUN make -C mosml-ver-2.10.1/src install

# [optional] delete building directories for smaller image sizes
RUN rm -rf polyml*
RUN rm -rf mosml*

# for developments using this base image with attached /ML volumes
ENV PATH=/ML/HOL-Omega/bin:$PATH
