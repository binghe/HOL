# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM riscv64/ubuntu:devel

MAINTAINER Chun Tian <binghe.lisp@gmail.com>

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM
ARG POLY_VERSION="5.9.1"

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# some necessary Debian packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev wget curl procps file unzip

# for Unicode display, learnt from Magnus Myreen
RUN apt-get install -qy locales-all terminfo man aptitude

# clean up downloaded packages after installation (this reduces Docker image sizes)
RUN apt-get clean

# 2. install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-${POLY_VERSION}.tar.gz \
    https://github.com/polyml/polyml/archive/refs/tags/v${POLY_VERSION}.tar.gz
RUN tar xzf polyml-${POLY_VERSION}.tar.gz
RUN cd polyml-${POLY_VERSION} && ./configure --enable-intinf-as-int
RUN make -C polyml-${POLY_VERSION} -j4
RUN make -C polyml-${POLY_VERSION} install
RUN rm -rf polyml-${POLY_VERSION} polyml-${POLY_VERSION}.tar.gz

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
