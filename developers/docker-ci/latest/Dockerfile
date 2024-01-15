# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM binghelisp/hol-dev:base

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

ARG    Z3_VERSION="4.12.4" # Dec 07, 2023
ARG YICES_VERSION="2.6.4"  # Oct 22, 2021

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Z3 legacy (2.19)
RUN wget -q -O z3-2.19.tar.gz https://github.com/Z3Prover/bin/raw/master/legacy/z3-2.19.tar.gz
RUN tar xzf z3-2.19.tar.gz
RUN mv z3 z3-2.19

# Z3 4.x
RUN wget -q https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip
RUN unzip z3-${Z3_VERSION}-x64-glibc-2.35.zip
RUN mv z3-${Z3_VERSION}-x64-glibc-2.35 z3-${Z3_VERSION}

# Yices legacy (1.0.40, Dec 4, 2013)
RUN wget -q https://yices.csl.sri.com/old/binaries/yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz
RUN tar xzf yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz

# Yices2
RUN wget -q https://yices.csl.sri.com/releases/${YICES_VERSION}/yices-${YICES_VERSION}-x86_64-pc-linux-gnu.tar.gz
RUN tar xzf yices-${YICES_VERSION}-x86_64-pc-linux-gnu.tar.gz

# cvc5
RUN wget -q https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux
RUN chmod a+x cvc5-Linux
