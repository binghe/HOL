# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM binghelisp/hol-dev:latest

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# NuRV 2.0.0
ARG SMV_VERSION="2.0.0"

mkdir -p solvers

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://es-static.fbk.eu/tools/nurv/releases/NuRV-${SMV_VERSION}-linuxx64.tar.bz2; \
    tar xjf NuRV-${SMV_VERSION}-linuxx64.tar.bz2; \
    mv NuRV-${SMV_VERSION}-linuxx64/NuRV solvers; \
    rm -rf NuRV-${SMV_VERSION}-linuxx64*; \
fi

RUN if [ "linux/arm64" = "$TARGETPLATFORM" ]; then \
    wget -q https://es-static.fbk.eu/tools/nurv/releases/NuRV-${SMV_VERSION}-linuxarm64.tar.bz2; \
    tar xjf NuRV-${SMV_VERSION}-linuxarm64.tar.bz2; \
    mv NuRV-${SMV_VERSION}-linuxarm64/NuRV solvers; \
    rm -rf NuRV-${SMV_VERSION}-linuxx64*; \
fi

ENV HOL4_SMV_EXECUTABLE=/ML/solvers/NuRV
