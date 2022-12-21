# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

# GitHub Actions' hardware specification for Linux virtual machines: 2-core CPU (x86_64)
ARG BUILDOPTS="--expk -j2"
ARG SML=poly

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

# building HOL
RUN ${SML} < tools/smart-configure.sml 
RUN bin/build ${BUILDOPTS}

# [optional] building some notable examples
RUN cd examples/miller && Holmake
RUN cd examples/probability && Holmake

# default entrypoint
ENTRYPOINT /ML/HOL/bin/hol
