# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

# By default (on Docker Hub, which cannot take arguments) we use Moscow ML.
# On GitHub Actions, PolyML (SML=poly) are used by passing these arguments.
ARG SML=mosml
ARG BUILDOPTS=--expk

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

# building HOL
RUN $SML < tools/smart-configure.sml 
RUN bin/build $BUILDOPTS

# This can be overrided by "docker run <command>"
CMD ["/ML/HOL/bin/hol"]
