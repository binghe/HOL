# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

# GitHub Actions' hardware specification for Linux virtual machines: 2-core CPU (x86_64)
ARG BUILDOPTS="--expk -j4"
ARG SML=poly

# Environment variables get the (overridden) values of (build) arguments
ENV ENV_SML       $SML
ENV ENV_BUILDOPTS $BUILDOPTS

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

# building HOL
RUN ${ENV_SML} < tools/smart-configure.sml 
RUN bin/build ${ENV_BUILDOPTS}

# This can be overrided by "docker run <command>"
CMD ["/ML/HOL/bin/hol"]
