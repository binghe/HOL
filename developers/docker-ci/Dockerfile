# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), CI image
#

# NOTE: this base image is built by "base/Dockerfile"
FROM binghelisp/hol-dev:latest

ARG BUILD_OPT="--expk -j4"

WORKDIR /ML/HOL

ENV PATH=/ML/HOL/bin:$PATH

# copy all files to the docker image
COPY --link . .

# build HOL
RUN poly < tools/smart-configure.sml 
RUN bin/build ${BUILD_OPT}

# start hol
ENTRYPOINT /ML/HOL/bin/hol
