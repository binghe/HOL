# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), CI image
#

# NOTE: this base image is built by "base/Dockerfile"
FROM binghelisp/hol-dev:latest

WORKDIR /HOL
VOLUME /HOL

ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# copy some visible files to the docker image
COPY . .

# NOTE: the following commands assume that HOL working directory has been
#       checked out in the current working directory (whose location is
#       given by GitHub Actions.
RUN ls -l
RUN poly < tools/smart-configure.sml 
RUN bin/build --expk -j4
