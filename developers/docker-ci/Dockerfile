# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), CI image
#

# NOTE: this base image is built by "base/Dockerfile"
FROM binghelisp/hol-dev:latest

ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# copy some visible files to the docker image
COPY bin         .
COPY sigobj      .
COPY src         .
COPY std.prelude .
COPY tools       .
COPY tools-poly  .
COPY examples    .

# NOTE: the following commands assume that HOL working directory has been
#       checked out in the current working directory (whose location is
#       given by GitHub Actions.
RUN poly < tools/smart-configure.sml 
RUN bin/build --expk -j4
