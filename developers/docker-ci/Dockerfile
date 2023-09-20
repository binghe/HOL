# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

RUN apt-get update -qy

# IDE
RUN apt-get install -qy emacs-nox
RUN apt-get clean

WORKDIR /ML
VOLUME /ML

# for HOL Emacs mode (Emacs is not installed by default, however)
COPY .emacs /root

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
