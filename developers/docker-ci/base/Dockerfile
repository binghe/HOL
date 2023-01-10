# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/i386,linux/amd64,linux/arm64 -t binghelisp/hol-dev .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM debian:stable

# The following two arguments are supported by "docker buildx" commands
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# necessary packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev wget curl procps
RUN apt-get clean

# install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-5.9.tar.gz https://github.com/polyml/polyml/archive/refs/tags/v5.9.tar.gz
RUN tar xzf polyml-5.9.tar.gz
RUN cd polyml-5.9 && ./configure --enable-intinf-as-int
RUN make -C polyml-5.9 -j4
RUN make -C polyml-5.9 -j4 compiler install
RUN rm -rf polyml*

# install Moscow ML (https://github.com/kfl/mosml.git)
RUN wget -q -O mosml-ver-2.10.1.tar.gz https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz
RUN tar xzf mosml-ver-2.10.1.tar.gz
RUN make -C mosml-ver-2.10.1/src world install
RUN rm -rf mosml*

# install MLton binary (https://github.com/MLton/mlton.git)
RUN if ["linux/amd64" = "$TARGETPLATFORM"]; then \
    wget -q https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz; fi
RUN if ["linux/amd64" = "$TARGETPLATFORM"]; then tar xzf mlton-20210117-1.amd64-linux-glibc2.31.tgz; fi
RUN if ["linux/amd64" = "$TARGETPLATFORM"]; then make -C mlton-20210117-1.amd64-linux-glibc2.31; fi
RUN rm -rf mlton-20210117-1.amd64-linux-glibc2.31*

# install OpenTheory with local packages
RUN wget -q -O opentheory-1.5.tar.gz https://github.com/binghe/opentheory/archive/refs/tags/v1.5.tar.gz
RUN tar xzf opentheory-1.5.tar.gz
RUN if ["linux/amd64" = "$TARGETPLATFORM"]; then make -C opentheory-1.5 mlton; else make -C opentheory-1.5 polyml; fi
RUN if ["linux/amd64" = "$TARGETPLATFORM"]; then cp opentheory-1.5/bin/mlton/opentheory /usr/local/bin; \
    else cp opentheory-1.5/bin/polyml/opentheory /usr/local/bin; fi
RUN rm -rf opentheory*
RUN wget -q -O /root/opentheory-local.tar.gz \
    https://github.com/binghe/opentheory/releases/download/v1.5/opentheory-local.tar.gz
RUN cd /root && tar xzf opentheory-local.tar.gz && rm opentheory-local.tar.gz

# for HOL Emacs mode (Emacs is not installed by default, however)
COPY .emacs /root
