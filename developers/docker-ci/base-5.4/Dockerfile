# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image for HOL-Omega
#
# e.g. docker buildx build --platform linux/386,linux/amd64 -t binghelisp/hol-dev:polyml-5.4 .

# GitHub Actions recommends Debian-based systems as base images
FROM ubuntu:16.04

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL-Omega/bin:/ML/HOL/bin:$PATH

# some necessary Debian packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev wget curl procps file

# for Unicode display, learnt from Magnus Myreen
RUN apt-get install -qy locales-all man aptitude
RUN apt-get clean

# 1. install Moscow ML (https://github.com/kfl/mosml.git)
RUN wget -q -O - https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz | tar xzf -
RUN make -C mosml-ver-2.10.1/src world install
RUN rm -rf mosml-ver-2.10.1

# 2. install polyml-5.4.1 (https://github.com/binghe/polyml)
RUN wget -q -O - https://github.com/binghe/polyml/archive/refs/tags/v5.4.1.tar.gz | tar xzf -
RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
       cd polyml-5.4.1 && ./configure --build=i686-pc-linux-gnu --enable-intinf-as-int; \
    else \
       cd polyml-5.4.1 && ./configure --enable-intinf-as-int; \
    fi
RUN make -C polyml-5.4.1 -j4
RUN make -C polyml-5.4.1 compiler install
RUN rm -rf polyml-5.4.1

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
