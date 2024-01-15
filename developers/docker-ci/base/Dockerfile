# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM debian:stable

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM
ARG POLY_VERSION="5.9.1"

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# some necessary Debian packages
RUN apt-get update -qy
RUN apt-get install -qy build-essential graphviz git libgmp-dev wget curl procps file unzip

# for Unicode display, learnt from Magnus Myreen
RUN apt-get install -qy locales-all terminfo man aptitude

# 1. install Moscow ML (https://github.com/kfl/mosml.git)
RUN wget -q -O - https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz | tar xzf -
RUN make -C mosml-ver-2.10.1/src world install
RUN rm -rf mosml-ver-2.10.1

# 2. install polyml (https://github.com/polyml/polyml.git)
RUN wget -q -O polyml-${POLY_VERSION}.tar.gz \
    https://github.com/polyml/polyml/archive/refs/tags/v${POLY_VERSION}.tar.gz
RUN tar xzf polyml-${POLY_VERSION}.tar.gz
RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
       cd polyml-${POLY_VERSION} && ./configure --build=i686-pc-linux-gnu --enable-intinf-as-int; \
    else \
       cd polyml-${POLY_VERSION} && ./configure --enable-intinf-as-int; \
    fi
RUN make -C polyml-${POLY_VERSION} -j4
RUN make -C polyml-${POLY_VERSION} install
RUN rm -rf polyml-${POLY_VERSION} polyml-${POLY_VERSION}.tar.gz

# 3. install MLton binary (https://github.com/MLton/mlton.git) for linux/amd64 only
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q -O - https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz | tar xzf -; fi
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then make -C mlton-20210117-1.amd64-linux-glibc2.31; fi
RUN rm -rf mlton-20210117-1.amd64-linux-glibc2.31

# 4. install OpenTheory (develop version)
RUN wget -q -O opentheory-develop.zip \
    https://github.com/binghe/opentheory/archive/refs/heads/develop.zip && unzip opentheory-develop.zip
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
        make -C opentheory-develop mlton; \
    else \
        make -C opentheory-develop polyml; \
    fi
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
        cp opentheory-develop/bin/mlton/opentheory /usr/local/bin; \
    else \
        cp opentheory-develop/bin/polyml/opentheory /usr/local/bin; \
    fi
RUN rm -rf opentheory-develop opentheory-develop.zip
RUN opentheory init && opentheory install base

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
