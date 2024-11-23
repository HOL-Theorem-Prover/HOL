# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/amd64,linux/arm64v8 .

# GitHub Actions recommends Debian-based systems as base images
FROM debian:trixie

LABEL org.opencontainers.image.authors="Chun Tian (binghe) <binghe.lisp@gmail.com>"

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM
ARG POLY_VERSION="master"

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML
VOLUME /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

# Some necessary Debian packages
# NOTE: GCC 13 is necessary for building Moscow ML (default compiler is now GCC 14).
RUN apt-get update -qy
RUN apt-get install -qy build-essential git libgmp-dev wget curl procps file unzip vim gcc-13
RUN apt-get clean

# for Unicode display, learnt from Magnus Myreen
RUN apt-get install -qy locales-all terminfo

# Extra graphics-related tools
RUN apt-get install -qy graphviz emacs-nox

# clean up downloaded packages after installation (this reduces Docker image sizes)
RUN apt-get clean

# 1. install Moscow ML (https://github.com/kfl/mosml.git) with GCC 13
COPY mosml-gcc-13.patch /ML
RUN wget -q -O - https://github.com/kfl/mosml/archive/refs/tags/ver-2.10.1.tar.gz | tar xzf -
RUN cd mosml-ver-2.10.1/src; patch -p0 < /ML/mosml-gcc-13.patch;
RUN cd mosml-ver-2.10.1; make -C src world install
RUN rm -rf mosml-ver-2.10.1 *.patch

# 2. install polyml (https://github.com/polyml/polyml.git)
RUN if [ "master" = "$POLY_VERSION" ]; then \
       wget -q -O polyml-${POLY_VERSION}.zip \
         https://github.com/polyml/polyml/archive/refs/heads/master.zip; \
       unzip polyml-${POLY_VERSION}.zip; \
    else \
       wget -q -O polyml-${POLY_VERSION}.tar.gz \
         https://github.com/polyml/polyml/archive/refs/tags/v${POLY_VERSION}.tar.gz; \
       tar xzf polyml-${POLY_VERSION}.tar.gz; \
    fi

RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
       cd polyml-${POLY_VERSION} && ./configure --build=i686-pc-linux-gnu --enable-intinf-as-int; \
    elif [ "linux/riscv64" = "$TARGETPLATFORM" ]; then \
       cd polyml-${POLY_VERSION} && ./configure --build=riscv64-pc-linux-gnu --enable-intinf-as-int; \
    else \
       cd polyml-${POLY_VERSION} && ./configure --enable-intinf-as-int; \
    fi

RUN make -C polyml-${POLY_VERSION} -j4
RUN make -C polyml-${POLY_VERSION} install
RUN rm -rf polyml-${POLY_VERSION}*

# 3. install MLton binary (https://github.com/MLton/mlton.git) for linux/amd64 only
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
       wget -q -O - \
          https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz | tar xzf -; \
    fi
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
       make -C mlton-20210117-1.amd64-linux-glibc2.31; \
    fi
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

ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en
ENV LC_ALL=en_US.UTF-8
