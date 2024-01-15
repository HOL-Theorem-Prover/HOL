# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/386,linux/amd64,linux/arm64 .

# GitHub Actions recommends Debian-based systems as base images
FROM --platform=$TARGETPLATFORM binghelisp/hol-dev:base

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML

# Use this mode when you need zero interaction while installing or upgrading the system via apt
ENV DEBIAN_FRONTEND=noninteractive
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/ML/HOL/bin:$PATH

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Z3 2.19 and 2.19.1
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ] || [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q -O z3-2.19.tar.gz https://github.com/Z3Prover/bin/raw/master/legacy/z3-2.19.tar.gz; \
    tar xzf z3-2.19.tar.gz; \
    mv z3 z3-2.19; \
fi

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ] || [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q -O z3-2.19.1.tar.gz https://github.com/Z3Prover/bin/raw/master/legacy/z3-2.19.1.tar.gz; \
    tar xzf z3-2.19.1.tar.gz; \
    mv z3 z3-2.19.1; \
fi

# Z3 4.x
ARG Z3_VERSION="4.12.4"

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip; \
    unzip z3-${Z3_VERSION}-x64-glibc-2.35.zip; \
    mv z3-${Z3_VERSION}-x64-glibc-2.35 z3-${Z3_VERSION}; \
fi

RUN if [ "linux/arm64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-arm64-glibc-2.35.zip; \
    unzip z3-${Z3_VERSION}-arm64-glibc-2.35.zip; \
    mv z3-${Z3_VERSION}-arm64-glibc-2.35 z3-${Z3_VERSION}; \
fi

# Yices 1.0.40
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://yices.csl.sri.com/old/binaries/yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz; \
    tar xzf yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz; \
fi
RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q https://yices.csl.sri.com/old/binaries/yices-1.0.40-i686-pc-linux-gnu-static-gmp.tar.gz; \
    tar xzf yices-1.0.40-i686-pc-linux-gnu-static-gmp.tar.gz; \
fi

# cvc5
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux; \
    chmod a+x cvc5-Linux; \
fi
