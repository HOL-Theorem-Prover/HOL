# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), base image
#
# e.g. docker buildx build --platform linux/amd64,linux/arm64v8 .

FROM binghelisp/hol-dev:base

LABEL org.opencontainers.image.authors="Chun Tian (binghe) <binghe.lisp@gmail.com>"

# The following two arguments are supported by "docker buildx"
ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN echo "I was running on $BUILDPLATFORM, building for $TARGETPLATFORM" > /tmp/log

WORKDIR /ML

# Z3 2.19 and 2.19.1
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ] || [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q -O z3-2.19.tar.gz https://github.com/Z3Prover/bin/raw/master/legacy/z3-2.19.tar.gz; \
    tar xzf z3-2.19.tar.gz; \
    mv z3 z3-2.19; \
    rm z3-2.19.tar.gz; \
fi

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ] || [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q -O z3-2.19.1.tar.gz https://github.com/Z3Prover/bin/raw/master/legacy/z3-2.19.1.tar.gz; \
    tar xzf z3-2.19.1.tar.gz; \
    mv z3 z3-2.19.1; \
    rm z3-2.19.1.tar.gz; \
fi

# Z3 4.12.4
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-x64-glibc-2.35.zip; \
    unzip z3-4.12.4-x64-glibc-2.35.zip; \
    mv z3-4.12.4-x64-glibc-2.35 z3-4.12.4; \
    rm z3-4.12.4-x64-glibc-2.35.zip; \
fi

RUN if [ "linux/arm64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-arm64-glibc-2.35.zip; \
    unzip z3-4.12.4-arm64-glibc-2.35.zip; \
    mv z3-4.12.4-arm64-glibc-2.35 z3-4.12.4; \
    rm z3-4.12.4-arm64-glibc-2.35.zip; \
fi

# Z3 4.x
ARG Z3_VERSION="4.13.0"

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip; \
    unzip z3-${Z3_VERSION}-x64-glibc-2.35.zip; \
    mv z3-${Z3_VERSION}-x64-glibc-2.35 z3-${Z3_VERSION}; \
    rm z3-${Z3_VERSION}-x64-glibc-2.35.zip; \
fi

RUN if [ "linux/arm64" = "$TARGETPLATFORM" ]; then \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-arm64-glibc-2.35.zip; \
    unzip z3-${Z3_VERSION}-arm64-glibc-2.35.zip; \
    mv z3-${Z3_VERSION}-arm64-glibc-2.35 z3-${Z3_VERSION}; \
    rm z3-${Z3_VERSION}-arm64-glibc-2.35.zip; \
fi

# Yices 1.0.40
RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://yices.csl.sri.com/old/binaries/yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz; \
    tar xzf yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz; \
    rm yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz; \
fi
RUN if [ "linux/386" = "$TARGETPLATFORM" ]; then \
    wget -q https://yices.csl.sri.com/old/binaries/yices-1.0.40-i686-pc-linux-gnu-static-gmp.tar.gz; \
    tar xzf yices-1.0.40-i686-pc-linux-gnu-static-gmp.tar.gz; \
    rm yices-1.0.40-i686-pc-linux-gnu-static-gmp.tar.gz; \
fi

# cvc5
ARG CVC5_VERSION="1.1.2"

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q -O cvc5-Linux-static.zip \
         https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-static.zip; \
    unzip cvc5-Linux-static.zip; \
    rm cvc5-Linux-static.zip; \
    ln -s cvc5-Linux-static/bin/cvc5 cvc5-Linux; \
fi

# NuRV 2.0.0
ARG SMV_VERSION="2.0.0"

RUN mkdir -p solvers

RUN if [ "linux/amd64" = "$TARGETPLATFORM" ]; then \
    wget -q https://es-static.fbk.eu/tools/nurv/releases/NuRV-${SMV_VERSION}-linuxx64.tar.bz2; \
    tar xjf NuRV-${SMV_VERSION}-linuxx64.tar.bz2; \
    mv NuRV-${SMV_VERSION}-linuxx64/NuRV solvers; \
    rm -rf NuRV-${SMV_VERSION}-linuxx64*; \
fi

RUN if [ "linux/arm64" = "$TARGETPLATFORM" ]; then \
    wget -q https://es-static.fbk.eu/tools/nurv/releases/NuRV-${SMV_VERSION}-linuxarm64.tar.bz2; \
    tar xjf NuRV-${SMV_VERSION}-linuxarm64.tar.bz2; \
    mv NuRV-${SMV_VERSION}-linuxarm64/NuRV solvers; \
    rm -rf NuRV-${SMV_VERSION}-linuxx64*; \
fi

ENV HOL4_SMV_EXECUTABLE=/ML/solvers/NuRV

# more packages for buliding HOL manuals (+pandoc for Markdown), etc.
RUN apt-get install -qy texlive-latex-recommended
RUN apt-get install -qy pandoc latexmk texlive-latex-extra
RUN apt-get install -qy texlive-fonts-extra texlive-science
RUN apt-get clean

# z3 and cvc5 as system packages
RUN apt-get install -qy z3 cvc5
RUN apt-get clean
