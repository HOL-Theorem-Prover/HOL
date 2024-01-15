# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#
# NOTE: this docker image is NOT for HOL developers to use interactively.

# This "base" image is described in "base/Dockerfile"
FROM --platform=$TARGETPLATFORM binghelisp/hol-dev:latest

# The following two arguments are supported by "docker buildx" commands
ARG TARGETPLATFORM
ARG BUILDPLATFORM

# GitHub Actions' hardware specification for Linux virtual machines: 2-core CPU (x86_64)
# By default we use 4 cores in other building environments (e.g. Docker Hub autobuilds)
ARG BUILDOPTS="--expk -j4"
ARG SML=poly

WORKDIR /ML/HOL

# fast copy all files to the docker image
COPY --link . .

ARG Z3_VERSION
ARG CVC_VERSION
ARG YICES_VERSION

# if --build-arg Z3_VERSION=2.19, set HOL4_Z3_EXECUTABLE to its full path,
# or set to null otherwise.
ENV HOL4_Z3_EXECUTABLE=${Z3_VERSION:+/ML/z3-${Z3_VERSION}/bin/z3}

# if --build-arg CVC_VERSION=5, set HOL4_CVC_EXECUTABLE to its full path,
# or set to null otherwise.
ENV HOL4_CVC_EXECUTABLE=${CVC_VERSION:+/ML/cvc${CVC_VERSION}-Linux}

# if --build-arg YICES_VERSION=1.0.40, set HOL4_YICES_EXECUTABLE to its full path,
# or set to null otherwise.
ENV HOL4_YICES_EXECUTABLE=${YICES_VERSION:+/ML/yices-${YICES_VERSION}/bin/yices}

# remove potential local poly-includes.ML for docker builds
RUN rm -f tools-poly/poly-includes.ML

# building HOL
RUN ${SML} < tools/smart-configure.sml 
RUN bin/build ${BUILDOPTS}

# This can be overrided by "docker run <command>"
CMD ["/ML/HOL/bin/hol"]
