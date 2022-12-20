# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

# Hardware specification for Windows and Linux virtual machines: 2-core CPU (x86_64)
ARG BUILD_OPT="--expk -j4"
ARG ML_PROG=poly

WORKDIR /ML/HOL

# copy all files to the docker image
COPY --link . .

# build HOL
RUN ${ML_PROG} < tools/smart-configure.sml 
RUN bin/build ${BUILD_OPT}

ENV PATH=/ML/HOL/bin:$PATH

# default entrypoint
ENTRYPOINT /ML/HOL/bin/hol
