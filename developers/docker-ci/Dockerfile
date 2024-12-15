# syntax=docker/dockerfile:1
#
# HOL4 building environment (Docker), the CI image
#
# NOTE: this docker image is NOT for HOL developers to use interactively.

# This "base" image is described in "base/Dockerfile"
FROM binghelisp/hol-dev:latest

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

# if --build-arg Z3_VERSION=anything, set HOL4_Z3_EXECUTABLE to system-installed z3
ENV HOL4_Z3_EXECUTABLE=${Z3_VERSION:+/usr/bin/z3}
RUN if [ "" != "${Z3_VERSION}" ]; then \
    echo "Using Z3 solver: `${HOL4_Z3_EXECUTABLE} -version`"; \
fi

# if --build-arg CVC_VERSION=5, set HOL4_CVC_EXECUTABLE to system-installed cvc5
ENV HOL4_CVC_EXECUTABLE=${CVC_VERSION:+/usr/bin/cvc5}
RUN if [ "" != "${CVC_VERSION}" ]; then \
    echo "Using CVC solver: `${HOL4_CVC_EXECUTABLE} --version | head -1`"; \
fi

# if --build-arg YICES_VERSION=1.0.40, set HOL4_YICES_EXECUTABLE to its full path,
# or set to null otherwise.
ENV HOL4_YICES_EXECUTABLE=${YICES_VERSION:+/ML/yices-${YICES_VERSION}/bin/yices}
RUN if [ "" != "${YICES_VERSION}" ]; then \
    echo "Using Yices solver: `${HOL4_YICES_EXECUTABLE} --version`"; \
fi

# remove potential local poly-includes.ML for docker builds
RUN rm -f tools-poly/poly-includes.ML

# Building HOL itself
RUN ${SML} < tools/smart-configure.sml 
RUN bin/build ${BUILDOPTS}

# Building HOL manuals when PolyML is used
RUN if [ "poly" = "${SML}" ]; then \
    if echo ${BUILDOPTS} | grep -q "otknl"; then \
       echo Skip manual building; \
    else \
       cd Manual; ../bin/Holmake -j2; \
    fi \
fi

# This can be overrided by "docker run <command>"
CMD ["/ML/HOL/bin/hol"]
