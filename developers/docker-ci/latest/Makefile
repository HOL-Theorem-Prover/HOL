DOCKER_IMAGE=binghelisp/hol-dev:latest

build:
	docker buildx build --platform linux/386,linux/amd64,linux/arm64,linux/riscv64 \
		-t $(DOCKER_IMAGE) .

push:
	docker push $(DOCKER_IMAGE)

# This runs the docker image in your native platform
run:
	docker run -ti --rm $(DOCKER_IMAGE)
