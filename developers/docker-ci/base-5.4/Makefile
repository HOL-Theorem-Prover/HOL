IMAGE=binghelisp/hol-dev:polyml-5.4

build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/386,linux/amd64 -t $(IMAGE) .

push: build
	docker push $(IMAGE)

run:
	docker run --rm -ti $(IMAGE)
