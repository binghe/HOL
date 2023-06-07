IMAGE=binghelisp/hol-dev

build:
	docker buildx build --platform linux/386 .
	docker buildx build --platform linux/amd64 .
	docker buildx build --platform linux/arm64 .
	docker buildx build --platform linux/386,linux/amd64,linux/arm64 -t $(IMAGE) .

push:
	docker push $(IMAGE)

run:
	docker run -ti --rm $(IMAGE)
