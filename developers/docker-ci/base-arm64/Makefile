IMAGE=binghelisp/hol-dev:arm64

build:
	docker build --platform linux/arm64/v8 -t $(IMAGE) .

push:
	docker push $(IMAGE)

run:
	docker run --rm --platform linux/arm64/v8 -v ML:/ML -ti $(IMAGE)
