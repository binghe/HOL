IMAGE=binghelisp/hol-dev:polyml-5.4

build:
	docker build -t $(IMAGE) .

push: build
	docker push $(IMAGE)

run:
	docker run --rm -ti $(IMAGE)
