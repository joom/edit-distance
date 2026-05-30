# Frontend to dune.

.PHONY: default build install uninstall test clean fmt

default: build

build:
	dune build

install:
	dune install

uninstall:
	dune uninstall

test:
	dune runtest

clean:
	dune clean
	git clean -dfXq .

fmt:
	dune build @fmt --auto-promote
