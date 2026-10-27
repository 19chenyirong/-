.PHONY: check build full download
JOBS ?= 2

check:
	python3 -B scripts/reproduce.py check

build:
	python3 -B scripts/reproduce.py build --jobs $(JOBS)

full:
	python3 -B scripts/reproduce.py full --jobs $(JOBS)

download:
	python3 -B scripts/fetch-qcp.py
