# SPDX-License-Identifier: Apache-2.0
CC ?= cc
CFLAGS_STRICT = -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -Wshadow -Wconversion -Iinclude
CFLAGS_SAN = -std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer -Iinclude

.PHONY: all test sanitize fuzz clean

all: build/cd_terrace_cli build/fuzz_cd_terrace

build:
	mkdir -p build

build/cd_terrace_cli: build src/cd_terrace.c tests/test_cd_terrace.c include/cd_terrace.h
	$(CC) $(CFLAGS_STRICT) src/cd_terrace.c tests/test_cd_terrace.c -o build/cd_terrace_cli

build/fuzz_cd_terrace: build src/cd_terrace.c tests/fuzz_cd_terrace.c include/cd_terrace.h
	$(CC) $(CFLAGS_STRICT) src/cd_terrace.c tests/fuzz_cd_terrace.c -o build/fuzz_cd_terrace

test: build/cd_terrace_cli
	./build/cd_terrace_cli --verify-all

sanitize: build src/cd_terrace.c tests/test_cd_terrace.c tests/fuzz_cd_terrace.c include/cd_terrace.h
	$(CC) $(CFLAGS_SAN) src/cd_terrace.c tests/test_cd_terrace.c -o build/cd_terrace_san
	./build/cd_terrace_san --verify-all
	$(CC) $(CFLAGS_SAN) src/cd_terrace.c tests/fuzz_cd_terrace.c -o build/fuzz_san
	./build/fuzz_san 25000

fuzz: build/fuzz_cd_terrace
	./build/fuzz_cd_terrace 100000

clean:
	rm -rf build
