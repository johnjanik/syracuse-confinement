# Makefile — collatz_tests numerical suite.
# Profiles:
#   make            -> FAST128 (default, __uint128_t orbit values)
#   make GMP=1      -> GMP backend (mpz_t; requires libgmp)
#   make DEBUG=1    -> enable invariant assertions (AIPM_DEBUG)
# Combine freely, e.g. `make GMP=1 DEBUG=1`.

CC      ?= cc
CSTD    := -std=c11
WARN    := -Wall -Wextra -Wshadow -Wconversion -Wno-sign-conversion
OPT     := -O2
CFLAGS  := $(CSTD) $(WARN) $(OPT) -D_POSIX_C_SOURCE=200809L -Iinclude
LDFLAGS :=
LDLIBS  := -lm

ifdef GMP
  CFLAGS += -DUSE_GMP
  LDLIBS += -lgmp
endif
ifdef DEBUG
  CFLAGS += -DAIPM_DEBUG -g
endif

SRC := $(wildcard src/*.c)
OBJ := $(SRC:.c=.o)
BIN := collatz_tests

.PHONY: all clean test
all: $(BIN)

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) -o $@ $^ $(LDLIBS)

src/%.o: src/%.c
	$(CC) $(CFLAGS) -c -o $@ $<

test: $(BIN)
	@$(MAKE) -C tests run

clean:
	rm -f $(OBJ) $(BIN)
	rm -f tests/*.o tests/test_runner
