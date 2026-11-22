# hlir-scan --makefile fixture: the compile options live here, not on the command line
CC      = gcc
MODE   ?= release
EXTRA   = -DEXTRA_FEATURE
CFLAGS  = -O2 -Wall -Iinc -DLIMIT=8 $(EXTRA) -fno-strict-overflow
ifeq ($(MODE),debug)
CFLAGS += -DDEBUG_CHECKS=1
endif
SRCS    = src/main.c src/util.c
OBJS    = $(SRCS:.c=.o)

all: $(OBJS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@
