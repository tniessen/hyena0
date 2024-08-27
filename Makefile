CXX = g++
LD = g++

SRCS := $(shell find src -name '*.cc')
OBJS := $(subst .cc,.o,$(SRCS))
DEPS := $(subst .cc,.d,$(SRCS))

CXXFLAGS := -std=c++20 -Wall -Wextra -pedantic -MMD -MP
LDFLAGS :=

ifeq ($(DEBUG),yes)
  CXXFLAGS += -g -O0 -fsanitize=undefined -fdiagnostics-color
  LDFLAGS += -fsanitize=undefined
else
  CXXFLAGS += -Ofast -flto
  LDFLAGS += -flto=auto
endif

all: hyena0

hyena0: $(OBJS)
	$(LD) $(LDFLAGS) -o $@ $^

.PHONY: clean
clean:
	rm -f src/*.o src/*.d hyena0

-include $(DEPS)
