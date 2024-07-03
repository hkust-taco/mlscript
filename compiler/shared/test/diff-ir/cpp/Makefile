CXX := clang++
CFLAGS := $(CFLAGS) -O3 -Wall -Wextra -std=c++20 -I. -I/opt/homebrew/include -Wno-inconsistent-missing-override
LDFLAGS := $(LDFLAGS) -L/opt/homebrew/lib -lmimalloc -lgmp
SRC :=
INCLUDES = mlsprelude.h
DST :=
DEFAULT_TARGET := mls
TARGET := $(or $(DST),$(DEFAULT_TARGET))

.PHONY: pre all run clean auto

all: $(TARGET)

run: $(TARGET) 
	./$(TARGET)

pre: $(SRC)
	sed -i '' 's#^//│ ##g' $(SRC)

clean:
	rm -r $(TARGET) $(TARGET).dSYM

auto: $(TARGET)

$(TARGET): $(SRC) $(INCLUDES)
	$(CXX) $(CFLAGS) $(LDFLAGS) $(SRC) -o $(TARGET)
