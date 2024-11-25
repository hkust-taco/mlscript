CXX := g++
CFLAGS := $(CFLAGS) -O3 -Wall -Wextra -std=c++20 -I. -Wno-inconsistent-missing-override -I/opt/homebrew/include
LDFLAGS := $(LDFLAGS) -lmimalloc -lgmp -L/opt/homebrew/lib
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
