CXX := /opt/llvm/bin/clang++
CFLAGS := $(CFLAGS) -O3 -Wall -Wextra -ggdb3 -std=c++20 -I/opt/homebrew/include -Wno-inconsistent-missing-override
LDFLAGS := $(LDFLAGS) -L/opt/homebrew/lib -lmimalloc -lgmp
SRC := gcd.cpp
INCLUDES = mlsprelude.h
TARGET := mls

.PHONY: pre all run clean

all: $(TARGET)

run: $(TARGET) 
	./$(TARGET)

pre: $(SRC)
	sed -i '' 's#^//│ ##g' $(SRC)

clean:
	rm -r $(TARGET) $(TARGET).dSYM

$(TARGET): $(SRC) $(INCLUDES)
	$(CXX) $(CFLAGS) $(LDFLAGS) $(SRC) -o $(TARGET)