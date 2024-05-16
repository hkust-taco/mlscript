CXX := /opt/llvm/bin/clang++
CFLAGS := $(CFLAGS) -O3 -Wall -Wextra -ggdb3 -std=c++20 -I/opt/homebrew/include #-fsanitize=address,leak
LDFLAGS := $(LDFLAGS) -Wl,-stack_size -Wl,0x20000000 -L/opt/homebrew/lib -lgmp -lmimalloc
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