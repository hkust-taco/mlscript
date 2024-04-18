CXX := clang++
CFLAGS := $(CFLAGS) -O3 -Wall -Wextra -ggdb3 -std=c++17 # -fsanitize=address
LDFLAGS := $(LDFLAGS) -Wl,-stack_size -Wl,0x20000000
SRC := mls.cpp
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

$(TARGET): pre $(SRC) $(INCLUDES)
	$(CXX) $(CFLAGS) $(LDFLAGS) $(SRC) -o $(TARGET)