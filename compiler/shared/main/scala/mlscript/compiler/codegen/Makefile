CC := /usr/bin/clang++
CFLAGS := -O3 -Wall -Wextra -ggdb3 -std=c++17 -fsanitize=address,undefined
LDFLAGS :=
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
	$(CC) $(CFLAGS) $(LDFLAGS) $(SRC) -o $(TARGET)