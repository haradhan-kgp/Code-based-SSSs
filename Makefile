CC     ?= gcc
CFLAGS ?= -O2 -Wall
TARGET  = ramp_sss

all: $(TARGET)

$(TARGET): ramp_sss.c
	$(CC) $(CFLAGS) -o $@ $< -lm

test: $(TARGET)
	./$(TARGET)

bench: $(TARGET)
	./$(TARGET) bench

latex: $(TARGET)
	./$(TARGET) latex

clean:
	rm -f $(TARGET)

.PHONY: all test bench latex clean
