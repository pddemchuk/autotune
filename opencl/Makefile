CC=g++
FLAGS=-L/usr/lib/x86_64-linux-gnu -lOpenCL
OBJ=sum

all: build run

.PHONY: build
build:
	$(CC) main.cpp $(FLAGS) -o $(OBJ)

.PHONY: run
run:
	@echo ;
	./sum

.PHONY: clean
clean:
	rm *.bin $(OBJ)
