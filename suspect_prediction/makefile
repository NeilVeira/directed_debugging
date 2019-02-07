CC = g++
#Using -Ofast instead of -O3 might result in faster code, but is supported only by newer GCC versions
#CFLAGS = -lm -pthread -O3 -march=native -Wall -funroll-loops -Wno-unused-result
CFLAGS = -lm -O3 -march=native -Wall -funroll-loops -Wno-unused-result -std=c++11

all: suspect2vec

suspect2vec : suspect2vec.cpp
	$(CC) suspect2vec.cpp -o suspect2vec $(CFLAGS)
clean:
	rm -rf suspect2vec 
