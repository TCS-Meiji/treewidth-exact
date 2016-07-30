CC = gcc
CFLAGS = -std=gnu99 -o2
#CFLAGS = -std=gnu99 -o0 -g

.PHONY: all
all: tw-exact

tw-exact: main.o l1.o l2.o l4.o l16.o l64.o graph.o 
	$(CC) -o tw-exact main.o l1.o l2.o l4.o l16.o l64.o graph.o 

main.o: main.c td.h graph.h 

l1.o: l1.c td.h graph.h

l2.o: l2.c td.h graph.h

l4.o: l4.c td.h graph.h

l16.o: l16.c td.h graph.h

l64.o: l64.c td.h graph.h

graph.o: graph.c td.h graph.h

.PHONY: clean
clean:
	rm -f *.o

.PHONY: test
#test: 
#	./run_test.sh


