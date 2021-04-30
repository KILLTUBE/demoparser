CC=gcc -Wfatal-errors

OBJ=common.o dump.o huff.o main.o msg.o parse.o

all: $(OBJ) dm_68

dm_68: *.c
	$(CC) -o dm_68 $(OBJ)

clean:
	rm -f dm_68 *.o
