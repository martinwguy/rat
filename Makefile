rat:	rat.c
	${CC} ${CFLAGS} -o rat rat.c

clean:
	rm -f *.o rat errs
