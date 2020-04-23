rat:	rat.c
	${CC} ${CFLAGS} -o rat rat.c

install: rat
	install -m 755 -s rat /usr/local/bin/
	install -m 644 rat.1 /usr/local/man/man1/

clean:
	rm -f *.o rat errs
