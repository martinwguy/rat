#ifndef lint
static char *sccsid = "@(#)rat.c	1.2 1.2 (UKC) %G%";
#endif  lint

/***

* program name:
	rat.c
* function:
	Rationalise a list of files by changing multiple copies into links
	to the same file.  If any argument is a directory, the contents of
	that directory are included in the list.  Recursion is limited to
	one level, and symbolic links are not followed.  If no arguments
	are given, the contents of the current directory are rationalised.
* how it works:
	The basic data structure is an "associativity list". This is a linked
	list of pointers to sublists. Each sublist represents an "equivalence
	class", and contains references to files which might be identical.
	We scan the list of files given on the command line, and insert each
	file into our list; either in an already-existing equivalence class
	or in a new class if the file is unlike any we have already seen.
	When this has been done, we try and amalgamate the files in each class
	together. This is done by unlinking and forming new links, e.g:

	two files "foo" and "bar" in an equivalence class:

		compare contents of files "foo" and "bar";
		if they are identical:
			unlink file "bar"
			link "foo" to "bar".
			remove "bar" from sublist.

		go on to the next file in the sublist.
	
	Each pair of files in each sublist is compared in this way; files
	are removed from the sublist when they have been linked to another
	file, or when they have been compared with every other file. This
	process repeats until the list contains less than two items.

	If we fail to link one file to another, we try again in the other
	direction.  E.g. if, say, we cannot unlink "bar", then we unlink
	"foo" and link it to "bar" instead.

	For safety reasons, we create a temporary link to each file before
	we unlink it; then if the link fails, the original is replaced.

* switches:
	-v	verbose; print names of files rationalised.
	-n	don't do any linking; just print names.
	-r	recurse down through directories. (careful here)
	-s	follow symbolic links. (not on pre-4.2) (very careful here)
	-u	ignore ownership of files.
* libraries used:
	standard
	-lndir on pre-4.2 systems
* environments:
	Berkeley 4.2BSD VMUNIX.
	Berkeley 4.1BSD VMUNIX.
* history:
	Chris Downey UKC August 1985

***/

#include <stdio.h>
#include <sys/types.h>			/* for off_t etc. */
#include <sys/stat.h>			/* for file sizes etc. */
#include <sys/file.h>			/* for opening files */
#include <errno.h>			/* for error messages */

/*
 * define NEWDIR if we have the new (4.2-style) directory-handling stuff.
 * otherwise, undefine NEWDIR so that the function enterdir() will use
 * the original unix directory structure.
 *
 * define ndir if you have the "ndir.h" emulation of the 4.2 library
 * stuff, but don't define it for systems that have the real thing.
 */
#ifdef	ndir
#include <ndir.h>
#else	ndir
#include <sys/dir.h>
#endif	ndir

#ifdef	DIRBLKSIZ
#define	NEWDIR
#else	DIRBLKSIZ
#undef	NEWDIR
#endif	DIRBLKSIZ


/*
 * if O_RDONLY isn't defined, we assume this is a pre-4.2 system.
 * we will therefore need our own bcmp() or rename() library functions.
 */
#ifndef	O_RDONLY
#define	O_RDONLY	0
#undef	BSD42
#else	O_RDONLY
#define	BSD42
#endif	O_RDONLY


/*
 * symbolic link handling is only available if there are any to handle.
 */
#ifdef	S_IFLNK
#define	USAGE	"usage: rat [-vnrsu] files\n"
#else	S_IFLNK
#define	USAGE	"usage: rat [-vnru] files\n"
#endif	S_IFLNK


#define ISDIR	1			/* return values from functions */
#define NOTDIR	0
#define NOFILE	-1


#define	min(a, b)	((a) < (b) ? (a) : (b))


/*
 * each file is described by the following structure, which is
 * a member of a linked list pointed to by head_t.
 */
typedef struct info {
	struct info *i_next;		/* pointer to next object */
	char *i_name;			/* pointer to file name */
	char *i_dir;			/* pointer to directory */
	ino_t i_ino;			/* inode number */
} info_t;

/*
 * head_t describes a list of associated files, pointed to by h_info,
 * together with common information.
 */
typedef struct header {
	struct	header *h_next;		/* pointer to next object */
	info_t	*h_info;		/* pointer to list of files */
	off_t	h_size;			/* size of files */
	dev_t	h_dev;			/* device number */
	short	h_uid;			/* ownership */
} head_t;


/*
 * internal function declarations.
 */
static	void	apply();

static	head_t	*associate();
static	head_t	*assoc();
static	int	enter();
static	int	newinfo();
static	head_t	*enterdir();
static	head_t	*newhead();

static	void	combine();
static	info_t	*comb2();
static	int	compare();
static	int	replace();
static	int	replace2();

static	char	*mkpath();
static	void	error();
static	void	fatal();


/*
 * library function declarations.
 */
extern	char	*malloc();
extern	char	*strcpy();


/*
 * name of program, for printing error messages.
 */
char	*progname;

/*
 * global option variables.
 */
static	int	verbose = 0;		/* print names of files rationalised */
static	int	noexec = 0;		/* don't actually do anything */
static	int	recursive = 0;		/* recurse down through directories */
#ifdef	S_IFLNK
static	int	symbolic = 0;		/* follow symlinks to directories */
#endif	S_IFLNK
static	int	ignore = 0;		/* ignore ownership of files */
static	int	debug = 0;		/* debugging level */

static	char	*dot = ".";		/* default if no files given */


main(argc, argv)
int argc;
char *argv[];
{
	register int i;			/* loop counter */

	progname = argv[0];

	/*
	 * parse option flags.
	 */
	for (argv++, argc--; argv[0][0] == '-'; argv++, argc--) {
		for (i = 1; argv[0][i] != '\0'; i++) {
			switch (argv[0][i]) {
			case 'v':		/* say what we are doing */
				verbose = 1;
				break;
			case 'n':		/* don't do anything */
				noexec = 1;
				verbose = 1;
				break;
			case 'r':		/* recursive mode */
				recursive = 1;
				break;
#ifdef	S_IFLNK
			case 's':		/* follow symlinks (4.2 only) */
				symbolic = 1;
				break;
#endif	S_IFLNK
			case 'u':		/* ignore ownership info */
				ignore = 1;
				break;
			case 'd':		/* debug - undocumented */
				debug = 1;
				break;
			default:
				fputs(USAGE, stderr);
				exit(1);
			}
		}
	}

	/*
	 * read all the files into an associativity list, and then
	 * apply "combine" to each equivalence class in turn.
	 */
	if (argc == 0) {		/* current directory is default */
		apply(combine, associate(1, &dot));
	} else {
		apply(combine, associate(argc, argv));
	}

	/*
	 * we always exit successfully at the moment. (if we get here).
	 */
	exit(0);
}

/*
 * apply the given function to each equivalence class in the given list.
 * this is like "map", but using side-effects.
 */
static void
apply(func, list)
register void (*func)();
register head_t *list;
{
	if (debug) {
		puts("apply");
	}

	while (list != (head_t *) 0) {
		(*func)(list->h_info);
		list = list->h_next;
	}
}

/*
 * associate the given vector of filenames into a list of lists of info_t.
 */
static head_t *
associate(argc, argv)
int argc;
char *argv[];
{
	register int count;		/* loop counter */
	head_t *list = (head_t *) 0;	/* pointer to linked list */

	if (debug) {
		puts("associate");
	}

	for (count = 0; count < argc; count++) {
		if (enter(argv[count], ".", &list) == ISDIR) {
			list = enterdir(argv[count], list);
		}
	}

	return(list);
}

/*
 * given a directory name and a linked list, add the files within the directory
 * to the list. recurse if directories are encountered and "-r" has been given.
 */
static head_t *
enterdir(dirname, list)
char *dirname;
head_t *list;
{
#ifdef	NEWDIR
	register DIR *dirp;		/* open directory pointer */
	register struct direct *dp;	/* pointer to each directory entry */
#else	NEWDIR
	register int fd;		/* descriptor for open directory */
	struct direct dirbuf;		/* structure for each directory entry */
	register struct direct *dp = &dirbuf;	/* pointer to dirbuf */
#endif	NEWDIR

	if (debug) {
		printf("enterdir(%s)\n", dirname);
	}

	/*
	 * open the directory.
	 */
#ifdef	NEWDIR
	if ((dirp = opendir(dirname)) == NULL) {
#else	NEWDIR
	if ((fd = open(dirname, O_RDONLY)) == -1) {
#endif	NEWDIR
		error(1, "cannot open directory %s", dirname);
		return(list);
	}

	/*
	 * search the directory, ignoring only "." and "..".
	 */
#ifdef	NEWDIR
	while ((dp = readdir(dirp)) != NULL) {
#else	NEWDIR
	while (read(fd, (char *) &dirbuf, sizeof(dirbuf)) > 0) {
		if (dirbuf.d_ino == 0)		/* slot not in use */
			continue;
#endif	NEWDIR
		if (strcmp(dp->d_name, ".") == 0
		  || strcmp(dp->d_name, "..") == 0) {
			continue;		/* skip self and parent */
		}

		/*
		 * if we encounter a directory, ignore it, unless
		 * the -r flag has been given.
		 */
		if (enter(dp->d_name, dirname, &list) == ISDIR && recursive) {
			list = enterdir(mkpath(dirname, dp->d_name), list);
		}
	}

	/*
	 * close the directory.
	 */
#ifdef	NEWDIR
	(void) closedir(dirp);
#else	NEWDIR
	(void) close(fd);
#endif	NEWDIR

	return(list);
}

/*
 * enter the file in the given associativity list. a file may be entered in an
 * existing class only if its size, device number and ownership are the same.
 * returns NOTDIR for successfully entered files, ISDIR for directories.
 * side-effects *listp.
 */
static int
enter(filename, directory, listp)
char *filename;
char *directory;
head_t **listp;
{
	head_t head;

	if (debug) {
		printf("enter(%s, %s)\n", filename, directory);
	}

	/*
	 * if the file does not exist, ignore it; if it is a directory,
	 * indicate that it is.
	 */
	switch (newinfo(filename, directory, &head)) {
	case NOFILE:
		return(NOTDIR);
	case ISDIR:
		return(ISDIR);
	}

	*listp = assoc(&head, *listp);

	return(NOTDIR);
}

/*
 * given a reference to a file, and an associativity list, enter the
 * file in an appropriate equivalence class.
 */
static head_t *
assoc(hp, list)
head_t *hp;
head_t *list;
{
	register head_t *hptr;		/* temp header structure */

	if (debug) {
		puts("assoc");
	}

	/*
	 * if list is empty, fill in the first member and return.
	 * all elements are initialised, including h_next, since
	 * this *must* be zero.
	 */
	if (list == (head_t *) 0) {
		hptr = newhead();
		hptr->h_info = hp->h_info;
		hptr->h_size = hp->h_size;
		hptr->h_dev = hp->h_dev;
		hptr->h_uid = hp->h_uid;
		hptr->h_next = (head_t *) 0;
		return(hptr);
	}

	/*
	 * if the file will fit into this class, insert it and return list.
	 */
	if (hp->h_size == list->h_size && hp->h_dev == list->h_dev &&
				(ignore || hp->h_uid == list->h_uid)) {
		if (debug) {
			printf("associating %s with %s\n", list->h_info->i_name,
							hp->h_info->i_name);
		}
		hp->h_info->i_next = list->h_info;
		list->h_info = hp->h_info;
	} else {
		/*
		 * otherwise, recurse.
		 */
		list->h_next = assoc(hp, list->h_next);
	}

	return(list);
}

/*
 * given an equivalence list, combine together all files which are identical.
 *
 * combine [] = undef
 * combine list = tillempty comb2 list
 *                where
 *                tillempty f x = fx, fx = []
 *                              = tillempty f fx
 *                                where
 *                                fx = f x
 *
 * i.e. keep doing comb2 a x until the result is empty.
 */
static void
combine(list)
info_t *list;
{
	if (debug) {
		puts("combine");
	}

	if (list == (info_t *) 0)
		return;

	do {
		list = comb2(list, list->i_next);
	} while (list != (info_t *) 0);
}

/*
 * attempt to combine the file given with each file in the given list.
 *
 * comb2 a [] = []
 * comb2 a (b:x) = comb2 a x, replace a b
 *                 b:(comb2 a x)
 */
static info_t *
comb2(elem, ilist)
register info_t *elem, *ilist;
{
	if (debug) {
		puts("comb2");
	}

	if (ilist == (info_t *) 0) {
		return((info_t *) 0);
	}

	if (replace(elem, ilist)) {
		return(comb2(elem, ilist->i_next));
	} else {
		ilist->i_next = comb2(elem, ilist->i_next);
		return(ilist);
	}
	/*NOTREACHED*/
}

/*
 * given two files, decide if they are identical, and if so, try and replace
 * one with a link to the other. we don't have to worry about ownership at
 * this stage, as this should already have been decided.
 *
 * returns 1 if the files were linked, or are already linked, or cannot be
 * linked due to some problem, and 0 if the files are different.
 *
 * replace a b = TRUE, linked a b	(a and b are already linked)
 *               FALSE, ~ compare a b
 *               TRUE, replace2 a b \/ replace2 b a
 *               TRUE
 */
static int
replace(a, b)
info_t *a, *b;
{
	if (debug) {
		puts("replace");
	}

	/*
	 * if the inode numbers are identical, they are already
	 * linked, so return 1 as if we had linked them.
	 */
	if (a->i_ino == b->i_ino) {
		return(1);
	}

	/*
	 * different contents; return false.
	 */
	if (compare(a->i_name, b->i_name) != 0) {
		return(0);
	}

	/*
	 * if it doesn't work one way, try it the other.
	 */
	if (replace2(a->i_name, b->i_name) == 0) {
		(void) replace2(b->i_name, a->i_name);
	}

	/*
	 * return 1 here - it is irrelevant whether we succeeded or not.
	 */
	return(1);
}

/*
 * this is the nasty bit; we musn't ever lose files here.
 *
 * replace the second filename with a link to the first.
 * returns 0 for failure, 1 for success, -1 for catastrophic
 * failure (i.e. one of the files may have been lost)
 */
static int
replace2(from, to)
char *from, *to;
{
	char newname[1024];		/* save file name */
	time_t clock;			/* time for temp file name */

	if (debug) {
		printf("replace2(%s, %s)\n", from, to);
	}

	/*
	 * if -n has been given, just print commands.
	 */
	if (noexec) {
		printf("link %s to %s\n", to, from);
		return(1);
	}

	/*
	 * before we throw "to" away, relink it to a temporary file.
	 */
	(void) time(&clock);
	(void) sprintf(newname, "%s%4.4x%4.4x", to, getpid()&0xffff,
							  clock&0xffff);

	if (debug) {
		puts("replace2 - creating save file");
	}

	if (rename(to, newname) == -1) {	/* cannot save file */
		if (debug) {
			error(1, "rename('%s', '%s')", to, newname);
		}
		return(0);
	}

	/*
	 * now try and link them together.
	 */
	if (debug) {
		puts("replace2 - linking");
	}

	if (link(from, to) == -1) {
		if (rename(newname, to) == -1) {
			if (debug) {
				error(1, "rename(%s, %s)", newname, to);
			}
			return(0);
		} else {
			error(1, "failed to link %s to %s - copy has been left on %s\n", to, from, newname);
			return(-1);
		}
	}

	/*
	 * this should never fail - we have only just created it.
	 */
	if (unlink(newname) == -1) {
		error(1, "cannot remove temporary file %s", newname);
	}

	/*
	 * only print out what we are doing when we have succeeded.
	 */
	if (verbose) {
		printf("linking %s to %s\n", to, from);
	}

	return(1);
}

/*
 * given a filename and the address of a header structure, fill it in with
 * the size and a pointer to a new info structure, which is filled in with
 * the filename and inode number.
 * if file is a symbolic link, follow it if it is a file, or a directory
 * and the -s flag has been given.
 * returns NOFILE, ISDIR or NOTDIR as appropriate.
 */
static int
newinfo(filename, directory, headerp)
char *filename;
char *directory;
head_t *headerp;
{
	struct stat stbuf;
	register info_t *infop;
	register char *cp;

	if (debug) {
		printf("newinfo(%s, %s)\n", filename, directory);
	}

	cp = mkpath(directory, filename);

	/*
	 * if the file does not exist, ignore it.
	 */
#ifdef	S_IFLNK
	if (lstat(cp, &stbuf) == -1) {
#else	S_IFLNK
	if (stat(cp, &stbuf) == -1) {
#endif	S_IFLNK
		(void) free(cp);
		return(NOFILE);
	}
	
	/*
	 * ignore directories and special files - we can't rationalise them.
	 */
	switch (stbuf.st_mode & S_IFMT) {
#ifdef	S_IFLNK
	case S_IFLNK:
		/*
		 * handle symlinks; first stat what it points to.
		 */
		if (!symbolic) {
			return(NOFILE);
		}

		if (stat(cp, &stbuf) == -1) {
			(void) free(cp);
			return(NOFILE);		/* nothing to point to */
		}

		switch (stbuf.st_mode & S_IFMT) {
		case S_IFDIR:			/* symlink to directory */
			(void) free(cp);
			return(ISDIR);
			/*NOTREACHED*/
		case S_IFREG:			/* symlink to regular file */
			break;
		default:			/* symlink to special file */
			(void) free(cp);
			return(NOFILE);
		}
		break;

#endif	S_IFLNK
	case S_IFDIR:				/* directory */
		(void) free(cp);
		return(ISDIR);

	case S_IFREG:				/* a regular file */
		break;

	default:				/* special file */
		(void) free(cp);
		return(NOFILE);
	}

	/*
	 * allocate memory for the new file info.
	 */
	infop = (info_t *) malloc(sizeof(info_t));
	if (infop == (info_t *) 0) {
		fatal("Out of memory");
	}

	/*
	 * fill in the information. we must zero all un-initialised
	 * elements, since malloc doesn't do this.
	 */
	infop->i_name = cp;
	infop->i_ino = stbuf.st_ino;
	infop->i_next = (info_t *) 0;
	infop->i_dir = (char *) 0;
	headerp->h_size = stbuf.st_size;
	headerp->h_dev = stbuf.st_dev;
	headerp->h_uid = stbuf.st_uid;
	headerp->h_info = infop;

	return(0);
}

/*
 * return a new head structure, uninitialised.
 */
static head_t *
newhead()
{
	register head_t *hp;

	hp = (head_t *) malloc(sizeof(head_t));
	if (hp == (head_t *) 0)
		fatal("Out of memory");

	return(hp);
}

/*
 * compare the given files. returns 0 for identical files, non-zero otherwise.
 * if files are not readable, they are considered to be different.
 */
static int
compare(file1, file2)
char *file1, *file2;
{
	register int fd1, fd2;		/* file descriptors */
	register int n1, n2;		/* count of bytes read */
	register int retval;		/* return value */
	char buf1[BUFSIZ];		/* buffers for comparison */
	char buf2[BUFSIZ];

	fd1 = open(file1, O_RDONLY);
	if (fd1 == -1) {
		return(-1);
	}

	fd2 = open(file2, O_RDONLY);
	if (fd2 == -1) {
		(void) close(fd1);
		return(-1);
	}

	/*
	 * compare the contents of the two files.
	 */
	do {
		n1 = read(fd1, buf1, sizeof(buf1));
		n2 = read(fd2, buf2, sizeof(buf2));
again:
		if (n1 != n2) {
			if (bcmp(buf1, buf2, min(n1, n2)) != 0) {
				retval = 1;
				break;
			}
			if (n2 > n1) {
				n1 = read(fd1, buf1, n2 - n1);
				bcopy(buf2 + n2, buf2, n2 - n1);
			} else {
				n2 = read(fd2, buf2, n1 - n2);
				bcopy(buf1 + n1, buf1, n1 - n2);
			}
			goto again;
		} else {
			if (bcmp(buf1, buf2, n1) != 0) {
				retval = 1;
				break;
			}
		}
		retval = n1 - n2;
	} while (n1 > 0 && n2 > 0);

	/*
	 * don't forget to close them files ...
	 */
	(void) close(fd1);
	(void) close(fd2);

	return(retval);
}

/*
 * given two strings a & b, concatenate them into a unix pathname.
 */
static char *
mkpath(dir, file)
char *dir, *file;
{
	register char *cp;		/* temp char pointer */
	register int opt = 0;		/* special case for a == "." */
	register int size;		/* number of bytes needed */

	/*
	 * if dir is "." or file begins with a slash, just use filename.
	 */
	if (dir == (char *) 0 || dir[0] == '\0'		/* null path */
	  || (dir[0] == '.' && dir[1] == '\0')		/* path is "." */
	  || file[0] == '/') {				/* file is absolute */
		opt = 1;
	}

	/*
	 * malloc enough space for "a/b\0".
	 */
	size = opt ? strlen(file) + 1 : strlen(dir) + strlen(file) + 2;
	cp = malloc((unsigned) size);
	if (cp == NULL) {
		fatal("Out of memory");
	}

	/*
	 * make the string - if opt is set, just use filename.
	 */
	if (opt) {
		(void) strcpy(cp, file);
	} else {
		(void) sprintf(cp, "%s/%s", dir, file);
	}

	return(cp);
}

/*
 * print an error message on stderr, consisting of:
 *
 *	<progname>: <message> [system error message]\n
 *
 * the system error message is only printed if the first argument is non-zero.
 */
/*VARARGS1*/
/*PRINTFLIKE*/
static void
error(syserr, string, a, b, c, d, e)
int syserr;
char *string;
char *a, *b, *c, *d, *e;
{
	register char *s;
	extern int errno;
	extern int sys_nerr;
	extern char *sys_errlist[];

	/*
	 * we must get the system error message first, as fprintf may change it.
	 */
	if (syserr) {
		s = (errno > sys_nerr) ? "Unknown error" : sys_errlist[errno];
	}

	fprintf(stderr, "%s: ", progname);
	fprintf(stderr, string, a, b, c, d, e);

	if (syserr) {
		fprintf(stderr, " [%s]\n", s);
	} else {
		putc('\n', stderr);
	}
}

/*
 * print an error message and die.
 */
/*VARARGS1*/
/*PRINTFLIKE*/
static void
fatal(string, a, b, c, d, e)
char *string;
char *a, *b, *c, *d, *e;
{
	error(1, string, a, b, c, d, e);
	exit(-1);
}

#ifndef	BSD42
/*
 * byte compare - return zero for identical buffers, non-zero otherwise.
 */
int
bcmp(c1, c2, n)
register char *c1, *c2;
register int n;
{
	while (n > 0 && *c1++ == *c2++)
		--n;
	return(n);
}

/*
 * byte copy - copies count bytes from from to to.
 */
int
bcopy(from, to, count)
register char *from, *to;
register int count;
{
	if (to < from) {
		while (count-- > 0) {
			*to++ = *from++;
		}
	} else {
		to += count;
		from += count;
		while (count-- > 0) {
			*--to = *--from;
		}
	}
}

/*
 * rename file "from" to "to".
 */
int
rename(from, to)
char *from, *to;
{
	if (link(from, to) == -1) {
		return(-1);
	}
	return(unlink(from));
}
#endif	BSD42
