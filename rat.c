#ifndef lint
static char *sccsid = "@(#)rat.c	1.8 (C.M.Downey) %G%";
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

	Note that allocated space is never freed; this is unnecessary, since
	by the time we have started using it, we will never need any more.

* switches:
	-v	verbose; print names of files rationalised.
	-n	don't do any linking; just print names.
	-r	recurse down through directories. (careful here)
	-s	follow symbolic links. (not on pre-4.2) (very careful here)
	-u	ignore ownership of files.
* libraries used:
	standard
* environments:
	Berkeley VAX 4.2BSD VMUNIX.
	Berkeley Orion 4.1BSD VMUNIX.
* history:
	Chris Downey UKC August 1985

***/

#include <stdio.h>
#include <sys/types.h>			/* for off_t etc. */
#include <sys/stat.h>			/* for file sizes etc. */
#include <sys/file.h>			/* for opening files */
#include <errno.h>			/* for error messages */

/*
 * Define NEWDIR if we have the new (4.2-style) directory-handling stuff.
 * otherwise, undefine NEWDIR so that the function enterdir() will use
 * the original unix directory structure.
 *
 * SunOS 3.5 apparently defines DIRSIZ instead of DIRBLKSIZ, so we
 * test for either of these to see if we have the new dir stuff.
 */
#include <sys/dir.h>

#if	defined(DIRBLKSIZ) || defined(DIRSIZ)
#	define	NEWDIR
#else	DIRBLKSIZ
#	undef	NEWDIR
#endif	DIRBLKSIZ


/*
 * If O_RDONLY isn't defined, we assume this is a pre-4.2 system.
 * we will therefore need our own bcmp() and rename() library functions.
 */
#ifndef	O_RDONLY
#	define	O_RDONLY	0
#	define	BCMP
#	define	RENAME
#else	O_RDONLY
#	undef	BCMP
#	undef	RENAME
#endif	O_RDONLY


/*
 * Symbolic link handling is only available if there are any to handle.
 */
#ifdef	S_IFLNK
#	define	USAGE	"usage: rat [-vnrsu] files\n"
#else	S_IFLNK
#	define	USAGE	"usage: rat [-vnru] files\n"
#endif	S_IFLNK


#define ISDIR	1			/* miscellaneous return values */
#define NOTDIR	0
#define NOFILE	-1

#define	min(a, b)	((a) < (b) ? (a) : (b))


/*
 * Each file is described by the following structure, which is
 * a member of a linked list pointed to by a "Head" structure.
 */
typedef struct info {
	struct info	*i_next;	/* pointer to next object */
	char		*i_name;	/* pointer to file name */
	char		*i_dir;		/* pointer to directory */
	ino_t		i_ino;		/* inode number */
} Info;

/*
 * Head describes a list of associated files, pointed to by h_info,
 * together with common information.
 */
typedef struct header {
	struct header	*h_next;	/* pointer to next object */
	Info		*h_info;	/* pointer to list of files */
	off_t		h_size;		/* size of files */
	dev_t		h_dev;		/* device number */
	int		h_uid;		/* ownership */
} Head;

/*
 * Internal function declarations.
 */
static	Head	*associate();
static	Head	*assoc();
static	int	enter();
static	int	newinfo();
static	Head	*enterdir();
static	Head	*newhead();

static	void	combine();
static	Info	*comb2();
static	int	compare();
static	int	replace();
static	int	replace2();

static	void	raisepriority();
static	void	lowerpriority();

static	char	*mkpath();
static	void	error();
static	void	fatal();

/*
 * Library function declarations.
 */
extern	char	*malloc();
extern	char	*strcpy();

/*
 * Name of program, for printing error messages.
 */
char	*progname;

/*
 * Stuff for raising and lowering priority.
 */
#define	PRIORITY	-5		/* how much to raise priority by */

static	int	niceness = 0;		/* current priority */
static	int	our_uid = -1;		/* our user id */

/*
 * Global option variables.
 */
static	int	verbose = 0;		/* print names of files rationalised */
static	int	noexec = 0;		/* don't actually do anything */
static	int	recursive = 0;		/* recurse down through directories */
static	int	ignore = 0;		/* ignore ownership of files */
static	int	debug = 0;		/* debugging level */

#ifdef	S_IFLNK
static	int	symbolic = 0;		/* follow symlinks to directories */
#endif	S_IFLNK

/*
 * Default directory if no files given.
 */
static	char	*dot = ".";

main(argc, argv)
int argc;
char *argv[];
{
	register Head *list;

	progname = argv[0];

	/*
	 * parse option flags.
	 */
	for (argv++, argc--; argv[0][0] == '-'; argv++, argc--) {
		register int i;

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
	 * Read all the files into an associativity list, and then
	 * apply "combine" to each equivalence class in turn.
	 * Current directory is default.
	 */
	if (argc == 0) {
		list = associate(1, &dot);
	} else {
		list = associate(argc, argv);
	}
	while (list != NULL) {
		combine(list->h_info);
		list = list->h_next;
	}

	/*
	 * We always exit successfully at the moment. (if we get here).
	 */
	exit(0);
}

/*
 * Associate the given vector of filenames into a list of lists of Info.
 * Return the list.
 */
static Head *
associate(argc, argv)
int argc;
char *argv[];
{
	register int count;		/* loop counter */
	Head *list = NULL;		/* pointer to linked list */

	if (debug) {
		puts("associate");
	}

	for (count = 0; count < argc; count++) {
		/*
		 * If we encounter a directory,
		 * call enterdir to handle it.
		 */
		if (enter(argv[count], ".", &list) == ISDIR) {
			list = enterdir(argv[count], list);
		}
	}

	return(list);
}

/*
 * Given a directory name and a linked list, add the files
 * within the directory to the list, and return the new list.
 * Recurse if directories are encountered and "-r" has been given.
 */
static Head *
enterdir(dirname, list)
char *dirname;
Head *list;
{
#ifdef	NEWDIR
	register DIR *dirp;		/* open directory pointer */
	register struct direct *dp;	/* pointer to each directory entry */
#else	NEWDIR
	register FILE *dirp;		/* descriptor for open directory */
	struct direct dirbuf;		/* structure for each directory entry */
	register struct direct *dp = &dirbuf;	/* pointer to dirbuf */
#endif	NEWDIR

	if (debug) {
		printf("enterdir(%s)\n", dirname);
	}

	/*
	 * Open the directory.
	 */
#ifdef	NEWDIR
	dirp = opendir(dirname);
#else	NEWDIR
	dirp = fopen(dirname, "r");
#endif	NEWDIR
	if (dirp == NULL) {
		error(1, "cannot open directory %s", dirname);
		return(list);
	}

	/*
	 * Search the directory, ignoring only "." and "..".
	 */
#ifdef	NEWDIR
	while ((dp = readdir(dirp)) != NULL) {
#else	NEWDIR
	while (fread((char *) &dirbuf, sizeof(dirbuf), 1, dirp) == 1) {
		if (dirbuf.d_ino == 0)		/* slot not in use */
			continue;
#endif	NEWDIR
		if (strcmp(dp->d_name, ".") == 0
		  || strcmp(dp->d_name, "..") == 0) {
			continue;		/* skip self and parent */
		}

		/*
		 * If we encounter a directory, ignore it,
		 * unless the -r flag has been given.
		 */
		if (enter(dp->d_name, dirname, &list) == ISDIR && recursive) {
			list = enterdir(mkpath(dirname, dp->d_name), list);
		}
	}

	/*
	 * Close the directory.
	 */
#ifdef	NEWDIR
	(void) closedir(dirp);
#else	NEWDIR
	(void) fclose(dirp);
#endif	NEWDIR

	return(list);
}

/*
 * Enter the file in the given associativity list.
 * A file may be entered in an existing class only
 * if its size, device number and ownership are the same.
 * Returns ISDIR if a directory is encountered,
 * and NOTDIR for successfully entered files.
 * Side-effects *listp.	(NASTY).
 */
static int
enter(filename, directory, listp)
char *filename;
char *directory;
Head **listp;
{
	Head head;

	if (debug) {
		printf("enter(%s, %s)\n", filename, directory);
	}

	/*
	 * If the file does not exist, ignore it; if it is a directory,
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
 * Given a reference to a file, and an associativity list,
 * enter the file in an appropriate equivalence class.
 *
 * We have to return the list we are given, in case it is
 * empty to start with and we create a new element.
 */
static Head *
assoc(hp, list)
Head *hp;				/* file to be entered */
Head *list;				/* list to put it in */
{
	register Head *listp;		/* current list element */
	register Head *hptr;		/* temp header structure */

	if (debug) {
		puts("assoc");
	}

	for (listp = list; listp != NULL; listp = listp->h_next) {
		/*
		 * If the file will fit into this class,
		 * insert it and return list.
		 */
		if (hp->h_size == listp->h_size &&
		     hp->h_dev == listp->h_dev &&
		    (ignore || hp->h_uid == listp->h_uid)) {

			if (debug) {
				printf("associating %s with %s\n",
							listp->h_info->i_name,
							hp->h_info->i_name);
			}

			hp->h_info->i_next = listp->h_info;
			listp->h_info = hp->h_info;
			return(list);
		}
	}

	/*
	 * If we have not found an appropriate class into which
	 * this file may be inserted, push a new element on to
	 * the head of the list.
	 */
	hptr = newhead();
	hptr->h_info = hp->h_info;
	hptr->h_size = hp->h_size;
	hptr->h_dev = hp->h_dev;
	hptr->h_uid = hp->h_uid;
	hptr->h_next = list;
	return(hptr);
}

/*
 * Given an equivalence list,
 * combine together all files which are identical.
 */
static void
combine(list)
register Info *list;
{
	if (debug) {
		puts("combine");
	}

	while (list != NULL && list->i_next != NULL) {
		list = comb2(list, list->i_next);
	}
}

/*
 * Attempt to combine the file given with each file in the given list.
 *
 * comb2 a [] = []
 * comb2 a (b:x) = comb2 a x, replace a b
 *                 b:(comb2 a x)
 */
static Info *
comb2(elem, ilist)
register Info *elem;
register Info *ilist;
{
	if (ilist == NULL)
		return(NULL);

	if (debug) {
		printf("comb2 \"%s\" \"%s\"\n", elem->i_name, ilist->i_name);
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
 * Given two files, decide if they are identical,
 * and if so, try and replace one with a link to the other.
 * we don't have to worry about ownership at this stage,
 * as this should already have been decided.
 *
 * Returns 1 if the files were linked, or are
 * already linked, or cannot be linked due to
 * a problem, and 0 if the files are different.
 *
 * replace a b = TRUE, linked a b	(a and b are already linked)
 *               FALSE, ~ compare a b
 *               TRUE, replace2 a b \/ replace2 b a	(side-effect)
 *               TRUE
 */
static int
replace(a, b)
register Info *a;
register Info *b;
{
	if (debug) {
		puts("replace");
	}

	/*
	 * If the inode numbers are identical, they are already
	 * linked, so return 1 as if we had linked them.
	 * The device numbers must be the same to get this far.
	 */
	if (a->i_ino == b->i_ino) {
		return(1);
	}

	/*
	 * Different contents; return false.
	 */
	if (compare(a->i_name, b->i_name) != 0) {
		return(0);
	}

	/*
	 * If it doesn't work one way, try it the other.
	 */
	if (replace2(a->i_name, b->i_name) == 0) {
		(void) replace2(b->i_name, a->i_name);
	}

	/*
	 * Return 1 here - it is irrelevant whether we succeeded or not.
	 */
	return(1);
}

/*
 * This is the nasty bit; we musn't ever lose files here.
 *
 * Replace the second filename with a link to the first.
 * Returns 0 for failure, 1 for success, -1 for catastrophic
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
	 * If -n has been given, just print commands.
	 */
	if (noexec) {
		printf("link %s to %s\n", to, from);
		return(1);
	}

	/*
	 * Before we throw "to" away, relink it to a temporary file.
	 */
	(void) time(&clock);
	(void) sprintf(newname, "%s%4.4x%4.4x", to, getpid()&0xffff,
							  clock&0xffff);

	if (debug) {
		puts("replace2 - creating save file");
	}

	/*
	 * Set priority high so that anyone trying to access the files
	 * will be less likely to notice their disappearance.
	 * We must be careful to lower it again afterwards.
	 */
	raisepriority();

	if (rename(to, newname) == -1) {	/* cannot save file */
		if (debug) {
			error(1, "rename('%s', '%s')", to, newname);
		}
		lowerpriority();
		return(0);
	}

	/*
	 * Now try and link them together.
	 */
	if (debug) {
		puts("replace2 - linking");
	}

	if (link(from, to) == -1) {
		if (rename(newname, to) == -1) {
			if (debug) {
				error(1, "rename(%s, %s)", newname, to);
			}
			lowerpriority();
			return(0);
		} else {
			error(1, "failed to link %s to %s - copy has been left on %s\n", to, from, newname);
			lowerpriority();
			return(-1);
		}
	}

	/*
	 * Don't forget to lower the priority again.
	 */
	lowerpriority();

	/*
	 * This should never fail - we have only just created it.
	 */
	if (unlink(newname) == -1) {
		error(1, "cannot remove temporary file %s", newname);
	}

	/*
	 * Only print out what we are doing when we have succeeded.
	 */
	if (verbose) {
		printf("linking %s to %s\n", to, from);
	}

	return(1);
}

/*
 * Given a filename and the address of a header structure, fill it in with
 * the size and a pointer to a new info structure, which is filled in with
 * the filename and inode number.
 * If file is a symbolic link, only follow it if it is a file,
 * or if it is a directory and the -s flag has been given.
 * Returns NOFILE, ISDIR or NOTDIR as appropriate.
 */
static int
newinfo(filename, directory, headerp)
register char *filename;
register char *directory;
register Head *headerp;
{
	struct stat stbuf;
	register Info *infop;
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
	infop = (Info *) malloc(sizeof(Info));
	if (infop == NULL) {
		fatal("Out of memory");
	}

	/*
	 * fill in the information. we must zero all un-initialised
	 * elements, since malloc doesn't do this.
	 */
	infop->i_name = cp;
	infop->i_ino = stbuf.st_ino;
	infop->i_next = NULL;
	infop->i_dir = NULL;

	headerp->h_size = stbuf.st_size;
	headerp->h_dev = stbuf.st_dev;
	headerp->h_uid = stbuf.st_uid;
	headerp->h_info = infop;

	return(0);
}

/*
 * return a new head structure, uninitialised.
 */
static Head *
newhead()
{
	register Head *hp;

	hp = (Head *) malloc(sizeof(Head));
	if (hp == NULL)
		fatal("Out of memory");

	return(hp);
}

/*
 * compare the given files. returns 0 for identical files, and 1 if they are
 * different. if files are not readable, they are considered to be different,
 * and -1 is returned.
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
	retval = 0;		/* files initially considered identical */
	do {
		n1 = read(fd1, buf1, sizeof(buf1));
		n2 = read(fd2, buf2, sizeof(buf2));
		if (n1 != n2) {
			/*
			 * files are different sizes.
			 */
			retval = 1;
			break;
		} else {
			if (bcmp(buf1, buf2, n1) != 0) {
				retval = 1;
				break;
			}
		}
	} while (n1 > 0 && n2 > 0);

	/*
	 * don't forget to close them files ...
	 */
	(void) close(fd1);
	(void) close(fd2);

	return(retval);
}

/*
 * raise process priority for critical code.
 * note that if we are already running at a high priority,
 * this may slow us down slightly between critical sections.
 */
static void
raisepriority()
{
	if (our_uid == -1) {
		our_uid = geteuid();
	}
	if (our_uid == 0) {
		(void) nice(PRIORITY);
		niceness += PRIORITY;
	}
}

/*
 * put the priority back where it was.
 */
static void
lowerpriority()
{
	if (our_uid == 0) {
		nice(-niceness);
		niceness = 0;
	}
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
	if (dir == NULL || dir[0] == '\0'		/* null path */
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

#ifdef	BCMP
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
#endif	BCMP

/*
 * rename file "from" to "to".
 */
#ifdef	RENAME
int
rename(from, to)
char *from, *to;
{
	if (link(from, to) == -1) {
		return(-1);
	}
	return(unlink(from));
}
#endif	RENAME
