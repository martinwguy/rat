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

	If either of the files to link together already has multiple links,
	we delete the one with the lower link count and keep the one with
	more links.

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
	-g	ignore group ownership of files.
	-p	ignore permissions of files.
	-z	Don't link zero-length files together.
	-f file	specify file containing filenames to rationalize; '-' means stdin
* libraries used:
	standard
* environments:
	(Berkeley VAX 4.2BSD VMUNIX)
	(Berkeley Orion 4.1BSD VMUNIX)
	Sun Solaris 5.5.1
* history:
	Chris Downey UKC August 1985
	Solaris port cmd Pfizer CR Sandwich 1/5/98

***/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>			/* for off_t etc. */
#include <unistd.h>			/* for uid_t etc. */
#include <sys/stat.h>			/* for file sizes etc. */
#include <sys/file.h>			/* for opening files */
#include <fcntl.h>			/* for opening files */
#include <errno.h>			/* for error messages */
#include <stdarg.h>
#include <time.h>			/* for time() */

/*
 * This code ported to POSIX from ancient BSD-style cmd Pfizer Sandwich 1/5/98.
 */
#include <dirent.h>

/*
 * Symbolic link handling is only available if there are any to handle.
 */
#define	USAGE	"usage: rat [-vnrsugpz] [ file ... | -f listfile ]\n"


#define ISDIR		1		/* miscellaneous return values */
#define NOTDIR		0
#define NOSUCHFILE	-1

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
	uid_t		h_uid;		/* ownership */
	gid_t		h_gid;		/* group ownership */
	uid_t		h_perms;	/* permissions */
} Head;

/*
 * Internal function declarations.
 */
static	Head	*associate(int, char **);
static	Head	*assocfromfile(char *);
static	Head	*enterdir(char *, Head *);
static	int	enter(char *, char *, Head **);
static	Head	*assoc(Head *, Head *);
static	int	newinfo(char *, char *, Head *);
static	Head	*newhead(void);

static	void	combine(Info *);
static	Info	*comb2(Info *, Info *);
static	int	compare(char *, char *);
static	int	replace(Info *, Info *);
static	int	replace2(char *, char *);

static	void	raisepriority(void);
static	void	lowerpriority(void);

static	char	*mkpath(char *, char *);
static	void	error(int, char *, ...);
static	void	verror(int, char *, va_list);
static	void	fatal(char *, ...);

/*
 * Name of program, for printing error messages.
 */
static	char	*progname;

/*
 * Stuff for raising and lowering priority.
 */
#define	PRIORITY	-5		/* how much to raise priority by */

static	int	niceness = 0;		/* current priority */
static	uid_t	our_uid = -1;		/* our user id */

/*
 * Global option variables.
 */
static	int	verbose = 0;		/* print names of files rationalised */
static	int	noexec = 0;		/* don't actually do anything */
static	int	recursive = 0;		/* recurse down through directories */
static	int	ignore_uid = 0;		/* ignore ownership of files */
static	int	ignore_gid = 0;		/* ignore group ownership of files */
static	int	ignore_perms = 0;	/* ignore permissions of files */
static	int	ignore_empty = 0;	/* ignore empty files */
static	int	debug = 0;		/* debugging level */

static	int	symbolic = 0;		/* follow symlinks to directories */

/*
 * Default directory if no files given.
 */
static	char	*dot = ".";

int
main(int argc, char *argv[])
{
    Head	*list;
    int		count;
    char	*inputfile = NULL;

    progname = argv[0];

    /*
     * parse option flags.
     */
    for (count = 1; count < argc && argv[count][0] == '-'; count++) {
	int i;

	for (i = 1; argv[count][i] != '\0'; i++) {
	    switch (argv[count][i]) {
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

	    case 's':		/* follow symlinks */
		symbolic = 1;
		break;

	    case 'u':		/* ignore ownership info */
		ignore_uid = 1;
		break;

	    case 'g':		/* ignore group ownership info */
		ignore_gid = 1;
		break;

	    case 'p':		/* ignore permissions info */
		ignore_perms = 1;
		break;

	    case 'z':		/* ignore empty files */
		ignore_empty = 1;
		break;

	    case 'f':		/* read list of filenames from file */
		if (count + 1 < argc) {
		    inputfile = argv[count + 1];
		} else {
		    (void) fputs(USAGE, stderr);
		}
		break;

	    case 'd':		/* debug - undocumented */
		debug = 1;
		break;

	    default:
		(void) fputs(USAGE, stderr);
		exit(1);
	    }
	}
    }

    /*
     * Read all the files into an associativity list, and then
     * apply "combine" to each equivalence class in turn.
     * Current directory is default.
     */
    if (inputfile != NULL) {
        list = assocfromfile(inputfile);
    } else if (count == argc) {
	list = associate(1, &dot);
    } else {
	list = associate(argc - count, argv + count);
    }

    while (list != NULL) {
	combine(list->h_info);
	list = list->h_next;
    }

    /*
     * We always exit successfully at the moment. (if we get here).
     */
    return(0);
}

/*
 * Associate the given vector of filenames into a list of lists of Info.
 * Return the list.
 */
static Head *
associate(int argc, char *argv[])
{
    register int count;		/* loop counter */
    Head *list = NULL;		/* pointer to linked list */

    if (debug) {
	(void) puts("associate");
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
 * Associate all files listed within the given filename into
 * a list of lists of Info. Return the list.
 */
static Head *
assocfromfile(char *filename)
{
    FILE	*infile;
    Head	*list = NULL;		/* pointer to linked list */
    char	buf[256];
    int		lineno;

    if (debug) {
	(void) printf("assocfromfile(%s)", filename);
    }

    if (strcmp(filename, "-") == 0) {
        infile = stdin;
    } else {
	infile = fopen(filename, "r");
	if (infile == NULL) {
	    fatal("Cannot open \"%s\"", filename);
	}
    }

    lineno = 1;
    while (fgets(buf, sizeof(buf), infile) != NULL) {

	char	*s;

	s = strchr(buf, '\n');
	if (s != NULL) {
	    *s = '\0';
	} else {
	    fatal("Line %d too long in \"%s\"", lineno, filename);
	}
	lineno++;

	/*
	 * If we encounter a directory,
	 * call enterdir to handle it.
	 */
	if (enter(buf, ".", &list) == ISDIR) {
	    list = enterdir(buf, list);
	}
    }

    (void) fclose(infile);

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
	DIR *dirp;		/* open directory pointer */
	struct dirent *dp;	/* pointer to each directory entry */

	if (debug) {
		(void) printf("enterdir(%s)\n", dirname);
	}

	/*
	 * Open the directory.
	 */
	dirp = opendir(dirname);
	if (dirp == NULL) {
		error(1, "cannot open directory %s", dirname);
		return(list);
	}

	/*
	 * Search the directory, ignoring only "." and "..".
	 */
	while ((dp = readdir(dirp)) != NULL) {
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
	(void) closedir(dirp);

	return(list);
}

/*
 * Enter the file in the given associativity list.
 * A file may be entered in an existing class only
 * if its size, device number, ownership and permissions are the same.
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
		(void) printf("enter(%s, %s)\n", filename, directory);
	}

	/*
	 * If the file does not exist, ignore it; if it is a directory,
	 * indicate that it is.
	 */
	switch (newinfo(filename, directory, &head)) {
	case NOSUCHFILE:
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
		(void) puts("assoc");
	}

	for (listp = list; listp != NULL; listp = listp->h_next) {
		/*
		 * If the file will fit into this class,
		 * insert it and return list.
		 */
		if (hp->h_size == listp->h_size &&
		     hp->h_dev == listp->h_dev &&
		    (ignore_uid || hp->h_uid == listp->h_uid) &&
		    (ignore_gid || hp->h_gid == listp->h_gid) &&
		    (ignore_perms || hp->h_perms == listp->h_perms)) {

			if (debug) {
				(void) printf("associating %s with %s\n",
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
	hptr->h_gid = hp->h_gid;
	hptr->h_perms = hp->h_perms;
	hptr->h_next = list;
	return(hptr);
}

/*
 * Given an equivalence list,
 * combine together all files which are identical.
 */
static void
combine(list)
Info *list;
{
	if (debug) {
		(void) puts("combine");
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
Info *elem;
Info *ilist;
{
	if (ilist == NULL)
		return(NULL);

	if (debug) {
		(void) printf("comb2 \"%s\" \"%s\"\n", elem->i_name, ilist->i_name);
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
Info *a;
Info *b;
{
	struct stat stbuf_a, stbuf_b;

	if (debug) {
		(void) puts("replace");
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
	 * Delete and replace the file with the lower link count.
	 */
	if (lstat(a->i_name, &stbuf_a) == -1) {
		fprintf(stderr, "Cannot restat %s\n", a->i_name);
		return(0);
	}
	if (lstat(b->i_name, &stbuf_b) == -1) {
		fprintf(stderr, "Cannot restat %s\n", b->i_name);
		return(0);
	}
	if (stbuf_b.st_nlink <= stbuf_a.st_nlink) {
		replace2(a->i_name, b->i_name);
	} else {
		replace2(b->i_name, a->i_name);
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
		(void) printf("replace2(%s, %s)\n", from, to);
	}

	/*
	 * If -n has been given, just print commands.
	 */
	if (noexec) {
		(void) printf("link %s to %s\n", to, from);
		return(1);
	}

	/*
	 * Before we throw "to" away, relink it to a temporary file.
	 */
	(void) time(&clock);
	(void) sprintf(newname, "%s%4.4x%4.4x", to,
						(unsigned) (getpid() & 0xffff),
						(unsigned) clock & 0xffff);

	if (debug) {
		(void) puts("replace2 - creating save file");
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
		(void) puts("replace2 - linking");
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
		(void) printf("linking %s to %s\n", to, from);
	}

	return(1);
}

/*
 * Given a filename and the address of a header structure, fill it in with
 * the size and a pointer to a new info structure, which is filled in with
 * the filename and inode number.
 * If file is a symbolic link, only follow it if it is a file,
 * or if it is a directory and the -s flag has been given.
 * Returns NOSUCHFILE, ISDIR or NOTDIR as appropriate.
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
		(void) printf("newinfo(%s, %s)\n", filename, directory);
	}

	cp = mkpath(directory, filename);

	/*
	 * if the file does not exist, ignore it.
	 */
	if (lstat(cp, &stbuf) == -1) {
		free(cp);
		return(NOSUCHFILE);
	}
	
	/*
	 * ignore directories and special files - we can't rationalise them.
	 */
	switch (stbuf.st_mode & S_IFMT) {
	case S_IFLNK:
		/*
		 * handle symlinks; first stat what it points to.
		 */
		if (!symbolic) {
			return(NOSUCHFILE);
		}

		if (stat(cp, &stbuf) == -1) {
			free(cp);
			return(NOSUCHFILE);		/* nothing to point to */
		}

		switch (stbuf.st_mode & S_IFMT) {
		case S_IFDIR:			/* symlink to directory */
			free(cp);
			return(ISDIR);
			/*NOTREACHED*/
		case S_IFREG:			/* symlink to regular file */
			break;
		default:			/* symlink to special file */
			free(cp);
			return(NOSUCHFILE);
		}
		break;

	case S_IFDIR:				/* directory */
		free(cp);
		return(ISDIR);

	case S_IFREG:				/* a regular file */
		break;

	default:				/* special file */
		free(cp);
		return(NOSUCHFILE);
	}

	/*
	 * ignore empty files, if that's what they asked for
	 */
	if (ignore_empty && stbuf.st_size == 0) {
		free(cp);
		return(NOSUCHFILE);
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
	headerp->h_gid = stbuf.st_gid;
	headerp->h_perms = stbuf.st_mode & ALLPERMS;
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
			if (memcmp(buf1, buf2, n1) != 0) {
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
		(void) nice(-niceness);
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
	register unsigned size;		/* number of bytes needed */

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
static void
error(int syserr, char *str, ...)
{
	va_list ap;

	va_start(ap, str);
	verror(syserr, str, ap);
	va_end(ap);
}

/*
 * print an error message on stderr, consisting of:
 *
 *	<progname>: <message> [system error message]\n
 *
 * the system error message is only printed if the first argument is non-zero.
 */
static void
verror(int syserr, char *string, va_list ap)
{
	char	errstr[64];

	/*
	 * Get the error string first, in case it gets changed by fprintf().
	 */
	(void) strncpy(errstr, strerror(errno), sizeof(errstr));

	(void) fprintf(stderr, "%s: ", progname);
	(void) vfprintf(stderr, string, ap);

	if (syserr) {
		(void) fprintf(stderr, " [%s]", errstr);
	}
	(void) putc('\n', stderr);
}

/*
 * print an error message and die.
 */
static void
fatal(char *string, ...)
{
	va_list	ap;

	va_start(ap, string);
	verror(1, string, ap);
	va_end(ap);

	exit(1);
}
