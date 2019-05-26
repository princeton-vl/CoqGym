/*++
 * NAME
 *	htimeout
 * SUMMARY
 *	run command with bounded time
 * SYNOPSIS
 *	htimeout [-signal] time command ...
 * DESCRIPTION
 *	htimeout executes a command and imposes an elapsed time limit.
 *	The command is run in a separate POSIX process group so that the
 *	right thing happens with commands that spawn child processes.
 *
 *	Arguments:
 * -signal
 *	Specify an optional signal to send to the controlled process.
 *	By default, htimeout sends SIGKILL, which cannot be caught
 *	or ignored.
 * time
 *	The elapsed time limit after which the command is terminated.
 * command
 *	The command to be executed.
 * DIAGNOSTICS
 *	The command exit status is the exit status of the command
 *	(status 1 in case of a usage error).
 * AUTHOR(S)
 *	Wietse Venema, modified by Lukasz Czajka
 *	This program is part of SATAN.
 *--*/

/* System libraries. */

#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>

/* Application-specific. */

#define perrorexit(s) { perror(s); exit(1); }

static void usage(const char* progname)
{
	fprintf(stderr, "usage: %s [-signal] time command...\n", progname);
	exit(1);
}

static void terminate(int sig)
{
	signal(SIGKILL, SIG_DFL);
	kill(0, SIGKILL);
}

int main(int argc, char *argv[])
{
	int     time_to_run = 0;
	pid_t   pid;
	pid_t   child_pid;
	int     status;

	if (argc < 3 || (time_to_run = atoi(argv[1])) <= 0)
		usage(argv[0]);

	/*
	 * Run the command and its watchdog in a separate process group so that
	 * both can be killed off with one signal.
	 */
	setsid();
	switch (child_pid = fork()) {
		case -1:					/* error */
			perrorexit("timeout: fork");
		case 00:					/* run controlled command */
			execvp(argv[2], argv + 2);
			perrorexit(argv[2]);
		default:					/* become watchdog */
			(void) signal(SIGHUP, terminate);
			(void) signal(SIGINT, terminate);
			(void) signal(SIGQUIT, terminate);
			(void) signal(SIGTERM, terminate);
			(void) signal(SIGALRM, terminate);
			alarm(time_to_run);
			while ((pid = wait(&status)) != -1 && pid != child_pid)
	    		/* void */ ;
                        if (pid == child_pid && WIFEXITED(status)) {
                            return WEXITSTATUS(status);
                        } else {
                            return 1;
                        }
	}
	return 0;
}
