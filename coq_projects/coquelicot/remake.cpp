/**
@mainpage Remake, a build system that bridges the gap between make and redo.

As with <b>make</b>, <b>remake</b> uses a centralized rule file, which is
named <b>Remakefile</b>. It contains rules with a <em>make</em>-like
syntax:

@verbatim
target1 target2 ... : prerequisite1 prerequisite2 ...
	shell script
	that builds
	the targets
@endverbatim

A target is known to be up-to-date if all its prerequisites are. If it
has no known prerequisites yet the file already exits, it is assumed to
be up-to-date. Obsolete targets are rebuilt thanks to the shell script
provided by the rule.

As with <b>redo</b>, <b>remake</b> supports dynamic dependencies in
addition to these static dependencies. Whenever a script executes
<tt>remake prerequisite4 prerequisite5 ...</tt>, these prerequisites are
rebuilt if they are obsolete. (So <b>remake</b> acts like
<b>redo-ifchange</b>.) Moreover, all the dependencies are stored in file
<b>.remake</b> so that they are remembered in subsequent runs. Note that
dynamic dependencies from previous runs are only used to decide whether a
target is obsolete; they are not automatically rebuilt when they are
obsolete yet a target depends on them. They will only be rebuilt once the
dynamic call to <b>remake</b> is executed.

In other words, the following two rules have almost the same behavior.

@verbatim
target1 target2 ... : prerequisite1 prerequisite2 ...
	shell script

target1 target2 ... :
	remake prerequisite1 prerequisite2 ...
	shell script
@endverbatim

(There is a difference if the targets already exist, have never been
built before, and the prerequisites are either younger or obsolete, since
the targets will not be rebuilt in the second case.)

The above usage of dynamic dependencies is hardly useful. Their strength
lies in the fact that they can be computed on the fly:

@verbatim
%.o : %.c
	gcc -MMD -MF $@.d -o $@ -c $<
	remake -r < $@.d
	rm $@.d

%.cmo : %.ml
	ocamldep $< | remake -r $@
	ocamlc -c $<

after.xml: before.xml rules.xsl
	xsltproc --load-trace -o after.xml rules.xsl before.xml 2> deps
	remake `sed -n -e "\\,//,! s,^.*URL=\"\\([^\"]*\\).*\$,\\1,p" deps`
	rm deps
@endverbatim

Note that the first rule fails if any of the header files included by
a C source file has to be automatically generated. In that case, one
should perform a first call to <b>remake</b> them before calling the
compiler. (Dependencies from several calls to <b>remake</b> are
cumulative, so they will all be remembered the next time.)

\section sec-usage Usage

Usage: <tt>remake <i>options</i> <i>targets</i></tt>

Options:

- <tt>-B</tt>, <tt>--always-make</tt>: Unconditionally make all targets.
- <tt>-d</tt>: Echo script commands.
- <tt>-f FILE</tt>: Read <tt>FILE</tt> as <b>Remakefile</b>.
- <tt>-j[N]</tt>, <tt>--jobs=[N]</tt>: Allow <tt>N</tt> jobs at once;
  infinite jobs with no argument.
- <tt>-k</tt>, <tt>--keep-going</tt>: Keep going when some targets cannot be made.
- <tt>-r</tt>: Look up targets from the dependencies on standard input.
- <tt>-s</tt>, <tt>--silent</tt>, <tt>--quiet</tt>: Do not echo targets.

\section sec-syntax Syntax

Lines starting with a space character or a tabulation are assumed to be rule
scripts. They are only allowed after a rule header.

Lines starting with <tt>#</tt> are considered to be comments and are ignored.
They do interrupt rule scripts though.

Any other line is either a variable definition or a rule header. If such a
line ends with a backslash, the following line break is ignored and the line
extends to the next one.

Variable definitions are a single name followed by equal followed by a list
of names, possibly empty.

Rule headers are a nonempty list of names, followed by a colon, followed by
another list of names, possibly empty. Basically, the syntax of a rule is as
follows:

@verbatim
targets : prerequisites
	shell script
@endverbatim

List of names are space-separated sequences of names. If a name contains a
space character, it should be put into double quotes. Names can not be any
of the following special characters <tt>:$(),="</tt>. Again, quotation
should be used. Quotation marks can be escaped by a backslash inside
quoted names.

\subsection sec-variables Variables

Variables can be used to factor lists of targets or prerequisites. They are
expanded as they are encountered during <b>Remakefile</b> parsing.

@verbatim
VAR2 = a
VAR1 = c d
VAR2 += $(VAR1) b
$(VAR2) e :
@endverbatim

Variable assignments can appear instead of prerequisites inside non-generic
rules with no script. They are then expanded inside the corresponding
generic rule.

@verbatim
foo.o: CFLAGS += -DBAR

%.o : %.c
	gcc $(CFLAGS) -MMD -MF $@.d -o $@ -c $<
	remake -r < $@.d
	rm $@.d
@endverbatim

Note: contrarily to <b>make</b>, variable names have to be enclosed in
parentheses. For instance, <tt>$y</tt> is not a shorthand for <tt>\$(y)</tt> and
is left unexpanded.

\subsection sec-autovars Automatic variables

The following special symbols can appear inside scripts:

- <tt>$&lt;</tt> expands to the first static prerequisite of the rule.
- <tt>$^</tt> expands to all the static prerequisites of the rule, including
  duplicates if any.
- <tt>$\@</tt> expands to the first target of the rule.
- <tt>$*</tt> expands to the string that matched <tt>%</tt> in a generic rule.
- <tt>$$</tt> expands to a single dollar symbol.

Note: contrarily to <b>make</b>, there are no corresponding variables. For
instance, <tt>$^</tt> is not a shorthand for <tt>$(^)</tt>. Another
difference is that <tt>$\@</tt> is always the first target, not the one that
triggered the rule.

\subsection sec-functions Built-in functions

<b>remake</b> also supports a few built-in functions inspired from <b>make</b>.

- <tt>$(addprefix <i>prefix</i>, <i>list</i>)</tt> returns the list obtained
  by prepending its first argument to each element of its second argument.
- <tt>$(addsuffix <i>suffix</i>, <i>list</i>)</tt> returns the list obtained
  by appending its first argument to each element of its second argument.

\subsection sec-order Order-only prerequisites

If the static prerequisites of a rule contain a pipe symbol, prerequisites
on its right do not cause the targets to become obsolete if they are newer
(unless they are also dynamically registered as dependencies). They are
meant to be used when the targets do not directly depend on them, but the
computation of their dynamic dependencies does.

@verbatim
%.o : %.c | parser.h
	gcc -MMD -MF $@.d -o $@ -c $<
	remake -r < $@.d
	rm $@.d

parser.c parser.h: parser.y
	yacc -d -o parser.c parser.y
@endverbatim

\subsection sec-special-tgt Special targets

Target <tt>.PHONY</tt> marks its prerequisites as being always obsolete.

\subsection sec-special-var Special variables

Variable <tt>.OPTIONS</tt> is handled specially. Its content enables some
features of <b>remake</b> that are not enabled by default.

- <tt>variable-propagation</tt>: When a variable is set in the prerequisite
  part of a rule, it is propagated to the rules of all the targets this rule
  depends on. This option also enables variables to be set on the command
  line. Note that, as in <b>make</b>, this features introduces non-determinism:
  the content of some variables will depend on the build order.

\section sec-semantics Semantics

\subsection src-obsolete When are targets obsolete?

A target is obsolete:

- if there is no file corresponding to the target, or to one of its siblings
  in a multi-target rule,
- if any of its dynamic prerequisites from a previous run or any of its static
  prerequisites is obsolete,
- if the latest file corresponding to its siblings or itself is older than any
  of its dynamic prerequisites or static prerequisites.

In all the other cases, it is assumed to be up-to-date (and so are all its
siblings). Note that the last rule above says "latest" and not "earliest". While
it might cause some obsolete targets to go unnoticed in corner cases, it allows
for the following kind of rules:

@verbatim
config.h stamp-config_h: config.h.in config.status
	./config.status config.h
	touch stamp-config_h
@endverbatim

A <tt>config.status</tt> file generally does not update header files (here
<tt>config.h</tt>) if they would not change. As a consequence, if not for the
<tt>stamp-config_h</tt> file above, a header would always be considered obsolete
once one of its prerequisites is modified. Note that touching <tt>config.h</tt>
rather than <tt>stamp-config_h</tt> would defeat the point of not updating it
in the first place, since the program files would need to be rebuilt.

Once all the static prerequisites of a target have been rebuilt, <b>remake</b>
checks whether the target still needs to be built. If it was obsolete only
because its prerequisites needed to be rebuilt and none of them changed, the
target is assumed to be up-to-date.

\subsection sec-rules How are targets (re)built?

There are two kinds of rules. If any of the targets or prerequisites contains
a <tt>%</tt> character, the rule is said to be <em>generic</em>. All the
targets of the rule shall then contain a single <tt>%</tt> character. All the
other rules are said to be <em>specific</em>.

A rule is said to <em>match</em> a given target:

- if it is specific and the target appears inside its target list,
- if it is generic and there is a way to replace the <tt>%</tt> character
  from one of its targets so that it matches the given target.

When <b>remake</b> tries to build a given target, it looks for a specific rule
that matches it. If there is one and its script is nonempty, it uses it to
rebuild the target.

Otherwise, it looks for a generic rule that matches the target. If there are
several matching rules, it chooses the one with the shortest pattern (and if
there are several ones, the earliest one). <b>remake</b> then looks for
specific rules that match each target of the generic rule. All the
prerequisites of these specific rules are added to those of the generic rule.
The script of the generic rule is used to build the target.

Example:

@verbatim
t%1 t2%: p1 p%2
	commands building t%1 and t2%

t2z: p4
	commands building t2z

ty1: p3

# t2x is built by the first rule (which also builds tx1) and its prerequisites are p1, px2
# t2y is built by the first rule (which also builds ty1) and its prerequisites are p1, py2, p3
# t2z is built by the second rule and its prerequisite is p4
@endverbatim

The set of rules from <b>Remakefile</b> is ill-formed:

- if any specific rule matching a target of the generic rule has a nonempty script,
- if any target of the generic rule is matched by a generic rule with a shorter pattern.

\section sec-compilation Compilation

- On Linux, MacOSX, and BSD: <tt>g++ -o remake remake.cpp</tt>
- On Windows: <tt>g++ -o remake.exe remake.cpp -lws2_32</tt>

Installing <b>remake</b> is needed only if <b>Remakefile</b> does not
specify the path to the executable for its recursive calls. Thanks to its
single source file, <b>remake</b> can be shipped inside other packages and
built at configuration time.

\section sec-differences Differences with other build systems

Differences with <b>make</b>:

- Dynamic dependencies are supported.
- For rules with multiple targets, the shell script is executed only once
  and is assumed to build all the targets. There is no need for
  convoluted rules that are robust enough for parallel builds. For generic
  rules, this is similar to the behavior of pattern rules from <b>gmake</b>.
- As with <b>redo</b>, only one shell is run when executing a script,
  rather than one per script line. Note that the shells are run with
  option <tt>-e</tt>, thus causing them to exit as soon as an error is
  encountered.
- The prerequisites of generic rules (known as implicit rules in make lingo)
  are not used to decide between several of them. <b>remake</b> does not
  select one for which it could satisfy the dependencies.
- Variables and built-in functions are expanded as they are encountered
  during <b>Remakefile</b> parsing.
- Target-specific variables are not propagated, unless specifically enabled,
  since this causes non-deterministic builds. This is the same for variables
  set on the command line.

Differences with <b>redo</b>:

- As with <b>make</b>, it is possible to write the following kind of rules
  in <b>remake</b>.
@verbatim
Remakefile: Remakefile.in ./config.status
	./config.status Remakefile
@endverbatim
- If a target is already built the first time <b>remake</b> runs, it still
  uses the static prerequisites of rules mentioning it to check whether it
  needs to be rebuilt. It does not assume it to be up-to-date. As with
  <b>redo</b> though, if its obsolete status would be due to a dynamic
  prerequisite, it will go unnoticed; it should be removed beforehand.
- Multiple targets are supported.
- <b>remake</b> has almost no features: no checksum-based dependencies, no
  compatibility with job servers, etc.

\section sec-limitations Limitations

- If a rule script calls <b>remake</b>, the current working directory should
  be the directory containing <b>Remakefile</b> (or the working directory
  from the original <b>remake</b> if it was called with option <b>-f</b>).
- As with <b>make</b>, variables passed on the command line should keep
  the same values, to ensure deterministic builds.
- Some cases of ill-formed rules are not caught by <b>remake</b> and can
  thus lead to unpredictable behaviors.

\section sec-links Links

@see http://cr.yp.to/redo.html for the philosophy of <b>redo</b> and
https://github.com/apenwarr/redo for an implementation and some comprehensive documentation.

\section sec-licensing Licensing

@author Guillaume Melquiond
@version 0.12
@date 2012-2014
@copyright
This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
\n
This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

\section sec-internals Internals

The parent <b>remake</b> process acts as a server. The other ones have a
REMAKE_SOCKET environment variable that tells them how to contact the
server. They send the content of the REMAKE_JOB_ID environment variable,
so that the server can associate the child targets to the jobs that
spawned them. They then wait for completion and exit with the status
returned by the server. This is handled by #client_mode.

The server calls #load_dependencies and #save_dependencies to serialize
dynamic dependencies from <b>.remake</b>. It loads <b>Remakefile</b> with
#load_rules. It then runs #server_mode, which calls #server_loop.

When building a target, the following sequence of events happens:

- #start calls #find_rule (and #find_generic_rule) to get the rule.
- It then creates a pseudo-client if the rule has static dependencies, or
  calls #run_script otherwise. In both cases, a new job is created; the
  rule and the variables are stored into #jobs.
- #run_script creates a shell process and stores it in #job_pids. It
  increases #running_jobs.
- The child process possibly calls <b>remake</b> with a list of targets.
- #accept_client receives a build request from a child process and adds
  it to #clients. It also records the new dependencies of the job into
  #dependencies. It increases #waiting_jobs.
- #handle_clients uses #get_status to look up the obsoleteness of the
  targets.
- Once the targets of a request have been built or one of them has failed,
  #handle_clients calls #complete_request and removes the request from
  #clients.
- If the build targets come from a pseudo-client, #complete_request calls
  #run_script. Otherwise it sends the reply to the corresponding child
  process and decreases #waiting_jobs.
- When a child process ends, #server_loop calls #finalize_job, which
  removes the process from #job_pids, decreases #running_jobs, and calls
  #complete_job.
- #complete_job removes the job from #jobs and calls #update_status
  to change the status of the targets. It also removes the target files in
  case of failure.
*/

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#define WINDOWS
#endif

#include <fstream>
#include <iostream>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifdef __APPLE__
#define MACOSX
#endif

#ifdef __linux__
#define LINUX
#endif

#ifdef WINDOWS
#include <windows.h>
#include <winbase.h>
#include <winsock2.h>
#define pid_t HANDLE
typedef SOCKET socket_t;
#else
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/wait.h>
typedef int socket_t;
enum { INVALID_SOCKET = -1 };
extern char **environ;
#endif

#if defined(WINDOWS) || defined(MACOSX)
enum { MSG_NOSIGNAL = 0 };
#endif

typedef std::list<std::string> string_list;

typedef std::set<std::string> string_set;

/**
 * Reference-counted shared object.
 * @note The default constructor delays the creation of the object until it
 *       is first dereferenced.
 */
template<class T>
struct ref_ptr
{
	struct content
	{
		size_t cnt;
		T val;
		content(): cnt(1) {}
		content(T const &t): cnt(1), val(t) {}
	};
	mutable content *ptr;
	ref_ptr(): ptr(NULL) {}
	ref_ptr(T const &t): ptr(new content(t)) {}
	ref_ptr(ref_ptr const &p): ptr(p.ptr) { if (ptr) ++ptr->cnt; }
	~ref_ptr() { if (ptr && --ptr->cnt == 0) delete ptr; }
	ref_ptr &operator=(ref_ptr const &p)
	{
		if (ptr == p.ptr) return *this;
		if (ptr && --ptr->cnt == 0) delete ptr;
		ptr = p.ptr;
		if (ptr) ++ptr->cnt;
		return *this;
	}
	T &operator*() const
	{
		if (!ptr) ptr = new content;
		return ptr->val;
	}
	T *operator->() const { return &**this; }
};

struct dependency_t
{
	string_list targets;
	string_set deps;
};

typedef std::map<std::string, ref_ptr<dependency_t> > dependency_map;

typedef std::map<std::string, string_list> variable_map;

/**
 * Build status of a target.
 */
enum status_e
{
	Uptodate, ///< Target is up-to-date.
	Todo,     ///< Target is missing or obsolete.
	Recheck,  ///< Target has an obsolete dependency.
	Running,  ///< Target is being rebuilt.
	RunningRecheck, ///< Static prerequisites are being rebuilt.
	Remade,   ///< Target was successfully rebuilt.
	Failed    ///< Build failed for target.
};

/**
 * Build status of a target.
 */
struct status_t
{
	status_e status; ///< Actual status.
	time_t last;     ///< Last-modified date.
};

typedef std::map<std::string, status_t> status_map;

/**
 * Delayed assignment to a variable.
 */
struct assign_t
{
	bool append;
	string_list value;
};

typedef std::map<std::string, assign_t> assign_map;

/**
 * A rule loaded from Remakefile.
 */
struct rule_t
{
	string_list targets; ///< Files produced by this rule.
	string_list deps;    ///< Dependencies used for an implicit call to remake at the start of the script.
	string_list wdeps;   ///< Like #deps, except that they are not registered as dependencies.
	assign_map assigns;  ///< Assignment of variables.
	std::string script;  ///< Shell script for building the targets.
};

typedef std::list<rule_t> rule_list;

typedef std::map<std::string, ref_ptr<rule_t> > rule_map;

/**
 * A job created from a set of rules.
 */

struct job_t
{
	rule_t rule;       ///< Original rule.
	std::string stem;  ///< Pattern used to instantiate the generic rule, if any.
	variable_map vars; ///< Values of local variables.
};

typedef std::map<int, job_t> job_map;

typedef std::map<pid_t, int> pid_job_map;

/**
 * Client waiting for a request to complete.
 *
 * There are two kinds of clients:
 * - real clients, which are instances of remake created by built scripts,
 * - pseudo clients, which are created by the server to build specific targets.
 *
 * Among pseudo clients, there are two categories:
 * - original clients, which are created for the targets passed on the
 *   command line by the user or for the initial regeneration of the rule file,
 * - dependency clients, which are created to handle rules that have
 *   explicit dependencies and thus to emulate a call to remake.
 */
struct client_t
{
	socket_t socket;     ///< Socket used to reply to the client (invalid for pseudo clients).
	int job_id;          ///< Job for which the built script called remake and spawned the client (negative for original clients).
	bool failed;         ///< Whether some targets failed in mode -k.
	string_list pending; ///< Targets not yet started.
	string_set running;  ///< Targets being built.
	variable_map vars;   ///< Variables set on request.
	bool delayed;        ///< Whether it is a dependency client and a script has to be started on request completion.
	client_t(): socket(INVALID_SOCKET), job_id(-1), failed(false), delayed(false) {}
};

typedef std::list<client_t> client_list;

/**
 * Map from variable names to their content.
 * Initialized with the values passed on the command line.
 */
static variable_map variables;

/**
 * Map from targets to their known dependencies.
 */
static dependency_map dependencies;

/**
 * Map from targets to their build status.
 */
static status_map status;

/**
 * Set of generic rules loaded from Remakefile.
 */
static rule_list generic_rules;

/**
 * Map from targets to specific rules loaded from Remakefile.
 */
static rule_map specific_rules;

/**
 * Map of jobs being built.
 */
static job_map jobs;

/**
 * Map from jobs to shell pids.
 */
static pid_job_map job_pids;

/**
 * List of clients waiting for a request to complete.
 * New clients are put to front, so that the build process is depth-first.
 */
static client_list clients;

/**
 * Maximum number of parallel jobs (non-positive if unbounded).
 * Can be modified by the -j option.
 */
static int max_active_jobs = 1;

/**
 * Whether to keep building targets in case of failure.
 * Can be modified by the -k option.
 */
static bool keep_going = false;

/**
 * Number of jobs currently running:
 * - it increases when a process is created in #run_script,
 * - it decreases when a completion message is received in #finalize_job.
 *
 * @note There might be some jobs running while #clients is empty.
 *       Indeed, if a client requested two targets to be rebuilt, if they
 *       are running concurrently, if one of them fails, the client will
 *       get a failure notice and might terminate before the other target
 *       finishes.
 */
static int running_jobs = 0;

/**
 * Number of jobs currently waiting for a build request to finish:
 * - it increases when a build request is received in #accept_client
 *   (since the client is presumably waiting for the reply),
 * - it decreases when a reply is sent in #complete_request.
 */
static int waiting_jobs = 0;

/**
 * Global counter used to produce increasing job numbers.
 * @see jobs
 */
static int job_counter = 0;

/**
 * Socket on which the server listens for client request.
 */
static socket_t socket_fd;

/**
 * Whether the request of an original client failed.
 */
static bool build_failure;

#ifndef WINDOWS
/**
 * Name of the server socket in the file system.
 */
static char *socket_name;
#endif

/**
 * Name of the first target of the first specific rule, used for default run.
 */
static std::string first_target;

/**
 * Whether a short message should be displayed for each target.
 */
static bool show_targets = true;

/**
 * Whether script commands are echoed.
 */
static bool echo_scripts = false;

/**
 * Time at the start of the program.
 */
static time_t now = time(NULL);

/**
 * Directory with respect to which command-line names are relative.
 */
static std::string working_dir;

/**
 * Directory with respect to which targets are relative.
 */
static std::string prefix_dir;

/**
 * Whether the prefix directory is different from #working_dir.
 */
static bool changed_prefix_dir;

/**
 * Whether target-specific variables are propagated to prerequisites.
 */
static bool propagate_vars = false;

/**
 * Whether targets are unconditionally obsolete.
 */
static bool obsolete_targets = false;

#ifndef WINDOWS
static volatile sig_atomic_t got_SIGCHLD = 0;

static void sigchld_handler(int)
{
	got_SIGCHLD = 1;
}

static void sigint_handler(int)
{
	// Child processes will receive the signal too, so just prevent
	// new jobs from starting and wait for the running jobs to fail.
	keep_going = false;
}
#endif

struct log
{
	bool active, open;
	int depth;
	log(): active(false), open(false), depth(0)
	{
	}
	std::ostream &operator()()
	{
		if (open) std::cerr << std::endl;
		assert(depth >= 0);
		std::cerr << std::string(depth * 2, ' ');
		open = false;
		return std::cerr;
	}
	std::ostream &operator()(bool o)
	{
		if (o && open) std::cerr << std::endl;
		if (!o) --depth;
		assert(depth >= 0);
		if (o || !open) std::cerr << std::string(depth * 2, ' ');
		if (o) ++depth;
		open = o;
		return std::cerr;
	}
};

static log debug;

struct log_auto_close
{
	bool still_open;
	log_auto_close(): still_open(true)
	{
	}
	~log_auto_close()
	{
		if (debug.active && still_open) debug(false) << "done\n";
	}
};

#define DEBUG if (debug.active) debug()
#define DEBUG_open log_auto_close auto_close; if (debug.active) debug(true)
#define DEBUG_close if ((auto_close.still_open = false), debug.active) debug(false)

/**
 * Strong typedef for strings that need escaping.
 * @note The string is stored as a reference, so the constructed object is
 *       meant to be immediately consumed.
 */
struct escape_string
{
	std::string const &input;
	escape_string(std::string const &s): input(s) {}
};

/**
 * Write the string in @a se to @a out if it does not contain any special
 * characters, a quoted and escaped string otherwise.
 */
static std::ostream &operator<<(std::ostream &out, escape_string const &se)
{
	std::string const &s = se.input;
	char const *quoted_char = ",: '";
	char const *escaped_char = "\"\\$!";
	bool need_quotes = false;
	char *buf = NULL;
	size_t len = s.length(), last = 0, j = 0;
	for (size_t i = 0; i < len; ++i)
	{
		if (strchr(escaped_char, s[i]))
		{
			need_quotes = true;
			if (!buf) buf = new char[len * 2];
			memcpy(&buf[j], &s[last], i - last);
			j += i - last;
			buf[j++] = '\\';
			buf[j++] = s[i];
			last = i + 1;
		}
		if (!need_quotes && strchr(quoted_char, s[i]))
			need_quotes = true;
	}
	if (!need_quotes) return out << s;
	out << '"';
	if (!buf) return out << s << '"';
	out.write(buf, j);
	out.write(&s[last], len - last);
	delete[] buf;
	return out << '"';
}

/**
 * @defgroup paths Path helpers
 *
 * @{
 */

/**
 * Initialize #working_dir.
 */
static void init_working_dir()
{
	char buf[1024];
	char *res = getcwd(buf, sizeof(buf));
	if (!res)
	{
		perror("Failed to get working directory");
		exit(EXIT_FAILURE);
	}
	working_dir = buf;
#ifdef WINDOWS
	for (size_t i = 0, l = working_dir.size(); i != l; ++i)
	{
		if (working_dir[i] == '\\') working_dir[i] = '/';
	}
#endif
	prefix_dir = working_dir;
}

/**
 * Initialize #prefix_dir and switch to it.
 */
static void init_prefix_dir()
{
	for (;;)
	{
		struct stat s;
		if (stat((prefix_dir + "/Remakefile").c_str(), &s) == 0)
		{
			if (!changed_prefix_dir) return;
			if (chdir(prefix_dir.c_str()))
			{
				perror("Failed to change working directory");
				exit(EXIT_FAILURE);
			}
			if (show_targets)
			{
				std::cout << "remake: Entering directory `" << prefix_dir << '\'' << std::endl;
			}
			return;
		}
		size_t pos = prefix_dir.find_last_of('/');
		if (pos == std::string::npos)
		{
			std::cerr << "Failed to locate Remakefile in the current directory or one of its parents" << std::endl;
			exit(EXIT_FAILURE);
		}
		prefix_dir.erase(pos);
		changed_prefix_dir = true;
	}
}

/**
 * Normalize an absolute path with respect to @a p.
 * Paths outside the subtree are left unchanged.
 */
static std::string normalize_abs(std::string const &s, std::string const &p)
{
	size_t l = p.length();
	if (s.compare(0, l, p)) return s;
	size_t ll = s.length();
	if (ll == l) return ".";
	if (s[l] != '/')
	{
		size_t pos = s.rfind('/', l);
		assert(pos != std::string::npos);
		return s.substr(pos + 1);
	}
	if (ll == l + 1) return ".";
	return s.substr(l + 1);
}

/**
 * Normalize path @a s (possibly relative to @a w) with respect to @a p.
 *
 * - If both @a p and @a w are empty, the function just removes ".", "..", "//".
 * - If only @a p is empty, the function returns an absolute path.
 */
static std::string normalize(std::string const &s, std::string const &w, std::string const &p)
{
#ifdef WINDOWS
	char const *delim = "/\\";
#else
	char delim = '/';
#endif
	size_t pos = s.find_first_of(delim);
	if (pos == std::string::npos && w == p) return s;
	bool absolute = pos == 0;
	if (!absolute && w != p && !w.empty())
		return normalize(w + '/' + s, w, p);
	size_t prev = 0, len = s.length();
	string_list l;
	for (;;)
	{
		if (pos != prev)
		{
			std::string n = s.substr(prev, pos - prev);
			if (n == "..")
			{
				if (!l.empty()) l.pop_back();
				else if (!absolute && !w.empty())
					return normalize(w + '/' + s, w, p);
			}
			else if (n != ".")
				l.push_back(n);
		}
		++pos;
		if (pos >= len) break;
		prev = pos;
		pos = s.find_first_of(delim, prev);
		if (pos == std::string::npos) pos = len;
	}
	string_list::const_iterator i = l.begin(), i_end = l.end();
	if (i == i_end) return absolute ? "/" : ".";
	std::string n;
	if (absolute) n.push_back('/');
	n.append(*i);
	for (++i; i != i_end; ++i)
	{
		n.push_back('/');
		n.append(*i);
	}
	if (absolute && !p.empty()) return normalize_abs(n, p);
	return n;
}

/**
 * Normalize the content of a list of targets.
 */
static void normalize_list(string_list &l, std::string const &w, std::string const &p)
{
	for (string_list::iterator i = l.begin(),
	     i_end = l.end(); i != i_end; ++i)
	{
		*i = normalize(*i, w, p);
	}
}

/** @} */

/**
 * @defgroup lexer Lexer
 *
 * @{
 */

/**
 * Skip spaces.
 */
static void skip_spaces(std::istream &in)
{
	char c;
	while (strchr(" \t", (c = in.get()))) {}
	if (in.good()) in.putback(c);
}

/**
 * Skip empty lines.
 */
static void skip_empty(std::istream &in)
{
	char c;
	while (strchr("\r\n", (c = in.get()))) {}
	if (in.good()) in.putback(c);
}

/**
 * Skip end of line. If @a multi is true, skip the following empty lines too.
 * @return true if there was a line to end.
 */
static bool skip_eol(std::istream &in, bool multi = false)
{
	char c = in.get();
	if (c == '\r') c = in.get();
	if (c != '\n' && in.good()) in.putback(c);
	if (c != '\n' && !in.eof()) return false;
	if (multi) skip_empty(in);
	return true;
}

enum
{
  Unexpected = 0,
  Word       = 1 << 1,
  Colon      = 1 << 2,
  Equal      = 1 << 3,
  Dollarpar  = 1 << 4,
  Rightpar   = 1 << 5,
  Comma      = 1 << 6,
  Plusequal  = 1 << 7,
  Pipe       = 1 << 8,
};

/**
 * Skip spaces and peek at the next token.
 * If it is one of @a mask, skip it (if it is not Word) and return it.
 * @note For composite tokens allowed by @a mask, input characters might
 *       have been eaten even for an Unexpected result.
 */
static int expect_token(std::istream &in, int mask)
{
	while (true)
	{
		skip_spaces(in);
		char c = in.peek();
		if (!in.good()) return Unexpected;
		int tok;
		switch (c)
		{
		case '\r':
		case '\n': return Unexpected;
		case ':': tok = Colon; break;
		case ',': tok = Comma; break;
		case '=': tok = Equal; break;
		case ')': tok = Rightpar; break;
		case '|': tok = Pipe; break;
		case '$':
			if (!(mask & Dollarpar)) return Unexpected;
			in.ignore(1);
			tok = Dollarpar;
			if (in.peek() != '(') return Unexpected;
			break;
		case '+':
			if (!(mask & Plusequal)) return Unexpected;
			in.ignore(1);
			tok = Plusequal;
			if (in.peek() != '=') return Unexpected;
			break;
		case '\\':
			in.ignore(1);
			if (skip_eol(in)) continue;
			in.putback('\\');
			return mask & Word ? Word : Unexpected;
		default:
			return mask & Word ? Word : Unexpected;
		}
		if (!(tok & mask)) return Unexpected;
		in.ignore(1);
		return tok;
	}
}

/**
 * Read a (possibly quoted) word.
 */
static std::string read_word(std::istream &in, bool detect_equal = true)
{
	int c = in.peek();
	std::string res;
	if (!in.good()) return res;
	char const *separators = " \t\r\n$(),:";
	bool quoted = c == '"';
	if (quoted) in.ignore(1);
	bool plus = false;
	while (true)
	{
		c = in.peek();
		if (!in.good()) return res;
		if (quoted)
		{
			in.ignore(1);
			if (c == '\\')
				res += in.get();
			else if (c == '"')
				quoted = false;
			else
				res += c;
			continue;
		}
		if (detect_equal && c == '=')
		{
			if (plus) in.putback('+');
			return res;
		}
		if (plus)
		{
			res += '+';
			plus = false;
		}
		if (strchr(separators, c)) return res;
		in.ignore(1);
		if (detect_equal && c == '+') plus = true;
		else res += c;
	}
}

/** @} */

/**
 * @defgroup stream Token streams
 *
 * @{
 */

/**
 * Possible results from word producers.
 */
enum input_status
{
	Success,
	SyntaxError,
	Eof
};

/**
 * Interface for word producers.
 */
struct generator
{
	virtual ~generator() {}
	virtual input_status next(std::string &) = 0;
};

/**
 * Generator for the words of a variable.
 */
struct variable_generator: generator
{
	std::string name;
	string_list::const_iterator vcur, vend;
	variable_generator(std::string const &, variable_map const *);
	input_status next(std::string &);
};

variable_generator::variable_generator(std::string const &n,
	variable_map const *local_variables): name(n)
{
	if (local_variables)
	{
		variable_map::const_iterator i = local_variables->find(name);
		if (i != local_variables->end())
		{
			vcur = i->second.begin();
			vend = i->second.end();
			return;
		}
	}
	variable_map::const_iterator i = variables.find(name);
	if (i == variables.end()) return;
	vcur = i->second.begin();
	vend = i->second.end();
}

input_status variable_generator::next(std::string &res)
{
	if (vcur != vend)
	{
		res = *vcur;
		++vcur;
		return Success;
	}
	return Eof;
}

/**
 * Generator for the words of an input stream.
 */
struct input_generator
{
	std::istream &in;
	generator *nested;
	variable_map const *local_variables;
	bool earliest_exit, done;
	input_generator(std::istream &i, variable_map const *lv, bool e = false)
		: in(i), nested(NULL), local_variables(lv), earliest_exit(e), done(false) {}
	input_status next(std::string &);
	~input_generator() { assert(!nested); }
};

static generator *get_function(input_generator const &, std::string const &);

input_status input_generator::next(std::string &res)
{
	if (nested)
	{
		restart:
		input_status s = nested->next(res);
		if (s == Success) return Success;
		delete nested;
		nested = NULL;
		if (s == SyntaxError) return SyntaxError;
	}
	if (done) return Eof;
	if (earliest_exit) done = true;
	switch (expect_token(in, Word | Dollarpar))
	{
	case Word:
		res = read_word(in, false);
		return Success;
	case Dollarpar:
	{
		std::string name = read_word(in, false);
		if (name.empty()) return SyntaxError;
		if (expect_token(in, Rightpar))
			nested = new variable_generator(name, local_variables);
		else
		{
			nested = get_function(*this, name);
			if (!nested) return SyntaxError;
		}
		goto restart;
	}
	default:
		return Eof;
	}
}

/**
 * Read a list of words from an input generator.
 * @return false if a syntax error was encountered.
 */
static bool read_words(input_generator &in, string_list &res)
{
	while (true)
	{
		res.push_back(std::string());
		input_status s = in.next(res.back());
		if (s == Success) continue;
		res.pop_back();
		return s == Eof;
	}
}

static bool read_words(std::istream &in, string_list &res)
{
	input_generator gen(in, NULL);
	return read_words(gen, res);
}

/**
 * Generator for the result of function addprefix.
 */
struct addprefix_generator: generator
{
	input_generator gen;
	string_list pre;
	string_list::const_iterator prei;
	size_t prej, prel;
	std::string suf;
	addprefix_generator(input_generator const &, bool &);
	input_status next(std::string &);
};

addprefix_generator::addprefix_generator(input_generator const &top, bool &ok)
	: gen(top.in, top.local_variables)
{
	if (!read_words(gen, pre)) return;
	if (!expect_token(gen.in, Comma)) return;
	prej = 0;
	prel = pre.size();
	ok = true;
}

input_status addprefix_generator::next(std::string &res)
{
	if (prej)
	{
		produce:
		if (prej == prel)
		{
			res = *prei + suf;
			prej = 0;
		}
		else
		{
			res = *prei++;
			++prej;
		}
		return Success;
	}
	switch (gen.next(res))
	{
	case Success:
		if (!prel) return Success;
		prei = pre.begin();
		prej = 1;
		suf = res;
		goto produce;
	case Eof:
		return expect_token(gen.in, Rightpar) ? Eof : SyntaxError;
	default:
		return SyntaxError;
	}
}

/**
 * Generator for the result of function addsuffix.
 */
struct addsuffix_generator: generator
{
	input_generator gen;
	string_list suf;
	string_list::const_iterator sufi;
	size_t sufj, sufl;
	std::string pre;
	addsuffix_generator(input_generator const &, bool &);
	input_status next(std::string &);
};

addsuffix_generator::addsuffix_generator(input_generator const &top, bool &ok)
	: gen(top.in, top.local_variables)
{
	if (!read_words(gen, suf)) return;
	if (!expect_token(gen.in, Comma)) return;
	sufj = 0;
	sufl = suf.size();
	ok = true;
}

input_status addsuffix_generator::next(std::string &res)
{
	if (sufj)
	{
		if (sufj != sufl)
		{
			res = *sufi++;
			++sufj;
			return Success;
		}
		sufj = 0;
	}
	switch (gen.next(res))
	{
	case Success:
		if (!sufl) return Success;
		sufi = suf.begin();
		sufj = 1;
		res += *sufi++;
		return Success;
	case Eof:
		return expect_token(gen.in, Rightpar) ? Eof : SyntaxError;
	default:
		return SyntaxError;
	}
}

/**
 * Return a generator for function @a name.
 */
static generator *get_function(input_generator const &in, std::string const &name)
{
	skip_spaces(in.in);
	generator *g = NULL;
	bool ok = false;
	if (name == "addprefix") g = new addprefix_generator(in, ok);
	else if (name == "addsuffix") g = new addsuffix_generator(in, ok);
	if (!g || ok) return g;
	delete g;
	return NULL;
}

/** @} */

/**
 * @defgroup database Dependency database
 *
 * @{
 */

/**
 * Load dependencies from @a in.
 */
static void load_dependencies(std::istream &in)
{
	if (false)
	{
		error:
		std::cerr << "Failed to load database" << std::endl;
		exit(EXIT_FAILURE);
	}

	while (!in.eof())
	{
		string_list targets;
		if (!read_words(in, targets)) goto error;
		if (in.eof()) return;
		if (targets.empty()) goto error;
		DEBUG << "reading dependencies of target " << targets.front() << std::endl;
		if (in.get() != ':') goto error;
		ref_ptr<dependency_t> dep;
		dep->targets = targets;
		string_list deps;
		if (!read_words(in, deps)) goto error;
		dep->deps.insert(deps.begin(), deps.end());
		for (string_list::const_iterator i = targets.begin(),
		     i_end = targets.end(); i != i_end; ++i)
		{
			dependencies[*i] = dep;
		}
		skip_empty(in);
	}
}

/**
 * Load known dependencies from file <tt>.remake</tt>.
 */
static void load_dependencies()
{
	DEBUG_open << "Loading database... ";
	std::ifstream in(".remake");
	if (!in.good())
	{
		DEBUG_close << "not found\n";
		return;
	}
	load_dependencies(in);
}


/**
 * Save all the dependencies in file <tt>.remake</tt>.
 */
static void save_dependencies()
{
	DEBUG_open << "Saving database... ";
	std::ofstream db(".remake");
	while (!dependencies.empty())
	{
		ref_ptr<dependency_t> dep = dependencies.begin()->second;
		for (string_list::const_iterator i = dep->targets.begin(),
		     i_end = dep->targets.end(); i != i_end; ++i)
		{
			db << escape_string(*i) << ' ';
			dependencies.erase(*i);
		}
		db << ':';
		for (string_set::const_iterator i = dep->deps.begin(),
		     i_end = dep->deps.end(); i != i_end; ++i)
		{
			db << ' ' << escape_string(*i);
		}
		db << std::endl;
	}
}

/** @} */

static void merge_rule(rule_t &dest, rule_t const &src);

/**
 * @defgroup parser Rule parser
 *
 * @{
 */

/**
 * Register a specific rule with an empty script:
 *
 * - Check that none of the targets already has an associated rule with a
 *   nonempty script.
 * - Create a new rule with a single target for each target, if needed.
 * - Add the prerequisites of @a rule to all these associated rules.
 */
static void register_transparent_rule(rule_t const &rule, string_list const &targets)
{
	assert(rule.script.empty());
	for (string_list::const_iterator i = targets.begin(),
	     i_end = targets.end(); i != i_end; ++i)
	{
		std::pair<rule_map::iterator, bool> j =
			specific_rules.insert(std::make_pair(*i, ref_ptr<rule_t>()));
		ref_ptr<rule_t> &r = j.first->second;
		if (j.second)
		{
			r = ref_ptr<rule_t>(rule);
			r->targets = string_list(1, *i);
			continue;
		}
		if (!r->script.empty())
		{
			std::cerr << "Failed to load rules: " << *i
				<< " cannot be the target of several rules" << std::endl;
			exit(EXIT_FAILURE);
		}
		assert(r->targets.size() == 1 && r->targets.front() == *i);
		merge_rule(*r, rule);
	}

	for (string_list::const_iterator i = targets.begin(),
	     i_end = targets.end(); i != i_end; ++i)
	{
		ref_ptr<dependency_t> &dep = dependencies[*i];
		if (dep->targets.empty()) dep->targets.push_back(*i);
		dep->deps.insert(rule.deps.begin(), rule.deps.end());
	}
}

/**
 * Register a specific rule with a nonempty script:
 *
 * - Check that none of the targets already has an associated rule.
 * - Create a single shared rule and associate it to all the targets.
 * - Merge the prerequisites of all the targets into a single set and
 *   add the prerequisites of the rule to it. (The preexisting
 *   prerequisites, if any, come from a previous run.)
 */
static void register_scripted_rule(rule_t const &rule)
{
	ref_ptr<rule_t> r(rule);
	for (string_list::const_iterator i = rule.targets.begin(),
	     i_end = rule.targets.end(); i != i_end; ++i)
	{
		std::pair<rule_map::iterator, bool> j =
			specific_rules.insert(std::make_pair(*i, r));
		if (j.second) continue;
		std::cerr << "Failed to load rules: " << *i
			<< " cannot be the target of several rules" << std::endl;
		exit(EXIT_FAILURE);
	}

	ref_ptr<dependency_t> dep;
	dep->targets = rule.targets;
	dep->deps.insert(rule.deps.begin(), rule.deps.end());
	for (string_list::const_iterator i = rule.targets.begin(),
	     i_end = rule.targets.end(); i != i_end; ++i)
	{
		ref_ptr<dependency_t> &d = dependencies[*i];
		dep->deps.insert(d->deps.begin(), d->deps.end());
		d = dep;
	}
}

/**
 * Read a rule starting with target @a first, if nonempty.
 * Store into #generic_rules or #specific_rules depending on its genericity.
 */
static void load_rule(std::istream &in, std::string const &first)
{
	DEBUG_open << "Reading rule for target " << first << "... ";
	if (false)
	{
		error:
		DEBUG_close << "failed\n";
		std::cerr << "Failed to load rules: syntax error" << std::endl;
		exit(EXIT_FAILURE);
	}
	rule_t rule;

	// Read targets and check genericity.
	string_list targets;
	if (!read_words(in, targets)) goto error;
	if (!first.empty()) targets.push_front(first);
	else if (targets.empty()) goto error;
	else DEBUG << "actual target: " << targets.front() << std::endl;
	bool generic = false;
	normalize_list(targets, "", "");
	for (string_list::const_iterator i = targets.begin(),
	     i_end = targets.end(); i != i_end; ++i)
	{
		if (i->empty()) goto error;
		if ((i->find('%') != std::string::npos) != generic)
		{
			if (i == targets.begin()) generic = true;
			else goto error;
		}
	}
	std::swap(rule.targets, targets);
	skip_spaces(in);
	if (in.get() != ':') goto error;

	bool assignment = false;

	// Read dependencies.
	{
		string_list v;
		if (expect_token(in, Word))
		{
			std::string d = read_word(in);
			if (int tok = expect_token(in, Equal | Plusequal))
			{
				if (!read_words(in, v)) goto error;
				assign_t &a = rule.assigns[d];
				a.append = tok == Plusequal;
				a.value.swap(v);
				assignment = true;
				goto end_line;
			}
			v.push_back(d);
		}

		if (!read_words(in, v)) goto error;
		normalize_list(v, "", "");
		rule.deps.swap(v);

		if (expect_token(in, Pipe))
		{
			if (!read_words(in, v)) goto error;
			normalize_list(v, "", "");
			rule.wdeps.swap(v);
		}
	}

	end_line:
	skip_spaces(in);
	if (!skip_eol(in, true)) goto error;

	// Read script.
	std::ostringstream buf;
	while (true)
	{
		char c = in.get();
		if (!in.good()) break;
		if (c == '\t' || c == ' ')
		{
			in.get(*buf.rdbuf());
			if (in.fail() && !in.eof()) in.clear();
		}
		else if (c == '\r' || c == '\n')
			buf << c;
		else
		{
			in.putback(c);
			break;
		}
	}
	rule.script = buf.str();

	// Register phony targets.
	if (rule.targets.front() == ".PHONY")
	{
		for (string_list::const_iterator i = rule.deps.begin(),
		     i_end = rule.deps.end(); i != i_end; ++i)
		{
			status[*i].status = Todo;
		}
		return;
	}

	// Add generic rules to the correct set.
	if (generic)
	{
		if (assignment) goto error;
		generic_rules.push_back(rule);
		return;
	}

	if (!rule.script.empty())
	{
		if (assignment) goto error;
		register_scripted_rule(rule);
	}
	else
	{
		// Swap away the targets to avoid costly copies when registering.
		string_list targets;
		std::swap(rule.targets, targets);
		register_transparent_rule(rule, targets);
		std::swap(rule.targets, targets);
	}

	// If there is no default target yet, mark it as such.
	if (first_target.empty())
		first_target = rule.targets.front();
}

/**
 * Load rules from @a remakefile.
 * If some rules have dependencies and non-generic targets, add these
 * dependencies to the targets.
 */
static void load_rules(std::string const &remakefile)
{
	DEBUG_open << "Loading rules... ";
	if (false)
	{
		error:
		std::cerr << "Failed to load rules: syntax error" << std::endl;
		exit(EXIT_FAILURE);
	}
	std::ifstream in(remakefile.c_str());
	if (!in.good())
	{
		std::cerr << "Failed to load rules: no Remakefile found" << std::endl;
		exit(EXIT_FAILURE);
	}
	skip_empty(in);

	string_list options;

	// Read rules
	while (in.good())
	{
		char c = in.peek();
		if (c == '#')
		{
			while (in.get() != '\n') {}
			skip_empty(in);
			continue;
		}
		if (c == ' ' || c == '\t') goto error;
		if (expect_token(in, Word))
		{
			std::string name = read_word(in);
			if (name.empty()) goto error;
			if (int tok = expect_token(in, Equal | Plusequal))
			{
				DEBUG << "Assignment to variable " << name << std::endl;
				string_list value;
				if (!read_words(in, value)) goto error;
				string_list &dest =
					*(name == ".OPTIONS" ? &options : &variables[name]);
				if (tok == Equal) dest.swap(value);
				else dest.splice(dest.end(), value);
				if (!skip_eol(in, true)) goto error;
			}
			else load_rule(in, name);
		}
		else load_rule(in, std::string());
	}

	// Set actual options.
	for (string_list::const_iterator i = options.begin(),
	     i_end = options.end(); i != i_end; ++i)
	{
		if (*i == "variable-propagation") propagate_vars = true;
		else
		{
			std::cerr << "Failed to load rules: unrecognized option" << std::endl;
			exit(EXIT_FAILURE);
		}
	}
}

/** @} */

/**
 * @defgroup rules Rule resolution
 *
 * @{
 */

static void merge_rule(rule_t &dest, rule_t const &src)
{
	dest.deps.insert(dest.deps.end(), src.deps.begin(), src.deps.end());
	dest.wdeps.insert(dest.wdeps.end(), src.wdeps.begin(), src.wdeps.end());
	for (assign_map::const_iterator i = src.assigns.begin(),
	     i_end = src.assigns.end(); i != i_end; ++i)
	{
		if (!i->second.append)
		{
			new_assign:
			dest.assigns[i->first] = i->second;
			continue;
		}
		assign_map::iterator j = dest.assigns.find(i->first);
		if (j == dest.assigns.end()) goto new_assign;
		j->second.value.insert(j->second.value.end(),
			i->second.value.begin(), i->second.value.end());
	}
}

/**
 * Substitute a pattern into a list of strings.
 */
static void substitute_pattern(std::string const &pat, string_list const &src, string_list &dst)
{
	for (string_list::const_iterator i = src.begin(),
	     i_end = src.end(); i != i_end; ++i)
	{
		size_t pos = i->find('%');
		if (pos == std::string::npos) dst.push_back(*i);
		else dst.push_back(i->substr(0, pos) + pat + i->substr(pos + 1));
	}
}

/**
 * Find a generic rule matching @a target:
 * - the one leading to shorter matches has priority,
 * - among equivalent rules, the earliest one has priority.
 */
static void find_generic_rule(job_t &job, std::string const &target)
{
	size_t tlen = target.length(), plen = tlen + 1;
	for (rule_list::const_iterator i = generic_rules.begin(),
	     i_end = generic_rules.end(); i != i_end; ++i)
	{
		for (string_list::const_iterator j = i->targets.begin(),
		     j_end = i->targets.end(); j != j_end; ++j)
		{
			size_t len = j->length();
			if (tlen < len) continue;
			if (plen <= tlen - (len - 1)) continue;
			size_t pos = j->find('%');
			if (pos == std::string::npos) continue;
			size_t len2 = len - (pos + 1);
			if (j->compare(0, pos, target, 0, pos) ||
			    j->compare(pos + 1, len2, target, tlen - len2, len2))
				continue;
			plen = tlen - (len - 1);
			job.stem = target.substr(pos, plen);
			job.rule = rule_t();
			job.rule.script = i->script;
			substitute_pattern(job.stem, i->targets, job.rule.targets);
			substitute_pattern(job.stem, i->deps, job.rule.deps);
			substitute_pattern(job.stem, i->wdeps, job.rule.wdeps);
			break;
		}
	}
}

/**
 * Find a specific rule matching @a target. Return a generic one otherwise.
 * If there is both a specific rule with an empty script and a generic rule, the
 * generic one is returned after adding the dependencies of the specific one.
 */
static void find_rule(job_t &job, std::string const &target)
{
	rule_map::const_iterator i = specific_rules.find(target),
		i_end = specific_rules.end();
	// If there is a specific rule with a script, return it.
	if (i != i_end && !i->second->script.empty())
	{
		job.rule = *i->second;
		return;
	}
	find_generic_rule(job, target);
	// If there is no generic rule, return the specific rule (no script), if any.
	if (job.rule.targets.empty())
	{
		if (i != i_end)
		{
			job.rule = *i->second;
			return;
		}
	}
	// Optimize the lookup when there is only one target (already looked up).
	if (job.rule.targets.size() == 1)
	{
		if (i == i_end) return;
		merge_rule(job.rule, *i->second);
		return;
	}
	// Add the dependencies of the specific rules of every target to the
	// generic rule. If any of those rules has a nonempty script, error out.
	for (string_list::const_iterator j = job.rule.targets.begin(),
	     j_end = job.rule.targets.end(); j != j_end; ++j)
	{
		i = specific_rules.find(*j);
		if (i == i_end) continue;
		if (!i->second->script.empty()) return;
		merge_rule(job.rule, *i->second);
	}
}

/** @} */

/**
 * @defgroup status Target status
 *
 * @{
 */

/**
 * Compute and memoize the status of @a target:
 * - if the file does not exist, the target is obsolete,
 * - if any dependency is obsolete or younger than the file, it is obsolete,
 * - otherwise it is up-to-date.
 *
 * @note For rules with multiple targets, all the targets share the same
 *       status. (If one is obsolete, they all are.) The second rule above
 *       is modified in that case: the latest target is chosen, not the oldest!
 */
static status_t const &get_status(std::string const &target)
{
	std::pair<status_map::iterator,bool> i =
		status.insert(std::make_pair(target, status_t()));
	status_t &ts = i.first->second;
	if (!i.second) return ts;
	DEBUG_open << "Checking status of " << target << "... ";
	dependency_map::const_iterator j = dependencies.find(target);
	if (j == dependencies.end())
	{
		struct stat s;
		if (stat(target.c_str(), &s) != 0)
		{
			DEBUG_close << "missing\n";
			ts.status = Todo;
			ts.last = 0;
			return ts;
		}
		DEBUG_close << "up-to-date\n";
		ts.status = Uptodate;
		ts.last = s.st_mtime;
		return ts;
	}
	if (obsolete_targets)
	{
		DEBUG_close << "forcefully obsolete\n";
		ts.status = Todo;
		ts.last = 0;
		return ts;
	}
	dependency_t const &dep = *j->second;
	status_e st = Uptodate;
	time_t latest = 0;
	for (string_list::const_iterator k = dep.targets.begin(),
	     k_end = dep.targets.end(); k != k_end; ++k)
	{
		struct stat s;
		if (stat(k->c_str(), &s) != 0)
		{
			if (st == Uptodate) DEBUG_close << *k << " missing\n";
			s.st_mtime = 0;
			st = Todo;
		}
		status[*k].last = s.st_mtime;
		if (s.st_mtime > latest) latest = s.st_mtime;
	}
	if (st != Uptodate) goto update;
	for (string_set::const_iterator k = dep.deps.begin(),
	     k_end = dep.deps.end(); k != k_end; ++k)
	{
		status_t const &ts_ = get_status(*k);
		if (latest < ts_.last)
		{
			DEBUG_close << "older than " << *k << std::endl;
			st = Todo;
			goto update;
		}
		if (ts_.status != Uptodate && st != Recheck)
		{
			DEBUG << "obsolete dependency " << *k << std::endl;
			st = Recheck;
		}
	}
	if (st == Uptodate) DEBUG_close << "all siblings up-to-date\n";
	update:
	for (string_list::const_iterator k = dep.targets.begin(),
	     k_end = dep.targets.end(); k != k_end; ++k)
	{
		status[*k].status = st;
	}
	return ts;
}

/**
 * Change the status of @a target to #Remade or #Uptodate depending on whether
 * its modification time changed.
 */
static void update_status(std::string const &target)
{
	DEBUG_open << "Rechecking status of " << target << "... ";
	status_map::iterator i = status.find(target);
	assert(i != status.end());
	status_t &ts = i->second;
	ts.status = Remade;
	if (ts.last >= now)
	{
		DEBUG_close << "possibly remade\n";
		return;
	}
	struct stat s;
	if (stat(target.c_str(), &s) != 0)
	{
		DEBUG_close << "missing\n";
		ts.last = 0;
	}
	else if (s.st_mtime != ts.last)
	{
		DEBUG_close << "remade\n";
		ts.last = s.st_mtime;
	}
	else
	{
		DEBUG_close << "unchanged\n";
		ts.status = Uptodate;
	}
}

/**
 * Check whether all the prerequisites of @a target ended being up-to-date.
 */
static bool still_need_rebuild(std::string const &target)
{
	status_map::const_iterator i = status.find(target);
	assert(i != status.end());
	if (i->second.status != RunningRecheck) return true;
	DEBUG_open << "Rechecking obsoleteness of " << target << "... ";
	dependency_map::const_iterator j = dependencies.find(target);
	assert(j != dependencies.end());
	dependency_t const &dep = *j->second;
	for (string_set::const_iterator k = dep.deps.begin(),
	     k_end = dep.deps.end(); k != k_end; ++k)
	{
		if (status[*k].status != Uptodate) return true;
	}
	for (string_list::const_iterator k = dep.targets.begin(),
	     k_end = dep.targets.end(); k != k_end; ++k)
	{
		status[*k].status = Uptodate;
	}
	DEBUG_close << "no longer obsolete\n";
	return false;
}

/** @} */

/**
 * @defgroup server Server
 *
 * @{
 */

/**
 * Handle job completion.
 */
static void complete_job(int job_id, bool success, bool started = true)
{
	DEBUG << "Completing job " << job_id << '\n';
	job_map::iterator i = jobs.find(job_id);
	assert(i != jobs.end());
	string_list const &targets = i->second.rule.targets;
	if (success)
	{
		bool show = show_targets && started;
		if (show) std::cout << "Finished";
		for (string_list::const_iterator j = targets.begin(),
		     j_end = targets.end(); j != j_end; ++j)
		{
			update_status(*j);
			if (show) std::cout << ' ' << *j;
		}
		if (show) std::cout << std::endl;
	}
	else
	{
		std::cerr << "Failed to build";
		for (string_list::const_iterator j = targets.begin(),
		     j_end = targets.end(); j != j_end; ++j)
		{
			std::cerr << ' ' << *j;
			update_status(*j);
			status_e &s = status[*j].status;
			if (s != Uptodate)
			{
				DEBUG << "Removing " << *j << '\n';
				remove(j->c_str());
			}
			s = Failed;
		}
		std::cerr << std::endl;
	}
	jobs.erase(i);
}

/**
 * Return the script obtained by substituting variables.
 */
static std::string prepare_script(job_t const &job)
{
	std::string const &s = job.rule.script;
	std::istringstream in(s);
	std::ostringstream out;
	size_t len = s.size();

	while (!in.eof())
	{
		size_t pos = in.tellg(), p = s.find('$', pos);
		if (p == std::string::npos || p == len - 1) p = len;
		out.write(&s[pos], p - pos);
		if (p == len) break;
		++p;
		switch (s[p])
		{
		case '$':
			out << '$';
			in.seekg(p + 1);
			break;
		case '<':
			if (!job.rule.deps.empty())
				out << job.rule.deps.front();
			in.seekg(p + 1);
			break;
		case '^':
		{
			bool first = true;
			for (string_list::const_iterator i = job.rule.deps.begin(),
			     i_end = job.rule.deps.end(); i != i_end; ++i)
			{
				if (first) first = false;
				else out << ' ';
				out << *i;
			}
			in.seekg(p + 1);
			break;
		}
		case '@':
			assert(!job.rule.targets.empty());
			out << job.rule.targets.front();
			in.seekg(p + 1);
			break;
		case '*':
			out << job.stem;
			in.seekg(p + 1);
			break;
		case '(':
		{
			in.seekg(p - 1);
			bool first = true;
			input_generator gen(in, &job.vars, true);
			while (true)
			{
				std::string w;
				input_status s = gen.next(w);
				if (s == SyntaxError)
				{
					// TODO
					return "false";
				}
				if (s == Eof) break;
				if (first) first = false;
				else out << ' ';
				out << w;
			}
			break;
		}
		default:
			// Let dollars followed by an unrecognized character
			// go through. This differs from Make, which would
			// use a one-letter variable.
			out << '$';
			in.seekg(p);
		}
	}

	return out.str();
}

/**
 * Execute the script from @a rule.
 */
static status_e run_script(int job_id, job_t const &job)
{
	ref_ptr<dependency_t> dep;
	dep->targets = job.rule.targets;
	dep->deps.insert(job.rule.deps.begin(), job.rule.deps.end());
	if (show_targets) std::cout << "Building";
	for (string_list::const_iterator i = job.rule.targets.begin(),
	     i_end = job.rule.targets.end(); i != i_end; ++i)
	{
		dependencies[*i] = dep;
		if (show_targets) std::cout << ' ' << *i;
	}
	if (show_targets) std::cout << std::endl;

	std::string script = prepare_script(job);

	std::ostringstream job_id_buf;
	job_id_buf << job_id;
	std::string job_id_ = job_id_buf.str();

	DEBUG_open << "Starting script for job " << job_id << "... ";
	if (script.empty())
	{
		DEBUG_close << "no script\n";
		complete_job(job_id, true);
		return Remade;
	}

	if (false)
	{
		error:
		DEBUG_close << "failed\n";
		complete_job(job_id, false);
		return Failed;
	}

#ifdef WINDOWS
	HANDLE pfd[2];
	if (false)
	{
		error2:
		CloseHandle(pfd[0]);
		CloseHandle(pfd[1]);
		goto error;
	}
	if (!CreatePipe(&pfd[0], &pfd[1], NULL, 0))
		goto error;
	if (!SetHandleInformation(pfd[0], HANDLE_FLAG_INHERIT, HANDLE_FLAG_INHERIT))
		goto error2;
	STARTUPINFO si;
	ZeroMemory(&si, sizeof(STARTUPINFO));
	si.cb = sizeof(STARTUPINFO);
	si.hStdError = GetStdHandle(STD_ERROR_HANDLE);
	si.hStdOutput = GetStdHandle(STD_OUTPUT_HANDLE);
	si.hStdInput = pfd[0];
	si.dwFlags |= STARTF_USESTDHANDLES;
	PROCESS_INFORMATION pi;
	ZeroMemory(&pi, sizeof(PROCESS_INFORMATION));
	if (!SetEnvironmentVariable("REMAKE_JOB_ID", job_id_.c_str()))
		goto error2;
	char const *argv = echo_scripts ? "SH.EXE -e -s -v" : "SH.EXE -e -s";
	if (!CreateProcess(NULL, (char *)argv, NULL, NULL,
	    true, 0, NULL, NULL, &si, &pi))
	{
		goto error2;
	}
	CloseHandle(pi.hThread);
	DWORD len = script.length(), wlen;
	if (!WriteFile(pfd[1], script.c_str(), len, &wlen, NULL) || wlen < len)
		std::cerr << "Unexpected failure while sending script to shell" << std::endl;
	CloseHandle(pfd[0]);
	CloseHandle(pfd[1]);
	++running_jobs;
	job_pids[pi.hProcess] = job_id;
	return Running;
#else
	int pfd[2];
	if (false)
	{
		error2:
		close(pfd[0]);
		close(pfd[1]);
		goto error;
	}
	if (pipe(pfd) == -1)
		goto error;
	if (setenv("REMAKE_JOB_ID", job_id_.c_str(), 1))
		goto error2;
	if (pid_t pid = vfork())
	{
		if (pid == -1) goto error2;
		ssize_t len = script.length();
		if (write(pfd[1], script.c_str(), len) < len)
			std::cerr << "Unexpected failure while sending script to shell" << std::endl;
		close(pfd[0]);
		close(pfd[1]);
		++running_jobs;
		job_pids[pid] = job_id;
		return Running;
	}
	// Child process starts here. Notice the use of vfork above.
	char const *argv[5] = { "sh", "-e", "-s", NULL, NULL };
	if (echo_scripts) argv[3] = "-v";
	close(pfd[1]);
	if (pfd[0] != 0)
	{
		dup2(pfd[0], 0);
		close(pfd[0]);
	}
	execve("/bin/sh", (char **)argv, environ);
	_exit(EXIT_FAILURE);
#endif
}

/**
 * Create a job for @a target according to the loaded rules.
 * Mark all the targets from the rule as running and reset their dependencies.
 * Inherit variables from @a current, if enabled.
 * If the rule has dependencies, create a new client to build them just
 * before @a current, and change @a current so that it points to it.
 */
static status_e start(std::string const &target, client_list::iterator &current)
{
	int job_id = job_counter++;
	DEBUG_open << "Starting job " << job_id << " for " << target << "... ";
	job_t &job = jobs[job_id];
	find_rule(job, target);
	if (job.rule.targets.empty())
	{
		status[target].status = Failed;
		DEBUG_close << "failed\n";
		std::cerr << "No rule for building " << target << std::endl;
		return Failed;
	}
	bool has_deps = !job.rule.deps.empty() || !job.rule.wdeps.empty();
	status_e st = Running;
	if (has_deps && status[target].status == Recheck)
		st = RunningRecheck;
	for (string_list::const_iterator i = job.rule.targets.begin(),
	     i_end = job.rule.targets.end(); i != i_end; ++i)
	{
		status[*i].status = st;
	}
	if (propagate_vars) job.vars = current->vars;
	for (assign_map::const_iterator i = job.rule.assigns.begin(),
	     i_end = job.rule.assigns.end(); i != i_end; ++i)
	{
		std::pair<variable_map::iterator, bool> k =
			job.vars.insert(std::make_pair(i->first, string_list()));
		string_list &v = k.first->second;
		if (i->second.append)
		{
			if (k.second)
			{
				variable_map::const_iterator j = variables.find(i->first);
				if (j != variables.end()) v = j->second;
			}
		}
		else if (!k.second) v.clear();
		v.insert(v.end(), i->second.value.begin(), i->second.value.end());
	}
	if (has_deps)
	{
		current = clients.insert(current, client_t());
		current->job_id = job_id;
		current->pending = job.rule.deps;
		current->pending.insert(current->pending.end(),
			job.rule.wdeps.begin(), job.rule.wdeps.end());
		if (propagate_vars) current->vars = job.vars;
		current->delayed = true;
		return RunningRecheck;
	}
	return run_script(job_id, job);
}

/**
 * Send a reply to a client then remove it.
 * If the client was a dependency client, start the actual script.
 */
static void complete_request(client_t &client, bool success)
{
	DEBUG_open << "Completing request from client of job " << client.job_id << "... ";
	if (client.delayed)
	{
		assert(client.socket == INVALID_SOCKET);
		if (success)
		{
			job_map::const_iterator i = jobs.find(client.job_id);
			assert(i != jobs.end());
			if (still_need_rebuild(i->second.rule.targets.front()))
				run_script(client.job_id, i->second);
			else complete_job(client.job_id, true, false);
		}
		else complete_job(client.job_id, false);
	}
	else if (client.socket != INVALID_SOCKET)
	{
		char res = success ? 1 : 0;
		send(client.socket, &res, 1, MSG_NOSIGNAL);
	#ifdef WINDOWS
		closesocket(client.socket);
	#else
		close(client.socket);
	#endif
		--waiting_jobs;
	}

	if (client.job_id < 0 && !success) build_failure = true;
}

/**
 * Return whether there are slots for starting new jobs.
 */
static bool has_free_slots()
{
	if (max_active_jobs <= 0) return true;
	return running_jobs - waiting_jobs < max_active_jobs;
}

/**
 * Handle client requests:
 * - check for running targets that have finished,
 * - start as many pending targets as allowed,
 * - complete the request if there are neither running nor pending targets
 *   left or if any of them failed.
 *
 * @return true if some child processes are still running.
 *
 * @post If there are pending requests, at least one child process is running.
 *
 * @invariant New free slots cannot appear during a run, since the only way to
 *            decrease #running_jobs is #finalize_job and the only way to
 *            increase #waiting_jobs is #accept_client. None of these functions
 *            are called during a run. So breaking out as soon as there no free
 *            slots left is fine.
 */
static bool handle_clients()
{
	DEBUG_open << "Handling client requests... ";
	restart:
	bool need_restart = false;

	for (client_list::iterator i = clients.begin(), i_next = i,
	     i_end = clients.end(); i != i_end && has_free_slots(); i = i_next)
	{
		++i_next;
		DEBUG_open << "Handling client from job " << i->job_id << "... ";

		// Remove running targets that have finished.
		for (string_set::iterator j = i->running.begin(), j_next = j,
		     j_end = i->running.end(); j != j_end; j = j_next)
		{
			++j_next;
			status_map::const_iterator k = status.find(*j);
			assert(k != status.end());
			switch (k->second.status)
			{
			case Running:
			case RunningRecheck:
				break;
			case Failed:
				i->failed = true;
				if (!keep_going) goto complete;
				// no break
			case Uptodate:
			case Remade:
				i->running.erase(j);
				break;
			case Recheck:
			case Todo:
				assert(false);
			}
		}

		// Start pending targets.
		while (!i->pending.empty())
		{
			std::string target = i->pending.front();
			i->pending.pop_front();
			switch (get_status(target).status)
			{
			case Running:
			case RunningRecheck:
				i->running.insert(target);
				break;
			case Failed:
				pending_failed:
				i->failed = true;
				if (!keep_going) goto complete;
				// no break
			case Uptodate:
			case Remade:
				break;
			case Recheck:
			case Todo:
				client_list::iterator j = i;
				switch (start(target, i))
				{
				case Failed:
					goto pending_failed;
				case Running:
					// A shell was started, check for free slots.
					j->running.insert(target);
					if (!has_free_slots()) return true;
					break;
				case RunningRecheck:
					// Switch to the dependency client that was inserted.
					j->running.insert(target);
					i_next = j;
					break;
				case Remade:
					// Nothing to run.
					need_restart = true;
					break;
				default:
					assert(false);
				}
			}
		}

		// Try to complete the request.
		// (This might start a new job if it was a dependency client.)
		if (i->running.empty() || i->failed)
		{
			complete:
			complete_request(*i, !i->failed);
			DEBUG_close << (i->failed ? "failed\n" : "finished\n");
			clients.erase(i);
			need_restart = true;
		}
	}

	if (running_jobs != waiting_jobs) return true;
	if (running_jobs == 0 && clients.empty()) return false;
	if (need_restart) goto restart;

	// There is a circular dependency.
	// Try to break it by completing one of the requests.
	assert(!clients.empty());
	std::cerr << "Circular dependency detected" << std::endl;
	client_list::iterator i = clients.begin();
	complete_request(*i, false);
	clients.erase(i);
	goto restart;
}

/**
 * Create a named unix socket that listens for build requests. Also set
 * the REMAKE_SOCKET environment variable that will be inherited by all
 * the job scripts.
 */
static void create_server()
{
	if (false)
	{
		error:
		perror("Failed to create server");
#ifndef WINDOWS
		error2:
#endif
		exit(EXIT_FAILURE);
	}
	DEBUG_open << "Creating server... ";

#ifdef WINDOWS
	// Prepare a windows socket.
	struct sockaddr_in socket_addr;
	socket_addr.sin_family = AF_INET;
	socket_addr.sin_addr.s_addr = inet_addr("127.0.0.1");
	socket_addr.sin_port = 0;

	// Create and listen to the socket.
	socket_fd = socket(AF_INET, SOCK_STREAM, 0);
	if (socket_fd == INVALID_SOCKET) goto error;
	if (!SetHandleInformation((HANDLE)socket_fd, HANDLE_FLAG_INHERIT, 0))
		goto error;
	if (bind(socket_fd, (struct sockaddr *)&socket_addr, sizeof(sockaddr_in)))
		goto error;
	int len = sizeof(sockaddr_in);
	if (getsockname(socket_fd, (struct sockaddr *)&socket_addr, &len))
		goto error;
	std::ostringstream buf;
	buf << socket_addr.sin_port;
	if (!SetEnvironmentVariable("REMAKE_SOCKET", buf.str().c_str()))
		goto error;
	if (listen(socket_fd, 1000)) goto error;
#else
	// Set signal handlers for SIGCHLD and SIGINT.
	// Block SIGCHLD (unblocked during select).
	sigset_t sigmask;
	sigemptyset(&sigmask);
	sigaddset(&sigmask, SIGCHLD);
	if (sigprocmask(SIG_BLOCK, &sigmask, NULL) == -1) goto error;
	struct sigaction sa;
	sa.sa_flags = 0;
	sigemptyset(&sa.sa_mask);
	sa.sa_handler = &sigchld_handler;
	if (sigaction(SIGCHLD, &sa, NULL) == -1) goto error;
	sa.sa_handler = &sigint_handler;
	if (sigaction(SIGINT, &sa, NULL) == -1) goto error;

	// Prepare a named unix socket in temporary directory.
	socket_name = tempnam(NULL, "rmk-");
	if (!socket_name) goto error2;
	struct sockaddr_un socket_addr;
	size_t len = strlen(socket_name);
	if (len >= sizeof(socket_addr.sun_path) - 1) goto error2;
	socket_addr.sun_family = AF_UNIX;
	strcpy(socket_addr.sun_path, socket_name);
	len += sizeof(socket_addr.sun_family);
	if (setenv("REMAKE_SOCKET", socket_name, 1)) goto error;

	// Create and listen to the socket.
#ifdef LINUX
	socket_fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
	if (socket_fd == INVALID_SOCKET) goto error;
#else
	socket_fd = socket(AF_UNIX, SOCK_STREAM, 0);
	if (socket_fd == INVALID_SOCKET) goto error;
	if (fcntl(socket_fd, F_SETFD, FD_CLOEXEC) < 0) goto error;
#endif
	if (bind(socket_fd, (struct sockaddr *)&socket_addr, len))
		goto error;
	if (listen(socket_fd, 1000)) goto error;
#endif
}

/**
 * Accept a connection from a client, get the job it spawned from,
 * get the targets, and mark them as dependencies of the job targets.
 */
static void accept_client()
{
	DEBUG_open << "Handling client request... ";

	// Accept connection.
#ifdef WINDOWS
	socket_t fd = accept(socket_fd, NULL, NULL);
	if (fd == INVALID_SOCKET) return;
	if (!SetHandleInformation((HANDLE)fd, HANDLE_FLAG_INHERIT, 0))
	{
		error2:
		std::cerr << "Unexpected failure while setting connection with client" << std::endl;
		closesocket(fd);
		return;
	}
	// WSAEventSelect puts sockets into nonblocking mode, so disable it here.
	u_long nbio = 0;
	if (ioctlsocket(fd, FIONBIO, &nbio)) goto error2;
#elif defined(LINUX)
	int fd = accept4(socket_fd, NULL, NULL, SOCK_CLOEXEC);
	if (fd < 0) return;
#else
	int fd = accept(socket_fd, NULL, NULL);
	if (fd < 0) return;
	if (fcntl(fd, F_SETFD, FD_CLOEXEC) < 0) return;
#endif
	clients.push_front(client_t());
	client_list::iterator proc = clients.begin();

	if (false)
	{
		error:
		DEBUG_close << "failed\n";
		std::cerr << "Received an ill-formed client message" << std::endl;
	#ifdef WINDOWS
		closesocket(fd);
	#else
		close(fd);
	#endif
		clients.erase(proc);
		return;
	}

	// Receive message. Stop when encountering two nuls in a row.
	std::vector<char> buf;
	size_t len = 0;
	while (len < sizeof(int) + 2 || buf[len - 1] || buf[len - 2])
	{
		buf.resize(len + 1024);
		ssize_t l = recv(fd, &buf[0] + len, 1024, 0);
		if (l <= 0) goto error;
		len += l;
	}

	// Parse job that spawned the client.
	int job_id;
	memcpy(&job_id, &buf[0], sizeof(int));
	proc->socket = fd;
	proc->job_id = job_id;
	job_map::const_iterator i = jobs.find(job_id);
	if (i == jobs.end()) goto error;
	DEBUG << "receiving request from job " << job_id << std::endl;
	if (propagate_vars) proc->vars = i->second.vars;

	// Parse the targets and the variable assignments.
	// Mark the targets as dependencies of the job targets.
	dependency_t &dep = *dependencies[i->second.rule.targets.front()];
	string_list *last_var = NULL;
	char const *p = &buf[0] + sizeof(int);
	while (true)
	{
		len = strlen(p);
		if (len == 0)
		{
			++waiting_jobs;
			break;
		}
		switch (*p)
		{
		case 'T':
		{
			if (len == 1) goto error;
			std::string target(p + 1, p + len);
			DEBUG << "adding dependency " << target << " to job\n";
			proc->pending.push_back(target);
			dep.deps.insert(target);
			break;
		}
		case 'V':
		{
			if (len == 1) goto error;
			std::string var(p + 1, p + len);
			DEBUG << "adding variable " << var << " to job\n";
			last_var = &proc->vars[var];
			last_var->clear();
			break;
		}
		case 'W':
		{
			if (!last_var) goto error;
			last_var->push_back(std::string(p + 1, p + len));
			break;
		}
		default:
			goto error;
		}
		p += len + 1;
	}

	if (!propagate_vars && !proc->vars.empty())
	{
		std::cerr << "Assignments are ignored unless 'variable-propagation' is enabled" << std::endl;
		proc->vars.clear();
	}
}

/**
 * Handle child process exit status.
 */
static void finalize_job(pid_t pid, bool res)
{
	pid_job_map::iterator i = job_pids.find(pid);
	assert(i != job_pids.end());
	int job_id = i->second;
	job_pids.erase(i);
	--running_jobs;
	complete_job(job_id, res);
}

/**
 * Loop until all the jobs have finished.
 *
 * @post There are no client requests left, not even virtual ones.
 */
static void server_loop()
{
	while (handle_clients())
	{
		DEBUG_open << "Handling events... ";
	#ifdef WINDOWS
		size_t len = job_pids.size() + 1;
		HANDLE h[len];
		int num = 0;
		for (pid_job_map::const_iterator i = job_pids.begin(),
		     i_end = job_pids.end(); i != i_end; ++i, ++num)
		{
			h[num] = i->first;
		}
		WSAEVENT aev = WSACreateEvent();
		h[num] = aev;
		WSAEventSelect(socket_fd, aev, FD_ACCEPT);
		DWORD w = WaitForMultipleObjects(len, h, false, INFINITE);
		WSAEventSelect(socket_fd, aev, 0);
		WSACloseEvent(aev);
		if (len <= w)
			continue;
		if (w == len - 1)
		{
			accept_client();
			continue;
		}
		pid_t pid = h[w];
		DWORD s = 0;
		bool res = GetExitCodeProcess(pid, &s) && s == 0;
		CloseHandle(pid);
		finalize_job(pid, res);
	#else
		sigset_t emptymask;
		sigemptyset(&emptymask);
		fd_set fdset;
		FD_ZERO(&fdset);
		FD_SET(socket_fd, &fdset);
		int ret = pselect(socket_fd + 1, &fdset, NULL, NULL, NULL, &emptymask);
		if (ret > 0 /* && FD_ISSET(socket_fd, &fdset)*/) accept_client();
		if (!got_SIGCHLD) continue;
		got_SIGCHLD = 0;
		pid_t pid;
		int status;
		while ((pid = waitpid(-1, &status, WNOHANG)) > 0)
		{
			bool res = WIFEXITED(status) && WEXITSTATUS(status) == 0;
			finalize_job(pid, res);
		}
	#endif
	}

	assert(clients.empty());
}

/**
 * Load dependencies and rules, listen to client requests, and loop until
 * all the requests have completed.
 * If Remakefile is obsolete, perform a first run with it only, then reload
 * the rules, and perform a second with the original clients.
 */
static void server_mode(std::string const &remakefile, string_list const &targets)
{
	load_dependencies();
	load_rules(remakefile);
	create_server();
	if (get_status(remakefile).status != Uptodate)
	{
		clients.push_back(client_t());
		clients.back().pending.push_back(remakefile);
		server_loop();
		if (build_failure) goto early_exit;
		variables.clear();
		specific_rules.clear();
		generic_rules.clear();
		first_target.clear();
		load_rules(remakefile);
	}
	clients.push_back(client_t());
	if (!targets.empty()) clients.back().pending = targets;
	else if (!first_target.empty())
		clients.back().pending.push_back(first_target);
	server_loop();
	early_exit:
	close(socket_fd);
#ifndef WINDOWS
	remove(socket_name);
	free(socket_name);
#endif
	save_dependencies();
	if (show_targets && changed_prefix_dir)
	{
		std::cout << "remake: Leaving directory `" << prefix_dir << '\'' << std::endl;
	}
	exit(build_failure ? EXIT_FAILURE : EXIT_SUCCESS);
}

/** @} */

/**
 * @defgroup client Client
 *
 * @{
 */

/**
 * Connect to the server @a socket_name, send a request for building @a targets
 * with some @a variables, and exit with the status returned by the server.
 */
static void client_mode(char *socket_name, string_list const &targets)
{
	if (false)
	{
		error:
		perror("Failed to send targets to server");
		exit(EXIT_FAILURE);
	}
	if (targets.empty()) exit(EXIT_SUCCESS);
	DEBUG_open << "Connecting to server... ";

	// Connect to server.
#ifdef WINDOWS
	struct sockaddr_in socket_addr;
	socket_fd = socket(AF_INET, SOCK_STREAM, 0);
	if (socket_fd == INVALID_SOCKET) goto error;
	socket_addr.sin_family = AF_INET;
	socket_addr.sin_addr.s_addr = inet_addr("127.0.0.1");
	socket_addr.sin_port = atoi(socket_name);
	if (connect(socket_fd, (struct sockaddr *)&socket_addr, sizeof(sockaddr_in)))
		goto error;
#else
	struct sockaddr_un socket_addr;
	size_t len = strlen(socket_name);
	if (len >= sizeof(socket_addr.sun_path) - 1) exit(EXIT_FAILURE);
	socket_fd = socket(AF_UNIX, SOCK_STREAM, 0);
	if (socket_fd == INVALID_SOCKET) goto error;
	socket_addr.sun_family = AF_UNIX;
	strcpy(socket_addr.sun_path, socket_name);
	if (connect(socket_fd, (struct sockaddr *)&socket_addr, sizeof(socket_addr.sun_family) + len))
		goto error;
#ifdef MACOSX
	int set_option = 1;
	if (setsockopt(socket_fd, SOL_SOCKET, SO_NOSIGPIPE, &set_option, sizeof(set_option)))
		goto error;
#endif
#endif

	// Send current job id.
	char *id = getenv("REMAKE_JOB_ID");
	int job_id = id ? atoi(id) : -1;
	if (send(socket_fd, (char *)&job_id, sizeof(job_id), MSG_NOSIGNAL) != sizeof(job_id))
		goto error;

	// Send targets.
	for (string_list::const_iterator i = targets.begin(),
	     i_end = targets.end(); i != i_end; ++i)
	{
		DEBUG_open << "Sending target " << *i << "... ";
		std::string s = 'T' + *i;
		ssize_t len = s.length() + 1;
		if (send(socket_fd, s.c_str(), len, MSG_NOSIGNAL) != len)
			goto error;
	}

	// Send variables.
	for (variable_map::const_iterator i = variables.begin(),
	     i_end = variables.end(); i != i_end; ++i)
	{
		DEBUG_open << "Sending variable " << i->first << "... ";
		std::string s = 'V' + i->first;
		ssize_t len = s.length() + 1;
		if (send(socket_fd, s.c_str(), len, MSG_NOSIGNAL) != len)
			goto error;
		for (string_list::const_iterator j = i->second.begin(),
		     j_end = i->second.end(); j != j_end; ++j)
		{
			std::string s = 'W' + *j;
			len = s.length() + 1;
			if (send(socket_fd, s.c_str(), len, MSG_NOSIGNAL) != len)
				goto error;
		}
	}

	// Send terminating nul and wait for reply.
	char result = 0;
	if (send(socket_fd, &result, 1, MSG_NOSIGNAL) != 1) goto error;
	if (recv(socket_fd, &result, 1, 0) != 1) exit(EXIT_FAILURE);
	exit(result ? EXIT_SUCCESS : EXIT_FAILURE);
}

/** @} */

/**
 * @defgroup ui User interface
 *
 * @{
 */

/**
 * Display usage and exit with @a exit_status.
 */
static void usage(int exit_status)
{
	std::cerr << "Usage: remake [options] [target] ...\n"
		"Options\n"
		"  -B, --always-make      Unconditionally make all targets.\n"
		"  -d                     Echo script commands.\n"
		"  -d -d                  Print lots of debugging information.\n"
		"  -f FILE                Read FILE as Remakefile.\n"
		"  -h, --help             Print this message and exit.\n"
		"  -j[N], --jobs=[N]      Allow N jobs at once; infinite jobs with no arg.\n"
		"  -k, --keep-going       Keep going when some targets cannot be made.\n"
		"  -r                     Look up targets from the dependencies on stdin.\n"
		"  -s, --silent, --quiet  Do not echo targets.\n";
	exit(exit_status);
}

/**
 * This program behaves in two different ways.
 *
 * - If the environment contains the REMAKE_SOCKET variable, the client
 *   connects to this socket and sends to the server its build targets.
 *   It exits once it receives the server reply.
 *
 * - Otherwise, it creates a server that waits for build requests. It
 *   also creates a pseudo-client that requests the targets passed on the
 *   command line.
 */
int main(int argc, char *argv[])
{
	std::string remakefile;
	string_list targets;
	bool literal_targets = false;
	bool indirect_targets = false;

	// Parse command-line arguments.
	for (int i = 1; i < argc; ++i)
	{
		std::string arg = argv[i];
		if (arg.empty()) usage(EXIT_FAILURE);
		if (literal_targets) goto new_target;
		if (arg == "-h" || arg == "--help") usage(EXIT_SUCCESS);
		if (arg == "-d")
			if (echo_scripts) debug.active = true;
			else echo_scripts = true;
		else if (arg == "-k" || arg =="--keep-going")
			keep_going = true;
		else if (arg == "-s" || arg == "--silent" || arg == "--quiet")
			show_targets = false;
		else if (arg == "-r")
			indirect_targets = true;
		else if (arg == "-B" || arg == "--always-make")
			obsolete_targets = true;
		else if (arg == "-f")
		{
			if (++i == argc) usage(EXIT_FAILURE);
			remakefile = argv[i];
		}
		else if (arg == "--")
			literal_targets = true;
		else if (arg.compare(0, 2, "-j") == 0)
			max_active_jobs = atoi(arg.c_str() + 2);
		else if (arg.compare(0, 7, "--jobs=") == 0)
			max_active_jobs = atoi(arg.c_str() + 7);
		else
		{
			if (arg[0] == '-') usage(EXIT_FAILURE);
			if (arg.find('=') != std::string::npos)
			{
				std::istringstream in(arg);
				std::string name = read_word(in);
				if (name.empty() || !expect_token(in, Equal)) usage(EXIT_FAILURE);
				read_words(in, variables[name]);
				continue;
			}
			new_target:
			targets.push_back(arg);
			DEBUG << "New target: " << arg << '\n';
		}
	}

	init_working_dir();
	normalize_list(targets, working_dir, working_dir);

	if (indirect_targets)
	{
		load_dependencies(std::cin);
		string_list l;
		targets.swap(l);
		if (l.empty() && !dependencies.empty())
		{
			l.push_back(dependencies.begin()->second->targets.front());
		}
		for (string_list::const_iterator i = l.begin(),
		     i_end = l.end(); i != i_end; ++i)
		{
			dependency_map::const_iterator j = dependencies.find(*i);
			if (j == dependencies.end()) continue;
			dependency_t const &dep = *j->second;
			for (string_set::const_iterator k = dep.deps.begin(),
			     k_end = dep.deps.end(); k != k_end; ++k)
			{
				targets.push_back(normalize(*k, working_dir, working_dir));
			}
		}
		dependencies.clear();
	}

#ifdef WINDOWS
	WSADATA wsaData;
	if (WSAStartup(MAKEWORD(2,2), &wsaData))
	{
		std::cerr << "Unexpected failure while initializing Windows Socket" << std::endl;
		return 1;
	}
#endif

	// Run as client if REMAKE_SOCKET is present in the environment.
	if (char *sn = getenv("REMAKE_SOCKET")) client_mode(sn, targets);

	// Otherwise run as server.
	if (remakefile.empty())
	{
		remakefile = "Remakefile";
		init_prefix_dir();
	}
	normalize_list(targets, working_dir, prefix_dir);
	server_mode(remakefile, targets);
}

/** @} */
