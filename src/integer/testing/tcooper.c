#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <signal.h>

#include <stdlib.h>
#include <stdio.h>

pid_t childpid;

void kill_child_exit(int ignored)
{
  kill(childpid, SIGKILL);
  exit(1);
}


int main(int argc, char *argv[])
{
  char *logfile;
  int timeout = argc > 3 ? atoi(argv[3]) : 5;
  int pipe_fds[2];
  if (argc < 3) {
    fprintf(stderr, "Usage: %s dp-program logfile [timeout]\n", argv[0]);
    exit(1);
  }
  logfile = argv[2];
  if (timeout <= 0) {
    fprintf(stderr, "Timeout must be positive non-zero\n");
    exit(1);
  }

  if (pipe(pipe_fds) != 0) {
    perror("Creating pipe in main");
    exit(1);
  }
  childpid = fork();
  if (childpid < 0) {
    perror("forking in main");
    exit(1);
  }
  if (childpid == 0) {
    /* in child */
    /* want to write stdout to pipe, stderr to log file */
    /* stdin must be the file test_coopers.sml */
    int logfile_fd;
    char *child_args[2] = {argv[1], 0};
    if (dup2(pipe_fds[1], STDOUT_FILENO) == -1) {
      perror("dup2 for stdout in child");
      exit(1);
    }
    close(STDIN_FILENO);
    logfile_fd = open(logfile, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (logfile_fd == -1) {
      perror("child opening logfile");
      exit(1);
    }
    if (dup2(logfile_fd, STDERR_FILENO) == -1) {
      perror("dup2 for stderr in child");
      exit(1);
    }
    /* can now exec hol */
    execv(child_args[0], child_args);
    perror("exec in child");
    exit(1);
  } else {
    /* in parent */
    fd_set to_watch;
    struct timeval tv;
    char buffer[80];
    int numread, read_anything = 0;
    signal(SIGINT, kill_child_exit);
    FD_ZERO(&to_watch);
    FD_SET(pipe_fds[0], &to_watch);
    select(pipe_fds[0] + 1, &to_watch, 0, 0, &tv);
    while (1) {
      int retval;
      FD_SET(pipe_fds[0], &to_watch);
      /* need to do this potentially redundant assignment to tv because
         select leaves the value of tv undefined */
      tv.tv_sec = timeout;
      tv.tv_usec = 0;
      retval = select(pipe_fds[0] + 1, &to_watch, 0, 0, &tv);
      if (retval == -1) {
        perror("select in parent");
        exit(1);
      }
      if (retval == 0) {
        /* nothing new to read - maybe the child has exited,
           otherwise interrupt the child */
        int status, wait_retval;
        wait_retval = waitpid(childpid, &status, WNOHANG);
        if (wait_retval == 0) {
          if (read_anything) {
            /* child still fine, interrupt it to wake it up */
            if (kill(childpid, SIGINT) == -1) {
              perror("kill in parent");
              exit(1);
            }
          }
          continue;
        } else if (wait_retval < 0) {
          perror("parent waiting");
          exit(1);
        }
        if (WIFEXITED(status)) {
          fprintf(stderr, "Child exited with code %d\n", WEXITSTATUS(status));
          exit(1);
        } else /* (WIFSIGNALLED(status)) is true */ {
          fprintf(stderr, "Child was stopped by signal %d\n",
                  WTERMSIG(status));
          exit(1);
        }
      }
      /* retval was one */
      numread = read(pipe_fds[0], buffer, 80);
      if (numread < 0) {
        if (errno == EINTR) continue;
        perror("read in parent");
        exit(1);
      }
      if (numread == 0) { exit(0); }
      read_anything = 1;
      write(STDOUT_FILENO, buffer, numread);
    }
  }
}





