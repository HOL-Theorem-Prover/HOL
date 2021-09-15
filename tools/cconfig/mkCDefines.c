#include <stdio.h>
#include <sys/ioctl.h>

int main(void)
{
  printf("structure CDefines =\nstruct\n");
  printf("  val TIOCGWINSZ = %lu\n", TIOCGWINSZ);
  printf("end\n");
  return 0;
}
