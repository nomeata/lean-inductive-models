#include <signal.h>
#include <stdint.h>
#include <stdlib.h>

/* Test-only: terminate the calling synthetic worker with a real native signal. */
void *modelgen_test_raise_signal(uint32_t selector) {
    int signal = selector == 0 ? SIGTERM : SIGSEGV;
    raise(signal);
    /* Returning an IO object is impossible after a successful raise. If the
       platform refuses it, leave a native status for the supervisor anyway. */
    _Exit(127);
}
