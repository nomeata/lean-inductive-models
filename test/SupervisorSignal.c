#include <signal.h>
#include <stdint.h>
#include <stdlib.h>

/* Test-only: terminate the calling synthetic worker with a real native signal. */
void *modelgen_test_raise_signal(uint32_t selector) {
    int sig = selector == 0 ? SIGTERM : SIGSEGV;
    /* Lean installs a SIGSEGV handler, so restore the native disposition this
       helper is meant to exercise before delivering the selected signal. */
    if (signal(sig, SIG_DFL) != SIG_ERR)
        raise(sig);
    /* Returning an IO object is impossible after successful delivery. If the
       platform refuses the reset or raise, leave a native status anyway. */
    _Exit(127);
}
