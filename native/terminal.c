#include <lean/lean.h>
#include <signal.h>
#include "interpreter.h"

static volatile sig_atomic_t interrupted;
static void on_signal(int sig) { (void)sig; interrupted = 1; }
static int32_t is_interrupted(void) { return interrupted != 0; }

LEAN_EXPORT lean_obj_res forms_terminal_run(b_lean_obj_arg specification) {
    struct sigaction action = {0}, old_term, old_hup, old_int;
    action.sa_handler = on_signal;
    sigemptyset(&action.sa_mask);
    interrupted = 0;
    if (sigaction(SIGTERM, &action, &old_term) != 0)
        goto signal_error;
    if (sigaction(SIGHUP, &action, &old_hup) != 0) {
        sigaction(SIGTERM, &old_term, NULL);
        goto signal_error;
    }
    if (sigaction(SIGINT, &action, &old_int) != 0) {
        sigaction(SIGTERM, &old_term, NULL);
        sigaction(SIGHUP, &old_hup, NULL);
        goto signal_error;
    }
    int32_t code = forms_ratatui_run((const uint8_t *)lean_string_cstr(specification),
                                   lean_string_size(specification) - 1, is_interrupted);
    sigaction(SIGTERM, &old_term, NULL);
    sigaction(SIGHUP, &old_hup, NULL);
    sigaction(SIGINT, &old_int, NULL);
    if (code < 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(forms_ratatui_error())));
    return lean_io_result_mk_ok(lean_mk_string(forms_ratatui_result()));
signal_error:
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Cannot install terminal signal handlers")));
}
