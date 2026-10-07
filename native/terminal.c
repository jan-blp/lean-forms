#include <lean/lean.h>
#include <signal.h>
#include <stdlib.h>
#include "screen.h"

extern int32_t forms_ratatui_start(void);
extern int32_t forms_ratatui_stop(void);
extern int32_t forms_ratatui_key(void);
extern int32_t forms_ratatui_size(void);
extern const char *forms_ratatui_error(void);

static int active;
static volatile sig_atomic_t interrupted;
static struct sigaction old_term, old_hup, old_int;

static lean_obj_res error(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(forms_ratatui_error())));
}

static void restore(void) {
    if (!active) return;
    active = 0;
    forms_ratatui_stop();
    sigaction(SIGTERM, &old_term, NULL);
    sigaction(SIGHUP, &old_hup, NULL);
    sigaction(SIGINT, &old_int, NULL);
}

static void on_signal(int sig) {
    (void)sig;
    interrupted = 1;
}

LEAN_EXPORT lean_obj_res forms_terminal_start(void) {
    int32_t code = forms_ratatui_start();
    if (code < 0) return error();
    if (code == 0) return lean_io_result_mk_ok(lean_box(0));
    interrupted = 0;
    struct sigaction action = {0};
    action.sa_handler = on_signal;
    sigemptyset(&action.sa_mask);
    sigaction(SIGTERM, &action, &old_term);
    sigaction(SIGHUP, &action, &old_hup);
    sigaction(SIGINT, &action, &old_int);
    active = 1;
    atexit(restore);
    return lean_io_result_mk_ok(lean_box(1));
}

LEAN_EXPORT lean_obj_res forms_terminal_stop(void) {
    restore();
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res forms_terminal_key(void) {
    int32_t code = interrupted ? 7 : forms_ratatui_key();
    if (interrupted) code = 7;
    if (code < 0) return error();
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)code));
}

LEAN_EXPORT lean_obj_res forms_terminal_size(void) {
    int32_t code = forms_ratatui_size();
    if (code < 0) return error();
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)code));
}

static FormsString string_view(b_lean_obj_arg text) {
    return (FormsString){
        .data = (const uint8_t *)lean_string_cstr(text),
        .len = lean_string_size(text) - 1
    };
}

/* Only this shim knows Lean's object layout: ScreenField has two object
 * fields, ScreenEditor has three, and Option.some has one payload. */
LEAN_EXPORT lean_obj_res forms_terminal_draw(b_lean_obj_arg fields, size_t selected,
                                            b_lean_obj_arg editor) {
    size_t count = lean_array_size(fields);
    if (count > SIZE_MAX / sizeof(FormsField))
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Too many screen fields")));
    FormsField *rows = count ? malloc(count * sizeof(FormsField)) : NULL;
    if (count && !rows)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Cannot allocate screen fields")));
    for (size_t i = 0; i < count; ++i) {
        lean_object *field = lean_array_uget_borrowed(fields, i);
        rows[i] = (FormsField){
            .label = string_view(lean_ctor_get(field, 0)),
            .value = string_view(lean_ctor_get(field, 1))
        };
    }
    FormsString error_text;
    FormsEditor draft;
    FormsScreen screen = {
        .fields = rows,
        .field_count = count,
        .selected = selected,
        .editor = NULL
    };
    if (!lean_is_scalar(editor)) {
        lean_object *value = lean_ctor_get(editor, 0);
        lean_object *error_option = lean_ctor_get(value, 2);
        draft = (FormsEditor){
            .label = string_view(lean_ctor_get(value, 0)),
            .text = string_view(lean_ctor_get(value, 1)),
            .error = NULL
        };
        if (!lean_is_scalar(error_option)) {
            error_text = string_view(lean_ctor_get(error_option, 0));
            draft.error = &error_text;
        }
        screen.editor = &draft;
    }
    int32_t code = forms_ratatui_draw(&screen);
    free(rows);
    if (code < 0) return error();
    return lean_io_result_mk_ok(lean_box(0));
}
