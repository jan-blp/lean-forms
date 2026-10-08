#ifndef FORMS_INTERPRETER_H
#define FORMS_INTERPRETER_H
#include <stddef.h>
#include <stdint.h>
/* Input is borrowed for the call. Result/error strings are thread-local and
 * borrowed until the next run on this thread; the C shim copies them to Lean. */
int32_t forms_ratatui_run(const uint8_t *data, size_t len, int32_t (*interrupted)(void));
const char *forms_ratatui_result(void);
const char *forms_ratatui_error(void);
#endif
