#ifndef FORMS_SCREEN_H
#define FORMS_SCREEN_H
#include <stddef.h>
#include <stdint.h>

/* All pointers are borrowed and valid only during forms_ratatui_draw.
 * Strings are UTF-8 byte spans (length excludes the trailing NUL).
 * NULL editor/error means absent; a present empty string is distinct.
 * fields may be NULL only when field_count is zero. Rust retains no pointers. */
typedef struct {
    const uint8_t *data;
    size_t len;
} FormsString;

typedef struct {
    FormsString label;
    FormsString value;
} FormsField;

typedef struct {
    FormsString label;
    FormsString text;
    const FormsString *error;
} FormsEditor;

typedef struct {
    const FormsField *fields;
    size_t field_count;
    size_t selected;
    const FormsEditor *editor;
} FormsScreen;

int32_t forms_ratatui_draw(const FormsScreen *screen);
#endif
