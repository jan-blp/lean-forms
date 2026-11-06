#include <lean/lean.h>
#include <string>
#include <cstdlib>
#include <malloc.h>

extern "C" lean_object * json_evaluate(lean_object *, lean_object *, lean_object *);
extern "C" lean_object * json_evaluate_typed(lean_object *, lean_object *, lean_object *);
extern "C" lean_object * json_check(lean_object *, lean_object *, lean_object *);
extern "C" lean_object * runtime_initialize_lean_x2dforms_JsonEval(uint8_t);

extern "C" void json_init() {
    static bool initialized = false;
    if (initialized) return;
    lean_object * result = runtime_initialize_lean_x2dforms_JsonEval(1);
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        abort();
    }
    lean_dec_ref(result);
    lean_io_mark_end_initialization();
    initialized = true;
}

// Test instrumentation; allocation and initialization use the stock Lean runtime.
extern "C" unsigned wasm_allocated_bytes() { return mallinfo().uordblks; }

// Explicit lengths preserve embedded NULs, which the JSON parser must reject
// rather than silently truncating a malformed request. The response is JSON text.
using Runner = lean_object * (*)(lean_object *, lean_object *, lean_object *);

static const char * run(Runner evaluate, const char * schema, size_t schema_len,
                                 const char * expression, size_t expression_len,
                                 const char * value, size_t value_len) {
    static std::string response;
    lean_object * result = evaluate(
        lean_mk_string_from_bytes(schema, schema_len),
        lean_mk_string_from_bytes(expression, expression_len),
        lean_mk_string_from_bytes(value, value_len));
    response.assign(lean_string_cstr(result), lean_string_size(result) - 1);
    lean_dec(result);
    return response.c_str();
}

extern "C" const char * json_run(const char * schema, size_t schema_len,
                                 const char * expression, size_t expression_len,
                                 const char * value, size_t value_len) {
    return run(json_evaluate, schema, schema_len, expression, expression_len, value, value_len);
}

extern "C" const char * json_run_typed(const char * schema, size_t schema_len,
                                       const char * expression, size_t expression_len,
                                       const char * value, size_t value_len) {
    return run(json_evaluate_typed, schema, schema_len, expression, expression_len, value, value_len);
}

extern "C" const char * json_run_checker(const char * schema, size_t schema_len,
                                         const char * checker, size_t checker_len,
                                         const char * value, size_t value_len) {
    return run(json_check, schema, schema_len, checker, checker_len, value, value_len);
}
