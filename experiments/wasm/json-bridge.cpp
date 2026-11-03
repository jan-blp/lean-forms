#include <lean/lean.h>
#include <string>

extern "C" lean_object * json_evaluate(lean_object *, lean_object *, lean_object *);
extern "C" lean_object * json_evaluate_typed(lean_object *, lean_object *, lean_object *);
extern "C" void wasm_runtime_init();
extern "C" void json_initialize_constants();

extern "C" void json_init() {
    static bool initialized = false;
    if (initialized) return;
    wasm_runtime_init();
    json_initialize_constants();
    initialized = true;
}

// Explicit lengths preserve embedded NULs, which the JSON parser must reject
// rather than silently truncating a malformed request. The response is JSON text.
static const char * run(bool typed, const char * schema, size_t schema_len,
                                 const char * expression, size_t expression_len,
                                 const char * value, size_t value_len) {
    static std::string response;
    lean_object * result = (typed ? json_evaluate_typed : json_evaluate)(
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
    return run(false, schema, schema_len, expression, expression_len, value, value_len);
}

extern "C" const char * json_run_typed(const char * schema, size_t schema_len,
                                       const char * expression, size_t expression_len,
                                       const char * value, size_t value_len) {
    return run(true, schema, schema_len, expression, expression_len, value, value_len);
}
