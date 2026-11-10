#include <lean/lean.h>
#include <string>
#include <cstdlib>

extern "C" lean_object * forms_handle_request(lean_object *);
extern "C" lean_object * runtime_initialize_lean_x2dforms_WasmEntry(uint8_t);

extern "C" void forms_init() {
    static bool initialized = false;
    if (initialized) return;
    lean_object * result = runtime_initialize_lean_x2dforms_WasmEntry(1);
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        abort();
    }
    lean_dec_ref(result);
    lean_io_mark_end_initialization();
    initialized = true;
}

extern "C" const char * forms_request(const char * request, size_t request_len) {
    lean_object * result = forms_handle_request(lean_mk_string_from_bytes(request, request_len));
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        abort();
    }
    lean_object * value = lean_io_result_get_value(result);
    static std::string response;
    response.assign(lean_string_cstr(value), lean_string_size(value) - 1);
    lean_dec_ref(result);
    return response.c_str();
}
