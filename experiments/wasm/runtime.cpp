#include <lean/lean.h>
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include <malloc.h>

// A deliberately restricted, single-threaded runtime: pure data and arithmetic only.
// No Lean IO or tasks. Each experiment handles its own Lean-level initialization.
extern "C" void wasm_runtime_init() {
    static bool initialized = false;
    if (initialized) return;
    initialized = true;
    lean::initialize_alloc();
    lean::initialize_debug();
    lean::initialize_object();
    lean::initialize_thread();
}

// The core runtime references this normally Lean-defined diagnostic function.
// Route it to Emscripten's stderr rather than linking Init.System.IO and its OS IO.
extern "C" lean_object * lean_io_eprintln(lean_object * message) {
    fputs(lean_string_cstr(message), stderr);
    fputc('\n', stderr);
    lean_dec(message);
    return lean_io_result_mk_ok(lean_box(0));
}

// Test instrumentation: live bytes reported by Emscripten's dlmalloc allocator.
extern "C" unsigned wasm_allocated_bytes() { return mallinfo().uordblks; }
