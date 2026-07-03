#include <lean/lean.h>

#if defined(_WIN32)
#define SUBVERSO_FFI_EXPORT __declspec(dllexport)
#elif defined(__GNUC__) || defined(__clang__)
#define SUBVERSO_FFI_EXPORT __attribute__((visibility("default")))
#else
#define SUBVERSO_FFI_EXPORT
#endif

SUBVERSO_FFI_EXPORT lean_object* lp_ffi_answer(void) {
  return lean_io_result_mk_ok(lean_box_uint32(37));
}
