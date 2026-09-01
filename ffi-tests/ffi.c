#include <lean/lean.h>

LEAN_EXPORT lean_object* lp_ffi_answer(void) {
  return lean_io_result_mk_ok(lean_box_uint32(37));
}
