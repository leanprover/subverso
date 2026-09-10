#include <lean/lean.h>

LEAN_EXPORT lean_obj_res foo(void) {
  return lean_io_result_mk_ok(lean_box_uint32(37));
}
