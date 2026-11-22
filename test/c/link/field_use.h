/* Shared by field_use_entry.c and field_use_body.c: mirrors the real-world drm_core_check_all_features() shape
   (dev->driver->driver_features, include/drm/drm_drv.h:522) that the DRM/amdgpu scan hit after the container_of fix.
   `target` is only ever read inside field_use_body.c's functions; field_use_entry.c's own AST never mentions it, so
   a per-unit used-fields check cannot see it is used at all -- only the --link whole-program view can. */
struct inner { int val; char tag[4]; };
struct outer { struct inner *target; };
