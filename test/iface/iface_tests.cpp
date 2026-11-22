// Tests for the interface-model reader (hlir/iface/Interface.h, DESIGN.md §22.357): the shipped models parse and
// mean what they say, and a mistake in one is REJECTED WITH A LINE NUMBER rather than silently ignored.
//
// Why the negative cases carry the weight here: an interface model is a small hand-written file that changes what
// every handler of that interface is assumed to receive. A typo that parses "successfully" would quietly weaken or
// distort the contract for a whole subsystem, with nothing in the scan output pointing back at it.
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/iface/Interface.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) {
  std::ifstream in(p);
  std::stringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

// parses `text`; on success `out` holds the file, on failure `err` holds the diagnostics
static bool parse(const std::string &text, iface::InterfaceFile &out, std::string &err) {
  Diagnostics d;
  bool ok = iface::parseInterfaceFile(text, "t.yaml", out, d);
  err = d.str();
  return ok;
}

// a minimal well-formed interface, with `extra` spliced in, so each negative case differs in exactly one way
static std::string wrap(const std::string &body) {
  return "version: 1\ninterfaces:\n  - interface: x\n    struct: y\n" + body;
}

int main() {
  // ---------------------------------------------------------------- the shipped Linux model
  {
    iface::InterfaceFile f;
    std::string err;
    CHECK(parse(slurp(std::string(HLIR_INTERFACES_DIR) + "/linux.yaml"), f, err), "models/interfaces/linux.yaml parses: " << err);
    const iface::InterfaceModel *m = f.byStruct("file_operations");
    CHECK(m, "the model is found by the vtable's struct tag");
    if (m) {
      CHECK(m->name == "file_operations", "interface name: " << m->name);
      // `.open` builds the session object every other slot receives; without that the contract says nothing.
      CHECK(m->sessionCtor == "open" && m->sessionDtor == "release" && m->sessionParam == "file",
            "session ctor/dtor/param: " << m->sessionCtor << "/" << m->sessionDtor << "/" << m->sessionParam);
      CHECK(m->prologue.size() == 1 && m->prologue[0] == "module_init",
            "module_init runs in full before any slot (DESIGN.md §22.357)");
      const iface::Slot *io = m->slot("unlocked_ioctl");
      CHECK(io && io->params.size() == 3, "unlocked_ioctl has three parameters");
      if (io && io->params.size() == 3) {
        // the three roles that make this contract worth having: the file is the kernel's, not the attacker's; the
        // command is the attacker's; and `arg` is a USERSPACE address, not a kernel pointer
        CHECK(io->params[0].role == iface::Role::Session, "filp is the session: " << iface::roleName(io->params[0].role));
        CHECK(io->params[1].role == iface::Role::Value, "cmd is attacker data: " << iface::roleName(io->params[1].role));
        CHECK(io->params[2].role == iface::Role::UserAddr, "arg is a user address: " << iface::roleName(io->params[2].role));
      }
      const iface::Slot *rd = m->slot("read");
      CHECK(rd, "read is a slot");
      if (rd) {
        const iface::ParamContract *buf = nullptr;
        for (auto &p : rd->params)
          if (p.name == "buf") buf = &p;
        CHECK(buf && buf->role == iface::Role::UserAddr && buf->dir == iface::Dir::Out && buf->sizeFrom == "count",
              "read's buf is a user address written by the callee, sized by count");
      }
      CHECK(m->slot("nonexistent") == nullptr, "an unknown slot name resolves to nothing");
    }
  }

  // ---------------------------------------------------------------- `size:` -- the real extent of a pointee
  //
  // A QNX resmgr handler is handed the receive buffer, of which `io_devctl_t` is only the 16-byte header; the
  // request payload starts right after it in the same allocation. Sized by its declared type, every handler in
  // that tree is out of bounds on its first payload access (models/interfaces/qnx_resmgr.yaml).
  {
    iface::InterfaceFile f;
    std::string err;
    CHECK(parse("version: 1\ninterfaces:\n  - interface: resmgr_io_funcs\n    struct: _resmgr_io_funcs\n"
                "    slots:\n      devctl: { params: { ctp: { role: kernel_owned }, "
                "msg: { role: value, dir: inout, size: { min: 2048, max: 2048 } }, ocb: { role: session } } }\n",
                f, err),
          "a contract may state a pointee's real byte count: " << err);
    const iface::InterfaceModel *m = f.byStruct("_resmgr_io_funcs");
    CHECK(m, "the resmgr io table is found by its struct tag");
    const iface::Slot *dc = m ? m->slot("devctl") : nullptr;
    CHECK(dc, "devctl is a slot");
    if (dc) {
      const iface::ParamContract *msg = nullptr, *ctp = nullptr;
      for (auto &p : dc->params) {
        if (p.name == "msg") msg = &p;
        if (p.name == "ctp") ctp = &p;
      }
      CHECK(msg && msg->sizeMin && msg->sizeMax && *msg->sizeMin == 2048 && *msg->sizeMax == 2048,
            "the receive buffer is 2048 bytes, fixed -- a RANGE would report an overrun whenever some size in it allows one");
      CHECK(msg && msg->dir == iface::Dir::InOut, "the handler writes its reply into the same buffer");
      // the size key is per-parameter: the context pointer keeps its declared extent
      CHECK(ctp && !ctp->sizeMin && !ctp->sizeMax, "a parameter without `size` is unaffected");
    }
  }

  // ---------------------------------------------------------------- a mistake must not parse
  struct Bad { const char *what; std::string body; };
  const Bad bad[] = {
      {"an unknown role", "    slots:\n      a: { params: { p: { role: nonsense } } }\n"},
      {"a parameter with no role", "    slots:\n      a: { params: { p: { dir: in } } }\n"},
      {"an unknown key", "    slotz: {}\n"},
      {"an unknown dir", "    slots:\n      a: { params: { p: { role: value, dir: sideways } } }\n"},
      {"size_from naming a parameter that is not there",
       "    slots:\n      a: { params: { p: { role: user_addr, size_from: missing } } }\n"},
      {"created_by naming something that is not a slot",
       "    session: { param: f, created_by: nope }\n    slots:\n      a: { params: { p: { role: value } } }\n"},
      {"a constructing slot that takes a session instead of producing one",
       "    session: { param: f, created_by: a }\n    slots:\n      a: { params: { f: { role: session } } }\n"},
      {"a constructing slot with no session_out",
       "    session: { param: f, created_by: a }\n    slots:\n      a: { params: { f: { role: kernel_owned } } }\n"},
      {"two session_out parameters in one slot",
       "    slots:\n      a: { params: { f: { role: session_out }, g: { role: session_out } } }\n"},
      {"no slots at all", "    label: untrusted\n"},
      // `size:` is the one key that can WIDEN an object, so a half-written one must not parse: taking the other
      // bound from the declaration is exactly the number the key exists to override.
      {"size with only a min", "    slots:\n      a: { params: { p: { role: value, size: { min: 16 } } } }\n"},
      {"size with only a max", "    slots:\n      a: { params: { p: { role: value, size: { max: 2048 } } } }\n"},
      {"size.min above size.max", "    slots:\n      a: { params: { p: { role: value, size: { min: 64, max: 16 } } } }\n"},
      {"size that is not a mapping", "    slots:\n      a: { params: { p: { role: value, size: 2048 } } }\n"},
      {"an unknown key inside size", "    slots:\n      a: { params: { p: { role: value, size: { min: 1, max: 2, exact: 3 } } } }\n"},
      {"size and size_from both stating one length",
       "    slots:\n      a: { params: { p: { role: value, size_from: n, size: { min: 1, max: 2 } }, n: { role: value } } }\n"},
  };
  for (auto &b : bad) {
    iface::InterfaceFile f;
    std::string err;
    CHECK(!parse(wrap(b.body), f, err), "rejected: " << b.what);
    CHECK(err.find(":") != std::string::npos, "the diagnostic for " << b.what << " carries a location: " << err);
  }
  {  // two interfaces may not claim the same vtable struct: the lookup is by tag, so one would shadow the other
    iface::InterfaceFile f;
    std::string err;
    CHECK(!parse("version: 1\ninterfaces:\n  - { interface: a, struct: dup, slots: { s: { params: { p: { role: value } } } } }\n"
                 "  - { interface: b, struct: dup, slots: { s: { params: { p: { role: value } } } } }\n",
                 f, err),
          "rejected: two interfaces claiming one struct tag");
  }
  {  // the version is a contract of its own: an unknown one must not be read as if it were version 1
    iface::InterfaceFile f;
    std::string err;
    CHECK(!parse("version: 2\ninterfaces: []\n", f, err), "rejected: an unsupported version");
    CHECK(!parse("interfaces: []\n", f, err), "rejected: a file with no version");
  }

  std::cout << "iface_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}
