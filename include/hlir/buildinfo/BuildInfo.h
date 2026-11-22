// Compile options of the code under analysis, taken from its build system: a Makefile (run as `make -n`, or parsed
// statically), a compile_commands.json, or a log of compiler invocations. Pure text logic, no clang: the result is a list
// of clang-style arguments (-I, -D, -U, -include, -isystem, -std=, ...) that the C frontend takes as LowerOptions.
//
// Running `make -n` executes whatever the Makefile executes outside recipes ($(shell ...), include-time rules, and recipes
// that call $(MAKE)); use the static mode on trees you do not trust.
#pragma once
#include <string>
#include <vector>

namespace hlir::buildinfo {

struct CompileCommand {
  std::string directory;             // working directory of the compiler invocation
  std::string file;                  // absolute path of the translation unit
  std::vector<std::string> args;     // every argument after the compiler name, shell-unquoted
  std::string origin;                // "make -n", "static Makefile", "compile_commands.json"
};

// What the frontend needs from a command: the relevant flags with relative paths made absolute.
struct FrontendFlags {
  std::vector<std::string> clangArgs;
  bool wrapSignedOverflow = false;   // -fwrapv / -fno-strict-overflow: signed overflow is defined, not undefined behaviour
  std::vector<std::string> warnings; // flags that cannot be honoured (e.g. -m32), dropped flags worth knowing about
  unsigned includeDirs = 0, defines = 0;
};

FrontendFlags frontendFlags(const CompileCommand &c);

// compile_commands.json (`command` or `arguments`, `directory`, `file`)
std::vector<CompileCommand> parseCompileCommands(const std::string &json, std::string &err);

// Output of `make -n [-w]` (or any log of compiler invocations): one command per compiler call; `cd dir &&` prefixes and
// "Entering directory" lines set the directory; ccache/distcc prefixes are skipped; ';' '&&' '||' '|' split commands.
std::vector<CompileCommand> parseMakeDryRun(const std::string &output, const std::string &startDir);

// Runs `make -n -B -k -w -C dir <args>` and returns its standard output (false + err if make cannot be run).
bool runMakeDryRun(const std::string &dir, const std::vector<std::string> &makeArgs, unsigned timeoutSeconds, std::string &output, std::string &err);

// A Makefile read without running anything: variable assignments (=, :=, ?=, +=), include, ifeq/ifneq/ifdef/ifndef, and the
// common functions (addprefix, patsubst, subst, strip, wildcard, filter-out, ...). The flags of every variable that holds
// compiler options apply to every source file listed in it (SRCS, SOURCES, OBJS, obj-y, ...) or to the files given.
// `warnings` explains what could not be evaluated ($(shell ...) is never executed).
std::vector<CompileCommand> parseMakefileStatic(const std::string &makefilePath, std::vector<std::string> &warnings);

// The compile commands of a project, looked up by source file.
class BuildDatabase {
 public:
  void add(std::vector<CompileCommand> cmds);
  // exact (symlink-resolved) path, else the unique command whose file shares the longest path suffix with `path`
  const CompileCommand *lookup(const std::string &path) const;
  // flags that apply to every file when the build system gave no per-file command (static Makefile without a source list)
  const CompileCommand *common() const { return common_.args.empty() && common_.directory.empty() ? nullptr : &common_; }
  std::vector<std::string> files() const;      // sorted, de-duplicated
  size_t size() const { return cmds_.size(); }

 private:
  std::vector<CompileCommand> cmds_;
  CompileCommand common_;
};

struct BuildSource {
  std::string makefile;              // a Makefile or the directory that holds one
  std::string target;                // optional make target (e.g. "modules", "all", an object file)
  std::vector<std::string> makeArgs; // extra make arguments (variables: M=drivers/x ARCH=x86)
  std::string mode = "dry-run";      // dry-run: run `make -n`; static: parse the Makefile without running anything
  std::string compileCommands;       // compile_commands.json
  unsigned timeoutSeconds = 300;
};

// Fills `db` from the build source; `notes` describes what was used (and falls back to static parsing when `make -n` gives
// nothing); false + err only when nothing usable was found.
bool loadBuildDatabase(const BuildSource &src, BuildDatabase &db, std::vector<std::string> &notes, std::string &err);

// shell-like word splitting (quotes, backslashes); exposed for tests
std::vector<std::string> shellSplit(const std::string &line);

}  // namespace hlir::buildinfo
