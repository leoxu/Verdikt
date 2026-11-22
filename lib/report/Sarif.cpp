// SARIF 2.1.0 (https://docs.oasis-open.org/sarif/sarif/v2.1.0/). Confirmed findings are results of level "error";
// findings the replay could not reproduce are level "note" with the reason; verdict, assumptions and incompleteness go into
// run/invocation properties so a consumer can judge how far to trust a clean run.
#include <set>

#include "Json.h"
#include "hlir/report/Report.h"

namespace hlir::report {

std::string toSarif(const Report &r) {
  Json j;
  j.beginObject().str("$schema", "https://json.schemastore.org/sarif-2.1.0.json").str("version", "2.1.0").beginArray("runs");
  // one SARIF run per entry keeps assumptions and verdicts attached to the entry they belong to
  for (auto &e : r.entries) {
    j.beginObject();
    j.beginObject("tool").beginObject("driver").str("name", r.tool).str("version", r.version)
        .str("informationUri", "https://example.invalid/hlir");
    std::set<std::string> rules;
    for (auto &f : e.findings) rules.insert(f.kind);
    j.beginArray("rules");
    for (auto &k : rules)
      j.beginObject().str("id", k).beginObject("shortDescription").str("text", "undefined behaviour or assertion failure: " + k).endObject().endObject();
    j.endArray().endObject().endObject();
    j.beginArray("results");
    for (auto &f : e.findings) {
      bool confirmed = f.replay != ReplayStatus::NotReproduced;
      j.beginObject().str("ruleId", f.kind).str("level", f.warning ? "warning" : confirmed ? "error" : "note");
      j.beginObject("message").str("text", f.message + (confirmed ? "" : " [not reproduced by replay: " + f.unconfirmedReason + "]")).endObject();
      if (f.loc.valid()) {
        j.beginArray("locations").beginObject().beginObject("physicalLocation");
        j.beginObject("artifactLocation").str("uri", f.loc.file).endObject();
        j.beginObject("region").num("startLine", f.loc.line).num("startColumn", f.loc.col ? f.loc.col : 1).endObject();
        j.endObject();
        j.beginArray("logicalLocations").beginObject().str("name", f.function).str("kind", "function").endObject().endArray();
        j.endObject().endArray();
      }
      j.beginObject("partialFingerprints").str("hlir/v1", f.id).endObject();
      j.beginObject("properties").str("replay", replayStatusName(f.replay)).str("engine", f.engine).str("op", f.op).str("origin", f.origin);
      j.beginArray("counterexample");
      for (auto &w : f.witness) j.beginObject().str("name", w.name).str("value", w.value).endObject();
      j.endArray().endObject().endObject();
    }
    j.endArray();
    j.beginArray("invocations").beginObject().boolean("executionSuccessful", e.incomplete.empty());
    j.beginArray("toolExecutionNotifications");
    for (auto &i : e.incomplete)
      j.beginObject().str("level", "warning").beginObject("message").str("text", i.code + ": " + i.detail).endObject().endObject();
    j.endArray().endObject().endArray();
    j.beginObject("properties").str("entry", e.function).str("verdict", verdictName(e.verdict)).str("spec", e.specFile);
    j.beginArray("assumptions");
    for (auto &a : e.assumptions) j.beginObject().str("category", a.category).str("text", a.text).endObject();
    j.endArray().endObject().endObject();
  }
  j.endArray().endObject();
  return j.str();
}

}  // namespace hlir::report
