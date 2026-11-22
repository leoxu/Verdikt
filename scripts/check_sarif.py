#!/usr/bin/env python3
"""Structural check of a SARIF 2.1.0 file produced by hlir-taint (no jsonschema dependency)."""
import json, sys

def fail(msg):
    print("SARIF check failed:", msg)
    sys.exit(1)

doc = json.load(open(sys.argv[1]))
if doc.get("version") != "2.1.0": fail("version")
if not isinstance(doc.get("runs"), list) or not doc["runs"]: fail("runs")
for run in doc["runs"]:
    drv = run.get("tool", {}).get("driver", {})
    if not drv.get("name"): fail("tool.driver.name")
    rules = {r["id"] for r in drv.get("rules", [])}
    for res in run.get("results", []):
        if res.get("ruleId") not in rules: fail("result ruleId not declared in tool.driver.rules")
        if res.get("level") not in ("error", "warning", "note", "none"): fail("level")
        if not res.get("message", {}).get("text"): fail("message.text")
        for loc in res.get("locations", []):
            pl = loc.get("physicalLocation", {})
            if not pl.get("artifactLocation", {}).get("uri"): fail("artifactLocation.uri")
            if pl.get("region", {}).get("startLine", 0) < 1: fail("region.startLine")
        if "hlir/v1" not in res.get("partialFingerprints", {}): fail("partialFingerprints")
    inv = run.get("invocations", [])
    if not inv or "executionSuccessful" not in inv[0]: fail("invocations[0].executionSuccessful")
    props = run.get("properties", {})
    if props.get("verdict") not in ("bug", "safe_under_assumptions", "unknown"): fail("properties.verdict")
print("SARIF OK:", sum(len(r.get("results", [])) for r in doc["runs"]), "result(s)")
