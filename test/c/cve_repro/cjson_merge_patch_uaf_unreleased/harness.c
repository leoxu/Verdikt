// Harness for the heap-use-after-free in merge_patch (cJSON_Utils.c, fixed on master commit
// 6d9f2443ab071f86e5d9b43025a40929ec41c46c, "Fix: heap-use-after-free in merge_patch when patch is subtree of
// target (#1065)", NOT YET in any tagged release -- still present in v1.7.19, the latest release at the time of
// this scan). No attacker-controlled input at all: this is a pure API-misuse / aliasing bug, reproduced exactly
// the way the fix commit's own regression test does it -- `patch` is obtained as a child of `target` itself
// (a subtree, i.e. an aliased pointer into target's own tree), then handed to cJSONUtils_MergePatch(target,
// patch): merge_patch's non-object branch calls cJSON_Delete(target) BEFORE cJSON_Duplicate(patch, 1), freeing
// the memory patch itself points into before it's read.
#include "cJSON.h"
#include "cJSON_Utils.h"

void merge_patch_uaf_entry(void) {
  cJSON *target = cJSON_CreateObject();
  cJSON *arr = cJSON_CreateArray();
  cJSON_AddItemToArray(arr, cJSON_CreateNumber(1));
  cJSON_AddItemToArray(arr, cJSON_CreateNumber(2));
  cJSON_AddItemToArray(arr, cJSON_CreateNumber(3));
  cJSON_AddItemToObject(target, "a", arr);
  cJSON *patch = cJSON_GetObjectItem(target, "a");  // patch is a subtree of target (aliased, not independent)
  cJSON *result = cJSONUtils_MergePatch(target, patch);
  cJSON_Delete(result);
}
