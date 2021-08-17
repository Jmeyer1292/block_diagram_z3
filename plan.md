## Impl Plan

* How to model timers?
* Expand support to static calls
* Standard project "build files" and analysis.
  * Should "just work" on a few "real" projects.
  * Support parsing more complicated UDT/DBs so long as they aren't "USED"
  * Cleanup demo experience with a real project.

---

* Statics
  * FB blocks translated to UDTs and supported by project parsing
  * Associating "entry-point" FBs with their DBs automatically


## Not Supported (So Far)
 * Default memory initializers

## Bugs
 * Aliasing problems with function references (e.g. an inout variable pointing to the same symbol as a global access in the same function)

## Cleanups / Misc
 - Thread safety, reuse of components, udt archive global state
