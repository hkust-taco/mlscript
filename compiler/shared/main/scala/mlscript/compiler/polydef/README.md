The goal of Polydef is to provide defunctionalization with
incremental on-the-fly analysis that updates when
new nodes are added (e.g. through macro expansion)

Incremental breakdown of to-do tasks:
* Create mutable pattern match term to allow for incremental updates
* Add unique ids to mlscript terms to track references
* Implement and adapt simple-sub for control-flow-analysis (with reference to lumberhack)