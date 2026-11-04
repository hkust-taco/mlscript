Resolver retention after merging hkmc2
2026-11-04

The experiment compares the retained cleanups with a matched control on the
current upstream compiler and full ctest corpus. It does not compare a new run
with the October timings to estimate the effect of the cleanups.

The merged implementation is 173fb9cd4dcbc538f76fc8c1f9bb589cfafe04dc.
It merges upstream 6a2b58bff0e56ccba907a72fdafad4ac4c89feae into the
pre-merge retention branch f155de27f6c0644fba5fcb8dad5842068b010f8a.
The control merges the same upstream into the namespace-only ancestor
fea7071d25d9a5494f6fc915632840ca3b2de3e2, before the retention changes.
Both contain the same namespace/upstream semantic conflict resolutions.
The control has none of the retention cleanups, interface pruning, or pruning
ownership tracking. The merged implementation keeps the nine cleanup stages;
pruning and its tracking machinery remain removed.

Validation and semantic integration

hkmc2AllTests/test passed after the semantic merge corrections on 2026-11-04
(67 seconds). The earlier complete merge run also passed (103 seconds).
Both JVM and Scala.js compile. All existing behavior tests remain, with the
regenerated golden outputs committed in the merge. The whole PR source/test
diff was checked for isolated whitespace changes; an older accidental
indentation change in a projection callback was removed.

The merge combines upstream builtin-operator result inference and arity
selection with the standalone resolver, preserves wrapped async/generator
results and namespace-sensitive callable identity, and integrates eager
wildcard-union misses into the common namespace/wildcard lookup path.
Upstream's exposed-open-member table and pending wildcard misses reside in the
temporary workspace, preserving their required erasure/block lifetimes.
The existing reference-walk test now exercises builtin-result callbacks and
an imported open-class override without retaining compilation services or
mutating a completed exporter's graph.

One automatic merge needed an additional correction: upstream projects a
transported type's substitution before interning, while the namespace branch
separates the published semantic type from its observation-specific view.
Both the intern key and published semantic type must use the projected value.
The extended growth regression fails against the uncorrected merge (103
retained instances where only 3 are relevant) and passes after correction.
The control includes this same correction.

Protocol

The harness and driver are unchanged from the earlier full-ctest experiment:
hkmc2Benchmarks/src/test/scala/hkmc2/ResolverSuiteBenchmark.scala and
hkmc2Benchmarks/bench_resolver_suite.py. Every registered ctest case runs in
sorted name order, sequentially, using its actual ScalaTest body and checks.
The current corpus contains 59 cases, compared with 58 in October.
Each full suite has a fresh CompilerCtx shared across its cases, including
prelude/runtime compilation, imports, lowering/optimization, finalization,
and JavaScript writes. SBT startup and execution of generated programs are
outside the measurements. Own build commands completed before sampling.
Other development JVMs remained on the machine.

The first timing attempt was interrupted when an unrelated Scala CLI Bloop
JVM was observed using 380.5% CPU, alongside the benchmark's 99.0%. The two
completed forks and interrupted third fork remain under timing-interrupted/;
none enter the reported timing/allocation summary. The whole timing protocol
was restarted after that work became idle, rather than filtering individual
slow samples. Process snapshots every 15 seconds accompany the replacement run. The
other compiler resumed intermittently, so the final timing interpretation
must account for the recorded host activity. The first attempt used the
workspace execution sandbox; the replacement ran with host access to collect
process statistics. Both variants use the same execution environment within
each attempt; timings across attempts are not a controlled comparison.

JDK 21.0.8, Scala 3.8.4, macOS 26.7.1 arm64.
  -Xms1g -Xmx1g -Xss8m -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xbatch

One benchmark JVM runs at a time, with serial GC and foreground JIT. The JVM
sees one processor; macOS still controls physical core placement. This is not
physical CPU affinity. Both variants use frozen identical harness/dependency
classes; only the main compiler JAR differs. The driver checks compiler JAR
hashes, the source corpus hash, and exact test ordering for every fork.

Timing/allocation: three fresh JVM forks per variant, 12 complete-suite
warmups and eight measured suites per fork. No explicit GC occurs during
these batches. Allocation uses the JVM-wide allocated-byte counter, including
terminated threads. Wall time, process CPU, GC and JIT counters are retained
for every warmup and measured batch. Summaries use the median of the three
fork means, with all fork ranges reported; no samples are filtered.
The schedule uses the original seed 582. With two variants, it happens to
put the retained implementation before the control in all three rounds;
it is interleaved but not counterbalanced.

Retained heap: separate fresh JVMs, three per variant, one complete suite
each, adding -XX:MarkSweepAlwaysCompactCount=1. Fully compacting post-GC
heap-pool collection snapshots are read with the context held and then
released; a weak reference must confirm collection. Current-heap/TLAB or
uncollected-garbage readings do not estimate retained session memory.
Heap forks ran before the timing forks; no heap sampling perturbs timing.

Results and interpretation

MiB = 1,048,576 bytes. Times and allocations are medians of the three fork
means; retained heap is the median of three separate held/released pairs.

Variant                      Observed s*  CPU s*   Allocated MiB  Retained MiB
Same-upstream control             6.653   6.654         11516.7         518.2
Retained cleanups                 6.210   6.210          9099.6         485.8
Difference                        -6.7%   -6.7%         -21.0%         -6.2%

* Timing is affected by concurrent host activity. An unrelated Scala CLI
Bloop JVM reached 399.1% CPU during a measured interval of the cleanup run;
control measurements also overlapped competing compilation. The process
snapshots are in timing-host-activity.jsonl. All replacement-run samples
remain included. These are observed timings, not an established speedup.
The earlier claim of roughly unchanged speed cannot be cleanly revalidated
under this interference. A quiet or isolated host is needed for that check.

Fork-mean ranges:
  Control: 6.541-6.689 s; 11516.6-11517.9 MiB allocated.
  Cleanups: 6.147-6.288 s; 9099.6-9126.5 MiB allocated.
The memory counters belong to the benchmark JVM, independently of the other
processes. Allocation remains substantially lower in every pair. Separate
retained-heap measurements agree across forks to within 72 bytes for the
cleanup variant and exactly for the control. Small differences in allocation
between forks can still reflect JIT optimization; the full ranges are saved.

The retained-heap benefit survives: 518.185 -> 485.804 MiB saves 32.381 MiB,
compared with 349.7 -> 315.3 MiB (34.4 MiB) in October. The absolute saving is
similar, while its percentage falls from 9.8% to 6.2% against the larger
current baseline. The current compiler/corpus retains more memory in both
variants; this comparison does not isolate which upstream changes caused it.
The allocation benefit is larger: about 21.0% now, compared with 3.0% in the
original experiment. This measures the combined retained cleanups; individual
stages were not re-benchmarked, so it does not attribute that increase to a
particular cleanup or upstream change.

The result supports retaining the simpler lifetime/cache cleanups. It does
not re-evaluate the discarded interface-pruning implementation: its earlier
cost/benefit figures remain historical results on the old compiler/corpus.
No pruning or body-ownership bookkeeping has been reintroduced.


Reproduction

1. Check out merged commit 173fb9cd4 and run hkmc2AllTests/test, then export
   hkmc2Benchmarks / Test / fullClasspath from SBT into classpath.txt.
   The compiled common test/harness classes must come from this checkout.

2. Reconstruct the control in a temporary directory. Use git merge-tree
   --write-tree --name-only with the full namespace and upstream revisions
   listed above. Its nonzero exit status is expected: the first output line
   is the tree containing five conflicted files. Extract that tree with
   git archive into the temporary directory, then run:

     python3 resolve-control.py <control-directory>

   The script combines the namespace and upstream changes, including the
   projected semantic transport fix. Its five resolved files were checked
   byte-for-byte against the compiler source used in this experiment.
   Run hkmc2JVM/compile in the control directory. Its tests need not be
   compiled: the experiment uses the merged checkout's common harness.

3. Archive each variant's hkmc2/jvm/target/scala-3.8.4/classes directory as
   phase-00.jar (control) or phase-01.jar (merged) in a build directory.
   Copy the exported classpath.txt there. Make a builds.json list following
   the recorded builds.json, with each newly built JAR's SHA-256. Build
   paths, class metadata and ZIP timestamps may change binary hashes;
   the recorded compiler-source hashes identify the source inputs.
   Those hashes cover sorted shared/src/main Scala paths, then sorted
   jvm/src/main Scala paths, each repository-relative path plus NUL followed
   by its bytes. Source roots are under hkmc2/.

4. Stop active SBT compilation/tests and run from the merged checkout:

     python3 hkmc2Benchmarks/bench_resolver_suite.py heap <checkout> <builds> <heap-output>
     python3 hkmc2Benchmarks/bench_resolver_suite.py timing <checkout> <builds> <timing-output>

   Output directories must not exist. Only the compiler JAR is swapped;
   the driver freezes common class directories automatically. The same
   checkout supplies all 59 source cases for both variants.

5. Summarize with the existing report script:

     python3 hkmc2Benchmarks/results/resolver-ctest-2026-10-26/summarize.py <timing-output> <heap-output>/retained-heap.csv

Files in this report retain the source/build provenance, raw timing and heap
samples, corpus manifest, per-fork summaries, run schedule, and metadata.
Compressed process logs contain every case invocation. The large compiler
and common-harness JARs are omitted; their hashes remain in the metadata.
The merge and benchmark report are separate commits.

